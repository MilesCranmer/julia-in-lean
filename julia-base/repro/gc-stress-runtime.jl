# Runtime stress for Julia master bbfa0ce4150. Inputs are deterministic; scheduling is not.
# src/clangsa checks C rooting and safepoint discipline. These workloads exercise
# GC phase transitions, task stacks, finalizer recursion and remembered-set lifetime.
using Libdl

mutable struct StressCell
    tag::UInt64
    child::Any
    bytes::Vector{UInt8}
end

mix(x::UInt64) = (x ⊻ (x >> 30)) * 0xbf58476d1ce4e5b9
step(x::UInt64) = mix(x + 0x9e3779b97f4a7c15)
cell(tag::UInt64, size::Int) = StressCell(tag, nothing, fill(UInt8(tag & 0xff), size))
valid(x::StressCell) = all(==(UInt8(x.tag & 0xff)), x.bytes)
check(x::StressCell) = valid(x) || error("GC_STRESS_INVARIANT payload tag=$(x.tag)")

function allocation_worker(seed, rounds)
    roots = [cell(step(seed + UInt64(i)), 64) for i in 1:128]
    state = seed
    for round in 1:rounds
        for i in 1:512
            state = step(state)
            size = i % 32 == 0 ? 32768 + Int(state & 0x1fff) : 16 + Int(state & 0x7ff)
            roots[mod1(i, length(roots))] = cell(state, size)
        end
        round % 4 == 0 && GC.gc(round % 8 == 0)
        foreach(check, roots)
        yield()
    end
    return xor(roots[1].tag, roots[end].tag)
end

function finalizer_worker(seed, rounds, calls, failures)
    retained = StressCell[]
    slots = Ref{Any}[]
    for round in 1:rounds, i in 1:64
        tag = step(seed + UInt64(64 * round + i))
        slot = Ref{Any}(nothing)
        push!(slots, slot)
        x = cell(tag, 32 + Int(tag & 0xff))
        finalizer(x) do target
            valid(target) || Threads.atomic_add!(failures, 1)
            temporary = cell(step(target.tag), 256)
            nested = cell(step(temporary.tag), 64)
            finalizer(nested) do inner
                valid(inner) || Threads.atomic_add!(failures, 1)
                Threads.atomic_add!(calls, 1)
            end
            GC.gc(false)
            finalize(nested)
            valid(temporary) || Threads.atomic_add!(failures, 1)
            slot[] = target
            Threads.atomic_add!(calls, 1)
        end
        if iseven(i)
            push!(retained, x)
        end
        if i % 16 == 0
            GC.gc(false)
        end
    end
    for x in retained
        finalize(x)
        check(x)
    end
    GC.gc(true)
    for slot in slots
        x = slot[]
        x === nothing || check(x)
    end
    return length(retained)
end

function task_worker(seed)
    roots = [cell(step(seed + UInt64(i)), 128 + i) for i in 1:32]
    threads = Set([Threads.threadid()])
    for iteration in 1:16
        child = Threads.@spawn cell(step(seed + UInt64(iteration)), 4096)
        yield()
        push!(threads, Threads.threadid())
        check(fetch(child))
        iteration % 4 == 0 && GC.gc(false)
        foreach(check, roots)
    end
    return roots, length(threads) > 1
end

# After this function returns, each young cell is reachable through an old parent.
@noinline function rewrite!(parent, slots, seed)
    fresh = Any[cell(step(seed + UInt64(i)), 32 + i) for i in eachindex(slots)]
    copyto!(slots, fresh)
    parent.child = fresh[end]
    return nothing
end

function remembered_worker(seed, rounds)
    parent = cell(seed, 16)
    slots = Any[nothing for _ in 1:128]
    GC.gc(true)
    GC.gc(true)
    for round in 1:rounds
        state = step(seed + UInt64(round))
        rewrite!(parent, slots, state)
        GC.gc(false)
        for i in eachindex(slots)
            x = slots[i]::StressCell
            x.tag == step(state + UInt64(i)) || error("GC_STRESS_INVARIANT remembered tag")
            check(x)
        end
        parent.child === slots[end] || error("GC_STRESS_INVARIANT parent edge")
        yield()
    end
    return parent.child.tag
end

@noinline function dead_pages(seed, count=4096)
    cells = [cell(step(seed + UInt64(i)), 16 + (i % 15) * 16) for i in 1:count]
    foreach(check, cells)
    return cells[mod1(Int(seed & 0xfff), length(cells))]
end

function sweep_worker(seed, rounds)
    survivors = [cell(seed, 32) for _ in 1:32]
    for round in 1:rounds
        survivors[mod1(round, length(survivors))] = dead_pages(step(seed + UInt64(round)))
        GC.gc(round % 4 == 0)
        # Refill pool pages while the optional background sweeper frees empty pages.
        survivors[mod1(round + 1, length(survivors))] = dead_pages(step(seed + UInt64(round + rounds)))
        foreach(check, survivors)
        yield()
    end
    return survivors[1].tag
end

foreign_tag(seed, worker, epoch) = step(seed ⊻ (UInt64(worker) << 32) ⊻ UInt64(epoch)) | UInt64(1)

function foreign_callback(seed::UInt64, worker::Cint, epoch::Cint)::UInt64
    tag = foreign_tag(seed, worker, epoch)
    roots = [cell(step(tag + UInt64(i)), 64 + i) for i in 1:64]
    GC.gc(false)
    return all(valid, roots) ? tag : UInt64(0)
end

function foreign_workload(seed, rounds, library)
    # @cfunction entry adopts new pthreads and restores GC-safe state on return:
    # src/llvm-ptls.cpp:173-208; test/foreign_thread_reuse.jl:27-46.
    precompile(foreign_callback, (UInt64, Cint, Cint))
    callback = @cfunction(foreign_callback, UInt64, (UInt64, Cint, Cint))
    handle = Libdl.dlopen(library)
    runner = Libdl.dlsym(handle, :gc_stress_foreign)
    workers = Threads.nthreads(:default)
    checksums = zeros(UInt64, workers)
    running = Threads.Atomic{Bool}(true)
    collections = Threads.Atomic{Int}(0)
    collector = Threads.@spawn begin
        while running[]
            temporary = [cell(step(seed + UInt64(i)), 128) for i in 1:128]
            GC.gc(false)
            foreach(check, temporary)
            Threads.atomic_add!(collections, 1)
            yield()
        end
    end
    try
        GC.@preserve checksums begin
            # The caller blocks in pthread_join while foreign callbacks allocate.
            result = @ccall gc_safe=true $runner(callback::Ptr{Cvoid}, seed::UInt64,
                workers::Cint, rounds::Cint, checksums::Ptr{UInt64})::Cint
            result == 0 || error("foreign pthread operation failed: $result")
        end
    finally
        running[] = false
        wait(collector)
        Libdl.dlclose(handle)
    end
    for worker in 0:(workers - 1)
        expected = UInt64(0)
        for epoch in 0:(2 * rounds - 1)
            expected ⊻= foreign_tag(seed, worker, epoch)
        end
        checksums[worker + 1] == expected || error("GC_STRESS_INVARIANT foreign checksum")
    end
    collections[] > 0 || error("GC_STRESS_COVERAGE no concurrent collection during foreign callbacks")
    println("GC_STRESS_COVERAGE adopted_threads=$(workers * rounds) callback_entries=$(2 * workers * rounds) concurrent_collections=$(collections[])")
end

function main()
    length(ARGS) == 4 || error("expected workload seed rounds foreign-library")
    workload, seed_text, rounds_text, library = ARGS
    seed = parse(UInt64, seed_text)
    rounds = parse(Int, rounds_text)
    rounds > 0 || error("rounds must be positive")
    workers = Threads.nthreads(:default)
    workers >= 2 || error("at least two default-pool threads are required")
    println("GC_STRESS_BEGIN workload=$workload seed=$seed rounds=$rounds threads=$workers gcthreads=$(Base.JLOptions().nmarkthreads),$(Base.JLOptions().nsweepthreads) version=$VERSION commit=$(Base.GIT_VERSION_INFO.commit)")
    flush(stdout)
    if workload == "allocation" || workload == "remembered" || workload == "sweep"
        # The initial burst pressures the stock GC's roughly 45 MiB warm page cache.
        burst_survivor = workload == "sweep" ? dead_pages(seed, 524288) : nothing
        workload == "sweep" && GC.gc(true)
        work = workload == "allocation" ? allocation_worker : workload == "remembered" ? remembered_worker : sweep_worker
        tasks = [Threads.@spawn work(step(seed + UInt64(worker)), rounds) for worker in 1:workers]
        println("GC_STRESS_COVERAGE checksum=$(reduce(xor, fetch.(tasks)))")
        burst_survivor === nothing || check(burst_survivor)
    elseif workload == "finalizers"
        calls, failures = Threads.Atomic{Int}(0), Threads.Atomic{Int}(0)
        tasks = [Threads.@spawn finalizer_worker(step(seed + UInt64(worker)), rounds, calls, failures) for worker in 1:workers]
        explicit = sum(fetch.(tasks))
        GC.gc(true)
        GC.gc(true)
        failures[] == 0 || error("GC_STRESS_INVARIANT finalizer payload")
        calls[] >= 2 * explicit || error("GC_STRESS_INVARIANT explicit finalizers")
        println("GC_STRESS_COVERAGE finalizer_calls=$(calls[]) explicit_finalizers=$explicit")
    elseif workload == "tasks"
        moved = 0
        for round in 1:rounds
            tasks = [Threads.@spawn task_worker(step(seed + UInt64(128 * round + i))) for i in 1:128]
            results = fetch.(tasks)
            GC.gc(round % 4 == 0)
            for (roots, migrated) in results
                foreach(check, roots)
                moved += migrated
            end
        end
        moved > 0 || error("GC_STRESS_COVERAGE no task migration observed")
        println("GC_STRESS_COVERAGE parent_tasks=$(128 * rounds) child_tasks=$(2048 * rounds) migrated_tasks=$moved")
    elseif workload == "foreign"
        foreign_workload(seed, rounds, library)
    else
        error("unknown workload: $workload")
    end
    GC.gc(true)
    println("GC_STRESS_OK workload=$workload seed=$seed rounds=$rounds")
end

main()
