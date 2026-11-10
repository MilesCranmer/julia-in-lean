# verify_call runs in the world `codeinst.min_world` (Compiler/src/reinfer.jl:235), but the
# interference fast path skips every interference entry whose primary_world is past that world
# (reinfer.jl:814). When a method is added after the loaded code instance was activated and
# before its edges are verified, the verifier accepts the edge up to the validation world,
# although the method lookup there gives a different method.
#
# Part 1 calls the verifier directly on a code instance whose min_world is older than the
# validation world, as in a load where another thread defines a method between activation
# (src/staticdata.c:4974-4986) and `insert_backedges` (base/loading.jl:1516).
# Part 2 shows stale code running after a real package load, with a second thread that defines
# the method in that window (needs `-t 2`; it is skipped otherwise).
const CC = Base.Compiler
const RU = CC.ReinferUtils
id = "compiler-reinfer-stale-min-world"

module M
h(x::Integer) = 1
g(x) = h(x)
end

mi_h = Base.specialize_method(only(methods(M.h)), Tuple{typeof(M.h),Int}, Core.svec())
mi_g = Base.specialize_method(only(methods(M.g)), Tuple{typeof(M.g),Int}, Core.svec())
wA = Base.get_world_counter()
@eval M h(x::Int) = 2          # changes what `h(::Int)` dispatches to
wV = Base.get_world_counter()
ci = Core.CodeInstance(mi_g, nothing, Any, Any, nothing, nothing, Int32(0), wA, UInt(1),
                       UInt32(0), nothing, nothing, Core.svec())
@atomic ci.edges = Core.svec(mi_h)  # recorded at wA: the call h(::Int) matched only h(::Integer)
_, mn, mx = RU.verify_method(ci, wV, RU.VerifyMethodWorkspace())
now = Base._methods_by_ftype(Tuple{typeof(M.h),Int}, -1, wV)
nowm = [m.method for m in now]
println("validation world ", wV, ", code instance min_world ", wA)
println("verify_method range: [", mn, ", ", mx, "]")
println("lookup of h(::Int) in the validation world: ", nowm)
part1 = mx >= wV && !(mi_h.def in nowm)
println("part 1 (verifier accepts a changed edge): ", part1)

# Part 2: a real package image.
part2 = nothing
if Threads.nthreads() >= 2
    dir = mktempdir()
    depot = mktempdir()
    for (name, src) in (
        "RISDep" => "module RISDep\nh(x::Integer) = 1\nmarker(x) = 0\nend\n",
        "RISPkg" => "module RISPkg\nusing RISDep\ng(x) = RISDep.h(x)\nRISDep.marker(::Val{:pkg}) = 1\nprecompile(g, (Int,))\nend\n")
        mkpath(joinpath(dir, name, "src"))
        write(joinpath(dir, name, "src", name * ".jl"), src)
        write(joinpath(dir, name, "Project.toml"),
              "name = \"$name\"\nuuid = \"$(Base.UUID(hash(name) % UInt128))\"\n" *
              (name == "RISPkg" ? "[deps]\nRISDep = \"$(Base.UUID(hash("RISDep") % UInt128))\"\n" : ""))
    end
    pushfirst!(DEPOT_PATH, depot)
    pushfirst!(LOAD_PATH, dir)
    # precompile both in a child process, then load in this one
    jl = Base.julia_cmd()
    run(`$jl --startup-file=no -e "pushfirst!(DEPOT_PATH, $(repr(depot))); pushfirst!(LOAD_PATH, $(repr(dir))); using RISPkg"`)
    @eval using RISDep
    # the image's methods are active once `marker` has its second method
    activated() = length(methods(RISDep.marker)) == 2
    started = Threads.Atomic{Bool}(false)
    defined = Threads.Atomic{Bool}(false)
    # Grab the require lock when the loader drops it around the image restore, wait for the
    # image's methods to activate, then define the method before the loader resumes.
    t = Threads.@spawn begin
        started[] = true
        deadline = time() + 60
        while !defined[] && time() < deadline
            if trylock(Base.require_lock)
                try
                    t1 = time() + 2
                    while !activated() && time() < t1
                        Libc.systemsleep(0.0005)
                    end
                    if activated()
                        Core.eval(RISDep, :(h(x::Int) = 2))
                        defined[] = true
                    end
                finally
                    unlock(Base.require_lock)
                end
            end
            Libc.systemsleep(0.0001)
        end
    end
    while !started[]; yield(); end
    @eval using RISPkg
    wait(t)
    if defined[]
        r_pkg = Base.invokelatest(RISPkg.g, 1)
        r_dep = Base.invokelatest(RISDep.h, 1)
        println("RISDep.h(1) = ", r_dep, ", RISPkg.g(1) = RISDep.h(1) gives ", r_pkg)
        part2 = r_dep == 2 && r_pkg == 1
    else
        println("part 2: the method was not defined inside the load window")
    end
    println("part 2 (stale image code runs): ", part2)
end
println(part1 && part2 !== false ? "REPRODUCED $id" : "NOT REPRODUCED $id")
