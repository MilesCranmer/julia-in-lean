using Artifacts
using Base: SHA1

if !isempty(ARGS) && ARGS[1] == "child"
    depot = ARGS[2]
    hash = SHA1(ARGS[3])
    empty!(Base.DEPOT_PATH)
    push!(Base.DEPOT_PATH, depot)
    Artifacts.load_overrides(force=true)
    Artifacts.query_override(hash)
    exit()
end

mktempdir() do root
    depot = joinpath(root, "depot")
    artifacts_dir = joinpath(depot, "artifacts")
    mkpath(artifacts_dir)
    first_hash = "1"^40
    second_hash = "2"^40
    write(joinpath(artifacts_dir, "Overrides.toml"),
          "$(first_hash) = \"$(second_hash)\"\n$(second_hash) = \"$(first_hash)\"\n")

    command = `$(Base.julia_cmd()) --startup-file=no --history-file=no $(@__FILE__) child $depot $first_hash`
    process = run(pipeline(ignorestatus(command), stdout=devnull, stderr=devnull); wait=false)
    status = timedwait(() -> Base.process_exited(process), 5.0; pollint=0.05)
    hung = status == :timed_out
    if hung
        kill(process)
    end
    wait(process)

    println("resolution status after 5 seconds = ", status)
    println("cyclic override hangs = ", hung)
    hung && println("REPRODUCED artifacts-override-cycle")
end
