mktempdir() do root
    depot = joinpath(root, "depot")
    mkpath(depot)
    old_depot_path = copy(DEPOT_PATH)
    try
        empty!(DEPOT_PATH)
        push!(DEPOT_PATH, depot)
        result = Base.load_path_expand("@../../outside")
        relative = relpath(result, depot)
        created = isfile(result)
        escaped = startswith(relative, ".." * Base.Filesystem.path_separator)
        println("path relative to depot = ", relative)
        println("created Project.toml    = ", created)
        println("escaped depot           = ", escaped)
        if relative == joinpath("..", "outside", "Project.toml") && escaped
            println("REPRODUCED loading-named-env-path-escape")
        end
    finally
        empty!(DEPOT_PATH)
        append!(DEPOT_PATH, old_depot_path)
    end
end
