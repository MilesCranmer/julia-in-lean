depot = mktempdir()
project = joinpath(depot, "environments", "scripts", "Project.toml")
mkpath(dirname(project))
write(project, "")
old = copy(DEPOT_PATH)
result = try
    empty!(DEPOT_PATH)
    push!(DEPOT_PATH, depot)
    Base.load_path_expand("@scripts")
finally
    append!(empty!(DEPOT_PATH), old)
end
println("named environment file: ", project)
println("load_path_expand(\"@scripts\") = ", repr(result))
if result != project
    println("REPRODUCED runtimecov-load-path-expand-script-prefix")
end
