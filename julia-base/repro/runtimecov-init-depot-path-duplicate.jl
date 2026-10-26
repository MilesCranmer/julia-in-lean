user_depot = joinpath(homedir(), ".julia")
old_env = get(ENV, "JULIA_DEPOT_PATH", nothing)
old = copy(DEPOT_PATH)
result = try
    ENV["JULIA_DEPOT_PATH"] = ":" * user_depot
    Base.init_depot_path()
    copy(DEPOT_PATH)
finally
    old_env === nothing ? delete!(ENV, "JULIA_DEPOT_PATH") : (ENV["JULIA_DEPOT_PATH"] = old_env)
    append!(empty!(DEPOT_PATH), old)
end
println("JULIA_DEPOT_PATH = ", repr(":" * user_depot))
println("DEPOT_PATH = ", result)
if count(==(user_depot), result) > 1
    println("REPRODUCED runtimecov-init-depot-path-duplicate")
end
