user_depot = joinpath(homedir(), ".julia")
child_code = "println(join(DEPOT_PATH, '\\n'))"
cmd = addenv(`$(Base.julia_cmd()) --startup-file=no -e $child_code`, "JULIA_DEPOT_PATH" => ":" * user_depot)
paths = String.(split(chomp(read(cmd, String)), '\n'))
println("JULIA_DEPOT_PATH = ", repr(":" * user_depot))
println("DEPOT_PATH = ", paths)
count(==(user_depot), paths) > 1 && println("REPRODUCED runtimecov-init-depot-path-duplicate")
