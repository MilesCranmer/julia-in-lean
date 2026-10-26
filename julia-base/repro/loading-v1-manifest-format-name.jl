mktempdir() do root
    env = joinpath(root, "env")
    package = joinpath(root, "manifest_format")
    source = joinpath(package, "src", "manifest_format.jl")
    mkpath(env)
    mkpath(dirname(source))
    write(source, "module manifest_format\nend\n")
    uuid = "11111111-1111-1111-1111-111111111111"
    write(joinpath(env, "Project.toml"), "[deps]\nmanifest_format = \"$uuid\"\n")
    write(joinpath(env, "Manifest.toml"), """
    [[manifest_format]]
    uuid = "$uuid"
    path = "../manifest_format"
    """)

    manifest = Base.parsed_toml(joinpath(env, "Manifest.toml"))
    old_load_path = copy(LOAD_PATH)
    try
        empty!(LOAD_PATH)
        push!(LOAD_PATH, env)
        found = Base.find_package("manifest_format")
        println("parsed manifest_format type = ", typeof(manifest["manifest_format"]))
        println("is v1 manifest              = ", Base.is_v1_format_manifest(manifest))
        println("manifest dependency names   = ", collect(keys(Base.get_deps(manifest))))
        println("find_package                 = ", found)
        println("source file exists           = ", isfile(source))
        if found === nothing && isfile(source) && !Base.is_v1_format_manifest(manifest)
            println("REPRODUCED loading-v1-manifest-format-name")
        end
    finally
        empty!(LOAD_PATH)
        append!(LOAD_PATH, old_load_path)
    end
end
