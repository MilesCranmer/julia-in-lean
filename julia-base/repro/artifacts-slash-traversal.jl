using Artifacts
using Base.BinaryPlatforms: Platform

mktempdir() do root
    hash_string = "0"^40
    artifact_dir = joinpath(root, hash_string)
    mkpath(artifact_dir)

    artifacts_toml = joinpath(root, "Artifacts.toml")
    write(artifacts_toml, "[payload]\ngit-tree-sha1 = \"$(hash_string)\"\n")
    artifact_dict = Artifacts.load_artifacts_toml(artifacts_toml)
    platform = Platform("x86_64", "linux")
    name, tail, hash = Artifacts.artifact_slash_lookup(
        "payload/../escaped.txt", artifact_dict, artifacts_toml, platform)

    path = Artifacts.with_artifacts_directory(root) do
        Artifacts.__artifact_str(
            Main, artifacts_toml, name, tail, artifact_dict, hash, platform, Val(nothing))
    end

    println("tail = ", repr(tail))
    println("returned path relative to artifact root = ", relpath(path, root))
    escaped = normpath(path) == joinpath(root, "escaped.txt")
    println("escaped artifact directory = ", escaped)
    escaped && println("REPRODUCED artifacts-slash-traversal")
end
