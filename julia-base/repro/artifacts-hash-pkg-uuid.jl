using Artifacts
using Base: UUID

mktempdir() do root
    depot = joinpath(root, "depot")
    mkpath(joinpath(depot, "artifacts"))
    replacement = joinpath(root, "replacement")
    mkpath(replacement)
    uuid = UUID("11111111-2222-3333-4444-555555555555")
    hash_string = "1"^40
    artifacts_toml = joinpath(root, "Artifacts.toml")
    write(artifacts_toml,
          "[payload]\ngit-tree-sha1 = \"$(hash_string)\"\ndownload = []\n")
    write(joinpath(depot, "artifacts", "Overrides.toml"),
          "[$(uuid)]\npayload = \"$(replacement)\"\n")

    old_depots = copy(Base.DEPOT_PATH)
    try
        empty!(Base.DEPOT_PATH)
        push!(Base.DEPOT_PATH, depot)
        Artifacts.load_overrides(force=true)

        hash = artifact_hash("payload", artifacts_toml; pkg_uuid=uuid)
        after_hash = Artifacts.query_override(hash)
        path_after_hash = artifact_path(hash)

        Artifacts.load_overrides(force=true)
        artifact_dict = Artifacts.parse_toml(artifacts_toml)
        select_downloadable_artifacts(artifact_dict, artifacts_toml; pkg_uuid=uuid)
        after_selection = Artifacts.query_override(hash)

        artifact_meta("payload", artifacts_toml; pkg_uuid=uuid)
        after_meta = Artifacts.query_override(hash)
        path_after_meta = artifact_path(hash)

        println("after artifact_hash = ", repr(after_hash))
        println("path after artifact_hash = ", relpath(path_after_hash, root))
        println("after dictionary selection = ", repr(after_selection))
        println("after artifact_meta = ", relpath(after_meta, root))
        println("path after artifact_meta = ", relpath(path_after_meta, root))
        ignored = after_hash === nothing && path_after_hash != replacement &&
                  after_selection === nothing && after_meta == replacement &&
                  path_after_meta == replacement
        println("pkg_uuid ignored = ", ignored)
        ignored && println("REPRODUCED artifacts-hash-pkg-uuid")
    finally
        empty!(Base.DEPOT_PATH)
        append!(Base.DEPOT_PATH, old_depots)
        Artifacts.ARTIFACT_OVERRIDES[] = nothing
    end
end
