import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Artifacts.Model
import JuliaLean.Artifacts.Props
import JuliaLean.Artifacts.Proofs
import JuliaLean.Artifacts.Refutations
import JuliaLean.Artifacts.Validation

namespace JuliaLean.Artifacts

open JuliaLean.Registry

private def file := "stdlib/Artifacts/src/Artifacts.jl"

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "artifacts-slash-traversal", juliaFile := file
    juliaFns := ["split_artifact_slash", "artifact_slash_lookup", "__artifact_str", "@artifact_str"]
    statement := "Artifact slash lookup accepts exactly a nonempty artifact name followed by nonempty child components other than `..`, and never returns a path outside the artifact directory."
    source := "stdlib/Artifacts/src/Artifacts.jl:677-679 (path names indexing into the artifact); artifact-container invariant"
    status := .refuted, prop := ``SlashLookupContained, thm := some ``slashLookupContained_refuted
    issue := "none found (queries: artifact path traversal, artifact slash indexing, artifact dot dot path, artifact macro path escape)"
    notes := "artifact\"payload/../escaped.txt\" returns the sibling path escaped.txt. Both slash kinds split; leading, repeated and trailing separators produce empty components rather than an error. Same on 1.13.2." },
  { id := "artifacts-hash-pkg-uuid", juliaFile := file
    juliaFns := ["artifact_hash", "select_downloadable_artifacts(::Dict, ...)", "process_overrides", "artifact_path"]
    statement := "Every Artifacts helper that accepts pkg_uuid processes the corresponding UUID/name override before returning."
    source := "stdlib/Artifacts/src/Artifacts.jl:315-320 (setting pkg_uuid resolves UUID/name overrides), 435-459"
    status := .refuted, prop := ``PkgUuidKeywordsProcessOverrides
    thm := some ``pkgUuidKeywordsProcessOverrides_refuted
    issue := "none found (queries: artifact_hash pkg_uuid, Artifacts artifact_hash override, artifact_hash UUID override, Artifacts pkg_uuid ignored, select_downloadable_artifacts pkg_uuid, select downloadable artifacts override, Artifacts selection UUID override)"
    notes := "artifact_hash and the Dict overload of select_downloadable_artifacts accept pkg_uuid but ignore it. artifact_meta with the same arguments registers the replacement. Same on 1.13.2." },
  { id := "artifacts-override-cycle", juliaFile := file
    juliaFns := ["load_overrides", "query_override(::SHA1)", "map_override_path(::SHA1)", "artifact_path", "artifact_paths"]
    statement := "Every accepted graph of artifact hash and path override targets eventually resolves to a path."
    source := "stdlib/Artifacts/src/Artifacts.jl:91-109,195-208,218-257 (hash redirects and path-returning queries)"
    status := .refuted, prop := ``AcceptedOverridesResolve
    thm := some ``acceptedOverridesResolve_refuted
    issue := "none found (queries: Artifacts override cycle, Overrides.toml cycle, artifact hash override recursion, query_override stack overflow)"
    notes := "Two hash overrides A -> B and B -> A keep query_override/artifact_path in mutual recursion for more than five seconds. Same on 1.13.2." },
  -- proven
  { id := "artifacts-slash-split", juliaFile := file
    juliaFns := ["split_artifact_slash"]
    statement := "A bare artifact name is unchanged, and forward and backward separators split a separator-free name and child component identically."
    source := "stdlib/Artifacts/src/Artifacts.jl:605-642 (docstring, examples and implementation)"
    status := .proven, prop := ``SlashSplitSemantics, thm := some ``slashSplitSemantics_proven
    notes := "Unsafe components are covered separately by artifacts-slash-traversal." },
  { id := "artifacts-unpack-required", juliaFile := file
    juliaFns := ["unpack_platform"]
    statement := "unpack_platform returns nothing when a platform-specific entry lacks os or arch."
    source := "stdlib/Artifacts/src/Artifacts.jl:274-304 (docstring and required-key checks)"
    status := .proven, prop := ``UnpackPlatformRequired, thm := some ``unpackPlatformRequired_proven },
  { id := "artifacts-pack-platform-tags", juliaFile := file
    juliaFns := ["pack_platform!"]
    statement := "pack_platform! writes every non-nothing platform tag into the metadata dictionary."
    source := "stdlib/Artifacts/src/Artifacts.jl:306-312"
    status := .proven, prop := ``PackPlatformTags, thm := some ``packPlatformTags_proven },
  { id := "artifacts-platform-best-match", juliaFile := file
    juliaFns := ["artifact_meta", "unpack_platform", "select_platform"]
    statement := "For platform-specific entries, artifact_meta returns the documented best matching platform entry, or nothing exactly when none matches."
    source := "stdlib/Artifacts/src/Artifacts.jl:377-384,408-415; base/binaryplatforms.jl:1204-1242"
    status := .proven, prop := ``ArtifactMetaSelectsBest, thm := some ``artifactMetaSelectsBest_proven
    notes := "Delegates ranking to the existing BinaryPlatforms proof. The known select_platform iteration-order tie is tracked as platforms-select-order and is not duplicated here." },
  { id := "artifacts-meta-requires-hash", juliaFile := file
    juliaFns := ["artifact_meta", "artifact_hash"]
    statement := "A selected artifact metadata dictionary is returned exactly when it contains git-tree-sha1."
    source := "stdlib/Artifacts/src/Artifacts.jl:422-453"
    status := .proven, prop := ``ArtifactMetaRequiresHash, thm := some ``artifactMetaRequiresHash_proven },
  { id := "artifacts-lazy-selection", juliaFile := file
    juliaFns := ["select_downloadable_artifacts"]
    statement := "Download selection includes exactly matching entries with a download stanza, excluding lazy entries unless include_lazy is true."
    source := "stdlib/Artifacts/src/Artifacts.jl:456-496 (loop and docstring)"
    status := .proven, prop := ``LazySelection, thm := some ``lazySelection_proven },
  { id := "artifacts-override-precedence", juliaFile := file
    juliaFns := ["load_overrides", "process_overrides"]
    statement := "Higher-priority depot overrides win, and a processed UUID/name override wins over an existing direct hash override for the bound artifact."
    source := "stdlib/Artifacts/src/Artifacts.jl:117-127,150-177,331-371"
    status := .proven, prop := ``OverridePrecedence, thm := some ``overridePrecedence_proven },
  { id := "artifacts-malformed-override-error", juliaFile := file
    juliaFns := ["parse_mapping", "load_overrides"]
    statement := "A malformed direct override emits an error and does not change the hash override mapping."
    source := "stdlib/Artifacts/src/Artifacts.jl:74-89,133-148"
    status := .proven, prop := ``MalformedOverridesReported
    thm := some ``malformedOverridesReported_proven
    notes := "The documented implementation logs @error and continues for malformed top-level entries; it does not promise to throw. Cyclic but individually well-formed mappings are covered separately." },
  { id := "artifacts-path-override", juliaFile := file
    juliaFns := ["query_override", "artifact_paths", "artifact_path", "artifact_exists"]
    statement := "A direct path override replaces all depot candidates, artifact_exists tests that path, and artifact_path returns it."
    source := "stdlib/Artifacts/src/Artifacts.jl:195-271"
    status := .proven, prop := ``ArtifactPathOverride, thm := some ``artifactPathOverride_proven }
]

end JuliaLean.Artifacts
