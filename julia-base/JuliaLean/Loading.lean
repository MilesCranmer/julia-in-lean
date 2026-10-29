import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Loading.Model
import JuliaLean.Loading.Props
import JuliaLean.Loading.Proofs
import JuliaLean.Loading.Refutations
import JuliaLean.Loading.Validation
import JuliaLean.Loading.CoverageEarlyEntries
import JuliaLean.Loading.CoverageManifestEntries
import JuliaLean.Loading.CoverageExtensionsEntries
import JuliaLean.Loading.CoverageRequireEntries
import JuliaLean.Loading.CoverageCacheEntries

namespace JuliaLean.Loading

open JuliaLean.Registry

private def loadingFile := "base/loading.jl"

/-- Registry entries of this area. -/
def coreEntries : List Entry := [
  -- refuted
  { id := "loading-v1-manifest-format-name", juliaFile := loadingFile
    juliaFns := ["is_v1_format_manifest", "get_deps", "find_package"]
    statement := "A v1 manifest package named manifest_format remains in the dependency map and can be located."
    source := "base/loading.jl:1112-1114 (explicit compatibility branch for this package name)"
    status := .refuted, prop := ``V1ManifestFormatPackagePreserved
    thm := some ``v1ManifestFormatPackagePreserved_refuted
    issue := "none found (queries: is_v1_format_manifest, manifest_format package name, old manifest manifest_format, package named manifest_format)"
    notes := "TOML parses [[manifest_format]] as Vector{Any}, but the collision branch checks Dict{String}; get_deps returns an empty v2 deps table. Same on 1.13.2." },
  { id := "loading-named-env-path-escape", juliaFile := "base/initdefs.jl"
    juliaFns := ["load_path_expand(::AbstractString)", "init_named_env!"]
    statement := "Every @name environment path remains below DEPOT_PATH[1]/environments."
    source := "base/initdefs.jl:209-217 (named environments are stored below a depot's environments directory)"
    status := .refuted, prop := ``NamedEnvContained, thm := some ``namedEnvContained_refuted
    issue := "none found (queries: load_path_expand traversal, JULIA_LOAD_PATH named environment .., named environment escape depot, load_path_expand)"
    notes := "@../../outside resolves outside the depot. Julia 1.13.2 returns that path; nightly also creates Project.toml there." },
  { id := "loading-workspace-home-prefix", juliaFile := loadingFile
    juliaFns := ["base_project", "workspace_manifest"]
    statement := "The workspace search applies its home boundary exactly to projects inside the home directory."
    source := "base/loading.jl:729-759 (home-boundary comment and upward workspace search)"
    status := .refuted, prop := ``WorkspaceHomeBoundary, thm := some ``workspaceHomeBoundary_refuted
    issue := "none found (queries: base_project home prefix, workspace home directory prefix, workspace sibling homedir, base_project startswith)"
    notes := "A project below sibling home2 is treated as below home and cannot find a workspace root above home2. Same on 1.13.2." },
  -- proven
  { id := "loading-precompiled-selection", juliaFile := loadingFile
    juliaFns := ["__require_prelocked"]
    statement := "Precompilation falls back on nothing, rejects an empty result or a non-string cache path, and derives an object path only when package images are enabled."
    source := "base/loading.jl:3220-3233", status := .proven
    prop := ``Coverage.Require.PrecompiledSelectionContract
    thm := some ``Coverage.Require.precompiledSelectionContract_proven },
  { id := "loading-identify-precedence", juliaFile := loadingFile
    juliaFns := ["identify_package_env", "identify_package", "environment_deps_get"]
    statement := "Package identification returns the first environment match and stops at a found-context missing-dependency sentinel."
    source := "base/loading.jl:378-423; manual code-loading environment-stack precedence"
    status := .proven, prop := ``LookupPrecedence, thm := some ``lookupPrecedence_proven },
  { id := "loading-locate-precedence", juliaFile := loadingFile
    juliaFns := ["locate_package_env", "locate_package", "manifest_uuid_load_spec"]
    statement := "Package location returns the first load specification in environment-stack order."
    source := "base/loading.jl:480-536; locate_package docstring"
    status := .proven, prop := ``LocatePrecedence, thm := some ``locatePrecedence_proven },
  { id := "loading-load-path-version", juliaFile := "base/initdefs.jl"
    juliaFns := ["load_path_expand"]
    statement := "Named environments replace the first three # placeholders with Julia major, minor, and patch versions, in that order."
    source := "base/initdefs.jl:214-217,346-348"
    status := .proven, prop := ``LoadPathVersionExpansion, thm := some ``loadPathVersionExpansion_proven },
  { id := "loading-manifest-fields-roundtrip", juliaFile := loadingFile
    juliaFns := ["parsed_toml", "explicit_project_deps_get", "explicit_manifest_deps_get", "explicit_manifest_entry_load_spec"]
    statement := "All modelled project and manifest fields round-trip through the typed loading representation."
    source := "base/loading.jl:767-979,1094-1304; Project.toml and Manifest.toml field semantics"
    status := .proven, prop := ``ManifestFieldsRoundtrip, thm := some ``manifestFieldsRoundtrip_proven },
  { id := "loading-extension-triggers", juliaFile := loadingFile
    juliaFns := ["ext_may_load_weakdep", "package_extension_get", "insert_extension_triggers", "run_extension_callbacks"]
    statement := "An extension admits exactly its declared weak-dependency triggers and becomes ready exactly when every trigger is loaded."
    source := "base/loading.jl:782-805,1753-1925; manual package-extension trigger rule"
    status := .proven, prop := ``ExtensionTriggersExact, thm := some ``extensionTriggersExact_proven },
  { id := "loading-cache-staleness", juliaFile := loadingFile
    juliaFns := ["stale_cachefile", "any_includes_stale", "checksums_invalid", "stale_prefs"]
    statement := "A cache is rejected exactly when one of the modelled header, flag, identity, dependency, source, checksum, or preference checks fails."
    source := "base/loading.jl:4802-5135 (cache rejection conditions)"
    status := .proven, prop := ``CacheStalenessExact, thm := some ``cacheStalenessExact_proven },
  { id := "loading-cache-relocatability", juliaFile := loadingFile
    juliaFns := ["isrelocatable", "replace_depot_path", "resolve_depot"]
    statement := "A cache is relocatable exactly when every include is depot-tagged and every dependency include tracks content."
    source := "base/loading.jl:2294-2322,4148-4185"
    status := .proven, prop := ``CacheRelocatabilityExact, thm := some ``cacheRelocatabilityExact_proven },
  { id := "loading-preferences-staleness", juliaFile := loadingFile
    juliaFns := ["get_preferences_blob", "stale_prefs", "toml_egal"]
    statement := "A preference snapshot stays fresh exactly while every observed value is unchanged and every observed-unset key remains absent."
    source := "base/loading.jl:4610-4640,4863-4909"
    status := .proven, prop := ``PreferencesStalenessExact, thm := some ``preferencesStalenessExact_proven },
  { id := "loading-cycle-detection", juliaFile := loadingFile
    juliaFns := ["canstart_loading", "start_loading", "end_loading"]
    statement := "Task-wait traversal reports a cycle exactly when it reaches the current task, and does not report an acyclic chain."
    source := "base/loading.jl:2561-2657 (package-lock wait graph and cycle error)"
    status := .proven, prop := ``CycleDetectionExact, thm := some ``cycleDetectionExact_proven }
]

def entries : List Entry := coreEntries ++ Coverage.Early.entries ++ Coverage.Manifest.entries ++
  Coverage.Extensions.entries ++ Coverage.Require.entries ++ Coverage.Cache.entries

end JuliaLean.Loading
