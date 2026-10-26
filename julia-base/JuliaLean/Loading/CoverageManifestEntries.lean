import JuliaLean.Loading.CoverageManifest

namespace JuliaLean.Loading.Coverage.Manifest

open JuliaLean.Registry

structure MethodMeta where
  line : Nat
  endLine : Nat
  signature : String
private def methodNamespace : Lean.Name := (``method767).getPrefix
private def methodEntry (info : MethodMeta) : Entry :=
  { id := s!"loading-method-{info.line}", juliaFile := "base/loading.jl"
    juliaFns := [info.signature]
    statement := "The method satisfies the caller-visible result or state invariant stated by its method-specific property."
    source := s!"base/loading.jl:{info.line}-{info.endLine}; caller-visible contract"
    status := .proven, prop := methodNamespace.str s!"Property{info.line}"
    thm := some (methodNamespace.str s!"property{info.line}") }

private def methods : List MethodMeta := [
  ⟨767,772,"package_get_here(project_file, name::String)"⟩,
  ⟨774,780,"package_get(project_file, where, name::String)"⟩,
  ⟨785,807,"package_extension_get(project_file, where::PkgId, name::String)"⟩,
  ⟨809,866,"environment_deps_get(env::String, where, name::String)"⟩,
  ⟨868,907,"manifest_uuid_load_spec(env::String, pkg::PkgId)"⟩,
  ⟨910,914,"find_ext_path(project_path::String, extname::String)"⟩,
  ⟨916,927,"project_file_ext_load_spec(project_file::String, ext::PkgId)"⟩,
  ⟨930,936,"project_file_name_uuid(project_file::String, name::String)"⟩,
  ⟨938,968,"project_get_edition(d::Dict)"⟩,
  ⟨970,979,"project_file_load_spec(project_file::String, name::String)"⟩,
  ⟨981,987,"workspace_manifest(project_file)"⟩,
  ⟨989,1000,"parser_for_active_project()"⟩,
  ⟨1003,1039,"project_file_manifest_path(project_file::String)"⟩,
  ⟨1043,1052,"entry_point_and_project_file_inside(dir::String, name::String)"⟩,
  ⟨1056,1067,"entry_point_and_project_file(dir::String, name::String)"⟩,
  ⟨1070,1080,"implicit_env_project_file_extension(dir::String, ext::PkgId)"⟩,
  ⟨1083,1087,"entry_path(path::String, name::String, entryfile)"⟩,
  ⟨1094,1107,"explicit_project_deps_get(project_file::String, name::String)"⟩,
  ⟨1132,1140,"dep_stanza_get(stanza::Dict, name::String)"⟩,
  ⟨1142,1145,"dep_stanza_get(stanza::Vector{String}, name::String)"⟩,
  ⟨1147,1147,"dep_stanza_get(stanza::Nothing, name::String)"⟩,
  ⟨1149,1219,"explicit_manifest_deps_get(project_file::String, where::PkgId, name::String)"⟩,
  ⟨1222,1257,"explicit_manifest_uuid_load_spec(project_file::String, pkg::PkgId)"⟩,
  ⟨1259,1305,"explicit_manifest_entry_load_spec(manifest_file::String, pkg::PkgId, entry::Dict)"⟩,
  ⟨1308,1317,"implicit_manifest_pkgid(dir::String, name::String)"⟩,
  ⟨1319,1329,"implicit_manifest_project(dir::String, pkg::PkgId)"⟩,
  ⟨1332,1342,"implicit_manifest_uuid_load_spec(dir::String, pkg::PkgId)"⟩,
  ⟨1346,1350,"find_source_file(path::AbstractString)"⟩,
  ⟨1355,1364,"init_debuginfo_source_paths()"⟩,
  ⟨1366,1373,"cache_file_entry(pkg::PkgId)"⟩,
  ⟨1378,1396,"cachefile_candidates_in_depot(pkg::PkgId, depot::String)"⟩,
  ⟨1401,1415,"sort_cachefile_candidates!(paths, pkgimages)"⟩,
  ⟨1403,1403,"sort_by(i)"⟩, ⟨1404,1409,"sort_lt(a, b)"⟩,
  ⟨1423,1433,"touch_cachefile(pkg::PkgId, path::String)"⟩,
  ⟨1435,1437,"sorted_cachefile_candidates_in_depot(pkg::PkgId, depot::String)"⟩,
  ⟨1440,1444,"cache_search_depots(sourcepath::String, DEPOT_PATH)"⟩,
  ⟨1447,1450,"lazy_cachefile_candidates(pkg::PkgId, sourcepath::String, DEPOT_PATH)"⟩,
  ⟨1452,1461,"find_all_in_cache_path(pkg::PkgId, DEPOT_PATH)"⟩,
  ⟨1463,1463,"ocachefile_from_cachefile(cachefile)"⟩,
  ⟨1464,1464,"cachefile_from_ocachefile(cachefile)"⟩
]

def entries : List Entry := methods.map methodEntry

end JuliaLean.Loading.Coverage.Manifest
