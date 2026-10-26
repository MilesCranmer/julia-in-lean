import JuliaLean.Loading.CoverageEarly

namespace JuliaLean.Loading.Coverage.Early

open JuliaLean.Registry

structure MethodMeta where
  line : Nat
  endLine : Nat
  signature : String

private def methodNamespace : Lean.Name := (``method10).getPrefix

private def methodEntry (info : MethodMeta) : Entry :=
  { id := s!"loading-method-{info.line}"
    juliaFile := "base/loading.jl"
    juliaFns := [info.signature]
    statement := "The method satisfies the caller-visible result or state invariant stated by its method-specific property."
    source := s!"base/loading.jl:{info.line}-{info.endLine}; caller-visible contract"
    status := .proven
    prop := methodNamespace.str s!"Property{info.line}"
    thm := some (methodNamespace.str s!"property{info.line}") }

private def methods : List MethodMeta := [
  ⟨10, 10, "isfile_casesensitive(path)"⟩,
  ⟨86, 93, "isaccessibledir(dir)"⟩,
  ⟨95, 102, "isaccessiblefile(file)"⟩,
  ⟨104, 111, "isaccessiblepath(path)"⟩,
  ⟨119, 123, "$name(bytes::Vector{UInt8})"⟩,
  ⟨124, 124, "$name(s::AbstractString)"⟩,
  ⟨125, 125, "parse(::Type{$name}, s::AbstractString)"⟩,
  ⟨126, 135, "tryparse(::Type{$name}, s::AbstractString)"⟩,
  ⟨137, 137, "string(hash::$name)"⟩,
  ⟨138, 138, "print(io::IO, hash::$name)"⟩,
  ⟨139, 139, "show(io::IO, hash::$name)"⟩,
  ⟨141, 141, "isless(a::$name, b::$name)"⟩,
  ⟨142, 142, "hash(a::$name, h::UInt)"⟩,
  ⟨143, 143, "==(a::$name, b::$name)"⟩,
  ⟨150, 160, "uuid5(namespace::UUID, key::String)"⟩,
  ⟨164, 183, "dummy_uuid(project_file::String)"⟩,
  ⟨189, 198, "slug(x::UInt32, p::Int)"⟩,
  ⟨200, 203, "package_slug(uuid::UUID, p::Int=5)"⟩,
  ⟨205, 209, "version_slug(uuid::UUID, sha1::SHA1, p::Int=5)"⟩,
  ⟨220, 234, "CachedTOMLDict(p::TOML.Parser, path::String)"⟩,
  ⟨236, 254, "get_updated_dict(p::TOML.Parser, f::CachedTOMLDict)"⟩,
  ⟨278, 287, "LoadingCache()"⟩,
  ⟨294, 294, "TOMLCache(p::TOML.Parser)"⟩,
  ⟨295, 295, "TOMLCache(p::TOML.Parser, d::Dict{String, Dict{String, Any}})"⟩,
  ⟨299, 299, "parsed_toml(project_file::AbstractString)"⟩,
  ⟨300, 322, "parsed_toml(project_file::AbstractString, toml_cache::TOMLCache, toml_lock::ReentrantLock)"⟩,
  ⟨327, 334, "find_package(arg)"⟩,
  ⟨337, 349, "is_stdlib(pkgid::PkgId)"⟩,
  ⟨358, 358, "identify_package_env(where::Module, name::String)"⟩,
  ⟨359, 404, "identify_package_env(where::PkgId, name::String)"⟩,
  ⟨405, 430, "identify_package_env(where::Nothing, name::String)"⟩,
  ⟨431, 431, "identify_package_env(name::String)"⟩,
  ⟨433, 447, "identify_stdlib_project_dep(stdlib::PkgId, depname::String)"⟩,
  ⟨449, 449, "_nothing_or_first(x)"⟩,
  ⟨476, 476, "identify_package(where::Module, name::String)"⟩,
  ⟨477, 477, "identify_package(where::PkgId, name::String)"⟩,
  ⟨478, 478, "identify_package(name::String)"⟩,
  ⟨480, 537, "locate_package_env(pkg::PkgId, stopenv)"⟩,
  ⟨553, 559, "locate_package(pkg::PkgId, stopenv)"⟩,
  ⟨561, 567, "locate_package_load_spec(pkg::PkgId, stopenv)"⟩,
  ⟨580, 589, "pathof(m::Module)"⟩,
  ⟨617, 634, "pkgdir(m::Module, paths::String...)"⟩,
  ⟨636, 646, "get_pkgversion_from_path(path)"⟩,
  ⟨663, 677, "pkgversion(m::Module)"⟩,
  ⟨690, 698, "locate_project_file(env::String)"⟩,
  ⟨704, 723, "env_project_file(env::String)"⟩,
  ⟨725, 765, "base_project(project_file)"⟩
]

def entries : List Entry := methods.map methodEntry

end JuliaLean.Loading.Coverage.Early
