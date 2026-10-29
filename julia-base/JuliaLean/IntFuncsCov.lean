import JuliaLean.Registry.Types
import JuliaLean.IntFuncsCov.Simple
import JuliaLean.IntFuncsCov.Char
import JuliaLean.IntFuncsCov.Hashing
import JuliaLean.IntFuncsCov.Version
import JuliaLean.IntFuncsCov.UuidPkgid

namespace JuliaLean.IntFuncsCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [



  { id := "intfuncscov-combinatorics-source", juliaFile := "base/combinatorics.jl"
    juliaFns := ["factorial_lookup", "factorial", "_foldoneto", "isperm", "_isperm",
      "invperm"]
    statement := "Factorial dispatch, generated folds, and every tuple, array, and Any32 permutation dispatch follow the source checks and loops."
    source := "base/combinatorics.jl:21-101,286-316", status := .proven
    prop := ``Simple.CombinatoricsSourceBehavior, thm := some ``Simple.combinatoricsSourceBehavior },
  { id := "intfuncscov-isperm-noninteger", juliaFile := "base/combinatorics.jl"
    juliaFns := ["isperm", "_isperm", "invperm"]
    statement := "isperm returns a Bool for every argument, and array and tuple forms agree on the same numeric elements."
    source := "base/combinatorics.jl:63-66,76-101,286-316", status := .refuted
    prop := ``Combinatorics.IspermTotal, thm := some ``Combinatorics.ispermTotal_refuted
    issue := "none found (queries: isperm, isperm float, isperm ArgumentError, invperm tuple)"
    notes := "Float64 and Bool vectors reach to_index and throw, while the same tuples compare numerically and return normally." },
  { id := "intfuncscov-invperm-empty-any", juliaFile := "base/combinatorics.jl"
    juliaFns := ["invperm(::AbstractVector)"]
    statement := "invperm returns an empty inverse for every empty vector that isperm accepts, independent of its declared element type."
    source := "base/combinatorics.jl:246-249,286-296", status := .refuted
    prop := ``Combinatorics.InvpermEmptyTotal,
    thm := some ``Combinatorics.invpermEmptyTotal_refuted
    issue := "none found (queries: invperm empty Any, invperm zero eltype, invperm empty vector)"
    notes := "invperm(Any[]) throws MethodError from zero(Any), while isperm(Any[]) is true and invperm(()) returns ()." },


  { id := "intfuncscov-version-number-source", juliaFile := "base/version.jl"
    juliaFns := ["VersionNumber", "print", "show", "tryparse", "parse", "v_str",
      "ident_cmp", "==", "isless", "hash", "issupbuild", "lowerbound", "upperbound",
      "thispatch", "thisminor", "thismajor", "nextpatch", "nextminor", "nextmajor",
      "Broadcast.broadcastable", "version_with_build_variant", "libllvm_path"]
    statement := "VersionNumber construction, parsing, printing, ordering, hashing, bounds, and successor helpers satisfy their universal source and semantic-version properties."
    source := "base/version.jl:56-293", status := .proven
    prop := ``Version.VersionNumberSourceBehavior, thm := some ``Version.versionNumberSourceBehavior },
  { id := "intfuncscov-version-bound-range", juliaFile := "base/version.jl"
    juliaFns := ["VersionBound", "getindex", "≲", "isless_ll", "stricterlower",
      "isless_uu", "stricterupper", "isjoinable", "hash(::VersionBound)", "VersionRange",
      "isempty(::VersionRange)", "print(::VersionRange)", "show(::VersionRange)",
      "in(::VersionNumber,::VersionRange)", "intersect(::VersionRange,::VersionRange)",
      "union!", "minimum(::VersionRange)"]
    statement := "Version bounds and ranges compare the stored significant prefix, preserve constructor normalization, and implement membership and intersection by the source bounds."
    source := "base/version.jl:299-504", status := .proven
    prop := ``Version.VersionBoundRangeBehavior, thm := some ``Version.versionBoundRangeBehavior },
  { id := "intfuncscov-version-spec", juliaFile := "base/version.jl"
    juliaFns := ["VersionSpec", "in(::VersionNumber,::VersionSpec)", "copy", "isempty",
      "intersect", "union", "==", "hash", "print", "show", "minimum"]
    statement := "VersionSpec constructors, membership, set operations, identity, hashing, display, and minimum use the canonical range list and source folds."
    source := "base/version.jl:509-620", status := .proven
    prop := ``Version.VersionSpecBehavior, thm := some ``Version.versionSpecBehavior },
  { id := "intfuncscov-matches-spec-unsorted", juliaFile := "base/version.jl"
    juliaFns := ["matches_spec_range!"]
    statement := "matches_spec_range! marks membership correctly even when the version list is unsorted."
    source := "base/version.jl:530-533", status := .refuted
    prop := ``Version.MatchesSpecRangeUnsorted, thm := some ``Version.matchesSpecRangeUnsorted_refuted
    issue := "none found (queries: matches_spec_range, VersionSpec, VersionBound)"
    notes := "The scan stops at the first value above a range and misses later in-range values." },
  { id := "intfuncscov-semver-spec-nothrow", juliaFile := "base/version.jl"
    juliaFns := ["semver_spec", "semver_interval", "inequality_interval", "hyphen_interval"]
    statement := "semver_spec with throw=false returns a VersionSpec or nothing for every string."
    source := "base/version.jl:626-751", status := .refuted
    prop := ``Version.SemverSpecNoThrow, thm := some ``Version.semverSpecNoThrow_refuted
    issue := "none found (queries: semver_spec, semver_spec throw, semver_spec InexactError, VersionSpec)"
    notes := "The matched <0 and 0.0.0 paths throw before the throw=false fallback." },
  { id := "intfuncscov-semver-source", juliaFile := "base/version.jl"
    juliaFns := ["semver_spec", "semver_interval", "inequality_interval", "hyphen_interval",
      "EditionNumber", "VersionedParse"]
    statement := "Compatibility specifier dispatch preserves its matched, unmatched, degenerate, and edition-forwarding source paths."
    source := "base/version.jl:626-764", status := .proven
    prop := ``Version.SemverSourceBehavior, thm := some ``Version.semverSourceBehavior },

  { id := "intfuncscov-uuid-bits", juliaFile := "base/uuid.jl"
    juliaFns := ["UUID", "convert(::Type{NTuple{2,UInt64}},::UUID)",
      "convert(::Type{NTuple{4,UInt32}},::UUID)", "UInt128", "hash", "_crc32c"]
    statement := "UUID constructors and tuple conversions preserve all 128 bits, and value forwarding supplies hashing and CRC with the same bits."
    source := "base/uuid.jl:11-39", status := .proven
    prop := ``UuidPkgid.UuidBitsBehavior, thm := some ``UuidPkgid.uuidBitsBehavior },
  { id := "intfuncscov-uuid-parse", juliaFile := "base/uuid.jl"
    juliaFns := ["takebytes", "parseuuid", "Parsers.parsevalue", "tryparse", "throw_malformed_uuid", "parse", "UUID(::AbstractString)"]
    statement := "UUID parsing consumes exactly the six source groups, checks dashes and hex digits, returns nothing from tryparse, and throws only in parse."
    source := "base/uuid.jl:41-96", status := .proven
    prop := ``UuidPkgid.UuidParseBehavior, thm := some ``UuidPkgid.uuidParseBehavior },
  { id := "intfuncscov-uuid-display", juliaFile := "base/uuid.jl"
    juliaFns := ["string", "print", "show", "isless", "broadcastable"]
    statement := "UUID string output has 36 characters and round-trips, ordering compares the 128-bit value, and display or broadcasting forwards that scalar value."
    source := "base/uuid.jl:98-124", status := .proven
    prop := ``UuidPkgid.UuidDisplayBehavior, thm := some ``UuidPkgid.uuidDisplayBehavior },
  { id := "intfuncscov-pkgid-source", juliaFile := "base/pkgid.jl"
    juliaFns := ["PkgId", "==", "hash", "show", "binpack", "binunpack"]
    statement := "PkgId normalizes zero UUIDs to nothing, compares and hashes both fields, displays them, and round-trips its binary packing for every name."
    source := "base/pkgid.jl:7-45", status := .proven
    prop := ``UuidPkgid.PkgIdBehavior, thm := some ``UuidPkgid.pkgIdBehavior }
]

end JuliaLean.IntFuncsCov
