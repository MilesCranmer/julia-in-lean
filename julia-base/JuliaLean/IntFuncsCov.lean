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
  { id := "intfuncscov-gcd-mixed-typemin", juliaFile := "base/intfuncs.jl"
    juliaFns := ["_promote_mixed_signs", "gcd(::Signed,::Unsigned)",
      "gcd(::Unsigned,::Signed)", "lcm(::Signed,::Unsigned)",
      "gcdx(::Signed,::Unsigned)", "gcdx(::Unsigned,::Signed)"]
    statement := "A signed typemin and same-width unsigned value have a representable gcd, lcm, and Bezout result in their promoted type."
    source := "base/intfuncs.jl:8,100,146-160,192-198,276-284", status := .refuted
    prop := ``Gcd.MixedTypeminRepresentable, thm := some ``Gcd.mixedTypeminRepresentable_refuted
    issue := "duplicate #59660; queries: gcd typemin, gcd InexactError, gcd unsigned signed, _promote_mixed_signs"
    notes := "Same-width signed typemin reaches abs(a % signed(R)) and throws InexactError before promotion." },
  { id := "intfuncscov-gcd-array-typemin", juliaFile := "base/intfuncs.jl"
    juliaFns := ["gcd(::AbstractArray{<:Integer})"]
    statement := "The gcd of an integer array returns its representable mathematical gcd."
    source := "base/intfuncs.jl:8,178-187", status := .refuted
    prop := ``Gcd.GcdArrayRepresentable, thm := some ``Gcd.gcdArrayRepresentable_refuted
    issue := "related #59660; queries: gcd typemin, gcd array OverflowError"
    notes := "Starting the fold at zero makes a leading typemin throw before a later element reduces the gcd." },
  { id := "intfuncscov-number-theory-source", juliaFile := "base/intfuncs.jl"
    juliaFns := ["gcd", "lcm", "absdiff", "_gcd", "_promote_mixed_signs", "gcdx",
      "_gcdx_update", "_bezout_coef", "invmod"]
    statement := "Number-theory loops, mixed dispatch, array folds, n-ary recursion, and modular-inverse wrappers follow the source branches for every model input."
    source := "base/intfuncs.jl:44-382", status := .proven
    prop := ``Simple.NumberTheorySourceBehavior, thm := some ``Simple.numberTheorySourceBehavior },
  { id := "intfuncscov-power-source", juliaFile := "base/intfuncs.jl"
    juliaFns := ["throw_domerr_powbysq", "power_by_squaring", "^", "literal_pow",
      "powermod", "_powermod_mi_legal", "_nextpow2", "_prevpow2", "ispow2"]
    statement := "Integer powers, literal-power dispatch, modular powers, power-of-two helpers, and error dispatch preserve the source branch order for every model input."
    source := "base/intfuncs.jl:384-624", status := .proven
    prop := ``Simple.PowerSourceBehavior, thm := some ``Simple.powerSourceBehavior },
  { id := "intfuncscov-digits-source", juliaFile := "base/intfuncs.jl"
    juliaFns := ["nextpow", "prevpow", "top_set_bit", "ndigits0z", "ndigits0znb",
      "ndigits0zpb", "ndigits", "bin", "oct", "dec", "hex", "_base", "split_sign",
      "string", "bitstring", "digits", "digits!", "hastypemax"]
    statement := "Power rounding, digit counting, integer formatting, bit strings, digit extraction, and type-extrema dispatch follow their source formulas for every model input."
    source := "base/intfuncs.jl:626-1281", status := .proven
    prop := ``Simple.DigitsSourceBehavior, thm := some ``Simple.digitsSourceBehavior },
  { id := "intfuncscov-combinatorial-source", juliaFile := "base/intfuncs.jl"
    juliaFns := ["isqrt", "factorial", "binomial"]
    statement := "Integer square root, factorial, and integer or generalized binomial dispatch use the source result types, checks, and arithmetic loops."
    source := "base/intfuncs.jl:1293-1433", status := .proven
    prop := ``Simple.CombinatoricsSourceBehavior, thm := some ``Simple.combinatoricsSourceBehavior },
  { id := "intfuncscov-clamp-source", juliaFile := "base/intfuncs.jl"
    juliaFns := ["clamp", "clamp!", "clamp(::Integer,::AbstractUnitRange)"]
    statement := "Clamp promotes or converts the selected bound or value, clamp! applies that operation in index order, and range clamp forwards its endpoints."
    source := "base/intfuncs.jl:1461-1533", status := .proven
    prop := ``Simple.ClampSourceBehavior, thm := some ``Simple.clampSourceBehavior },

  { id := "intfuncscov-hash-primitives", juliaFile := "base/hashing.jl"
    juliaFns := ["hash", "_jl_type_hash", "mul_parts", "hash_mix", "hash_mix_linear",
      "hash_finalizer", "hash_64_64", "hash_64_32", "hash_32_32"]
    statement := "Hash primitive multiplication, mixing, finalization, and forwarding use wrapping UInt arithmetic and the source argument order."
    source := "base/hashing.jl:40-77", status := .proven
    prop := ``Hashing.HashPrimitiveBehavior, thm := some ``Hashing.hashPrimitiveBehavior },
  { id := "intfuncscov-hash-numeric", juliaFile := "base/hashing.jl"
    juliaFns := ["IntegerCodeUnits", "size", "length", "getindex", "load_le_array",
      "codeunits", "utf8units", "iterate", "hash_integer", "_hash_integer",
      "hash(::Float64)", "hash(::Float32)", "hash(::Float16)", "hash(::Real)"]
    statement := "Integer code units are the minimal little-endian magnitude bytes, while integer, float, real, and string hash dispatch follows the source normalization paths."
    source := "base/hashing.jl:79-245", status := .proven
    prop := ``Hashing.HashIntegerUnitsBehavior, thm := some ``Hashing.hashIntegerUnitsBehavior },
  { id := "intfuncscov-hash-structural", juliaFile := "base/hashing.jl"
    juliaFns := ["hash(::QuoteNode)", "hash(::PhiNode)", "hash(::PhiCNode)",
      "hash(::Expr)", "hash(::CodeInfo)", "hash(::DebugInfo)", "hash(::Symbol)",
      "hash(::GlobalRef)", "hash(::PartialStruct)"]
    statement := "Compiler-IR hashes mix their tag seed and fields in the source order for every field hash callback."
    source := "base/hashing.jl:248-293", status := .proven
    prop := ``Hashing.HashStructuralBehavior, thm := some ``Hashing.hashStructuralBehavior },
  { id := "intfuncscov-hash-bytes", juliaFile := "base/hashing.jl"
    juliaFns := ["load_le", "hash_bytes", "load_le_array", "concat_shift",
      "read_uint64_from_uint8_iter"]
    statement := "Pointer, array, and iterator byte hashing produce the same rapid-hash value for the same byte sequence, including every length branch and 48-byte chunk."
    source := "base/hashing.jl:296-647", status := .proven
    prop := ``Hashing.HashBytesBehavior, thm := some ``Hashing.hashBytesBehavior },

  { id := "intfuncscov-multiplicative-inverse-source", juliaFile := "base/multinverses.jl"
    juliaFns := ["unsigned", "SignedMultiplicativeInverse", "UnsignedMultiplicativeInverse",
      "div", "rem", "divrem", "mod", "multiplicativeinverse"]
    statement := "Magic-number constructors and division, remainder, modulus, divrem, and dispatch agree with the source algorithms for every fixed-width input."
    source := "base/multinverses.jl:8-164", status := .proven
    prop := ``Simple.MultiplicativeInverseSourceBehavior,
    thm := some ``Simple.multiplicativeInverseSourceBehavior },

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

  { id := "intfuncscov-char-encoding", juliaFile := "base/char.jl"
    juliaFns := ["AbstractChar", "Char", "codepoint", "ismalformed", "isoverlong",
      "unsafe_codepoint", "decode_overlong", "UInt32", "UInt32_cold", "Char_cold", "convert", "rem"]
    statement := "Character construction, decoding, malformed and overlong checks, unsafe decoding, and numeric conversion follow the source bit operations for every Char bit pattern."
    source := "base/char.jl:54-239", status := .proven
    prop := ``Char.CharEncodingBehavior, thm := some ``Char.charEncodingBehavior },
  { id := "intfuncscov-char-scalar", juliaFile := "base/char.jl"
    juliaFns := ["typemin", "typemax", "size", "ndims", "length", "IteratorSize",
      "firstindex", "lastindex", "getindex", "first", "last", "eltype", "iterate",
      "isempty", "in", "==", "isless", "hash", "widen", "-%", "-", "+%", "+"]
    statement := "AbstractChar scalar indexing, iteration, comparison, traits, and arithmetic preserve the source values, checks, and codepoint arithmetic."
    source := "base/char.jl:241-300", status := .proven
    prop := ``Char.CharScalarBehavior, thm := some ``Char.charScalarBehavior },
  { id := "intfuncscov-char-display", juliaFile := "base/char.jl"
    juliaFns := ["print", "show_invalid", "show", "show(::MIME\"text/plain\")"]
    statement := "Character printing emits the encoded bytes; invalid display emits byte escapes; plain display preserves the literal and reports malformed, overlong, and codepoint state."
    source := "base/char.jl:305-392", status := .proven
    prop := ``Char.CharDisplayBehavior, thm := some ``Char.charDisplayBehavior },

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
