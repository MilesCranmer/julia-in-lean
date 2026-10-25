import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Platforms.Props
import JuliaLean.Platforms.Refute
import JuliaLean.Platforms.MatchProofs
import JuliaLean.Platforms.SelectProofs
import JuliaLean.Platforms.CtorProofs
import JuliaLean.Platforms.Show
import JuliaLean.Platforms.DlProof
import JuliaLean.Platforms.CoreRoundtrip

namespace JuliaLean.Platforms

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "platforms-triplet-roundtrip", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["triplet(::AbstractPlatform)", "parse(::Type{Platform}, ::String)", "Platform(arch, os; kwargs...)"]
    statement := "parse(Platform, triplet(p)) == p for every Platform p accepted with validate_strict = true."
    source := "invariant; base/binaryplatforms.jl:755-759 (parse \"Parses a string platform triplet back into a Platform object\")"
    status := .refuted, prop := ``TripletRoundtrip, thm := some ``tripletRoundtrip_refuted
    issue := "none found (queries: BinaryPlatforms triplet, BinaryPlatforms triplet roundtrip, triplet os_version, libgfortran_version minor)"
    notes := "Platform(\"x86_64\", \"linux\"; foo = \"\", validate_strict = true) has triplet \"x86_64-linux-gnu-foo+\", which parse rejects. Also: libgfortran_version 6 (unparsable triplet), 4.1 (reparsed as 4.0.0), os_version on Linux/Windows (dropped). Same on 1.13.2." },
  { id := "platforms-openbsd-os-version", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["triplet(::AbstractPlatform)", "parse(::Type{Platform}, ::String)"]
    statement := "parse(Platform, triplet(p)) == p for every Platform p that parse(Platform, s) returns."
    source := "invariant; base/binaryplatforms.jl:755-759"
    status := .refuted, prop := ``ParseTripletParse, thm := some ``parseTripletParse_refuted
    issue := "none found (queries: openbsd platform triplet, openbsd os_version, BinaryPlatforms openbsd, triplet os_version, BinaryPlatforms triplet)"
    notes := "parse(Platform, \"x86_64-unknown-openbsd7.4\") has os_version 7.4.0, but its triplet is \"x86_64-unknown-openbsd\" (os_str prints no OpenBSD version). Same on 1.13.2." },
  { id := "platforms-validate-os-version", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["validate_tags(::Dict)", "triplet(::AbstractPlatform)", "os_version(::AbstractPlatform)"]
    statement := "triplet(p) returns for every Platform p accepted with validate_strict = true."
    source := "base/binaryplatforms.jl:135-138 (non-VersionNumber values are kept, but validate_strict \"will cause an error later on\")"
    status := .refuted, prop := ``StrictTripletTotal, thm := some ``strictTripletTotal_refuted
    issue := "none found (queries: validate_strict, os_version VersionNumber, BinaryPlatforms validate_strict, triplet os_version)"
    notes := "Platform(\"x86_64\", \"macos\"; os_version = \"foo\", validate_strict = true) is accepted; triplet and os_version throw ArgumentError. validate_tags checks libgfortran_version and cxxlib_version only. Same on 1.13.2." },
  { id := "platforms-match-reflexive", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["platforms_match(::AbstractPlatform, ::AbstractPlatform)"]
    statement := "platforms_match(p, p) == true for every Platform p accepted with validate_strict = true."
    source := "base/binaryplatforms.jl:1128-1141 (platforms_match docstring)"
    status := .refuted, prop := ``MatchReflexive, thm := some ``matchReflexive_refuted
    issue := "none found (queries: julia_version platforms_match, BinaryPlatforms julia_version, platforms_match, validate_strict)"
    notes := "julia_version = \"foo\" passes validate_strict; the julia_version strategy calls VersionNumber(\"foo\") and throws. Same on 1.13.2." },
  { id := "platforms-compare-strategies-alias", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["Platform(arch, os, tags; compare_strategies)"]
    statement := "The Platform constructor leaves the caller's compare_strategies Dict unchanged."
    source := "invariant (a constructor does not modify its arguments); base/binaryplatforms.jl:45-47"
    status := .refuted, prop := ``CtorKeepsStrategies, thm := some ``ctorKeepsStrategies_refuted
    issue := "none found (queries: compare_strategies, Platform compare_strategies, platforms_match)"
    notes := "With a julia_version tag the constructor inserts the julia_version strategy into the caller's Dict and stores that Dict; a concretely typed Dict throws MethodError instead. Same on 1.13.2." },
  { id := "platforms-select-order", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["select_platform(::Dict, ::AbstractPlatform)"]
    statement := "select_platform(d, host) depends only on the entries of d, not on its iteration order."
    source := "invariant; base/binaryplatforms.jl:1204-1209 (select_platform docstring)"
    status := .refuted, prop := ``SelectOrderIndependent, thm := some ``selectOrderIndependent_refuted
    issue := "none found (queries: select_platform, select_platform order)"
    notes := "Keys with libgfortran_version 5.0.0 and 5.5.0 share the triplet x86_64-linux-gnu-libgfortran5 and the same match loss; the stable sort keeps iteration order, so two equal Dicts built in different insertion orders select different values. Same on 1.13.2." },
  { id := "platforms-dl-name-four-part", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["parse_dl_name_version(::String, ::String)"]
    statement := "parse_dl_name_version(\"name.so.N1.N2...\", \"linux\") returns for every numeric soversion with components below 2^32."
    source := "base/binaryplatforms.jl:868-876 (docstring: parses what it can; throws only for paths that are not dynamic libraries)"
    status := .refuted, prop := ``DlNameNoThrow, thm := some ``dlNameNoThrow_refuted
    issue := "none found (queries: parse_dl_name_version, dynamic library invalid version string, soversion)"
    notes := "\"libcublas.so.12.1.3.1\" throws ArgumentError(\"invalid version string: 12.1.3.1\"); the regex accepts any number of components but VersionNumber at most three. Same for macOS and Windows names, and on 1.13.2." },
  { id := "platforms-detect-libstdcxx-csl", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["detect_libstdcxx_version(::Int)", "_get_libstdcxx_handle()"]
    statement := "detect_libstdcxx_version(m) returns a version whenever a loaded libstdc++ exports GLIBCXX_3.4.k for some 18 <= k <= m."
    source := "base/binaryplatforms.jl:1006-1012 (docstring: finds the libstdc++ version Julia is linked against)"
    status := .refuted, prop := ``DetectLibstdcxx, thm := some ``detectLibstdcxx_refuted
    issue := "#63967 (open, duplicate); queries: detect_libstdcxx_version, libstdcxx HostPlatform, _get_libstdcxx_handle"
    notes := "When CompilerSupportLibraries_jll is loaded (always on master), _get_libstdcxx_handle returns nothing in the branch meant to open its libstdc++. Reproduced on 1.13.2 after `using CompilerSupportLibraries_jll`. Separately, the default max_minor_version = 30 is below what the bundled libstdc++ exports (GLIBCXX_3.4.34 on Linux x86-64), so 1.13.2 reports v\"3.4.30\" without CSL (documented cap, not written up)." },
  { id := "platforms-match-symmetric", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["platforms_match(::AbstractPlatform, ::AbstractPlatform)", "compare_version_cap", "compare_default"]
    statement := "platforms_match(a, b) == platforms_match(b, a) whenever both return, for platforms using the comparison strategies defined in binaryplatforms.jl."
    source := "base/binaryplatforms.jl:1128-1146 (platforms_match docstring), 325-355 (compare_version_cap)"
    status := .proven, prop := ``MatchSymmetric, thm := some ``matchSymmetric_proven
    notes := "With a user-defined asymmetric strategy f, symmetry needs f(x, y, true, false) == f(y, x, false, true); compare_version_cap satisfies it." },
  { id := "platforms-match-order-independent", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["platforms_match(::AbstractPlatform, ::AbstractPlatform)"]
    statement := "The result of platforms_match does not depend on the iteration order of union(keys(tags(a)), keys(tags(b))) (whenever it returns)."
    source := "invariant; base/binaryplatforms.jl:1154"
    status := .proven, prop := ``MatchOrderIndependent, thm := some ``matchOrderIndependent_proven
    notes := "Which exception is thrown can depend on the order, when one key compares false and another throws." },
  { id := "platforms-match-semantics", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["platforms_match(::AbstractPlatform, ::AbstractPlatform)"]
    statement := "platforms_match(a, b) is true exactly when every key both have matches under the selected strategy and sanitize is present in both or neither; keys in only one platform are otherwise ignored."
    source := "base/binaryplatforms.jl:1128-1152 (platforms_match docstring)"
    status := .proven, prop := ``MatchSemantics, thm := some ``matchSemantics_proven },
  { id := "platforms-match-conflicting-strategies", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["platforms_match(::AbstractPlatform, ::AbstractPlatform)"]
    statement := "platforms_match never returns true when a and b set different non-default comparison strategies for a key both have."
    source := "base/binaryplatforms.jl:1140-1141 (\"We throw an error if custom comparison strategies are used on both a and b and they are not the same\")"
    status := .proven, prop := ``MatchConflictingStrategies, thm := some ``matchConflictingStrategies_proven
    notes := "It throws ArgumentError unless an earlier key in the iteration order already compared false." },
  { id := "platforms-strategy-semantics", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["compare_version_cap", "Platform constructor julia_version strategy"]
    statement := "compare_version_cap treats the requesting side's version as an upper bound (two caps: equality), and the default julia_version strategy compares major and minor only."
    source := "base/binaryplatforms.jl:325-355 (compare_version_cap docstring), 90-97"
    status := .proven, prop := ``StrategySemantics, thm := some ``strategySemantics_proven },
  { id := "platforms-select-best", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["select_platform(::Dict, ::AbstractPlatform)"]
    statement := "select_platform returns nothing only when no key matches, and otherwise the value of a matching key with the smallest match_loss whose triplet is lexicographically largest among matching keys with that loss."
    source := "base/binaryplatforms.jl:1204-1209 (docstring), 1222-1242 (comments: best match, then reverse-sorted triplet)"
    status := .proven, prop := ``SelectBest, thm := some ``selectBest_proven
    notes := "Relies on sort! being stable (the default since Julia 1.9); ties between equal triplets are platforms-select-order." },
  { id := "platforms-addtag-nonos", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["add_tag!(::Dict{String,String}, ::String, ::String)"]
    statement := "add_tag! throws exactly when the tag name or the lowercased value contains one of + - space / < > : \" ' \\ | ? *."
    source := "base/binaryplatforms.jl:155-158 (comment listing the disallowed characters)"
    status := .proven, prop := ``AddTagRejectsNonos, thm := some ``addTagRejectsNonos_proven
    notes := "The Platform docstring (base/binaryplatforms.jl:32-33) says tags and values are alphanumeric and period characters; the code deliberately accepts more (underscores, Unicode, empty strings)." },
  { id := "platforms-constructor-defaults", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["Platform(arch, os)", "arch", "os", "libc", "call_abi", "CPUID.normalize_arch"]
    statement := "Platform(arch, os) has arch normalize_arch(arch), os lowercase(os), libc glibc on Linux and msvcrt on Windows (none elsewhere), and call_abi eabihf exactly on 32-bit ARM Linux."
    source := "base/binaryplatforms.jl:381-461 (accessor docstrings and doctests), 71-83"
    status := .proven, prop := ``ConstructorDefaults, thm := some ``constructorDefaults_proven },
  { id := "platforms-show-tag-names", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["show(::IO, ::Platform)"]
    statement := "Every tag name show(::IO, ::Platform) prints as a keyword argument is a valid argument name, so repr(p) is valid Julia."
    source := "base/binaryplatforms.jl:198 (\"Allow us to easily serialize Platform objects\"), 32-33 (tag names may contain periods)"
    status := .refuted, prop := ``ShowKeysAreNames, thm := some ``showKeysAreNames_refuted
    issue := "none found (queries: Platform show, Platform repr, BinaryPlatforms show)"
    notes := "repr(Platform(\"x86_64\", \"linux\", Dict(\"cuda.version\" => \"11.8\"))) prints `cuda.version = \"11.8\"`, which does not parse; names starting with a digit or equal to a keyword fail too. show also drops comparison strategies (HostPlatform). Same on 1.13.2." },
  { id := "platforms-dl-name-inverse", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["parse_dl_name_version(::String, ::String)", "platform_dlext(::AbstractPlatform)"]
    statement := "parse_dl_name_version recovers (name, v) from the file name name.so[.v] (Linux/BSD), name[.v].dylib (macOS) or name[-v].dll (Windows) with the extension platform_dlext(p), for every name without '/' the scheme does not make ambiguous and every version without prerelease or build part."
    source := "base/binaryplatforms.jl:868-907 (docstring and the naming comments in parse_dl_name_version), 840-855 (platform_dlext)"
    status := .proven, prop := ``DlNameInverse, thm := some ``dlNameInverse_proven
    notes := "Ambiguous names (excluded): on macOS a name ending in .<digits> (plus a tag when unversioned), e.g. libpython3.10.dylib parses as (\"libpython3\", v\"10\"); on Windows an unversioned name ending in -, -<digits/dots> or -<digits/dots><tag>." },
  { id := "platforms-core-triplet-roundtrip", juliaFile := "base/binaryplatforms.jl"
    juliaFns := ["triplet(::AbstractPlatform)", "parse(::Type{Platform}, ::String)", "Platform(arch, os; libc, call_abi)"]
    statement := "parse(Platform, triplet(p)) == p for every Platform(arch, os; libc?, call_abi?) accepted with validate_strict = true (every architecture/OS/libc/call ABI combination)."
    source := "invariant; base/binaryplatforms.jl:755-759"
    status := .proven, prop := ``CoreTripletRoundtrip, thm := some ``coreTripletRoundtrip_proven
    notes := "61 accepted combinations of 7 architectures, 5 OSes, libc and call_abi. The round trip fails once other tags are involved: see platforms-triplet-roundtrip and platforms-openbsd-os-version." }
]

end JuliaLean.Platforms
