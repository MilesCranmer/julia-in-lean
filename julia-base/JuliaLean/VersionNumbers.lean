import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.VersionNumbers.Model
import JuliaLean.VersionNumbers.Props
import JuliaLean.VersionNumbers.Refute
import JuliaLean.VersionNumbers.Next
import JuliaLean.VersionNumbers.Range

namespace JuliaLean.VersionNumbers

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "versionnumbers-tryparse-throws", juliaFile := "base/version.jl"
    juliaFns := ["tryparse(::Type{VersionNumber}, ::AbstractString)", "split_idents"]
    statement := "tryparse(VersionNumber, s) returns a VersionNumber or nothing and never throws, for every string s."
    source := "base/parse.jl (tryparse docstring: returns nothing if the string is not valid)", status := .refuted
    prop := ``TryparseNothrow, thm := some ``tryparseNothrow_refuted
    issue := "PR #59609 (open, duplicate); queries: tryparse VersionNumber, VersionNumber overflow, VersionNumber OverflowError, VersionNumber unicode"
    notes := "parse(VInt, ...) and parse(UInt64, ...) throw: tryparse(VersionNumber, \"4294967296\") throws OverflowError, and \"\\u0661\" (matched by \\d under UCP) throws ArgumentError. Same on 1.13.2." },
  { id := "versionnumbers-ident-trailing-newline", juliaFile := "base/version.jl"
    juliaFns := ["VersionNumber(major, minor, patch, pre, bld)", "print(::IO, ::VersionNumber)", "parse(::Type{VersionNumber}, ::AbstractString)"]
    statement := "parse(VersionNumber, string(v)) == v for every VersionNumber v the constructor accepts."
    source := "invariant; base/version.jl:11-16 (semver identifiers), 65, 75 (identifier checks)", status := .refuted
    prop := ``PrintParseRoundtrip, thm := some ``printParseRoundtrip_refuted
    issue := "none found (queries: VersionNumber newline, VersionNumber prerelease identifier, version.jl regex, VersionNumber)"
    notes := "`$` matches before a final newline: VersionNumber(1, 0, 0, (\"a\\n\",)) is accepted and reparses as v\"1.0.0-a\"; parse(VersionNumber, \"1.2.3\\n\") also succeeds. Same on 1.13.2." },
  { id := "versionnumbers-ident-nonascii", juliaFile := "base/version.jl"
    juliaFns := ["tryparse(::Type{VersionNumber}, ::AbstractString)", "VersionNumber(major, minor, patch, pre, bld)"]
    statement := "Every identifier of a VersionNumber returned by parse consists of [0-9A-Za-z-]."
    source := "base/version.jl:11-14 (semver 2.0.0-rc.2), manual Version Number Literals", status := .refuted
    prop := ``ParseIdentCharset, thm := some ``parseIdentCharset_refuted
    issue := "none found (queries: VersionNumber unicode, VersionNumber prerelease identifier, VersionNumber)"
    notes := "Caseless [a-z] under UCP also matches U+017F and U+212A: v\"1-\\u017f\" parses. Same on 1.13.2." },
  { id := "versionnumbers-negative-inexacterror", juliaFile := "base/version.jl"
    juliaFns := ["VersionNumber(major::Integer, minor, patch, pre, bld)"]
    statement := "VersionNumber(major, minor, patch, pre, bld) with a negative integer component or identifier throws ArgumentError."
    source := "base/version.jl:58-60, 63, 73 (the constructor's negative-value checks)", status := .refuted
    prop := ``NegativeArgumentError, thm := some ``negativeArgumentError_refuted
    issue := "none found (queries: VersionNumber negative, VersionNumber InexactError, VersionNumber)"
    notes := "VInt(major)/UInt64(x) at base/version.jl:87-89 throw InexactError first; the ArgumentError checks are dead. Same on 1.13.2." },
  { id := "versionnumbers-range-print-upper", juliaFile := "base/version.jl"
    juliaFns := ["print(::IO, ::VersionRange)", "VersionRange(::AbstractString)", "in(::VersionNumber, ::VersionRange)"]
    statement := "VersionRange(string(r)) contains exactly the versions r contains, for every range built from well-formed bounds."
    source := "invariant; base/version.jl:466 (show prints VersionRange(\"<string(r)>\"))", status := .refuted
    prop := ``RangePrintRoundtrip, thm := some ``rangePrintRoundtrip_refuted
    issue := "none found (queries: VersionRange print, VersionRange show, VersionRange, VersionSpec print, compat star range)"
    notes := "string(VersionRange(\"*-2\")) == \"0 -2.0.0\", whose reparse excludes v\"2.5.0\". On 1.13.2 the same code is Pkg.Versions.VersionRange (the repro uses it there)." },
  { id := "versionnumbers-eq-structural", juliaFile := "base/version.jl"
    juliaFns := ["==(::VersionNumber, ::VersionNumber)"]
    statement := "a == b holds exactly when all five fields of a and b are equal."
    source := "base/version.jl:194-201", status := .proven
    prop := ``EqStructural, thm := some ``eqStructural_proven },
  { id := "versionnumbers-hash-consistent", juliaFile := "base/version.jl"
    juliaFns := ["hash(::VersionNumber, ::UInt)", "==(::VersionNumber, ::VersionNumber)"]
    statement := "a == b implies hash(a, h) == hash(b, h), for any hash methods of the fields."
    source := "base/hashing.jl (hash docstring: isequal(x,y) implies hash(x)==hash(y))", status := .proven
    prop := ``HashConsistent, thm := some ``hashConsistent_proven },
  { id := "versionnumbers-isless-total-order", juliaFile := "base/version.jl"
    juliaFns := ["isless(::VersionNumber, ::VersionNumber)", "<", "=="]
    statement := "isless on VersionNumber is a strict total order whose incomparable pairs are exactly the == pairs."
    source := "base/version.jl:18-20 (comparison operators follow semver), base/operators.jl (isless docstring: total order)", status := .proven
    prop := ``IslessTotalOrder, thm := some ``islessTotalOrder_proven },
  { id := "versionnumbers-semver-precedence", juliaFile := "base/version.jl"
    juliaFns := ["isless(::VersionNumber, ::VersionNumber)"]
    statement := "Pre-releases precede the release; builds follow the normal version; numeric identifiers compare numerically, alphanumeric ones in ASCII order, numeric before alphanumeric; a longer pre-release with equal prefix is later."
    source := "base/version.jl:18-20 (semver 2.0.0-rc.2 rules)", status := .proven
    prop := ``SemverPrecedence, thm := some ``semverPrecedence_proven },
  { id := "versionnumbers-typemin-typemax", juliaFile := "base/version.jl"
    juliaFns := ["typemin(::Type{VersionNumber})", "typemax(::Type{VersionNumber})"]
    statement := "typemin(VersionNumber) == v\"0-\" <= v <= typemax(VersionNumber) for every VersionNumber v."
    source := "base/version.jl:173-178 (typemin/typemax)", status := .proven
    prop := ``TypeminTypemax, thm := some ``typeminTypemax_proven },
  { id := "versionnumbers-bounds-bracket", juliaFile := "base/version.jl"
    juliaFns := ["lowerbound(::VersionNumber)", "upperbound(::VersionNumber)"]
    statement := "lowerbound(v) precedes exactly the versions whose major.minor.patch is at least v's (pre-releases included), and upperbound(v) follows exactly those whose major.minor.patch is at most v's."
    source := "manual, Version Number Literals (v\"0.3-\" is lower than any 0.3 release, including its pre-releases)", status := .proven
    prop := ``BoundsBracket, thm := some ``boundsBracket_proven },
  { id := "versionnumbers-next-least", juliaFile := "base/version.jl"
    juliaFns := ["nextpatch", "nextminor", "nextmajor"]
    statement := "Below typemax(UInt32), nextpatch(v) is the least plain version above v, nextminor(v) the least plain x.y.0 above v, nextmajor(v) the least plain x.0.0 above v, also for pre-release and build inputs."
    source := "invariant (names; base/version.jl:240-242)", status := .proven
    prop := ``NextLeast, thm := some ``nextLeast_proven },
  { id := "versionnumbers-next-overflow", juliaFile := "base/version.jl"
    juliaFns := ["nextpatch", "nextminor", "nextmajor"]
    statement := "When the component to increment is typemax(UInt32) and v is no pre-release, nextpatch/nextminor/nextmajor throw InexactError rather than wrap."
    source := "invariant (no silent wraparound)", status := .proven
    prop := ``NextOverflow, thm := some ``nextOverflow_proven },
  { id := "versionnumbers-this-monotone", juliaFile := "base/version.jl"
    juliaFns := ["thispatch", "thisminor", "thismajor"]
    statement := "thispatch, thisminor, thismajor always succeed, drop the annotations and lower components, and are monotone."
    source := "invariant (base/version.jl:236-238)", status := .proven
    prop := ``ThisMonotone, thm := some ``thisMonotone_proven }
]

end JuliaLean.VersionNumbers
