import JuliaLean.Platforms.Basic

/-!
# `parse(::Type{Platform}, triplet)` (`base/binaryplatforms.jl:659-838`)

`triplet_regex` is compiled with Julia's default options (`UTF | UCP`, no
`s`): `\d` is a Unicode decimal digit, `.` is any character but `\n`, and `$`
also matches before a final `\n`. The alternatives of each group appear in the
iteration order of the mapping `Dict`s, which was printed on Linux x86-64 (identical
on 1.13.2 and master):

    arch_mapping:     armv6l, x86_64, i686, aarch64, powerpc64le, armv7l, riscv64
    os_mapping:       macos, openbsd, linux, freebsd, windows
    libc_mapping:     musl, ucrt, msvcrt, glibc, libc_nothing
    call_abi_mapping: eabi, call_abi_nothing, eabihf
    libgfortran:      libgfortran_nothing, libgfortran5, libgfortran3, libgfortran4
    cxxstring_abi:    cxx03, cxx11, cxxstring_nothing
    libstdcxx:        libstdcxx, libstdcxx_nothing

The pattern printed on master is

    ^((?<armv6l>armv6l)|(?<x86_64>(x86_|amd)64)|(?<i686>i\d86)|(?<aarch64>(aarch64|arm64))|
    (?<powerpc64le>p(ower)?pc64le)|(?<armv7l>arm(v7l)?)|(?<riscv64>(rv64|riscv64)))
    ((?<macos>-apple-darwin[\d\.]*)|(?<openbsd>-(.*-)?openbsd[\d\.]*)|(?<linux>-(.*-)?linux)|
    (?<freebsd>-(.*-)?freebsd[\d\.]*)|(?<windows>-w64))
    ((?<musl>-musl)|(?<ucrt>-ucrt-mingw32)|(?<msvcrt>-mingw32)|(?<glibc>-gnu)|(?<libc_nothing>))
    ((?<eabi>eabi)|(?<call_abi_nothing>)|(?<eabihf>eabihf))
    ((?<libgfortran_nothing>)|(?<libgfortran5>(-libgfortran5)|(-gcc8))|
    (?<libgfortran3>(-libgfortran3)|(-gcc4))|(?<libgfortran4>(-libgfortran4)|(-gcc7)))
    ((?<cxx03>-cxx03)|(?<cxx11>-cxx11)|(?<cxxstring_nothing>))
    ((?<libstdcxx>-libstdcxx\d+)|(?<libstdcxx_nothing>))(?<tags>(?:-[^-]+\+[^-]+)*)?$

Only the named groups are captured in the model (the others need no capture).
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (Re matchRe capture isUcpDigit VersionNumber versionOf u32)
open JuliaLean.VersionNumbers.Re

/-- A literal string. -/
def lit (s : Str) : Re := seqs (s.map chr)

/-- Ordered alternation of a list of patterns. -/
def alts : List Re → Re
  | [] => cls (fun _ => false)
  | [a] => a
  | a :: as => alt a (alts as)

/-- `.` without the `s` flag. -/
def notNL (c : Char) : Bool := c != '\n'

/-- `[\d\.]`. -/
def digitDot (c : Char) : Bool := isUcpDigit c || c == '.'

/-- `[^-]`. -/
def notDash (c : Char) : Bool := c != '-'

/-- A mapping: named alternatives in `Dict` order, each with its group number and pattern. -/
abbrev Mapping := List (Str × Nat × Re)

def mappingRe (m : Mapping) : Re := alts (m.map fun (_, i, r) => group i r)

def archMapping : Mapping := [
  (s% "armv6l", 1, lit (s% "armv6l")),
  (s% "x86_64", 2, seq (alt (lit (s% "x86_")) (lit (s% "amd"))) (lit (s% "64"))),
  (s% "i686", 3, seqs [chr 'i', cls isUcpDigit, lit (s% "86")]),
  (s% "aarch64", 4, alt (lit (s% "aarch64")) (lit (s% "arm64"))),
  (s% "powerpc64le", 5, seqs [chr 'p', opt (lit (s% "ower")), lit (s% "pc64le")]),
  (s% "armv7l", 6, seq (lit (s% "arm")) (opt (lit (s% "v7l")))),
  (s% "riscv64", 7, alt (lit (s% "rv64")) (lit (s% "riscv64")))]

/-- `-(.*-)?NAME[\d\.]*` (`withVersion`) or `-(.*-)?NAME`. -/
def anyPrefixed (name : Str) (withVersion : Bool) : Re :=
  seqs [chr '-', opt (seq (star (cls notNL)) (chr '-')), lit name,
    if withVersion then star (cls digitDot) else eps]

def osMapping : Mapping := [
  (s% "macos", 10, seq (lit (s% "-apple-darwin")) (star (cls digitDot))),
  (s% "openbsd", 11, anyPrefixed (s% "openbsd") true),
  (s% "linux", 12, anyPrefixed (s% "linux") false),
  (s% "freebsd", 13, anyPrefixed (s% "freebsd") true),
  (s% "windows", 14, lit (s% "-w64"))]

def libcMapping : Mapping := [
  (s% "musl", 20, lit (s% "-musl")),
  (s% "ucrt", 21, lit (s% "-ucrt-mingw32")),
  (s% "msvcrt", 22, lit (s% "-mingw32")),
  (s% "glibc", 23, lit (s% "-gnu")),
  (s% "libc_nothing", 24, eps)]

def callAbiMapping : Mapping := [
  (s% "eabi", 30, lit (s% "eabi")),
  (s% "call_abi_nothing", 31, eps),
  (s% "eabihf", 32, lit (s% "eabihf"))]

def libgfortranMapping : Mapping := [
  (s% "libgfortran_nothing", 40, eps),
  (s% "libgfortran5", 41, alt (lit (s% "-libgfortran5")) (lit (s% "-gcc8"))),
  (s% "libgfortran3", 42, alt (lit (s% "-libgfortran3")) (lit (s% "-gcc4"))),
  (s% "libgfortran4", 43, alt (lit (s% "-libgfortran4")) (lit (s% "-gcc7")))]

def cxxstringMapping : Mapping := [
  (s% "cxx03", 50, lit (s% "-cxx03")),
  (s% "cxx11", 51, lit (s% "-cxx11")),
  (s% "cxxstring_nothing", 52, eps)]

def libstdcxxMapping : Mapping := [
  (s% "libstdcxx", 60, seq (lit (s% "-libstdcxx")) (plus (cls isUcpDigit))),
  (s% "libstdcxx_nothing", 61, eps)]

/-- Group number of `(?<tags>...)`. -/
def tagsGroup : Nat := 70

/-- `triplet_regex`, `base/binaryplatforms.jl:733-753`. -/
def tripletRe : Re :=
  seqs [mappingRe archMapping, mappingRe osMapping, mappingRe libcMapping, mappingRe callAbiMapping,
    mappingRe libgfortranMapping, mappingRe cxxstringMapping, mappingRe libstdcxxMapping,
    opt (group tagsGroup (star (seqs [chr '-', plus (cls notDash), chr '+', plus (cls notDash)]))),
    eol]

/-- A field returned by `get_field`: a key name, a `VersionNumber`, or `nothing`. -/
inductive Field where
  | key (k : Str)
  | ver (v : VersionNumber)
  | none

/-- `get_field(m, mapping)`, `base/binaryplatforms.jl:765-782`: the first key
(in `Dict` order) whose group participated in the match. Returns `nothing`
(here `Field.none` as well) when no group did, which a successful match rules out. -/
def getField (m : VersionNumbers.Caps) : Mapping → Jl Field
  | [] => pure .none
  | (k, i, _) :: rest =>
    match capture m i with
    | none => getField m rest
    | some cap =>
      if k.reverse.take 8 == (s% "_nothing").reverse then pure .none
      else if startsWith k (s% "libgfortran") then do
        let n ← VersionNumbers.parseUnsigned .i64 (k.drop 11)
        .ver <$> VersionNumbers.versionNumber n (JInt.wrap .i64 0) (JInt.wrap .i64 0)
      else if startsWith k (s% "libstdcxx") then do
        let n ← VersionNumbers.parseUnsigned .i64 (cap.drop 10)
        .ver <$> VersionNumbers.versionNumber (JInt.wrap .i64 3) (JInt.wrap .i64 4) n
      else pure (.key k)

def fieldVal : Field → TagVal
  | .key k => .str k
  | .ver v => .ver v
  | .none => .none

/-- `split(s, sep)` (keeping empty fields). -/
def splitOn (sep : Char) : Str → List Str
  | [] => [[]]
  | c :: cs =>
    match splitOn sep cs with
    | [] => [[c]]
    | w :: ws => if c == sep then [] :: w :: ws else (c :: w) :: ws

/-- `split(s, sep; keepempty=false)`. -/
def splitKeepNonempty (sep : Char) (s : Str) : List Str := (splitOn sep s).filter (!·.isEmpty)

/-- `split_tags(tagstr)`, `base/binaryplatforms.jl:793-799`: each field
`k+v...` gives `k => v`; a field without `+` is a `BoundsError` (the regex
rules it out). -/
def splitTags (tagstr : Str) : Jl (List (Str × Str)) :=
  (splitKeepNonempty '-' tagstr).mapM fun f =>
    match splitOn '+' f with
    | k :: v :: _ => pure (k, v)
    | _ => throw .boundsError

/-- Insert into a `Dict{String,Any}` given as a list with unique keys. -/
def dput {V : Type} (d : Dict V) (k : Str) (v : V) : Dict V := dset d k v

/-- `extract_os_version(os_name, pattern)` with `pattern = r".*NAME([\d.]+)"sa`
(byte mode, `\d` ASCII, `.` any byte), `base/binaryplatforms.jl:803-809`.
The pattern is unanchored, but its leading `.*` (with `s`) makes the match at
offset 0 the first one whenever there is a match. -/
def extractOsVersion (osField : Str) (name : Str) : Jl (Option VersionNumber) :=
  let asciiDigitDot (c : Char) : Bool := ('0' ≤ c ∧ c ≤ '9') || c == '.'
  let re := seqs [star (cls fun _ => true), lit name, group 1 (plus (cls asciiDigitDot))]
  match matchRe re osField with
  | none => pure none
  | some m => some <$> VersionNumbers.parse ((capture m 1).getD [])

section
variable (lc : Char → Char)

/-- `parse(::Type{Platform}, triplet::String; validate_strict)`,
`base/binaryplatforms.jl:760-825`. The `Dict{String,Any}` handed to the
constructor is built with `tags[k] = v` and `merge!` (a later write to an
existing key replaces it) and the constructor iterates it in hash order. That
order matters only for `libstdcxx_version` (written as `cxxlib_version`)
against an extended `cxxlib_version` tag; on Linux x86-64 `cxxlib_version` always
comes first (differential test, 56 such inputs), so the model passes
`libstdcxx_version` last and the other keys in insertion order. -/
def parsePlatform (validateStrict : Bool) (t : Str) : Jl Platform := do
  match matchRe tripletRe t with
  | none => throw (.argumentError "not an officially supported platform")
  | some m =>
    let archF ← getField m archMapping
    let osF ← getField m osMapping
    let (a, o) ← match archF, osF with
      | .key a, .key o => pure (a, o)
      | _, _ => throw (.methodError "Platform")
    let d : Dict TagVal := []
    let d := dput d (s% "libc") (fieldVal (← getField m libcMapping))
    let d := dput d (s% "call_abi") (fieldVal (← getField m callAbiMapping))
    let d := dput d (s% "libgfortran_version") (fieldVal (← getField m libgfortranMapping))
    let d := dput d (s% "libstdcxx_version") (fieldVal (← getField m libstdcxxMapping))
    let d := dput d (s% "cxxstring_abi") (fieldVal (← getField m cxxstringMapping))
    let ext ← splitTags ((capture m tagsGroup).getD [])
    let d := ext.foldl (fun d kv => dput d kv.1 (.str kv.2)) d
    let osv ← if o == s% "macos" then extractOsVersion ((capture m 10).getD []) (s% "darwin")
      else if o == s% "freebsd" then extractOsVersion ((capture m 13).getD []) (s% "freebsd")
      else if o == s% "openbsd" then extractOsVersion ((capture m 11).getD []) (s% "openbsd")
      else pure none
    let d := dput d (s% "os_version") (match osv with | some v => .ver v | none => .none)
    let isStd (e : Str × TagVal) : Bool := e.1 == s% "libstdcxx_version"
    platform lc a o (d.filter (!isStd ·) ++ d.filter isStd) validateStrict

end

end JuliaLean.Platforms
