import JuliaLean.Core
import JuliaLean.VersionNumbers.Model
import JuliaLean.Platforms.Lit

/-!
# `Platform` objects (`base/binaryplatforms.jl`, master `bbfa0ce4150`)

Julia `String`s are lists of characters (valid UTF-8). `Dict{String,String}`
tag maps are association lists with unique keys (`Tags`); the model never
relies on their order, because Julia's `Dict` order is hash-based: functions
that iterate a Julia `Dict` either sort first (as `triplet` does) or take the
iteration order as an explicit argument.

`lowercase(::String)` maps every character through utf8proc's simple
lowercase mapping; the mapping is a parameter `lc : Char → Char`, constrained
only on ASCII and on the reserved punctuation (`LcSpec`).
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber vprint)

abbrev Str := List Char

/-! ## Strings -/

/-- Uppercase ASCII letters and their lowercase forms. -/
def upperLower : List (Char × Char) :=
  (s% "ABCDEFGHIJKLMNOPQRSTUVWXYZ").zip (s% "abcdefghijklmnopqrstuvwxyz")

/-- ASCII lowercase. -/
def asciiLower (c : Char) : Char := ((upperLower.find? (·.1 == c)).map (·.2)).getD c

/-- The characters `add_tag!` rejects: `raw"""+- /<>:"'\|?*"""`,
`base/binaryplatforms.jl:159`. -/
def nonos : Str := ['+', '-', ' ', '/', '<', '>', ':', '"', '\'', '\\', '|', '?', '*']

def isNono (c : Char) : Bool := nonos.contains c

/-- What the model assumes of utf8proc's lowercase mapping: the ASCII part,
and that no character other than the (caseless) punctuation in `nonos` maps
to one of them. -/
def LcSpec (lc : Char → Char) : Prop :=
  (∀ c : Char, c.toNat < 128 → lc c = asciiLower c) ∧ (∀ c : Char, isNono (lc c) = true → lc c = c)

/-- `lowercase(s::String)`. -/
def lower (lc : Char → Char) (s : Str) : Str := s.map lc

/-- `isless(a::String, b::String)`: lexicographic on code points, which is
the byte order of valid UTF-8. -/
def strLt : Str → Str → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else strLt as bs

/-- `startswith(s, p)`. -/
def startsWith (s p : Str) : Bool := s.take p.length == p

/-- Insert `x`, which precedes every element of the sorted list in the input,
before the first element not less than it (keeps the sort stable). -/
def insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt y x then y :: insertBy lt x ys else x :: y :: ys

/-- A stable sort (`sort!` is stable by default). -/
def sortBy {α : Type} (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy lt x (sortBy lt xs)

/-! ## `Dict{String,V}` as an association list with unique keys -/

abbrev Dict (V : Type) := List (Str × V)

def dget {V : Type} (d : Dict V) (k : Str) : Option V := (d.find? (·.1 == k)).map (·.2)

def haskey {V : Type} (d : Dict V) (k : Str) : Bool := (dget d k).isSome

/-- `d[k] = v`. -/
def dset {V : Type} (d : Dict V) (k : Str) (v : V) : Dict V :=
  if haskey d k then d.map (fun p => if p.1 == k then (k, v) else p) else d ++ [(k, v)]

def keys {V : Type} (d : Dict V) : List Str := d.map (·.1)

/-- `==(::Dict, ::Dict)` for dictionaries with unique keys. -/
def deq {V : Type} [BEq V] (a b : Dict V) : Bool :=
  a.length == b.length && a.all (fun p => dget b p.1 == some p.2)

abbrev Tags := Dict Str

/-! ## Comparison strategies -/

/-- The `Function`s that can be stored as comparison strategies. `==` on
functions is `===`, so two strategies are equal exactly when they are the
same constructor. `user n` is any other function. -/
inductive Strat where
  /-- `compare_default`, `base/binaryplatforms.jl:321-323`. -/
  | dflt
  /-- `compare_version_cap`, `base/binaryplatforms.jl:340-355`. -/
  | cap
  /-- The `julia_version` closure of the constructor, `base/binaryplatforms.jl:92-96`. -/
  | juliaMinor
  | user (n : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- `struct Platform`, `base/binaryplatforms.jl:39-101`. -/
structure Platform where
  tags : Tags
  strats : Dict Strat
  deriving DecidableEq

/-- `==(a::Platform, b::Platform)`, `base/binaryplatforms.jl:193-195`. -/
def peq (a b : Platform) : Bool := deq a.tags b.tags && deq a.strats b.strats

/-- A tag value accepted by the constructor: `Union{String,VersionNumber,Nothing}`. -/
inductive TagVal where
  | str (s : Str)
  | ver (v : VersionNumber)
  | none

/-! ## Construction -/

section
variable (lc : Char → Char)

/-- `CPUID.normalize_arch`, `base/cpuid.jl:286-302`. -/
def normalizeArch (arch : Str) : Str :=
  let arch := lower lc arch
  if arch == s% "amd64" then s% "x86_64"
  else if [s% "i386", s% "i486", s% "i586"].contains arch then s% "i686"
  else if arch == s% "armv6" then s% "armv6l"
  else if [s% "arm", s% "armv7", s% "armv8", s% "armv8l"].contains arch then s% "armv7l"
  else if arch == s% "arm64" then s% "aarch64"
  else if arch == s% "ppc64le" then s% "powerpc64le"
  else arch

/-- `add_tag!(tags, tag, value)`, `base/binaryplatforms.jl:154-171`. -/
def addTag (tags : Tags) (tag value : Str) : Jl Tags := do
  if tag.any isNono then throw (.argumentError "Invalid character in tag name")
  let value := lower lc value
  if value.any isNono then throw (.argumentError "Invalid character in tag value")
  return dset tags tag value

/-- `string(value)` for a `String` or `VersionNumber`. -/
def tagString : TagVal → Str
  | .str s => s
  | .ver v => vprint v
  | .none => []

/-- `add_platform_tag!(tags, tag, value)`, `base/binaryplatforms.jl:116-151`. -/
def addPlatformTag (tags : Tags) (tag : Str) (value : TagVal) : Jl Tags := do
  let tag := lower lc tag
  match value with
  | .none => return tags
  | _ =>
  let (tags, tag) ← (if tag == s% "libstdcxx_version" then do
      let tags ← if haskey tags (s% "cxxlib") then pure tags else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
      pure (tags, s% "cxxlib_version")
    else if tag == s% "cxxstring_abi" then do
      let tags ← if haskey tags (s% "cxxlib") then pure tags else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
      pure (tags, tag)
    else pure (tags, tag) : Jl (Tags × Str))
  let value ← (if [s% "libgfortran_version", s% "cxxlib_version", s% "os_version"].contains tag then
      match value with
      | .ver v => pure (TagVal.str (vprint v))
      | .str s => do
        match ← VersionNumbers.tryparse s with
        | some v => pure (TagVal.str (vprint v))
        | none => pure value
      | .none => pure value
    else pure value : Jl TagVal)
  addTag lc tags tag (tagString value)

/-- `validate_tags(tags)`, `base/binaryplatforms.jl:222-293`. `tags[k]` on a
missing key throws `KeyError`, modelled as `argumentError "KeyError"` (it is
unreachable: the constructor always sets `libc` on Linux and Windows and
`call_abi` on 32-bit ARM Linux). -/
def validateTags (tags : Tags) : Jl Unit := do
  let get (k : Str) : Jl Str := match dget tags k with
    | some v => pure v
    | none => throw (.argumentError "KeyError")
  let arch ← get (s% "arch")
  let os ← get (s% "os")
  if ![s% "x86_64", s% "i686", s% "armv7l", s% "armv6l", s% "aarch64", s% "powerpc64le", s% "riscv64"].contains arch then
    throw (.argumentError "invalid arch")
  if ![s% "linux", s% "macos", s% "freebsd", s% "openbsd", s% "windows"].contains os then
    throw (.argumentError "invalid os")
  if os == s% "windows" && ![s% "x86_64", s% "i686", s% "armv7l", s% "aarch64"].contains arch then
    throw (.argumentError "Invalid os/arch combination")
  if os == s% "macos" && ![s% "x86_64", s% "aarch64"].contains arch then
    throw (.argumentError "Invalid os/arch combination")
  if os == s% "linux" then
    if ![s% "glibc", s% "musl"].contains (← get (s% "libc")) then throw (.argumentError "Invalid os/libc combination")
  else if os == s% "windows" then
    if ![s% "msvcrt", s% "ucrt"].contains (← get (s% "libc")) then throw (.argumentError "Invalid os/libc combination")
  else
    if haskey tags (s% "libc") then throw (.argumentError "Invalid os/libc combination")
  -- `tags[k]` below is only reached when `haskey(tags, k)` holds (short-circuit `||`/`&&`).
  let val (k : Str) : Str := (dget tags k).getD []
  if os == s% "linux" && [s% "armv7l", s% "armv6l"].contains arch then
    if !haskey tags (s% "call_abi") || ![s% "eabihf", s% "eabi"].contains (val (s% "call_abi")) then
      throw (.argumentError "Invalid os/arch/call_abi combination")
  else
    if haskey tags (s% "call_abi") then throw (.argumentError "Invalid os/arch/call_abi combination")
  if haskey tags (s% "libgfortran_version") then
    if (← VersionNumbers.tryparse (val (s% "libgfortran_version"))).isNone then
      throw (.argumentError "must be a valid VersionNumber")
  if haskey tags (s% "cxxlib") && ![s% "libstdcxx", s% "libcxx"].contains (val (s% "cxxlib")) then
    throw (.argumentError "invalid cxxlib")
  if haskey tags (s% "cxxstring_abi") then
    if ![s% "cxx03", s% "cxx11"].contains (val (s% "cxxstring_abi")) || !haskey tags (s% "cxxlib")
        || val (s% "cxxlib") != s% "libstdcxx" then
      throw (.argumentError "invalid cxxstring_abi")
  if haskey tags (s% "cxxlib_version") then
    if (← VersionNumbers.tryparse (val (s% "cxxlib_version"))).isNone then
      throw (.argumentError "must be a valid VersionNumber")

/-- The loop over `_tags` in the constructor, `base/binaryplatforms.jl:56-69`;
`_tags` is given in its iteration order. -/
def addAll : Tags → List (Str × TagVal) → Jl Tags
  | tags, [] => pure tags
  | tags, (tag, value) :: rest => do
    let tag := lower lc tag
    if tag == s% "arch" || tag == s% "os" then throw (.argumentError "Cannot double-pass key")
    match value with
    | .none => addAll tags rest
    | _ => addAll (← addPlatformTag lc tags tag value) rest

/-- `Platform(arch, os, _tags; validate_strict, compare_strategies)`,
`base/binaryplatforms.jl:45-100`. Returns the platform and the caller's
`compare_strategies` dictionary after the call: the constructor writes into
that `Dict` and stores it in the new object (`new` converts without copying
when it already is a `Dict{String,Function}`). -/
def mkPlatform (arch os : Str) (tagsIn : List (Str × TagVal)) (validateStrict : Bool)
    (cs : Dict Strat) : Jl (Platform × Dict Strat) := do
  let os := lower lc os
  let arch := normalizeArch lc arch
  let tags : Tags := [(s% "arch", arch), (s% "os", os)]
  let tags ← addAll lc tags tagsIn
  let tags := if os == s% "linux" && !haskey tags (s% "libc") then dset tags (s% "libc") (s% "glibc") else tags
  let tags := if os == s% "windows" && !haskey tags (s% "libc") then dset tags (s% "libc") (s% "msvcrt") else tags
  let tags := if os == s% "linux" && [s% "armv7l", s% "armv6l"].contains arch && !haskey tags (s% "call_abi") then
    dset tags (s% "call_abi") (s% "eabihf") else tags
  if validateStrict then validateTags tags
  let cs := if haskey tags (s% "julia_version") && !haskey cs (s% "julia_version") then
    dset cs (s% "julia_version") Strat.juliaMinor else cs
  return (⟨tags, cs⟩, cs)

/-- `Platform(arch, os; kwargs...)` with default `compare_strategies`. -/
def platform (arch os : Str) (tagsIn : List (Str × TagVal)) (validateStrict : Bool) : Jl Platform :=
  (·.1) <$> mkPlatform lc arch os tagsIn validateStrict []

end

/-! ## Accessors -/

def tget (p : Platform) (k : Str) : Option Str := dget p.tags k

/-- `arch(p)`, `base/binaryplatforms.jl:394`. -/
def arch (p : Platform) : Option Str := tget p (s% "arch")
/-- `os(p)`, `base/binaryplatforms.jl:410`. -/
def os (p : Platform) : Option Str := tget p (s% "os")
/-- `libc(p)`, `base/binaryplatforms.jl:445`. -/
def libc (p : Platform) : Option Str := tget p (s% "libc")
/-- `call_abi(p)`, `base/binaryplatforms.jl:461`. -/
def callAbi (p : Platform) : Option Str := tget p (s% "call_abi")
/-- `cxxstring_abi(p)`, `base/binaryplatforms.jl:520`. -/
def cxxstringAbi (p : Platform) : Option Str := tget p (s% "cxxstring_abi")

/-- `VNorNothing(d, key)`, `base/binaryplatforms.jl:481-487`
(`VersionNumber(v::String)` is `parse(VersionNumber, v)`). -/
def vnOrNothing (d : Tags) (k : Str) : Jl (Option VersionNumber) :=
  match dget d k with
  | none => pure none
  | some v => some <$> VersionNumbers.parse v

/-- `libgfortran_version(p)`, `base/binaryplatforms.jl:495`. -/
def libgfortranVersion (p : Platform) : Jl (Option VersionNumber) := vnOrNothing p.tags (s% "libgfortran_version")

/-- `libstdcxx_version(p)`, `base/binaryplatforms.jl:504-513`. -/
def libstdcxxVersion (p : Platform) : Jl (Option VersionNumber) :=
  if haskey p.tags (s% "libstdcxx_version") then vnOrNothing p.tags (s% "libstdcxx_version")
  else if tget p (s% "cxxlib") == some (s% "libstdcxx") then vnOrNothing p.tags (s% "cxxlib_version")
  else pure none

/-- `os_version(p)`, `base/binaryplatforms.jl:530`. -/
def osVersion (p : Platform) : Jl (Option VersionNumber) := vnOrNothing p.tags (s% "os_version")

/-- `print` of an unsigned integer. -/
def showNat (n : Nat) : Str := Nat.toDigits 10 n

/-- `os_str(p)`, `base/binaryplatforms.jl:605-629`. -/
def osStr (p : Platform) : Jl Str := do
  if os p == some (s% "linux") then return s% "-linux"
  else if os p == some (s% "macos") then
    match ← osVersion p with
    | some v => return s% "-apple-darwin" ++ showNat v.major.val.toNat
    | none => return s% "-apple-darwin"
  else if os p == some (s% "windows") then return s% "-w64"
  else if os p == some (s% "freebsd") then
    match ← osVersion p with
    | some v => return s% "-unknown-freebsd" ++ showNat v.major.val.toNat ++ ['.'] ++ showNat v.minor.val.toNat
    | none => return s% "-unknown-freebsd"
  else if os p == some (s% "openbsd") then return s% "-unknown-openbsd"
  else return s% "-unknown"

/-- `libc_str(p)`, `base/binaryplatforms.jl:632-645`. -/
def libcStr (p : Platform) : Str :=
  match libc p with
  | none => []
  | some lc =>
    if lc == s% "glibc" then s% "-gnu"
    else if lc == s% "msvcrt" then s% "-mingw32"
    else if lc == s% "ucrt" then s% "-ucrt-mingw32"
    else '-' :: lc

/-- `call_abi_str(p)`, `base/binaryplatforms.jl:646-649`. -/
def callAbiStr (p : Platform) : Str := (callAbi p).getD []

/-- Tags `triplet` never prints as `-key+value`, `base/binaryplatforms.jl:589`. -/
def tripletSkip : List Str :=
  [s% "os", s% "arch", s% "libc", s% "call_abi", s% "libgfortran_version", s% "libstdcxx_version",
   s% "cxxstring_abi", s% "os_version"]

/-- The loop over the sorted extra tags in `triplet`, `base/binaryplatforms.jl:588-601`;
`cxx` and `sv` say whether `cxxstring_abi_` and `libstdcxx_version_` are not `nothing`. -/
def extraTags (p : Platform) (cxx sv : Bool) : Tags → Str
  | [] => []
  | (tag, val) :: rest =>
    if tripletSkip.contains tag then extraTags p cxx sv rest
    else if tag == s% "cxxlib" && val == s% "libstdcxx" && (cxx || sv) then extraTags p cxx sv rest
    else if tag == s% "cxxlib_version" && tget p (s% "cxxlib") == some (s% "libstdcxx") then extraTags p cxx sv rest
    else ('-' :: tag ++ '+' :: val) ++ extraTags p cxx sv rest

/-- `triplet(p)`, `base/binaryplatforms.jl:565-603`. The `arch(p)::Union{Symbol,String}`
assertion fails (`TypeError`, modelled as `argumentError`) when there is no `arch` tag,
which a constructed `Platform` always has. -/
def triplet (p : Platform) : Jl Str := do
  let a ← match arch p with
    | some a => pure a
    | none => throw (.argumentError "TypeError")
  let str := a ++ (← osStr p) ++ libcStr p ++ callAbiStr p
  let gf ← libgfortranVersion p
  let str := match gf with
    | some v => str ++ s% "-libgfortran" ++ showNat v.major.val.toNat
    | none => str
  let cxx := cxxstringAbi p
  let str := match cxx with
    | some c => str ++ '-' :: c
    | none => str
  let sv ← libstdcxxVersion p
  let str := match sv with
    | some v => str ++ s% "-libstdcxx" ++ showNat v.patch.val.toNat
    | none => str
  return str ++ extraTags p cxx.isSome sv.isSome (sortBy (fun a b => strLt a.1 b.1) p.tags)

/-- `platform_dlext(p)`, `base/binaryplatforms.jl:847-855`. -/
def platformDlext (p : Platform) : Str :=
  if os p == some (s% "windows") then s% "dll"
  else if os p == some (s% "macos") then s% "dylib"
  else s% "so"

end JuliaLean.Platforms
