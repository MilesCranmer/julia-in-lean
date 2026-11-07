import Lean
import JuliaLean.Core
import JuliaLean.base.version
import JuliaLean.base.expr

/-! String literals as character lists for the `Platforms` model. -/

namespace JuliaLean.Platforms

/-- `s% "abc"`: the characters of a string literal as a `List Char` literal
(computed at elaboration time, so the kernel never decodes a `String`). -/
elab "s% " s:str : term => return Lean.toExpr s.getString.toList

end JuliaLean.Platforms


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


/-!
# `platforms_match` and `select_platform` (`base/binaryplatforms.jl:295-355, 1128-1246`)

`union(keys(tags(a)), keys(tags(b)))` is a `Set`, whose iteration order is
hash-based; it is an explicit argument `order` (any duplicate-free list of
exactly the keys of either platform). User-defined comparison strategies
(`Strat.user n`) have semantics `usem n`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber vless veq)

/-- Semantics of user-defined comparison functions. -/
abbrev UserSem := Nat → Str → Str → Bool → Bool → Jl Bool

/-- `a <= b` for `VersionNumber`s (`(a < b) | (a == b)`). -/
def vle (a b : VersionNumber) : Bool := vless a b || veq a b

/-- Calling a comparison strategy, `base/binaryplatforms.jl:1183`. -/
def compare (usem : UserSem) : Strat → Str → Str → Bool → Bool → Jl Bool
  | .dflt, a, b, _, _ => pure (a == b)
  | .cap, a, b, ar, br => do
    let a ← VersionNumbers.parse a
    let b ← VersionNumbers.parse b
    if ar && br then return veq a b
    if ar then return vle b a else return vle a b
  | .juliaMinor, a, b, _, _ => do
    let a ← VersionNumbers.parse a
    let b ← VersionNumbers.parse b
    return a.major == b.major && a.minor == b.minor
  | .user n, a, b, ar, br => usem n a b ar br

/-- `get_compare_strategy(p, key)` for a key `p` has, `base/binaryplatforms.jl:302-307`. -/
def strategy (p : Platform) (k : Str) : Strat := (dget p.strats k).getD .dflt

/-- `strict_presence_tags`, `base/binaryplatforms.jl:312`. -/
def strictPresenceTags : List Str := [s% "sanitize"]

/-- One iteration of the loop of `platforms_match`: `some r` continues
(`r = true`) or returns `false` (`r = false`). -/
def matchKey (usem : UserSem) (a b : Platform) (k : Str) : Jl Bool :=
  match tget a k, tget b k with
  | some ak, some bk => do
    let aComp := strategy a k
    let bComp := strategy b k
    if aComp != .dflt && bComp != .dflt && aComp != bComp then
      throw (.argumentError "Cannot compare Platform objects with two different non-default comparison strategies")
    let comparator := if bComp != .dflt then bComp else aComp
    compare usem comparator ak bk (aComp == comparator) (bComp == comparator)
  | _, _ => pure !(strictPresenceTags.contains k)

/-- `platforms_match(a, b)`, `base/binaryplatforms.jl:1153-1188`, iterating the
keys in `order`. -/
def platformsMatch (usem : UserSem) (order : List Str) (a b : Platform) : Jl Bool :=
  match order with
  | [] => pure true
  | k :: rest => do
    if ← matchKey usem a b k then platformsMatch usem rest a b else return false

/-- `order` is an iteration order of `union(keys(tags(a)), keys(tags(b)))`. -/
def IsUnionOrder (order : List Str) (a b : Platform) : Prop :=
  order.Nodup ∧ ∀ k, k ∈ order ↔ (haskey a.tags k = true ∨ haskey b.tags k = true)

/-- Every comparison strategy stored in `p` is one defined in `base/binaryplatforms.jl`. -/
def BuiltinStrats (p : Platform) : Prop := ∀ e ∈ p.strats, ∀ n, e.2 ≠ .user n

/-! ## `select_platform` -/

/-- Keys of `a` not among the keys of `b`. -/
def keysNotIn (a b : List Str) : List Str := a.filter (!b.contains ·)

/-- `match_loss(a, b)`, `base/binaryplatforms.jl:1226-1230`:
`length(union) - length(intersect)` of the two key sets. -/
def matchLoss (a b : Platform) : Nat :=
  let ka := keys a.tags
  let kb := keys b.tags
  (ka.length + (keysNotIn kb ka).length) - (ka.filter (kb.contains ·)).length

/-- The sort order of `select_platform`, `base/binaryplatforms.jl:1235-1242`, on
precomputed `(loss, triplet)` keys: smaller loss first, then larger triplet. -/
def selLt (x y : Nat × Str) : Bool := if x.1 != y.1 then x.1 < y.1 else strLt y.2 x.2

/-- The first element of a stable sort by `lt`: the earliest element that no
other element is strictly less than (for a strict weak order `lt`). -/
def firstMin {α : Type} (lt : α → α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    match firstMin lt xs with
    | none => some x
    | some y => if lt y x then some y else some x

/-- `filter(f, xs)` with a throwing predicate, in iteration order. -/
def filterJ {β : Type} (f : β → Jl Bool) : List β → Jl (List β)
  | [] => pure []
  | x :: xs => do
    let keep ← f x
    let rest ← filterJ f xs
    return if keep then x :: rest else rest

/-- `map(f, xs)` with a throwing function. -/
def mapJ {β γ : Type} (f : β → Jl γ) : List β → Jl (List γ)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let rest ← mapJ f xs
    return y :: rest

/-- `select_platform(download_info, platform)`, `base/binaryplatforms.jl:1215-1246`.
`entries` lists the `Dict` entries in the order in which the matching keys are
collected (the iteration order of `filter(..., keys(download_info))`), and
`order p` is the key order `platforms_match(p, platform)` iterates.
`sort!` is stable, so the selected key is the first candidate that is minimal
for `lt`. With two or more candidates the model computes every candidate's
triplet up front, where Julia computes it only when two losses tie (the two
differ only when `triplet` throws). -/
def selectPlatform {α : Type} (usem : UserSem) (order : Platform → List Str)
    (entries : List (Platform × α)) (host : Platform) : Jl (Option α) := do
  let ps ← filterJ (fun e => platformsMatch usem (order e.1) e.1 host) entries
  match ps with
  | [] => return none
  | [e] => return some e.2
  | _ =>
    let keyed ← mapJ (fun e => do return ((matchLoss e.1 host, ← triplet e.1), e)) ps
    return (firstMin (fun x y => selLt x.1 y.1) keyed).map (·.2.2)

end JuliaLean.Platforms


/-!
# `parse(::Type{Platform}, triplet)` (`base/binaryplatforms.jl:659-838`)

`triplet_regex` is compiled with Julia's default options (`UTF | UCP`, no
`s`): `\d` is a Unicode decimal digit, `.` is any character but `\n`, and `$`
also matches before a final `\n`. The alternatives of each group appear in the
iteration order of the mapping `Dict`s, which was observed to be identical
on 1.13.2 and master:

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
against an extended `cxxlib_version` tag; `cxxlib_version` was observed to
come first (differential test, 56 such inputs), so the model passes
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


/-!
# `parse_dl_name_version` (`base/binaryplatforms.jl:868-929`)

The three patterns carry the `a` flag (byte mode: no UTF, no UCP), so `\d`,
`\w` and `[A-Za-z]` are ASCII classes, `.` with `s` matches any byte, and `i`
(Windows) makes letters caseless. Every literal and class in the patterns is
ASCII, so a match can only start or end a capture next to an ASCII byte: on
valid UTF-8 the byte-mode match is the character-level match the model
computes, with a non-ASCII character matching no class.

Each pattern is `^(.*?)REST`. The lazy `(.*?)` tries 0, 1, 2, ... characters,
and for each length the rest is matched with PCRE's backtracking order, so the
match is the first split point at which `REST` matches the remaining suffix.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (Re matchRe capture VersionNumber)
open JuliaLean.VersionNumbers.Re

def isAsciiDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isAsciiAlpha (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
/-- `\w` in byte mode. -/
def isWord (c : Char) : Bool := isAsciiDigit c || isAsciiAlpha c || c == '_'

/-- A literal string. -/
def litD (s : Str) : Re := seqs (s.map chr)

/-- A caseless literal (`i` flag). -/
def litCI (s : Str) : Re := seqs (s.map fun c => cls fun d => asciiLower d == asciiLower c)

/-- Group numbers: 2 the version, 3 the trailing tag. -/
def verGroup : Nat := 2

/-- `\.so(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?$`, the part of the Linux/BSD
pattern after `^(.*?)`, `base/binaryplatforms.jl:907`. -/
def soRest : Re :=
  seqs [litD (s% ".so"),
    opt (seq (group verGroup (plus (seq (chr '.') (plus (cls isAsciiDigit)))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '-')))))),
    eol]

/-- `(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?\.dylib$`, `base/binaryplatforms.jl:904`. -/
def dylibRest : Re :=
  seqs [opt (seq (group verGroup (plus (seq (chr '.') (plus (cls isAsciiDigit)))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '-')))))),
    litD (s% ".dylib"), eol]

/-- `(?:-(?:((?:[\.\d]+)+)([A-Za-z][\w\.]*)?)?)?\.dll$` with `i`,
`base/binaryplatforms.jl:901`. -/
def dllRest : Re :=
  seqs [opt (seq (chr '-') (opt (seq (group verGroup (plus (plus (cls fun c => c == '.' || isAsciiDigit c))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '.')))))))),
    litCI (s% ".dll"), eol]

/-- The pattern for `os`, `base/binaryplatforms.jl:896-908`. -/
def dlRest (os : Str) : Re :=
  if os == s% "windows" then dllRest else if os == s% "macos" then dylibRest else soRest

/-- `match(r"^(.*?)REST", s)`: the first split point at which `rest` matches,
with the captured prefix and the captures of `rest`. -/
def lazyMatch (rest : Re) (s : Str) : Option (Str × VersionNumbers.Caps) :=
  go [] s
where
  go (pre : Str) : Str → Option (Str × VersionNumbers.Caps)
    | [] => (matchRe rest []).map (pre, ·)
    | c :: t =>
      match matchRe rest (c :: t) with
      | some m => some (pre, m)
      | none => go (pre ++ [c]) t

/-- `basename(path)` on Unix: the part after the last `/`, `base/path.jl:280-330`. -/
def basename (path : Str) : Str := (path.reverse.takeWhile (· != '/')).reverse

/-- `strip(s, c)`. -/
def stripChar (c : Char) (s : Str) : Str := ((s.dropWhile (· == c)).reverse.dropWhile (· == c)).reverse

/-- `parse_dl_name_version(path::String, os::String)`, `base/binaryplatforms.jl:893-924`. -/
def parseDlNameVersion (path os : Str) : Jl (Str × Option VersionNumber) := do
  match lazyMatch (dlRest os) (basename path) with
  | none => throw (.argumentError "Invalid dynamic library path")
  | some (name, m) =>
    match capture m verGroup with
    | none => return (name, none)
    | some [] => return (name, none)
    | some v => return (name, some (← VersionNumbers.parse (stripChar '.' v)))

end JuliaLean.Platforms


/-!
# `detect_libstdcxx_version` (`base/binaryplatforms.jl:931-1027`)

The process state the function observes is an explicit `Proc`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber)

/-- What `detect_libstdcxx_version` observes of the running process. -/
structure Proc where
  /-- `get_csl_member(:libstdcxx) !== nothing`: `CompilerSupportLibraries_jll` is
  loaded and defines `libstdcxx`. -/
  cslLibstdcxx : Bool
  /-- `Libdl.dllist()`. -/
  dllist : List Str
  /-- `dlsym(h, "GLIBCXX_3.4.$m"; throw_error=false) !== nothing` for the loaded
  libstdc++ (the one `dlopen(path, RTLD_NOLOAD)` returns a handle to). -/
  glibcxx : Nat → Bool

/-- `occursin(needle, s)`. -/
def occursIn (needle s : Str) : Bool :=
  (List.range (s.length + 1)).any fun i => startsWith (s.drop i) needle

/-- `_get_libstdcxx_handle()`, `base/binaryplatforms.jl:965-980`; the handle is
represented by the path it was opened from. -/
def getLibstdcxxHandle (p : Proc) : Option Str :=
  if p.cslLibstdcxx then none
  else (p.dllist.filter (occursIn (s% "libstdc++"))).head?

/-- The loop `for minor_version in max_minor_version:-1:18`, from `m` down. -/
def searchMinor (p : Proc) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, m => if m < 18 then none else if p.glibcxx m then some m else searchMinor p fuel (m - 1)

/-- `detect_libstdcxx_version(max_minor_version)`, `base/binaryplatforms.jl:1013-1027`. -/
def detectLibstdcxxVersion (p : Proc) (maxMinor : Nat) : Jl (Option VersionNumber) :=
  match getLibstdcxxHandle p with
  | none => pure none
  | some _ =>
    match searchMinor p (maxMinor + 1) maxMinor with
    | none => pure none
    | some m => some <$> VersionNumbers.parse (s% "3.4." ++ showNat m)

end JuliaLean.Platforms


section

/-!
# Remaining method models for `base/binaryplatforms.jl`

Core construction, parsing, triplet, dynamic-library and matching behavior is reused from
`JuliaLean.Platforms`.  This module models the thin overloads, mutation wrappers, display,
host detection and nested helpers that the original area did not register separately.
-/

namespace JuliaLean.DocsSyntaxCov.Binary

open JuliaLean JuliaLean.Platforms
open JuliaLean.VersionNumbers (VersionNumber)

def joinStr (sep : Str) : List Str → Str
  | [] => []
  | [x] => x
  | x :: xs => x ++ sep ++ joinStr sep xs

def tagvalueString (v : Str) : TagVal := .str v
def tagvalueSymbol (v : Str) : TagVal := .str v
def tagvalueAbstractString (convertString : Str → Str) (v : Str) : TagVal := .str (convertString v)

def tags (p : Platform) : Tags := p.tags
def getindex (p : Platform) (k : Str) : DJ Str := match dget p.tags k with
  | some v => .ok v | none => .error (.keyError (String.mk k))
def haskeyP (p : Platform) (k : Str) : Bool := haskey p.tags k

/-- `setindex!` delegates to `add_platform_tag!` and returns the platform. -/
def setindex (lc : Char → Char) (p : Platform) (v k : Str) : Jl Platform := do
  let tags ← addPlatformTag lc p.tags k (TagVal.str v)
  pure { p with tags := tags }

def platformHash (hashTags : Tags → Nat → Nat) (hashStrats : Dict Strat → Nat → Nat)
    (p : Platform) (h : Nat) : Nat :=
  let h := Nat.xor h 0x506c6174666f726d
  let h := hashTags p.tags h
  hashStrats p.strats h

def platformEq (a b : Platform) : Bool := peq a b

def showPair (p : Str × Str) : Str := p.1 ++ s% " = \"" ++ p.2 ++ s% "\""

/-- The serializing `show(::IO, ::Platform)`, lines 199-209. -/
def showPlatform (p : Platform) : Str :=
  let others := sortBy (fun a b => strLt a.1 b.1) (p.tags.filter fun kv => kv.1 != s% "arch" && kv.1 != s% "os")
  s% "Platform(\"" ++ (arch p).getD [] ++ s% "\", \"" ++ (os p).getD [] ++ s% "\"; " ++
    joinStr (s% ", ") (others.map showPair) ++ [')']

def platformNames : List (Option Str × Str) :=
  [(some (s% "linux"), s% "Linux"), (some (s% "macos"), s% "macOS"),
   (some (s% "windows"), s% "Windows"), (some (s% "freebsd"), s% "FreeBSD"),
   (some (s% "openbsd"), s% "OpenBSD"), (none, s% "Unknown")]

def platformName (p : Platform) : DJ Str := match platformNames.find? (·.1 == os p) with
  | some x => .ok x.2 | none => .error (.keyError (String.mk ((os p).getD [])))

/-- The text/plain display, lines 212-220. -/
def showPlatformPlain (p : Platform) : DJ Str := do
  let name ← platformName p
  let others := sortBy (fun a b => strLt a.1 b.1)
    (p.tags.filter fun kv => kv.1 != s% "os" && kv.1 != s% "arch")
  let suffix := if others.isEmpty then [] else
    s% " {" ++ joinStr (s% ", ") (others.map fun kv => kv.1 ++ ['='] ++ kv.2) ++ ['}']
  pure (name ++ [' '] ++ (arch p).getD [] ++ suffix)

def throwInvalidKey (tags : Tags) (k : Str) : Jl Unit :=
  .error (.argumentError ("invalid key " ++ String.mk k))
def throwOsMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/arch combination")
def throwLibcMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/libc combination")
def throwCallAbiMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/call_abi combination")
def throwVersionNumber (_tags : Tags) (k : Str) : Jl Unit :=
  .error (.argumentError ("invalid version " ++ String.mk k))

def setCompareStrategy (p : Platform) (key : Str) (f : Strat) : Jl Platform :=
  if !haskey p.tags key then .error (.argumentError "nonexistent tag")
  else .ok { p with strats := dset p.strats key f }

def getCompareStrategy (p : Platform) (key : Str) (dflt : Strat := .dflt) : Jl Strat :=
  if !haskey p.tags key then .error (.argumentError "nonexistent tag")
  else .ok ((dget p.strats key).getD dflt)

def getCompareStrategyAbstract (_p : Tags) (_key : Str) (dflt : Strat := .dflt) : Strat := dflt

def compareDefault (a b : Str) (_ar _br : Bool) : Bool := a == b

/-- `HostPlatform(p)`, lines 370-378. -/
def hostPlatform (p : Platform) : Platform :=
  let p := if haskey p.tags (s% "os_version") then
    { p with strats := dset p.strats (s% "os_version") .cap } else p
  if dget p.tags (s% "cxxlib") == some (s% "libstdcxx") && haskey p.tags (s% "cxxlib_version") then
    { p with strats := dset p.strats (s% "cxxlib_version") .cap } else p

structure CurrentOS where
  windows : Bool
  apple : Bool
  freebsd : Bool
  openbsd : Bool

def currentOs (s : CurrentOS) : Str := if s.windows then s% "windows" else if s.apple then s% "macos"
  else if s.freebsd then s% "freebsd" else if s.openbsd then s% "openbsd" else s% "linux"

def cxxstringAbi (p : Platform) : Option Str := tget p (s% "cxxstring_abi")
def wordsize (p : Platform) : Nat := if [s% "i686", s% "armv6l", s% "armv7l"].contains ((arch p).getD []) then 32 else 64

def isapple (p : Platform) : Bool := os p == some (s% "macos")
def islinux (p : Platform) : Bool := os p == some (s% "linux")
def iswindows (p : Platform) : Bool := os p == some (s% "windows")
def isfreebsd (p : Platform) : Bool := os p == some (s% "freebsd")
def isopenbsd (p : Platform) : Bool := os p == some (s% "openbsd")
def isbsd (p : Platform) : Bool := [s% "freebsd", s% "openbsd", s% "macos"].contains ((os p).getD [])
def isunix (p : Platform) : Bool := isbsd p || islinux p

/-- Nested `get_set`, lines 671-674. -/
def getSet {S : Type} (families : Dict (List (Str × S))) (arch name : Str) : DJ S := do
  let all ← match dget families arch with | some x => .ok x | none => .error (.keyError (String.mk arch))
  match all.find? (fun x => x.1 == name) with | some x => .ok x.2 | none => .error (.errorException "not found")

/-- Nested regex helper `c(mapping)`, line 736. -/
def collapseMapping (mapping : List (Str × Str)) : Str :=
  ['('] ++ joinStr (s% "|") (mapping.map fun kv => s% "(?<" ++ kv.1 ++ s% ">" ++ kv.2 ++ [')']) ++ [')']

def parseAbstract (convertString : Str → Str) (validate : Bool) (triplet : Str) : Jl Platform :=
  parsePlatform asciiLower validate (convertString triplet)

def tryparsePlatform (parse : Str → Jl Platform) (triplet : Str) : Option Platform :=
  match parse triplet with | .ok p => some p | .error _ => none

def thisOsName (windows apple : Bool) : Str := if windows then s% "windows" else if apple then s% "macos" else s% "other"

def parseDlAbstract (toString : Str → Str) (path os : Str) : Jl (Str × Option VersionNumber) :=
  parseDlNameVersion (toString path) (toString os)

structure LoadedModule where
  name : String
  members : List (String × Str)

def getCslMember (mods : List LoadedModule) (member : String) : Option Str :=
  match mods.find? (·.name == "CompilerSupportLibraries_jll") with
  | none => none
  | some m => (m.members.find? (·.1 == member)).map Prod.snd

def occursInStr (needle hay : Str) : Bool :=
  (List.range (hay.length + 1)).any fun i => ((hay.drop i).take needle.length == needle)

def getLibgfortranPath (mods : List LoadedModule) (dllist : List Str) : Option Str :=
  (getCslMember mods "libgfortran_path").orElse fun _ => dllist.find? (occursInStr (s% "libgfortran"))

def getLibstdcxxHandle (mods : List LoadedModule) (dllist : List Str) (openFn : Str → Option Nat) : Option Nat :=
  match getCslMember mods "libstdcxx" with
  | some _ => none
  | none => (dllist.find? (occursInStr (s% "libstdc++"))).bind openFn

def detectLibgfortranVersion (path : Option Str) (os : Str) : Jl (Option VersionNumber) := match path with
  | none => .error (.methodError "parse_dl_name_version(nothing)")
  | some p => (parseDlNameVersion p os).map Prod.snd

def openLibllvm {A : Type} (names : List Str) (openFn : Str → Option Nat) (closeFn : Nat → Unit)
    (f : Nat → A) : DJ A :=
  match names.findSome? openFn with
  | none => .error (.errorException "Unable to open libLLVM!")
  | some h =>
    let r := f h
    let _ := closeFn h
    .ok r

def detectCxxstringAbi (dllist : List Str) (openFn : Str → Option Nat) (hasSymbol : Nat → Str → Bool)
    (closeFn : Nat → Unit) (names : List Str) : DJ (Option Str) :=
  if !(dllist.any (occursInStr (s% "libstdc++"))) then .ok none
  else openLibllvm names openFn closeFn fun h =>
    if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleEv") then some (s% "cxx03")
    else if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleB5cxx11Ev") then some (s% "cxx11") else none

structure HostVersions where
  gfortran : Option Nat
  cxxabi : Option Str
  libstdcxx : Option Nat
  julia : VersionNumber

def hostTriplet (build ext : Str) (v : HostVersions) : Str :=
  let s := if occursInStr (s% "-libgfortran") build then build else
    match v.gfortran with | none => build | some n => build ++ s% "-libgfortran" ++ Nat.toDigits 10 n
  let s := if occursInStr (s% "-cxx") s then s else match v.cxxabi with | none => s | some a => s ++ ['-'] ++ a
  let s := if occursInStr (s% "-libstdcxx") s then s else
    match v.libstdcxx with | none => s | some n => s ++ s% "-libstdcxx" ++ Nat.toDigits 10 n
  let s := s ++ ext
  if occursInStr (s% "-julia_version+") s then s else s ++ s% "-julia_version+" ++
    Nat.toDigits 10 v.julia.major.val.toNat ++ ['.'] ++ Nat.toDigits 10 v.julia.minor.val.toNat ++
    ['.'] ++ Nat.toDigits 10 v.julia.patch.val.toNat

def hostPlatform0 (parse : Str → Jl Platform) (triplet : Str) : Jl Platform := do
  pure (hostPlatform (← parse triplet))

def matchStringLeft (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a : Str) (b : Platform) : Jl Bool := do platformsMatch usem (order (← parse a) b) (← parse a) b

def matchStringRight (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a : Platform) (b : Str) : Jl Bool := do platformsMatch usem (order a (← parse b)) a (← parse b)

def matchStrings (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a b : Str) : Jl Bool := do
  let a ← parse a; let b ← parse b; platformsMatch usem (order a b) a b

def matchAbstractStrings (toString : Str → Str) (f : Str → Str → Jl Bool) (a b : Str) : Jl Bool :=
  f (toString a) (toString b)

def matchLoss (a b : Platform) : Nat :=
  let union := (keys a.tags ++ keys b.tags).eraseDups
  let inter := (keys a.tags).filter (keys b.tags).contains
  union.length - inter.length

end JuliaLean.DocsSyntaxCov.Binary

end


/-!
# Model of `base/binaryplatforms.jl`

Each Julia method has a source block and a typed Lean mirror. The mirrors call the existing
platform, parser, matching, and host-operation models. Host OS flags, loaded modules, versions,
dynamic-library handles, and symbol lookup are explicit typed inputs. Only the CPUID ISA table
and compile-time precompile forms remain untranslated.
-/

namespace JuliaLean.base.binaryplatforms

open JuliaLean

abbrev Str := JuliaLean.Platforms.Str
abbrev Tags := JuliaLean.Platforms.Tags
abbrev TagVal := JuliaLean.Platforms.TagVal
abbrev Strat := JuliaLean.Platforms.Strat
abbrev UserSem := JuliaLean.Platforms.UserSem
abbrev VersionNumber := JuliaLean.VersionNumbers.VersionNumber
abbrev CurrentOS := JuliaLean.DocsSyntaxCov.Binary.CurrentOS
abbrev LoadedModule := JuliaLean.DocsSyntaxCov.Binary.LoadedModule
abbrev HostVersions := JuliaLean.DocsSyntaxCov.Binary.HostVersions


/--
Julia source: base/binaryplatforms.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractPlatform; end
```
-/
abbrev AbstractPlatform := JuliaLean.Platforms.Platform

/--
Julia source: base/binaryplatforms.jl:39-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Platform <: AbstractPlatform
    tags::Dict{String,String}
    # The "compare strategy" allows selective overriding on how a tag is compared
    compare_strategies::Dict{String,Function}

```
-/
abbrev Platform := JuliaLean.Platforms.Platform

/--
Julia source: base/binaryplatforms.jl:45-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Platform(arch::String, os::String, _tags::Dict{String};
                      validate_strict::Bool = false,
                      compare_strategies::Dict{String,<:Function} = Dict{String,Function}())
        # A wee bit of normalization
        os = lowercase(os)
        arch = CPUID.normalize_arch(arch)

        tags = Dict{String,String}(
            "arch" => arch,
            "os" => os,
        )
        for (tag, value) in _tags
            value = value::Union{String,VersionNumber,Nothing}
            tag = lowercase(tag)
            if tag ∈ ("arch", "os")
                throw(ArgumentError("Cannot double-pass key $(tag)"))
            end

            # Drop `nothing` values; this means feature is not present or use default value.
            if value === nothing
                continue
            end

            add_platform_tag!(tags, tag, value)
        end

        # Auto-map call_abi and libc where necessary:
        if os == "linux" && !haskey(tags, "libc")
            # Default to `glibc` on Linux
            tags["libc"] = "glibc"
        end
        if os == "windows" && !haskey(tags, "libc")
            # Default to `msvcrt` on Windows
            tags["libc"] = "msvcrt"
        end
        if os == "linux" && arch ∈ ("armv7l", "armv6l") && "call_abi" ∉ keys(tags)
            # default `call_abi` to `eabihf` on 32-bit ARM
            tags["call_abi"] = "eabihf"
        end

        # If the user is asking for strict validation, do so.
        if validate_strict
            validate_tags(tags)
        end

        # By default, we compare julia_version only against major and minor versions:
        if haskey(tags, "julia_version") && !haskey(compare_strategies, "julia_version")
            compare_strategies["julia_version"] = (a::String, b::String, a_comparator, b_comparator) -> begin
                a = VersionNumber(a)
                b = VersionNumber(b)
                return a.major == b.major && a.minor == b.minor
            end
        end

        return new(tags, compare_strategies)
    end
```
-/
def PlatformFromDict (lc arch os tagsIn validateStrict cs) :=
  JuliaLean.Platforms.mkPlatform lc arch os tagsIn validateStrict cs

/--
Julia source: base/binaryplatforms.jl:104-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Platform(arch::String, os::String;
                  validate_strict::Bool = false,
                  compare_strategies::Dict{String,<:Function} = Dict{String,Function}(),
                  kwargs...)
    tags = Dict{String,Any}(String(tag)::String=>tagvalue(value) for (tag, value) in kwargs)
    return Platform(arch, os, tags; validate_strict, compare_strategies)
end
```
-/
def platformWithKeywords (lc arch os tagsIn validateStrict cs) :=
  JuliaLean.Platforms.mkPlatform lc arch os tagsIn validateStrict cs

/--
Julia source: base/binaryplatforms.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tagvalue(v::Union{String,VersionNumber,Nothing}) = v
```
-/
def tagvalueString (v) :=
  JuliaLean.DocsSyntaxCov.Binary.tagvalueString v

/--
Julia source: base/binaryplatforms.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tagvalue(v::Symbol) = String(v)
```
-/
def tagvalueSymbol (v) :=
  JuliaLean.DocsSyntaxCov.Binary.tagvalueSymbol v

/--
Julia source: base/binaryplatforms.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tagvalue(v::AbstractString) = convert(String, v)::String
```
-/
def tagvalueAbstractString (convertString v) :=
  JuliaLean.DocsSyntaxCov.Binary.tagvalueAbstractString convertString v

/--
Julia source: base/binaryplatforms.jl:116-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add_platform_tag!(tags::Dict{String,String}, tag::String, value::Union{String,VersionNumber,Nothing})
    tag = lowercase(tag)

    # Drop `nothing` values; this means feature is not present or use default value.
    if value === nothing
        return nothing
    end

    # For compatibility, libstdcxx_version counts as both cxxlib=libstdcxx and
    # cxxlib_version, but don't override an explicit existing cxxlib tag (the
    # verifier will check for inconsistencies).
    if tag == "libstdcxx_version"
        haskey(tags, "cxxlib") || add_tag!(tags, "cxxlib", "libstdcxx")
        tag = "cxxlib_version"
    elseif tag == "cxxstring_abi"
        # Implies cxxlib=libstdcxx for compatibility
        haskey(tags, "cxxlib") || add_tag!(tags, "cxxlib", "libstdcxx")
    end

    # Normalize things that are known to be version numbers so that comparisons are easy.
    # Note that in our effort to be extremely compatible, we actually allow something that
    # doesn't parse nicely into a VersionNumber to persist, but if `validate_strict` is
    # set to `true`, it will cause an error later on.
    if tag ∈ ("libgfortran_version", "cxxlib_version", "os_version")
        if isa(value, VersionNumber)
            value = string(value)
        elseif isa(value, String)
            v = tryparse(VersionNumber, value)
            if isa(v, VersionNumber)
                value = string(v)
            end
        end
    end

    return add_tag!(tags, tag, string(value)::String)
end
```
-/
def addPlatformTag (lc tags tag value) :=
  JuliaLean.Platforms.addPlatformTag lc tags tag value

/--
Julia source: base/binaryplatforms.jl:154-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add_tag!(tags::Dict{String,String}, tag::String, value::String)
    # I know we said only alphanumeric and dots, but let's be generous so that we can expand
    # our support in the future while remaining as backwards-compatible as possible.  The
    # only characters that are absolutely disallowed right now are `-`, `+`, ` ` and things
    # that are illegal in filenames:
    nonos = raw"""+- /<>:"'\|?*"""
    if any(occursin(nono, tag) for nono in nonos)
        throw(ArgumentError("Invalid character in tag name \"$(tag)\"!"))
    end

    # Normalize and reject nonos
    value = lowercase(value)
    if any(occursin(nono, value) for nono in nonos)
        throw(ArgumentError("Invalid character in tag value \"$(value)\"!"))
    end
    tags[tag] = value
    return value
end
```
-/
def addTag (lc tags tag value) :=
  JuliaLean.Platforms.addTag lc tags tag value

/--
Julia source: base/binaryplatforms.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tags(p::Platform) = p.tags
```
-/
def tags (p) :=
  JuliaLean.DocsSyntaxCov.Binary.tags p

/--
Julia source: base/binaryplatforms.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.getindex(p::AbstractPlatform, k::String) = getindex(tags(p), k)
```
-/
def getindex (p k) :=
  JuliaLean.DocsSyntaxCov.Binary.getindex p k

/--
Julia source: base/binaryplatforms.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.haskey(p::AbstractPlatform, k::String) = haskey(tags(p), k)
```
-/
def haskeyP (p k) :=
  JuliaLean.DocsSyntaxCov.Binary.haskeyP p k

/--
Julia source: base/binaryplatforms.jl:179-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.setindex!(p::AbstractPlatform, v::String, k::String)
    add_platform_tag!(tags(p), k, v)
    return p
end
```
-/
def setindex (lc p v k) :=
  JuliaLean.DocsSyntaxCov.Binary.setindex lc p v k

/--
Julia source: base/binaryplatforms.jl:185-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.hash(p::Platform, h::UInt)
    h ⊻= 0x506c6174666f726d % UInt
    h = hash(p.tags, h)
    h = hash(p.compare_strategies, h)
    return h
end
```
-/
def platformHash (hashTags hashStrats p h) :=
  JuliaLean.DocsSyntaxCov.Binary.platformHash hashTags hashStrats p h

/--
Julia source: base/binaryplatforms.jl:193-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.:(==)(a::Platform, b::Platform)
    return a.tags == b.tags && a.compare_strategies == b.compare_strategies
end
```
-/
def platformEq (a b) :=
  JuliaLean.DocsSyntaxCov.Binary.platformEq a b

/--
Julia source: base/binaryplatforms.jl:199-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, p::Platform)
    print(io, "Platform(")
    show(io, arch(p))
    print(io, ", ")
    show(io, os(p))
    print(io, "; ")
    # Sort tags so that the output does not depend on `Dict` iteration order
    other_tags = sort!(filter!(kv -> kv[1] ∉ ("arch", "os"), collect(tags(p))); by=first)
    join(io, ("$(k) = $(repr(v))" for (k, v) in other_tags), ", ")
    print(io, ")")
end
```
-/
def showPlatform (p) :=
  JuliaLean.DocsSyntaxCov.Binary.showPlatform p

/--
Julia source: base/binaryplatforms.jl:212-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/plain", p::Platform)
    str = string(platform_name(p), " ", arch(p))
    # Add on all the other tags not covered by os/arch:
    other_tags = sort!(filter!(kv -> kv[1] ∉ ("os", "arch"), collect(tags(p))))
    if !isempty(other_tags)
        str = string(str, " {", join([string(k, "=", v) for (k, v) in other_tags], ", "), "}")
    end
    print(io, str)
end
```
-/
def showPlatformPlain (p) :=
  JuliaLean.DocsSyntaxCov.Binary.showPlatformPlain p

/--
Julia source: base/binaryplatforms.jl:222-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function validate_tags(tags::Dict)
    throw_invalid_key(k) = throw(ArgumentError("Key \"$(k)\" cannot have value \"$(tags[k])\""))
    # Validate `arch`
    if tags["arch"] ∉ ("x86_64", "i686", "armv7l", "armv6l", "aarch64", "powerpc64le", "riscv64")
        throw_invalid_key("arch")
    end
    # Validate `os`
    if tags["os"] ∉ ("linux", "macos", "freebsd", "openbsd", "windows")
        throw_invalid_key("os")
    end
    # Validate `os`/`arch` combination
    throw_os_mismatch() = throw(ArgumentError("Invalid os/arch combination: $(tags["os"])/$(tags["arch"])"))
    if tags["os"] == "windows" && tags["arch"] ∉ ("x86_64", "i686", "armv7l", "aarch64")
        throw_os_mismatch()
    end
    if tags["os"] == "macos" && tags["arch"] ∉ ("x86_64", "aarch64")
        throw_os_mismatch()
    end

    # Validate `os`/`libc` combination
    throw_libc_mismatch() = throw(ArgumentError("Invalid os/libc combination: $(tags["os"])/$(tags["libc"])"))
    if tags["os"] == "linux"
        # Linux always has a `libc` entry
        if tags["libc"] ∉ ("glibc", "musl")
            throw_libc_mismatch()
        end
    elseif tags["os"] == "windows"
        if tags["libc"] ∉ ("msvcrt", "ucrt")
            throw_libc_mismatch()
        end
    else
        # Nothing else is allowed to have a `libc` entry
        if haskey(tags, "libc")
            throw_libc_mismatch()
        end
    end

    # Validate `os`/`arch`/`call_abi` combination
    throw_call_abi_mismatch() = throw(ArgumentError("Invalid os/arch/call_abi combination: $(tags["os"])/$(tags["arch"])/$(tags["call_abi"])"))
    if tags["os"] == "linux" && tags["arch"] ∈ ("armv7l", "armv6l")
        # If an ARM linux does not have `call_abi` set to something valid, be sad.
        if !haskey(tags, "call_abi") || tags["call_abi"] ∉ ("eabihf", "eabi")
            throw_call_abi_mismatch()
        end
    else
        # Nothing else should have a `call_abi`.
        if haskey(tags, "call_abi")
            throw_call_abi_mismatch()
        end
    end

    # Validate `libgfortran_version` is a parsable `VersionNumber`
    throw_version_number(k) = throw(ArgumentError("\"$(k)\" cannot have value \"$(tags[k])\", must be a valid VersionNumber"))
    if "libgfortran_version" in keys(tags) && tryparse(VersionNumber, tags["libgfortran_version"]) === nothing
        throw_version_number("libgfortran_version")
    end

    # Validate `cxxlib` is one of the valid options.
    if haskey(tags, "cxxlib") && tags["cxxlib"] ∉ ("libstdcxx", "libcxx")
        throw_invalid_key("cxxlib")
    end

    # Validate `cxxstring_abi` is one of the two valid options and only used with libstdc++.
    if haskey(tags, "cxxstring_abi") && (tags["cxxstring_abi"] ∉ ("cxx03", "cxx11") || !haskey(tags, "cxxlib") || tags["cxxlib"] != "libstdcxx")
        throw_invalid_key("cxxstring_abi")
    end

    # Validate `cxxlib_version` is a parsable `VersionNumber`
    if haskey(tags, "cxxlib_version") && tryparse(VersionNumber, tags["cxxlib_version"]) === nothing
        throw_version_number("cxxlib_version")
    end
end
```
-/
def validateTags (tags) :=
  JuliaLean.Platforms.validateTags tags

/--
Julia source: base/binaryplatforms.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_invalid_key(k) = throw(ArgumentError("Key \"$(k)\" cannot have value \"$(tags[k])\""))
```
-/
def throwInvalidKey (tags k) :=
  JuliaLean.DocsSyntaxCov.Binary.throwInvalidKey tags k

/--
Julia source: base/binaryplatforms.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_os_mismatch() = throw(ArgumentError("Invalid os/arch combination: $(tags["os"])/$(tags["arch"])"))
```
-/
def throwOsMismatch (tags) :=
  JuliaLean.DocsSyntaxCov.Binary.throwOsMismatch tags

/--
Julia source: base/binaryplatforms.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_libc_mismatch() = throw(ArgumentError("Invalid os/libc combination: $(tags["os"])/$(tags["libc"])"))
```
-/
def throwLibcMismatch (tags) :=
  JuliaLean.DocsSyntaxCov.Binary.throwLibcMismatch tags

/--
Julia source: base/binaryplatforms.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_call_abi_mismatch() = throw(ArgumentError("Invalid os/arch/call_abi combination: $(tags["os"])/$(tags["arch"])/$(tags["call_abi"])"))
```
-/
def throwCallAbiMismatch (tags) :=
  JuliaLean.DocsSyntaxCov.Binary.throwCallAbiMismatch tags

/--
Julia source: base/binaryplatforms.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_version_number(k) = throw(ArgumentError("\"$(k)\" cannot have value \"$(tags[k])\", must be a valid VersionNumber"))
```
-/
def throwVersionNumber (tags k) :=
  JuliaLean.DocsSyntaxCov.Binary.throwVersionNumber tags k

/--
Julia source: base/binaryplatforms.jl:295-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set_compare_strategy!(p::Platform, key::String, f::Function)
    if !haskey(p.tags, key)
        throw(ArgumentError("Cannot set comparison strategy for nonexistent tag $(key)!"))
    end
    p.compare_strategies[key] = f
end
```
-/
def setCompareStrategy (p key f) :=
  JuliaLean.DocsSyntaxCov.Binary.setCompareStrategy p key f

/--
Julia source: base/binaryplatforms.jl:302-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_compare_strategy(p::Platform, key::String, default = compare_default)
    if !haskey(p.tags, key)
        throw(ArgumentError("Cannot get comparison strategy for nonexistent tag $(key)!"))
    end
    return get(p.compare_strategies, key, default)
end
```
-/
def getCompareStrategy (p key default) :=
  JuliaLean.DocsSyntaxCov.Binary.getCompareStrategy p key default

/--
Julia source: base/binaryplatforms.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_compare_strategy(p::AbstractPlatform, key::String, default = compare_default) = default
```
-/
def getCompareStrategyAbstract (p : Platform) (key : Str) (default : Strat := .dflt) : Strat :=
  JuliaLean.DocsSyntaxCov.Binary.getCompareStrategyAbstract p.tags key default

/--
Julia source: base/binaryplatforms.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const strict_presence_tags = ("sanitize",)
```
-/
def strictPresenceTags := JuliaLean.Platforms.strictPresenceTags

/--
Julia source: base/binaryplatforms.jl:321-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compare_default(a::String, b::String, a_requested::Bool, b_requested::Bool)
    return a == b
end
```
-/
def compareDefault (a b aRequested bRequested) :=
  JuliaLean.DocsSyntaxCov.Binary.compareDefault a b aRequested bRequested

/--
Julia source: base/binaryplatforms.jl:340-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compare_version_cap(a::String, b::String, a_requested::Bool, b_requested::Bool)
    a = VersionNumber(a)
    b = VersionNumber(b)

    # If both b and a requested, then we fall back to equality:
    if a_requested && b_requested
        return a == b
    end

    # Otherwise, do the comparison between the single version cap and the single version:
    if a_requested
        return b <= a
    else
        return a <= b
    end
end
```
-/
def compareVersionCap (usem : UserSem) (a b : Str) (aRequested bRequested : Bool) : Jl Bool :=
  JuliaLean.Platforms.compare usem .cap a b aRequested bRequested

/--
Julia source: base/binaryplatforms.jl:370-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function HostPlatform(p::AbstractPlatform)
    if haskey(p, "os_version")
        set_compare_strategy!(p, "os_version", compare_version_cap)
    end
    if haskey(p, "cxxlib") && p["cxxlib"] == "libstdcxx" && haskey(p, "cxxlib_version")
        set_compare_strategy!(p, "cxxlib_version", compare_version_cap)
    end
    return p
end
```
-/
def hostPlatform (p) :=
  JuliaLean.DocsSyntaxCov.Binary.hostPlatform p

/--
Julia source: base/binaryplatforms.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
arch(p::AbstractPlatform) = get(tags(p), "arch", nothing)
```
-/
def arch (p) :=
  JuliaLean.Platforms.arch p

/--
Julia source: base/binaryplatforms.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
os(p::AbstractPlatform) = get(tags(p), "os", nothing)
```
-/
def os (p) :=
  JuliaLean.Platforms.os p

/--
Julia source: base/binaryplatforms.jl:413-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function os()
    if Sys.iswindows()
        return "windows"
    elseif Sys.isapple()
        return "macos"
    elseif Sys.isfreebsd()
        return "freebsd"
    elseif Sys.isopenbsd()
        return "openbsd"
    else
        return "linux"
    end
end
```
-/
def currentOs (sys : CurrentOS) : Str := JuliaLean.DocsSyntaxCov.Binary.currentOs sys

/--
Julia source: base/binaryplatforms.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
libc(p::AbstractPlatform) = get(tags(p), "libc", nothing)
```
-/
def libc (p) :=
  JuliaLean.Platforms.libc p

/--
Julia source: base/binaryplatforms.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
call_abi(p::AbstractPlatform) = get(tags(p), "call_abi", nothing)
```
-/
def callAbi (p) :=
  JuliaLean.Platforms.callAbi p

/--
Julia source: base/binaryplatforms.jl:463-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const platform_names = Dict(
    "linux" => "Linux",
    "macos" => "macOS",
    "windows" => "Windows",
    "freebsd" => "FreeBSD",
    "openbsd" => "OpenBSD",
    nothing => "Unknown",
)
```
-/
def platformNames := JuliaLean.DocsSyntaxCov.Binary.platformNames

/--
Julia source: base/binaryplatforms.jl:477-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function platform_name(p::AbstractPlatform)
    return platform_names[os(p)]
end
```
-/
def platformName (p) :=
  JuliaLean.DocsSyntaxCov.Binary.platformName p

/--
Julia source: base/binaryplatforms.jl:481-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function VNorNothing(d::Dict, key)
    v = get(d, key, nothing)
    if v === nothing
        return nothing
    end
    return VersionNumber(v)::VersionNumber
end
```
-/
def vnOrNothing (d key) :=
  JuliaLean.Platforms.vnOrNothing d key

/--
Julia source: base/binaryplatforms.jl:495-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
libgfortran_version(p::AbstractPlatform) = VNorNothing(tags(p), "libgfortran_version")
```
-/
def libgfortranVersion (p) :=
  JuliaLean.Platforms.libgfortranVersion p

/--
Julia source: base/binaryplatforms.jl:504-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function libstdcxx_version(p::AbstractPlatform)
    platform_tags = tags(p)
    if haskey(platform_tags, "libstdcxx_version")
        return VNorNothing(platform_tags, "libstdcxx_version")
    end
    if get(platform_tags, "cxxlib", nothing) == "libstdcxx"
        return VNorNothing(platform_tags, "cxxlib_version")
    end
    return nothing
end
```
-/
def libstdcxxVersion (p) :=
  JuliaLean.Platforms.libstdcxxVersion p

/--
Julia source: base/binaryplatforms.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cxxstring_abi(p::AbstractPlatform) = get(tags(p), "cxxstring_abi", nothing)
```
-/
def cxxstringAbi (p) :=
  JuliaLean.DocsSyntaxCov.Binary.cxxstringAbi p

/--
Julia source: base/binaryplatforms.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
os_version(p::AbstractPlatform) = VNorNothing(tags(p), "os_version")
```
-/
def osVersion (p) :=
  JuliaLean.Platforms.osVersion p

/--
Julia source: base/binaryplatforms.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wordsize(p::AbstractPlatform) = (arch(p) ∈ ("i686", "armv6l", "armv7l")) ? 32 : 64
```
-/
def wordsize (p) :=
  JuliaLean.DocsSyntaxCov.Binary.wordsize p

/--
Julia source: base/binaryplatforms.jl:565-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function triplet(p::AbstractPlatform)
    str = string(
        arch(p)::Union{Symbol,String},
        os_str(p),
        libc_str(p),
        call_abi_str(p),
    )

    # Tack on optional compiler ABI flags
    libgfortran_version_ = libgfortran_version(p)
    if libgfortran_version_ !== nothing
        str = string(str, "-libgfortran", libgfortran_version_.major)
    end
    cxxstring_abi_ = cxxstring_abi(p)
    if cxxstring_abi_ !== nothing
        str = string(str, "-", cxxstring_abi_)
    end
    libstdcxx_version_ = libstdcxx_version(p)
    if libstdcxx_version_ !== nothing
        str = string(str, "-libstdcxx", libstdcxx_version_.patch)
    end

    # Tack on all extra tags, sorted so that the output does not depend on `Dict` iteration order
    for (tag, val) in sort!(collect(tags(p)); by=first)
        if tag ∈ ("os", "arch", "libc", "call_abi", "libgfortran_version", "libstdcxx_version", "cxxstring_abi", "os_version")
            continue
        end
        if tag == "cxxlib" && val == "libstdcxx" && (cxxstring_abi_ !== nothing || libstdcxx_version_ !== nothing)
            # Implied by above
            continue
        end
        if tag == "cxxlib_version" && get(tags(p), "cxxlib", nothing) == "libstdcxx"
            # Emitted as a libstdcxx compatibility tag above
            continue
        end
        str = string(str, "-", tag, "+", val)
    end
    return str
end
```
-/
def triplet (p) :=
  JuliaLean.Platforms.triplet p

/--
Julia source: base/binaryplatforms.jl:605-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function os_str(p::AbstractPlatform)
    if os(p) == "linux"
        return "-linux"
    elseif os(p) == "macos"
        osvn = os_version(p)
        if osvn !== nothing
            return "-apple-darwin$(osvn.major)"
        else
            return "-apple-darwin"
        end
    elseif os(p) == "windows"
        return "-w64"
    elseif os(p) == "freebsd"
        osvn = os_version(p)
        if osvn !== nothing
            return "-unknown-freebsd$(osvn.major).$(osvn.minor)"
        else
            return "-unknown-freebsd"
        end
    elseif os(p) == "openbsd"
        return "-unknown-openbsd"
    else
        return "-unknown"
    end
end
```
-/
def osStr (p) :=
  JuliaLean.Platforms.osStr p

/--
Julia source: base/binaryplatforms.jl:632-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function libc_str(p::AbstractPlatform)
    lc = libc(p)
    if lc === nothing
        return ""
    elseif lc === "glibc"
        return "-gnu"
    elseif lc === "msvcrt"
        return "-mingw32"
    elseif lc === "ucrt"
        return "-ucrt-mingw32"
    else
        return string("-", lc)
    end
end
```
-/
def libcStr (p) :=
  JuliaLean.Platforms.libcStr p

/--
Julia source: base/binaryplatforms.jl:646-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function call_abi_str(p::AbstractPlatform)
    cabi = call_abi(p)
    cabi === nothing ? "" : string(cabi::Union{Symbol,String})
end
```
-/
def callAbiStr (p) :=
  JuliaLean.Platforms.callAbiStr p

/--
Julia source: base/binaryplatforms.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.isapple(p::AbstractPlatform) = os(p) == "macos"
```
-/
def isapple (p) :=
  JuliaLean.DocsSyntaxCov.Binary.isapple p

/--
Julia source: base/binaryplatforms.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.islinux(p::AbstractPlatform) = os(p) == "linux"
```
-/
def islinux (p) :=
  JuliaLean.DocsSyntaxCov.Binary.islinux p

/--
Julia source: base/binaryplatforms.jl:653-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.iswindows(p::AbstractPlatform) = os(p) == "windows"
```
-/
def iswindows (p) :=
  JuliaLean.DocsSyntaxCov.Binary.iswindows p

/--
Julia source: base/binaryplatforms.jl:654-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.isfreebsd(p::AbstractPlatform) = os(p) == "freebsd"
```
-/
def isfreebsd (p) :=
  JuliaLean.DocsSyntaxCov.Binary.isfreebsd p

/--
Julia source: base/binaryplatforms.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.isopenbsd(p::AbstractPlatform) = os(p) == "openbsd"
```
-/
def isopenbsd (p) :=
  JuliaLean.DocsSyntaxCov.Binary.isopenbsd p

/--
Julia source: base/binaryplatforms.jl:656-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.isbsd(p::AbstractPlatform) = os(p) ∈ ("freebsd", "openbsd", "macos")
```
-/
def isbsd (p) :=
  JuliaLean.DocsSyntaxCov.Binary.isbsd p

/--
Julia source: base/binaryplatforms.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Sys.isunix(p::AbstractPlatform) = Sys.isbsd(p) || Sys.islinux(p)
```
-/
def isunix (p) :=
  JuliaLean.DocsSyntaxCov.Binary.isunix p

/--
Julia source: base/binaryplatforms.jl:659-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const arch_mapping = Dict(
    "x86_64" => "(x86_|amd)64",
    "i686" => "i\\d86",
    "aarch64" => "(aarch64|arm64)",
    "armv7l" => "arm(v7l)?", # if we just see `arm-linux-gnueabihf`, we assume it's `armv7l`
    "armv6l" => "armv6l",
    "powerpc64le" => "p(ower)?pc64le",
    "riscv64" => "(rv64|riscv64)",
)
```
-/
def archMapping := JuliaLean.Platforms.archMapping

/--
Julia source: base/binaryplatforms.jl:698-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const os_mapping = Dict(
    "macos" => "-apple-darwin[\\d\\.]*",
    "freebsd" => "-(.*-)?freebsd[\\d\\.]*",
    "openbsd" => "-(.*-)?openbsd[\\d\\.]*",
    "windows" => "-w64",
    "linux" => "-(.*-)?linux",
)
```
-/
def osMapping := JuliaLean.Platforms.osMapping

/--
Julia source: base/binaryplatforms.jl:705-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const libc_mapping = Dict(
    "libc_nothing" => "",
    "ucrt"  => "-ucrt-mingw32",
    "msvcrt" => "-mingw32", # We default to msvcrt for plain -mingw32 on Windows
    "glibc" => "-gnu",
    "musl" => "-musl",
)
```
-/
def libcMapping := JuliaLean.Platforms.libcMapping

/--
Julia source: base/binaryplatforms.jl:712-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const call_abi_mapping = Dict(
    "call_abi_nothing" => "",
    "eabihf" => "eabihf",
    "eabi" => "eabi",
)
```
-/
def callAbiMapping := JuliaLean.Platforms.callAbiMapping

/--
Julia source: base/binaryplatforms.jl:717-722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const libgfortran_version_mapping = Dict(
    "libgfortran_nothing" => "",
    "libgfortran3" => "(-libgfortran3)|(-gcc4)", # support old-style `gccX` versioning
    "libgfortran4" => "(-libgfortran4)|(-gcc7)",
    "libgfortran5" => "(-libgfortran5)|(-gcc8)",
)
```
-/
def libgfortranMapping := JuliaLean.Platforms.libgfortranMapping

/--
Julia source: base/binaryplatforms.jl:723-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const cxxstring_abi_mapping = Dict(
    "cxxstring_nothing" => "",
    "cxx03" => "-cxx03",
    "cxx11" => "-cxx11",
)
```
-/
def cxxstringMapping := JuliaLean.Platforms.cxxstringMapping

/--
Julia source: base/binaryplatforms.jl:728-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const libstdcxx_version_mapping = Dict{String,String}(
    "libstdcxx_nothing" => "",
    "libstdcxx" => "-libstdcxx\\d+",
)
```
-/
def libstdcxxMapping := JuliaLean.Platforms.libstdcxxMapping

/--
Julia source: base/binaryplatforms.jl:733-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const triplet_regex = let
    # Helper function to collapse dictionary of mappings down into a regex of
    # named capture groups joined by "|" operators
    c(mapping) = string("(",join(["(?<$k>$v)" for (k, v) in mapping], "|"), ")")

    Regex(string(
        "^",
        # First, the core triplet; arch/os/libc/call_abi
        c(arch_mapping),
        c(os_mapping),
        c(libc_mapping),
        c(call_abi_mapping),
        # Next, optional things, like libgfortran/libstdcxx/cxxstring abi
        c(libgfortran_version_mapping),
        c(cxxstring_abi_mapping),
        c(libstdcxx_version_mapping),
        # Finally, the catch-all for extended tags
        "(?<tags>(?:-[^-]+\\+[^-]+)*)?",
        "\$",
    ))
end
```
-/
def tripletRegex := JuliaLean.Platforms.tripletRe

/--
Julia source: base/binaryplatforms.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    c(mapping) = string("(",join(["(?<$k>$v)" for (k, v) in mapping], "|"), ")")
```
-/
def collapseMapping (mapping) :=
  JuliaLean.DocsSyntaxCov.Binary.collapseMapping mapping

/--
Julia source: base/binaryplatforms.jl:760-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.parse(::Type{Platform}, triplet::String; validate_strict::Bool = false)
    m = match(triplet_regex, triplet)
    if m !== nothing
        # Helper function to find the single named field within the giant regex
        # that is not `nothing` for each mapping we give it.
        get_field(m, mapping) = begin
            for k in keys(mapping)
                if m[k] !== nothing
                    # Convert our sentinel `nothing` values to actual `nothing`
                    if endswith(k, "_nothing")
                        return nothing
                    end
                    # Convert libgfortran/libstdcxx version numbers
                    if startswith(k, "libgfortran")
                        return VersionNumber(parse(Int,k[12:end]))
                    elseif startswith(k, "libstdcxx")
                        return VersionNumber(3, 4, parse(Int,m[k][11:end]))
                    else
                        return k
                    end
                end
            end
        end

        # Extract the information we're interested in:
        tags = Dict{String,Any}()
        arch = get_field(m, arch_mapping)
        os = get_field(m, os_mapping)
        tags["libc"] = get_field(m, libc_mapping)
        tags["call_abi"] = get_field(m, call_abi_mapping)
        tags["libgfortran_version"] = get_field(m, libgfortran_version_mapping)
        tags["libstdcxx_version"] = get_field(m, libstdcxx_version_mapping)
        tags["cxxstring_abi"] = get_field(m, cxxstring_abi_mapping)
        function split_tags(tagstr)
            tag_fields = split(tagstr, "-"; keepempty=false)
            if isempty(tag_fields)
                return Pair{String,String}[]
            end
            return map(v -> String(v[1]) => String(v[2]), split.(tag_fields, "+"))
        end
        merge!(tags, Dict(split_tags(m["tags"])))

        # Special parsing of os version number, if any exists
        function extract_os_version(os_name, pattern)
            m_osvn = match(pattern, m[os_name])
            if m_osvn !== nothing
                return VersionNumber(m_osvn.captures[1])
            end
            return nothing
        end
        os_version = nothing
        if os == "macos"
            os_version = extract_os_version("macos", r".*darwin([\d.]+)"sa)
        end
        if os == "freebsd"
            os_version = extract_os_version("freebsd", r".*freebsd([\d.]+)"sa)
        end
        if os == "openbsd"
            os_version = extract_os_version("openbsd", r".*openbsd([\d.]+)"sa)
        end
        tags["os_version"] = os_version

        return Platform(arch, os, tags; validate_strict)
    end
    throw(ArgumentError("Platform `$(triplet)` is not an officially supported platform"))
end
```
-/
def parsePlatform (lc validateStrict triplet) :=
  JuliaLean.Platforms.parsePlatform lc validateStrict triplet

/--
Julia source: base/binaryplatforms.jl:765-782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        get_field(m, mapping) = begin
            for k in keys(mapping)
                if m[k] !== nothing
                    # Convert our sentinel `nothing` values to actual `nothing`
                    if endswith(k, "_nothing")
                        return nothing
                    end
                    # Convert libgfortran/libstdcxx version numbers
                    if startswith(k, "libgfortran")
                        return VersionNumber(parse(Int,k[12:end]))
                    elseif startswith(k, "libstdcxx")
                        return VersionNumber(3, 4, parse(Int,m[k][11:end]))
                    else
                        return k
                    end
                end
            end
        end
```
-/
def getField (m mapping) :=
  JuliaLean.Platforms.getField m mapping

/--
Julia source: base/binaryplatforms.jl:793-799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function split_tags(tagstr)
            tag_fields = split(tagstr, "-"; keepempty=false)
            if isempty(tag_fields)
                return Pair{String,String}[]
            end
            return map(v -> String(v[1]) => String(v[2]), split.(tag_fields, "+"))
        end
```
-/
def splitTags (tagstr) :=
  JuliaLean.Platforms.splitTags tagstr

/--
Julia source: base/binaryplatforms.jl:803-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function extract_os_version(os_name, pattern)
            m_osvn = match(pattern, m[os_name])
            if m_osvn !== nothing
                return VersionNumber(m_osvn.captures[1])
            end
            return nothing
        end
```
-/
def extractOsVersion (osField name) :=
  JuliaLean.Platforms.extractOsVersion osField name

/--
Julia source: base/binaryplatforms.jl:826-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.parse(::Type{Platform}, triplet::AbstractString; kwargs...) =
    parse(Platform, convert(String, triplet)::String; kwargs...)
```
-/
def parseAbstract (convertString validate triplet) :=
  JuliaLean.DocsSyntaxCov.Binary.parseAbstract convertString validate triplet

/--
Julia source: base/binaryplatforms.jl:829-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.tryparse(::Type{Platform}, triplet::AbstractString)
    try
        parse(Platform, triplet)
    catch e
        if isa(e, InterruptException)
            rethrow(e)
        end
        return nothing
    end
end
```
-/
def tryparsePlatform (parse triplet) :=
  JuliaLean.DocsSyntaxCov.Binary.tryparsePlatform parse triplet

/--
Julia source: base/binaryplatforms.jl:847-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function platform_dlext(p::AbstractPlatform = HostPlatform())
    if os(p) == "windows"
        return "dll"
    elseif os(p) == "macos"
        return "dylib"
    else
        return "so"
    end
end
```
-/
def platformDlext (p) :=
  JuliaLean.Platforms.platformDlext p

/--
Julia source: base/binaryplatforms.jl:858-866 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _this_os_name()
    if Sys.iswindows()
        return "windows"
    elseif Sys.isapple()
        return "macos"
    else
        return "other"
    end
end
```
-/
def thisOsName (windows apple) :=
  JuliaLean.DocsSyntaxCov.Binary.thisOsName windows apple

/--
Julia source: base/binaryplatforms.jl:893-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_dl_name_version(path::String, os::String=_this_os_name())
    # Use an extraction regex that matches the given OS
    # A tag may follow the soversion (`libLLVM.so.21.1jl`), but only after a version.
    local dlregex
    # Keep this up to date with _this_os_name
    if os == "windows"
        # On Windows, libraries look like `libnettle-6.dll`.
        # Stay case-insensitive, the suffix might be `.DLL`.
        dlregex = r"^(.*?)(?:-(?:((?:[\.\d]+)+)([A-Za-z][\w\.]*)?)?)?\.dll$"isa
    elseif os == "macos"
        # On OSX, libraries look like `libnettle.6.3.dylib`
        dlregex = r"^(.*?)(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?\.dylib$"sa
    else
        # On Linux and other BSDs, libraries look like `libnettle.so.6.3.0`
        dlregex = r"^(.*?)\.so(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?$"sa
    end

    m = match(dlregex, basename(path))
    if m === nothing
        throw(ArgumentError("Invalid dynamic library path '$path'"))
    end

    # Extract name and version
    name = m.captures[1]
    version = m.captures[2]
    if version === nothing || isempty(version)
        version = nothing
    else
        version = VersionNumber(strip(version, '.'))
    end
    return name, version
end
```
-/
def parseDlNameVersion (path os) :=
  JuliaLean.Platforms.parseDlNameVersion path os

/--
Julia source: base/binaryplatforms.jl:927-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_dl_name_version(path::AbstractString, os::AbstractString=_this_os_name())
    return parse_dl_name_version(string(path)::String, string(os)::String)
end
```
-/
def parseDlAbstract (toString path os) :=
  JuliaLean.DocsSyntaxCov.Binary.parseDlAbstract toString path os

/--
Julia source: base/binaryplatforms.jl:931-944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_csl_member(member::Symbol)
    # If CompilerSupportLibraries_jll is a stdlib, we can just grab things from it
    csl_pkgids = filter(pkgid -> pkgid.name == "CompilerSupportLibraries_jll", keys(Base.loaded_modules))
    if !isempty(csl_pkgids)
        CSL_mod = Base.loaded_modules[first(csl_pkgids)]

        # This can fail during bootstrap, so we skip in that case.
        if isdefined(CSL_mod, member)
            return getproperty(CSL_mod, member)
        end
    end

    return nothing
end
```
-/
def getCslMember (mods member) :=
  JuliaLean.DocsSyntaxCov.Binary.getCslMember mods member

/--
Julia source: base/binaryplatforms.jl:947-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _get_libgfortran_path()
    # If CompilerSupportLibraries_jll is a stdlib, we can just directly ask for
    # the path here, without checking `dllist()`:
    libgfortran_path = get_csl_member(:libgfortran_path)
    if libgfortran_path !== nothing
        return libgfortran_path::String
    end

    # Otherwise, look for it having already been loaded by something
    libgfortran_paths = filter!(x -> occursin("libgfortran", x), Libdl.dllist())
    if !isempty(libgfortran_paths)
        return first(libgfortran_paths)::String
    end

    # One day, I hope to not be linking against libgfortran in base Julia
    return nothing
end
```
-/
def getLibgfortranPath (mods dllist) :=
  JuliaLean.DocsSyntaxCov.Binary.getLibgfortranPath mods dllist

/--
Julia source: base/binaryplatforms.jl:965-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _get_libstdcxx_handle()
    # If CompilerSupportLibraries_jll is a stdlib, we can just directly open it
    libstdcxx = get_csl_member(:libstdcxx)
    if libstdcxx !== nothing
        return nothing
    end

    # Otherwise, look for it having already been loaded by something
    libstdcxx_paths = filter!(x -> occursin("libstdc++", x), Libdl.dllist())
    if !isempty(libstdcxx_paths)
        return Libdl.dlopen(first(libstdcxx_paths), Libdl.RTLD_NOLOAD)::Ptr{Cvoid}
    end

    # One day, I hope to not be linking against libstdc++ in base Julia
    return nothing
end
```
-/
def getLibstdcxxHandle (mods dllist openFn) :=
  JuliaLean.DocsSyntaxCov.Binary.getLibstdcxxHandle mods dllist openFn

/--
Julia source: base/binaryplatforms.jl:989-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function detect_libgfortran_version()
    libgfortran_path = _get_libgfortran_path()
    _, version = parse_dl_name_version(libgfortran_path, os())
    if version === nothing
        # Even though we complain about this, we allow it to continue in the hopes that
        # we shall march on to a BRIGHTER TOMORROW.  One in which we are not shackled
        # by the constraints of libgfortran compiler ABIs upon our precious programming
        # languages; one where the mistakes of yesterday are mere memories and not
        # continual maintenance burdens upon the children of the dawn; one where numeric
        # code may be cleanly implemented in a modern language and not bestowed onto the
        # next generation by grizzled ancients, documented only with a faded yellow
        # sticky note that bears a hastily-scribbled "good luck".
        @warn("Unable to determine libgfortran version from '$(libgfortran_path)'")
    end
    return version
end
```
-/
def detectLibgfortranVersionFrom (mods : List LoadedModule) (dllist : List Str) (os : Str) :
    Jl (Option VersionNumber) :=
  JuliaLean.DocsSyntaxCov.Binary.detectLibgfortranVersion
    (JuliaLean.DocsSyntaxCov.Binary.getLibgfortranPath mods dllist) os

/--
Julia source: base/binaryplatforms.jl:1013-1027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function detect_libstdcxx_version(max_minor_version::Int=30)
    # Brute-force our way through GLIBCXX_* symbols to discover which version we're linked against
    libstdcxx = _get_libstdcxx_handle()

    if libstdcxx !== nothing
        # Try all GLIBCXX versions down to GCC v4.8:
        # https://gcc.gnu.org/onlinedocs/libstdc++/manual/abi.html
        for minor_version in max_minor_version:-1:18
            if Libdl.dlsym(libstdcxx, "GLIBCXX_3.4.$(minor_version)"; throw_error=false) !== nothing
                return VersionNumber("3.4.$(minor_version)")
            end
        end
    end
    return nothing
end
```
-/
def detectLibstdcxxVersionFrom (mods : List LoadedModule) (dllist : List Str)
    (openFn : Str → Option Nat) (hasSymbol : Nat → Str → Bool) (maxMinor : Nat) :
    Jl (Option VersionNumber) :=
  let handle := JuliaLean.DocsSyntaxCov.Binary.getLibstdcxxHandle mods dllist openFn
  let proc : JuliaLean.Platforms.Proc := {
    cslLibstdcxx := (JuliaLean.DocsSyntaxCov.Binary.getCslMember mods "libstdcxx").isSome
    dllist := dllist
    glibcxx := fun minor =>
      match handle with
      | none => false
      | some h => hasSymbol h (s% "GLIBCXX_3.4." ++ Nat.toDigits 10 minor)
  }
  JuliaLean.Platforms.detectLibstdcxxVersion proc maxMinor

/--
Julia source: base/binaryplatforms.jl:1038-1071 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function detect_cxxstring_abi()
    # First, if we're not linked against libstdc++, then early-exit because this doesn't matter.
    libstdcxx_paths = filter!(x -> occursin("libstdc++", x), Libdl.dllist())
    if isempty(libstdcxx_paths)
        # We were probably built by `clang`; we don't link against `libstdc++`` at all.
        return nothing
    end

    function open_libllvm(f::Function)
        for lib_name in (Base.libllvm_name, "libLLVM", "LLVM", "libLLVMSupport")
            hdl = Libdl.dlopen_e(lib_name)
            if hdl != C_NULL
                try
                    return f(hdl)
                finally
                    Libdl.dlclose(hdl)
                end
            end
        end
        error("Unable to open libLLVM!")
    end

    return open_libllvm() do hdl
        # Check for llvm::sys::getProcessTriple(), first without cxx11 tag:
        if Libdl.dlsym_e(hdl, "_ZN4llvm3sys16getProcessTripleEv") != C_NULL
            return "cxx03"
        elseif Libdl.dlsym_e(hdl, "_ZN4llvm3sys16getProcessTripleB5cxx11Ev") != C_NULL
            return "cxx11"
        else
            @warn("Unable to find llvm::sys::getProcessTriple() in libLLVM!")
            return nothing
        end
    end
end
```
-/
def detectCxxstringAbi (dllist openFn hasSymbol closeFn names) :=
  JuliaLean.DocsSyntaxCov.Binary.detectCxxstringAbi dllist openFn hasSymbol closeFn names

/--
Julia source: base/binaryplatforms.jl:1046-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function open_libllvm(f::Function)
        for lib_name in (Base.libllvm_name, "libLLVM", "LLVM", "libLLVMSupport")
            hdl = Libdl.dlopen_e(lib_name)
            if hdl != C_NULL
                try
                    return f(hdl)
                finally
                    Libdl.dlclose(hdl)
                end
            end
        end
        error("Unable to open libLLVM!")
    end
```
-/
def openLibllvm {A : Type} (names openFn closeFn f) :=
  JuliaLean.DocsSyntaxCov.Binary.openLibllvm (A := A) names openFn closeFn f

/--
Julia source: base/binaryplatforms.jl:1082-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function host_triplet(build_triplet::String = Base.BUILD_TRIPLET, ext_tags::String = Base.BUILD_EXT_TAGS)
    str = build_triplet

    if !occursin("-libgfortran", str)
        libgfortran_version = detect_libgfortran_version()
        if libgfortran_version !== nothing
            str = string(str, "-libgfortran", libgfortran_version.major)
        end
    end

    if !occursin("-cxx", str)
        cxxstring_abi = detect_cxxstring_abi()
        if cxxstring_abi !== nothing
            str = string(str, "-", cxxstring_abi)
        end
    end

    if !occursin("-libstdcxx", str)
        libstdcxx_version = detect_libstdcxx_version()
        if libstdcxx_version !== nothing
            str = string(str, "-libstdcxx", libstdcxx_version.patch)
        end
    end

    # Add on any extended tags recorded by the build
    str = string(str, ext_tags)

    # Add on julia_version extended tag
    if !occursin("-julia_version+", str)
        str = string(str, "-julia_version+", VersionNumber(VERSION.major, VERSION.minor, VERSION.patch))
    end
    return str
end
```
-/
def hostTriplet (build ext versions) :=
  JuliaLean.DocsSyntaxCov.Binary.hostTriplet build ext versions

/--
Julia source: base/binaryplatforms.jl:1124-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function HostPlatform()
    return HostPlatform(parse(Platform, host_triplet()))::Platform
end
```
-/
def hostPlatformFrom (parse : Str → Jl Platform) (build ext : Str) (versions : HostVersions) :
    Jl Platform :=
  JuliaLean.DocsSyntaxCov.Binary.hostPlatform0 parse
    (JuliaLean.DocsSyntaxCov.Binary.hostTriplet build ext versions)

/--
Julia source: base/binaryplatforms.jl:1153-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function platforms_match(a::AbstractPlatform, b::AbstractPlatform)
    for k in union(keys(tags(a)::Dict{String,String}), keys(tags(b)::Dict{String,String}))
        ak = get(tags(a), k, nothing)
        bk = get(tags(b), k, nothing)

        # A tag missing from one side acts as a wildcard, except for strict tags
        if ak === nothing || bk === nothing
            if k in strict_presence_tags
                return false
            end
            continue
        end

        a_comp = get_compare_strategy(a, k)
        b_comp = get_compare_strategy(b, k)

        # Throw an error if `a` and `b` have both set non-default comparison strategies for `k`
        # and they're not the same strategy.
        if a_comp !== compare_default && b_comp !== compare_default && a_comp !== b_comp
            throw(ArgumentError("Cannot compare Platform objects with two different non-default comparison strategies for the same key \"$(k)\""))
        end

        # Select the custom comparator, if we have one.
        comparator = a_comp
        if b_comp !== compare_default
            comparator = b_comp
        end

        # Call the comparator, passing in which objects requested this comparison (one, the other, or both)
        # For some comparators this doesn't matter, but for non-symmetrical comparisons, it does.
        if !(@invokelatest(comparator(ak, bk, a_comp === comparator, b_comp === comparator))::Bool)
            return false
        end
    end
    return true
end
```
-/
def platformsMatch (usem order a b) :=
  JuliaLean.Platforms.platformsMatch usem order a b

/--
Julia source: base/binaryplatforms.jl:1190-1192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function platforms_match(a::String, b::AbstractPlatform)
    return platforms_match(parse(Platform, a), b)
end
```
-/
def platformsMatchStringLeft (parse usem order a b) :=
  JuliaLean.DocsSyntaxCov.Binary.matchStringLeft parse usem order a b

/--
Julia source: base/binaryplatforms.jl:1193-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function platforms_match(a::AbstractPlatform, b::String)
    return platforms_match(a, parse(Platform, b))
end
```
-/
def platformsMatchStringRight (parse usem order a b) :=
  JuliaLean.DocsSyntaxCov.Binary.matchStringRight parse usem order a b

/--
Julia source: base/binaryplatforms.jl:1196-1196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
platforms_match(a::String, b::String) = platforms_match(parse(Platform, a), parse(Platform, b))
```
-/
def platformsMatchStrings (parse usem order a b) :=
  JuliaLean.DocsSyntaxCov.Binary.matchStrings parse usem order a b

/--
Julia source: base/binaryplatforms.jl:1199-1199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
platforms_match(a::AbstractString, b::AbstractPlatform) = platforms_match(string(a)::String, b)
```
-/
def platformsMatchAbstractLeft (toString : Str → Str) (parse : Str → Jl Platform)
    (usem : UserSem) (order : Platform → Platform → List Str) (a : Str) (b : Platform) : Jl Bool :=
  JuliaLean.DocsSyntaxCov.Binary.matchStringLeft parse usem order (toString a) b

/--
Julia source: base/binaryplatforms.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
platforms_match(a::AbstractPlatform, b::AbstractString) = platforms_match(a, string(b)::String)
```
-/
def platformsMatchAbstractRight (toString : Str → Str) (parse : Str → Jl Platform)
    (usem : UserSem) (order : Platform → Platform → List Str) (a : Platform) (b : Str) : Jl Bool :=
  JuliaLean.DocsSyntaxCov.Binary.matchStringRight parse usem order a (toString b)

/--
Julia source: base/binaryplatforms.jl:1201-1201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
platforms_match(a::AbstractString, b::AbstractString) = platforms_match(string(a)::String, string(b)::String)
```
-/
def platformsMatchAbstractStrings (toString f a b) :=
  JuliaLean.DocsSyntaxCov.Binary.matchAbstractStrings toString f a b

/--
Julia source: base/binaryplatforms.jl:1215-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function select_platform(download_info::Dict, platform::AbstractPlatform = HostPlatform())
    ps = collect(filter(p -> platforms_match(p, platform), keys(download_info)))

    if isempty(ps)
        return nothing
    end

    # At this point, we may have multiple possibilities.  We now engage a multi-
    # stage selection algorithm, where we first sort the matches by how complete
    # the match is, e.g. preferring matches where the intersection of tags is
    # equal to the union of the tags:
    function match_loss(a, b)
        a_tags = Set(keys(tags(a)))
        b_tags = Set(keys(tags(b)))
        return length(union(a_tags, b_tags)) - length(intersect(a_tags, b_tags))
    end

    # We prefer these better matches, and secondarily reverse-sort by triplet so
    # as to generally choose the latest release (e.g. a `libgfortran5` tarball
    # over a `libgfortran3` tarball).
    sort!(ps, lt = (a, b) -> begin
        loss_a = match_loss(a, platform)
        loss_b = match_loss(b, platform)
        if loss_a != loss_b
            return loss_a < loss_b
        end
        return triplet(a) > triplet(b)
    end)

    # @invokelatest here to not get invalidated by new defs of `==(::Function, ::Function)`
    return @invokelatest getindex(download_info, first(ps))
end
```
-/
def selectPlatform {α : Type} (usem order entries host) :=
  JuliaLean.Platforms.selectPlatform (α := α) usem order entries host

/--
Julia source: base/binaryplatforms.jl:1226-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function match_loss(a, b)
        a_tags = Set(keys(tags(a)))
        b_tags = Set(keys(tags(b)))
        return length(union(a_tags, b_tags)) - length(intersect(a_tags, b_tags))
    end
```
-/
def matchLoss (a b) :=
  JuliaLean.DocsSyntaxCov.Binary.matchLoss a b

-- Reason: The architecture-to-feature map depends on `CPUID.ISAs_by_family` data from cpuid.jl.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:668-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Keep this in sync with `CPUID.ISAs_by_family`
-- # These are the CPUID side of the microarchitectures targeted by GCC flags in BinaryBuilder.jl
-- const arch_march_isa_mapping = let
-- /Source

/-!
Julia source: base/binaryplatforms.jl:671-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function get_set(arch, name)
        all = CPUID.ISAs_by_family[arch]
        return all[findfirst(x -> x.first == name, all)].second
    end
```
-/
def firstFeatureIndex {Set : Type} : List (String × Set) → String → Option Nat
  | [], _ => none
  | (feature, _) :: rest, name =>
    if feature == name then some 1 else (firstFeatureIndex rest name).map (· + 1)

def getSet {Arch Set : Type} (familySets : Arch → List (String × Set))
    (arch : Arch) (name : String) : Jl Set := do
  let all := familySets arch
  let index := firstFeatureIndex all name
  let pair ← match index with
    | some index =>
      match all[index - 1]? with
      | some pair => pure pair
      | none => throw .boundsError
    | none => throw (.methodError "getindex")
  pure pair.2

-- Reason: The architecture map's values depend on CPU feature data from cpuid.jl.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:675-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Dict(
--         "i686" => [
--             "pentium4" => get_set("i686", "pentium4"),
--             "prescott" => get_set("i686", "prescott"),
--         ],
--         "x86_64" => [
--             "x86_64" => get_set("x86_64", "x86_64"),
--             "avx" => get_set("x86_64", "sandybridge"),
--             "avx2" => get_set("x86_64", "haswell"),
--             "avx512" => get_set("x86_64", "skylake_avx512"),
--         ],
--         "aarch64" => [
--             "armv8_0" => get_set("aarch64", "armv8.0-a"),
--             "armv8_1" => get_set("aarch64", "armv8.1-a"),
--             "armv8_2_crypto" => get_set("aarch64", "armv8.2-a+crypto"),
--             "a64fx" => get_set("aarch64", "a64fx"),
--             "apple_m1" => get_set("aarch64", "apple_m1"),
--         ],
--         "riscv64" => [
--             "riscv64" => get_set("riscv64", "riscv64"),
--         ],
--     )
-- end
-- /Source

-- Reason: These precompile forms affect compiler latency and have no runtime method bodies.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1248-1253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # precompiles to reduce latency (see https://github.com/JuliaLang/julia/pull/43990#issuecomment-1025692379)
-- Dict{Platform,String}()[HostPlatform()] = ""
-- Platform("x86_64", "linux", Dict{String,Any}(); validate_strict=true)
-- Platform("x86_64", "linux", Dict{String,String}(); validate_strict=false)  # called this way from Artifacts.unpack_platform
-- 
-- end # module
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module BinaryPlatforms
-- 
-- export AbstractPlatform, Platform, HostPlatform, platform_dlext, tags, arch, os,
--        os_version, libc, libgfortran_version, libstdcxx_version,
--        cxxstring_abi, parse_dl_name_version, detect_libgfortran_version,
--        detect_libstdcxx_version, detect_cxxstring_abi, call_abi, wordsize, triplet,
--        select_platform, platforms_match, platform_name
-- import .Libc.Libdl
-- 
-- ### Submodule with information about CPU features
-- include("cpuid.jl")
-- using .CPUID
-- 
-- # This exists to ease compatibility with old-style Platform objects
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:18-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Platform
-- 
-- A `Platform` represents all relevant pieces of information that a julia process may need
-- to know about its execution environment, such as the processor architecture, operating
-- system, libc implementation, etc...  It is, at its heart, a key-value mapping of tags
-- (such as `arch`, `os`, `libc`, etc...) to values (such as `"arch" => "x86_64"`, or
-- `"os" => "windows"`, etc...).  `Platform` objects are extensible in that the tag mapping
-- is open for users to add their own mappings to, as long as the mappings do not conflict
-- with the set of reserved tags: `arch`, `os`, `os_version`, `libc`, `call_abi`,
-- `libgfortran_version`, `libstdcxx_version`, `cxxlib`, `cxxlib_version`,
-- `cxxstring_abi` and `julia_version`.
-- 
-- Valid tags and values are composed of alphanumeric and period characters.  All tags and
-- values will be lowercased when stored to reduce variation.
-- 
-- Example:
-- 
--     Platform("x86_64", "windows"; cuda = "10.1")
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # Passing `tags` as a `Dict` avoids the need to infer different NamedTuple specializations
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:101-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # Keyword interface (to avoid inference of specialized NamedTuple methods, use the Dict interface for `tags`)
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:152-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Simple tag insertion that performs a little bit of validation
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:172-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Other `Platform` types can override this (I'm looking at you, `AnyPlatform`)
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:175-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Make it act more like a dict
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:183-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Hash definition to ensure that it's stable
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:191-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Simple equality definition; for compatibility testing, use `platforms_match()`
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:196-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Allow us to easily serialize Platform objects
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:210-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Make showing the platform a bit more palatable
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:294-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:309-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Tags for which absence is meaningful: a platform without the tag only matches
-- # platforms that also lack it (rather than acting as a wildcard).
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:313-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     compare_default(a::String, b::String, a_requested::Bool, b_requested::Bool)
-- 
-- Default comparison strategy that falls back to `a == b`.  This only ever happens if both
-- `a` and `b` request this strategy, as any other strategy is preferable to this one.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:324-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     compare_version_cap(a::String, b::String, a_comparator, b_comparator)
-- 
-- Example comparison strategy for `set_comparison_strategy!()` that implements a version
-- cap for host platforms that support _up to_ a particular version number.  As an example,
-- if an artifact is built for macOS 10.9, it can run on macOS 10.11, however if it were
-- built for macOS 10.12, it could not.  Therefore, the host platform of macOS 10.11 has a
-- version cap at `v"10.11"`.
-- 
-- Note that because both hosts and artifacts are represented with `Platform` objects it
-- is possible to call `platforms_match()` with two artifacts, a host and an artifact, an
-- artifact and a host, and even two hosts.  We attempt to do something intelligent for all
-- cases, but in the case of comparing version caps between two hosts, we return `true` only
-- if the two host platforms are in fact identical.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:356-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- 
-- """
--     HostPlatform(p::AbstractPlatform)
-- 
-- Convert a `Platform` to act like a "host"; e.g. if it has a version-bound tag such as
-- `"libstdcxx_version" => "3.4.26"`, it will treat that value as an upper bound, rather
-- than a characteristic.  `Platform` objects that define artifacts generally denote the
-- SDK or version that the artifact was built with, but for platforms, these versions are
-- generally the maximal version the platform can support.  The way this transformation
-- is implemented is to change the appropriate comparison strategies to treat these pieces
-- of data as bounds rather than points in any comparison.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:379-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     arch(p::AbstractPlatform)
-- 
-- Get the architecture for the given `Platform` object as a `String`.
-- 
-- # Examples
-- ```jldoctest
-- julia> arch(Platform("aarch64", "Linux"))
-- "aarch64"
-- 
-- julia> arch(Platform("amd64", "freebsd"))
-- "x86_64"
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:395-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     os(p::AbstractPlatform)
-- 
-- Get the operating system for the given `Platform` object as a `String`.
-- 
-- # Examples
-- ```jldoctest
-- julia> os(Platform("armv7l", "Linux"))
-- "linux"
-- 
-- julia> os(Platform("aarch64", "macos"))
-- "macos"
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:411-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # As a special helper, it's sometimes useful to know the current OS at compile-time
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:426-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     libc(p::AbstractPlatform)
-- 
-- Get the libc for the given `Platform` object as a `String`.  Returns `nothing` on
-- platforms with no explicit `libc` choices (which is most platforms).
-- 
-- # Examples
-- ```jldoctest
-- julia> libc(Platform("armv7l", "Linux"))
-- "glibc"
-- 
-- julia> libc(Platform("aarch64", "linux"; libc="musl"))
-- "musl"
-- 
-- julia> libc(Platform("i686", "Windows"))
-- "msvcrt"
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:446-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     call_abi(p::AbstractPlatform)
-- 
-- Get the call ABI for the given `Platform` object as a `String`.  Returns `nothing` on
-- platforms with no explicit `call_abi` choices (which is most platforms).
-- 
-- # Examples
-- ```jldoctest
-- julia> call_abi(Platform("armv7l", "Linux"))
-- "eabihf"
-- 
-- julia> call_abi(Platform("x86_64", "macos"))
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:471-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     platform_name(p::AbstractPlatform)
-- 
-- Get the "platform name" of the given platform, returning e.g. "Linux" or "Windows".
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:488-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     libgfortran_version(p::AbstractPlatform)
-- 
-- Get the libgfortran version dictated by this `Platform` object as a `VersionNumber`,
-- or `nothing` if no compatibility bound is imposed.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:496-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     libstdcxx_version(p::AbstractPlatform)
-- 
-- Get the libstdc++ version dictated by this `Platform` object, or `nothing` if no
-- compatibility bound is imposed.  This is a compatibility accessor for
-- `cxxlib = "libstdcxx"` platforms with a `cxxlib_version`.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:514-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     cxxstring_abi(p::AbstractPlatform)
-- 
-- Get the c++ string ABI dictated by this `Platform` object, or `nothing` if no ABI is imposed.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:521-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     os_version(p::AbstractPlatform)
-- 
-- Get the OS version dictated by this `Platform` object, or `nothing` if no OS version is
-- imposed/no data is available.  This is most commonly used by MacOS and FreeBSD objects
-- where we have high platform SDK fragmentation, and features are available only on certain
-- platform versions.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:531-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     wordsize(p::AbstractPlatform)
-- 
-- Get the word size for the given `Platform` object.
-- 
-- # Examples
-- ```jldoctest
-- julia> wordsize(Platform("armv7l", "linux"))
-- 32
-- 
-- julia> wordsize(Platform("x86_64", "macos"))
-- 64
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:547-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     triplet(p::AbstractPlatform)
-- 
-- Get the target triplet for the given `Platform` object as a `String`.
-- 
-- # Examples
-- ```jldoctest
-- julia> triplet(Platform("x86_64", "MacOS"))
-- "x86_64-apple-darwin"
-- 
-- julia> triplet(Platform("i686", "Windows"))
-- "i686-w64-mingw32"
-- 
-- julia> triplet(Platform("armv7l", "Linux"; libgfortran_version="3"))
-- "armv7l-linux-gnueabihf-libgfortran3"
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:604-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:630-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Helper functions for Linux and FreeBSD libc/abi mishmashes
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:650-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:658-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:754-759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parse(::Type{Platform}, triplet::AbstractString)
-- 
-- Parses a string platform triplet back into a `Platform` object.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:828-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:839-846 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     platform_dlext(p::AbstractPlatform = HostPlatform())
-- 
-- Return the dynamic library extension for the given platform, defaulting to the
-- currently running platform.  E.g. returns "so" for a Linux-based platform,
-- "dll" for a Windows-based platform, etc...
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:856-857 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Not general purpose, just for parse_dl_name_version
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:867-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parse_dl_name_version(path::String, platform::AbstractPlatform)
-- 
-- Given a path to a dynamic library, parse out what information we can
-- from the filename.  E.g. given something like "lib/libfoo.so.3.2",
-- this function returns `"libfoo", v"3.2"`.  If the path name is not a
-- valid dynamic library, this method throws an error.  If no soversion
-- can be extracted from the filename, as in "libbar.so" this method
-- returns `"libbar", nothing`.
-- 
-- A soversion may carry a trailing tag, as Julia's own LLVM does; the tag is not part of the
-- name and is not reported.
-- 
-- # Examples
-- ```jldoctest
-- julia> parse_dl_name_version("lib/libfoo.so.3.2", "linux")
-- ("libfoo", v"3.2.0")
-- 
-- julia> parse_dl_name_version("libbar.so", "linux")
-- ("libbar", nothing)
-- 
-- julia> parse_dl_name_version("libLLVM.so.21.1jl", "linux")
-- ("libLLVM", v"21.1.0")
-- ```
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:925-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Adapter for `AbstractString`
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:930-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:945-946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:964-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:981-988 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     detect_libgfortran_version()
-- 
-- Inspects the current Julia process to determine the libgfortran version this Julia is
-- linked against (if any).  Returns `nothing` if no libgfortran version dependence is
-- detected.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1005-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     detect_libstdcxx_version(max_minor_version::Int=30)
-- 
-- Inspects the currently running Julia process to find out what version of libstdc++
-- it is linked against (if any).  `max_minor_version` is the latest version in the
-- 3.4 series of GLIBCXX where the search is performed.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1028-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     detect_cxxstring_abi()
-- 
-- Inspects the currently running Julia process to see what version of the C++11 string ABI
-- it was compiled with (this is only relevant if compiled with `g++`; `clang` has no
-- incompatibilities yet, bless its heart).  In reality, this actually checks for symbols
-- within LLVM, but that is close enough for our purposes, as you can't mix configurations
-- between Julia and LLVM; they must match.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1072-1081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     host_triplet(build_triplet::String = Base.BUILD_TRIPLET, ext_tags::String = Base.BUILD_EXT_TAGS)
-- 
-- Build host triplet out of `Sys.MACHINE` and various introspective utilities that
-- detect compiler ABI values such as `libgfortran_version`, `libstdcxx_version` and
-- `cxxstring_abi`.  We do this without using any `Platform` tech as it must run before
-- we have much of that built.  Extended tags recorded by the build (e.g. `-sanitize+address`)
-- are appended after the compiler ABI tags, as the triplet grammar requires.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1115-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     HostPlatform()
-- 
-- Return the `Platform` object that corresponds to the current host system, with all
-- relevant comparison strategies set to host platform mode.  This is equivalent to:
-- 
--     HostPlatform(parse(Platform, Base.BinaryPlatforms.host_triplet()))
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1127-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     platforms_match(a::AbstractPlatform, b::AbstractPlatform)
-- 
-- Return `true` if `a` and `b` are matching platforms, where matching is determined by
-- comparing all keys contained within the platform objects, and if both objects contain
-- entries for that key, they must match.  Comparison, by default, is performed using
-- the `==` operator, however this can be overridden on a key-by-key basis by adding
-- "comparison strategies" through `set_compare_strategy!(platform, key, func)`.
-- 
-- Note that as the comparison strategy is set on the `Platform` object, and not globally,
-- a custom comparison strategy is first looked for within the `a` object, then if none
-- is found, it is looked for in the `b` object.  Finally, if none is found in either, the
-- default of `==(ak, bk)` is used.  We throw an error if custom comparison strategies are
-- used on both `a` and `b` and they are not the same custom comparison.
-- 
-- The reserved tags `os_version` and `libstdcxx_version` use this mechanism to provide
-- bounded version constraints, where an artifact can specify that it was built using APIs
-- only available in macOS `v"10.11"` and later, or an artifact can state that it requires
-- a libstdc++ that is at least `v"3.4.22"`, etc...
-- 
-- Keys present in only one of `a` or `b` are normally ignored, with the exception of the
-- `sanitize` tag: a sanitized platform (e.g. `x86_64-linux-gnu-sanitize+memory`) never
-- matches a platform without a `sanitize` tag, since instrumented and uninstrumented
-- binaries cannot be mixed.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1197-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Adapters for AbstractString backedge avoidance
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1202-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     select_platform(download_info::Dict, platform::AbstractPlatform = HostPlatform())
-- 
-- Given a `download_info` dictionary mapping platforms to some value, choose
-- the value whose key best matches `platform`, returning `nothing` if no matches
-- can be found.
-- 
-- Platform attributes such as architecture, libc, calling ABI, etc... must all
-- match exactly, however attributes such as compiler ABI can have wildcards
-- within them such as `nothing` which matches any version of GCC.
-- """
-- /Source

-- Reason: This range contains only source documentation, comments, whitespace, or module scaffolding; it has no runtime method body.
-- UNTRANSLATED
-- Source: base/binaryplatforms.jl:1247-1247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.binaryplatforms
