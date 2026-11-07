import JuliaLean.Core
import JuliaLean.base.parse

/-!
# Backtracking regular-expression matcher

The fragment of PCRE2 used by `base/version.jl`, with the matching order of
PCRE2's backtracking engine: alternatives are tried left to right, `*` and `?`
are greedy and give back one iteration at a time, a failed branch restores the
captures it set, and a group's capture is the substring of its latest
completed iteration on the successful path.

Strings are lists of characters (valid UTF-8 `String`s). The patterns are
compiled by Julia with `UTF | UCP` (`base/regex.jl:7`), so character classes
are Unicode-aware; each class is given as a predicate (`Re.cls`).

`$` without the `m` flag matches at the end of the subject or before a newline
that is the last character (PCRE2 `DOLLAR_ENDONLY` is not set).
-/

namespace JuliaLean.VersionNumbers

/-- Captures of a match: group number and captured substring, latest first. -/
abbrev Caps := List (Nat × List Char)

/-- Regular expressions: a character class, the empty pattern, concatenation,
ordered alternation, greedy `*`, a numbered capturing group and `$`. -/
inductive Re where
  | cls (p : Char → Bool)
  | eps
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  | group (i : Nat) (a : Re)
  | eol

namespace Re

/-- Greedy `a?`. -/
def opt (a : Re) : Re := alt a eps

/-- Greedy `a+`. -/
def plus (a : Re) : Re := seq a (star a)

/-- A single literal character. -/
def chr (c : Char) : Re := cls (· == c)

/-- Concatenation of a list of patterns. -/
def seqs : List Re → Re
  | [] => eps
  | [a] => a
  | a :: as => seq a (seqs as)

end Re

/-- Continuation: the rest of the subject and the captures so far. -/
abbrev Kont := List Char → Caps → Option Caps

/-- One level of the matcher. `rec` matches a further iteration of a `*`; an
iteration that consumes nothing ends the loop (PCRE2 breaks a loop on an empty
iteration), so every call of `rec` consumes at least one character. -/
def step (rec : Re → List Char → Caps → Kont → Option Caps) :
    Re → List Char → Caps → Kont → Option Caps
  | .cls p, s, c, k =>
    match s with
    | x :: t => if p x then k t c else none
    | [] => none
  | .eps, s, c, k => k s c
  | .seq a b, s, c, k => step rec a s c (fun s' c' => step rec b s' c' k)
  | .alt a b, s, c, k =>
    match step rec a s c k with
    | some r => some r
    | none => step rec b s c k
  | .star a, s, c, k =>
    match step rec a s c (fun s' c' => if s'.length < s.length then rec (.star a) s' c' k else none) with
    | some r => some r
    | none => k s c
  | .group i a, s, c, k => step rec a s c (fun s' c' => k s' ((i, s.take (s.length - s'.length)) :: c'))
  | .eol, s, c, k => if s = [] ∨ s = ['\n'] then k s c else none

/-- The matcher with `n` levels of loop iteration. Each level consumes a
character, so `n = length + 1` levels never run out on a subject of that length. -/
def matchFuel : Nat → Re → List Char → Caps → Kont → Option Caps
  | 0 => fun _ _ _ _ => none
  | n + 1 => step (matchFuel n)

/-- `match(r, s)` for a pattern starting with `^` (no multiline flag): an
anchored match at the start of `s`; the captures of the first match, or
`none` (`nothing`). -/
def matchRe (r : Re) (s : List Char) : Option Caps :=
  matchFuel (s.length + 1) r s [] (fun _ c => some c)

/-- `occursin(r, s)` for a pattern starting with `^`. -/
def occursRe (r : Re) (s : List Char) : Bool := (matchRe r s).isSome

/-- `m.captures[i]`: the latest capture of group `i`, `nothing` if unset. -/
def capture (c : Caps) (i : Nat) : Option (List Char) :=
  (c.find? (·.1 == i)).map (·.2)

end JuliaLean.VersionNumbers


/-!
# `VersionNumber` (`base/version.jl`, master `bbfa0ce4150`)

A `String` is a list of characters; `cmp` on `String`s is lexicographic on
code points, which for valid UTF-8 is the byte order Julia's `memcmp`
comparison uses. `VInt = UInt32` components are `JInt .u32`, numeric
identifiers `JInt .u64`.
-/

namespace JuliaLean.VersionNumbers

open JuliaLean

deriving instance DecidableEq for Except

/-- An element of `VerTuple = Tuple{Vararg{Union{UInt64,String}}}`, `base/version.jl:5`. -/
inductive Ident where
  | num (n : JInt .u64)
  | str (s : List Char)
  deriving DecidableEq

/-- `struct VersionNumber`, `base/version.jl:49-54`. -/
structure VersionNumber where
  major : JInt .u32
  minor : JInt .u32
  patch : JInt .u32
  pre : List Ident
  build : List Ident
  deriving DecidableEq

/-! ## Character classes (`UTF | UCP`, caseless where the pattern has `i`) -/

/-- Maximal runs of code points matched by `\d` with `UCP` (Unicode `Nd`), as
reported by `r"^\d$"` on the nightly build. -/
def ndRuns : List (Nat × Nat) := [(48, 57), (1632, 1641), (1776, 1785), (1984, 1993), (2406, 2415), (2534, 2543), (2662,
  2671), (2790, 2799), (2918, 2927), (3046, 3055), (3174, 3183), (3302, 3311), (3430, 3439),
  (3558, 3567), (3664, 3673), (3792, 3801), (3872, 3881), (4160, 4169), (4240, 4249), (6112,
  6121), (6160, 6169), (6470, 6479), (6608, 6617), (6784, 6793), (6800, 6809), (6992, 7001),
  (7088, 7097), (7232, 7241), (7248, 7257), (42528, 42537), (43216, 43225), (43264, 43273),
  (43472, 43481), (43504, 43513), (43600, 43609), (44016, 44025), (65296, 65305), (66720,
  66729), (68912, 68921), (68928, 68937), (69734, 69743), (69872, 69881), (69942, 69951),
  (70096, 70105), (70384, 70393), (70736, 70745), (70864, 70873), (71248, 71257), (71360,
  71369), (71376, 71395), (71472, 71481), (71904, 71913), (72016, 72025), (72688, 72697),
  (72784, 72793), (73040, 73049), (73120, 73129), (73184, 73193), (73552, 73561), (90416,
  90425), (92768, 92777), (92864, 92873), (93008, 93017), (93552, 93561), (118000, 118009),
  (120782, 120831), (123200, 123209), (123632, 123641), (124144, 124153), (124401, 124410),
  (125264, 125273), (130032, 130041)]

/-- `\d` under `UCP`. -/
def isUcpDigit (c : Char) : Bool := ndRuns.any (fun r => r.1 ≤ c.val.toNat ∧ c.val.toNat ≤ r.2)

def isAsciiDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

def isAsciiLetter (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')

/-- Caseless `[a-z]`: ASCII letters, U+017F (long s) and U+212A (Kelvin sign),
whose case folds are `s` and `k`. -/
def isLetterCI (c : Char) : Bool := isAsciiLetter c || c.val == 0x17F || c.val == 0x212A

/-- Caseless `[0-9a-z-]`. -/
def isAlnumHyCI (c : Char) : Bool := isAsciiDigit c || isLetterCI c || c == '-'

/-- Caseless `[a-z-]`. -/
def isLetterHyCI (c : Char) : Bool := isLetterCI c || c == '-'

/-! ## Patterns -/

open Re in
/-- `r"^(?:|[0-9a-z-]*[a-z-][0-9a-z-]*)$"i`, `base/version.jl:65,75`. -/
def identRe : Re :=
  seqs [alt eps (seqs [star (cls isAlnumHyCI), cls isLetterHyCI, star (cls isAlnumHyCI)]), eol]

open Re in
/-- `VERSION_REGEX`, `base/version.jl:115-125`, flags `ix`. Groups: 1 major,
2 minor, 3 patch, 4 bare `-`, 5 pre-release, 6 bare `+`, 7 build. -/
def versionRe : Re :=
  let an := cls isAlnumHyCI
  seqs [
    opt (cls (fun c => c == 'v' || c == 'V')),
    group 1 (plus (cls isUcpDigit)),
    opt (seq (chr '.') (group 2 (plus (cls isUcpDigit)))),
    opt (seq (chr '.') (group 3 (plus (cls isUcpDigit)))),
    alt (group 4 (chr '-'))
      (seq
        (opt (group 5 (alt
          (seqs [cls isLetterCI, star an, star (seq (chr '.') (plus an))])
          (seqs [chr '-', star (seq (plus an) (chr '.')), plus an]))))
        (alt (group 6 (chr '+'))
          (opt (seq (chr '+') (group 7 (seq (star (seq (plus an) (chr '.'))) (plus an))))))),
    eol]

open Re in
/-- `r"^\d+$"`, `base/version.jl:129`. -/
def digitsRe : Re := seqs [plus (cls isUcpDigit), eol]

/-! ## Integer parsing -/

def digitsValue (s : List Char) : Nat :=
  s.foldl (fun n c => 10 * n + (c.val.toNat - '0'.val.toNat)) 0

/-- `parse(T, s)` for unsigned `T` and a string of `\d` characters,
`base/parse.jl:127-171` and `base/parsers/ints.jl:86-157`: the leading ASCII
digits overflowing `T` is an `OverflowError`; otherwise any other character
(a non-ASCII digit) is an `ArgumentError`. -/
def parseUnsigned (t : IntTy) (s : List Char) : Jl (JInt t) :=
  let pre := s.takeWhile isAsciiDigit
  if s.isEmpty then .error (.argumentError "input string is empty or only contains whitespace")
  else if (pre ≠ [] ∧ (digitsValue pre : Int) > t.max) then .error (.overflowError "overflow parsing")
  else if pre.length < s.length then .error (.argumentError "invalid base 10 digit")
  else JInt.convert (t.name) t (digitsValue pre)

/-! ## Construction -/

/-- The `for ident in pre` loop of the inner constructor, `base/version.jl:61-70`. -/
def checkPre (pre bld : List Ident) : List Ident → Jl Unit
  | [] => pure ()
  | .num n :: rest =>
    if n.val < 0 then throw (.argumentError "invalid negative pre-release identifier")
    else checkPre pre bld rest
  | .str s :: rest =>
    if !occursRe identRe s || (s.isEmpty && !(pre.length == 1 && bld.isEmpty)) then
      throw (.argumentError "invalid pre-release identifier")
    else checkPre pre bld rest

/-- The `for ident in bld` loop of the inner constructor, `base/version.jl:71-80`. -/
def checkBuild (bld : List Ident) : List Ident → Jl Unit
  | [] => pure ()
  | .num n :: rest =>
    if n.val < 0 then throw (.argumentError "invalid negative build identifier")
    else checkBuild bld rest
  | .str s :: rest =>
    if !occursRe identRe s || (s.isEmpty && bld.length != 1) then
      throw (.argumentError "invalid build identifier")
    else checkBuild bld rest

/-- The inner constructor, `base/version.jl:56-82`. -/
def newVersion (major minor patch : JInt .u32) (pre bld : List Ident) : Jl VersionNumber := do
  if major.val < 0 then throw (.argumentError "invalid negative major version")
  if minor.val < 0 then throw (.argumentError "invalid negative minor version")
  if patch.val < 0 then throw (.argumentError "invalid negative patch version")
  checkPre pre bld pre
  checkBuild bld bld
  return ⟨major, minor, patch, pre, bld⟩

/-- An argument of the outer constructor: an `Int` or an `AbstractString`. -/
inductive IdentArg where
  | int (x : JInt .i64)
  | str (s : List Char)

/-- `x isa Integer ? UInt64(x) : String(x)`, `base/version.jl:88-89`. -/
def convIdent : IdentArg → Jl Ident
  | .int x => do return .num (← JInt.convert (IntTy.u64.name) .u64 x.val)
  | .str s => return .str s

/-- `VersionNumber(major::Integer, minor, patch, pre, bld)` for `Int` components,
`base/version.jl:84-89`. -/
def versionNumber (major minor patch : JInt .i64) (pre bld : List IdentArg := []) : Jl VersionNumber := do
  let ma ← JInt.convert (IntTy.u32.name) .u32 major.val
  let mi ← JInt.convert (IntTy.u32.name) .u32 minor.val
  let pa ← JInt.convert (IntTy.u32.name) .u32 patch.val
  let p ← pre.mapM convIdent
  let b ← bld.mapM convIdent
  newVersion ma mi pa p b

/-- `VersionNumber(major, minor, patch, pre, bld)` with `UInt32` components and
already converted identifiers (`VInt(x)` and `UInt64(x)`/`String(x)` are the
identity), `base/version.jl:84-89`. -/
def versionOf (major minor patch : JInt .u32) (pre bld : List Ident := []) : Jl VersionNumber :=
  newVersion major minor patch pre bld

/-- `typemax(VInt)`. -/
def vmax : JInt .u32 := JInt.typemax .u32

def u32 (n : Int) : JInt .u32 := JInt.wrap .u32 n

/-- `typemax(VersionNumber)`, `base/version.jl:173-176`. -/
def typemaxV : VersionNumber := ⟨vmax, vmax, vmax, [], [.str []]⟩

/-- `typemin(VersionNumber) = v"0-"`, `base/version.jl:178`. -/
def typeminV : VersionNumber := ⟨u32 0, u32 0, u32 0, [.str []], []⟩

/-! ## Comparison -/

/-- `cmp(a::String, b::String)`. -/
def cmpStr : List Char → List Char → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a.val < b.val then -1 else if b.val < a.val then 1 else cmpStr as bs

def cmpInt (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

/-- `ident_cmp` on identifiers, `base/version.jl:180-183`. -/
def identCmp : Ident → Ident → Int
  | .num a, .num b => cmpInt a.val b.val
  | .num _, .str b => if b.isEmpty then 1 else -1
  | .str a, .num _ => if a.isEmpty then -1 else 1
  | .str a, .str b => cmpStr a b

/-- The zip loop of `ident_cmp(A::VerTuple, B::VerTuple)`, `base/version.jl:186-189`. -/
def zipCmp : List Ident → List Ident → Int
  | a :: as, b :: bs => let c := identCmp a b; if c != 0 then c else zipCmp as bs
  | _, _ => 0

/-- `ident_cmp(A::VerTuple, B::VerTuple)`, `base/version.jl:185-192`. -/
def tupleCmp (A B : List Ident) : Int :=
  let c := zipCmp A B
  if c != 0 then c
  else if A.length < B.length then -1 else if B.length < A.length then 1 else 0

/-- `==(a::VersionNumber, b::VersionNumber)`, `base/version.jl:194-201`. -/
def veq (a b : VersionNumber) : Bool :=
  if a.major != b.major then false
  else if a.minor != b.minor then false
  else if a.patch != b.patch then false
  else if tupleCmp a.pre b.pre != 0 then false
  else if tupleCmp a.build b.build != 0 then false
  else true

/-- `issupbuild`, `base/version.jl:203`. -/
def issupbuild (v : VersionNumber) : Bool := v.build == [.str []]

/-- `isless(a::VersionNumber, b::VersionNumber)` (and `<`), `base/version.jl:205-222`. -/
def vless (a b : VersionNumber) : Bool :=
  if a.major.val < b.major.val then true
  else if a.major.val > b.major.val then false
  else if a.minor.val < b.minor.val then true
  else if a.minor.val > b.minor.val then false
  else if a.patch.val < b.patch.val then true
  else if a.patch.val > b.patch.val then false
  else if !a.pre.isEmpty && b.pre.isEmpty then true
  else if a.pre.isEmpty && !b.pre.isEmpty then false
  else
    let c := tupleCmp a.pre b.pre
    if c < 0 then true
    else if c > 0 then false
    else if !issupbuild a && issupbuild b then true
    else if issupbuild a && !issupbuild b then false
    else tupleCmp a.build b.build < 0

/-- `hash(v::VersionNumber, h::UInt)`, `base/version.jl:224-231`, for any
`hash` methods on `UInt32` (`hu`) and on `VerTuple` (`ht`). -/
def vhash (hu : JInt .u32 → UInt64 → UInt64) (ht : List Ident → UInt64 → UInt64)
    (v : VersionNumber) (h : UInt64) : UInt64 :=
  let h := h ^^^ 0x8ff4ffdb75f9fede
  let h := hu v.major h
  let h := hu v.minor h
  let h := hu v.patch h
  let h := ht v.pre (~~~h)
  ht v.build (~~~h)

/-! ## Bounds and neighbours -/

/-- `lowerbound`, `base/version.jl:233`. -/
def lowerbound (v : VersionNumber) : Jl VersionNumber := versionOf v.major v.minor v.patch [.str []] []

/-- `upperbound`, `base/version.jl:234`. -/
def upperbound (v : VersionNumber) : Jl VersionNumber := versionOf v.major v.minor v.patch [] [.str []]

/-- `thispatch`, `base/version.jl:236`. -/
def thispatch (v : VersionNumber) : Jl VersionNumber := versionOf v.major v.minor v.patch

/-- `thisminor`, `base/version.jl:237`. -/
def thisminor (v : VersionNumber) : Jl VersionNumber := versionOf v.major v.minor (u32 0)

/-- `thismajor`, `base/version.jl:238`. -/
def thismajor (v : VersionNumber) : Jl VersionNumber := versionOf v.major (u32 0) (u32 0)

/-- `x + 1` for `x::UInt32`: promoted to `Int`, which cannot overflow, then
`VInt(x + 1)` in the outer constructor. -/
def succU32 (x : JInt .u32) : Jl (JInt .u32) := JInt.convert (IntTy.u32.name) .u32 (x.val + 1)

/-- `nextpatch`, `base/version.jl:240`. -/
def nextpatch (v : VersionNumber) : Jl VersionNumber := do
  let t ← thispatch v
  if vless v t then return t
  versionOf v.major v.minor (← succU32 v.patch)

/-- `nextminor`, `base/version.jl:241`. -/
def nextminor (v : VersionNumber) : Jl VersionNumber := do
  let t ← thisminor v
  if vless v t then return t
  versionOf v.major (← succU32 v.minor) (u32 0)

/-- `nextmajor`, `base/version.jl:242`. -/
def nextmajor (v : VersionNumber) : Jl VersionNumber := do
  let t ← thismajor v
  if vless v t then return t
  versionOf (← succU32 v.major) (u32 0) (u32 0)

/-! ## Printing and parsing -/

/-- Decimal digits of `n` (`print(io, ::Unsigned)`). -/
def showNat (n : Nat) : List Char := Nat.toDigits 10 n

def showIdent : Ident → List Char
  | .num n => showNat n.val.toNat
  | .str s => s

/-- `join(io, idents, '.')`. -/
def joinIdents : List Ident → List Char
  | [] => []
  | [a] => showIdent a
  | a :: as => showIdent a ++ ['.'] ++ joinIdents as

/-- `print(io, v::VersionNumber)` (`string(v)`), `base/version.jl:94-110`. -/
def vprint (v : VersionNumber) : List Char :=
  if veq v typemaxV then ['∞']
  else
    showNat v.major.val.toNat ++ ['.'] ++ showNat v.minor.val.toNat ++ ['.'] ++ showNat v.patch.val.toNat
      ++ (if v.pre.isEmpty then [] else '-' :: joinIdents v.pre)
      ++ (if v.build.isEmpty then [] else '+' :: joinIdents v.build)

/-- `eachsplit(s, '.')`. -/
def splitDots : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitDots cs with
    | [] => [[c]]
    | w :: ws => if c == '.' then [] :: w :: ws else (c :: w) :: ws

/-- `split_idents`, `base/version.jl:127-131`. -/
def splitIdents (s : List Char) : Jl (List Ident) :=
  (splitDots s).mapM fun ident =>
    if occursRe digitsRe ident then do return .num (← parseUnsigned .u64 ident)
    else return .str ident

/-- `tryparse(::Type{VersionNumber}, v)`, `base/version.jl:133-147`. -/
def tryparse (v : List Char) : Jl (Option VersionNumber) := do
  if v == ['∞'] then return some typemaxV
  match matchRe versionRe v with
  | none => return none
  | some m =>
    let major ← parseUnsigned .u32 ((capture m 1).getD [])
    let minor ← match capture m 2 with
      | some s => parseUnsigned .u32 s
      | none => pure (u32 0)
    let patch ← match capture m 3 with
      | some s => parseUnsigned .u32 s
      | none => pure (u32 0)
    let prerl := match capture m 5 with
      | some ('-' :: rest) => some rest
      | p => p
    let pre ← match prerl with
      | some p => splitIdents p
      | none => pure (if (capture m 4).isSome then [.str []] else [])
    let build ← match capture m 7 with
      | some b => splitIdents b
      | none => pure (if (capture m 6).isSome then [.str []] else [])
    some <$> newVersion major minor patch pre build

/-- `parse(::Type{VersionNumber}, v)`, `base/version.jl:149-153`. -/
def parse (v : List Char) : Jl VersionNumber := do
  match ← tryparse v with
  | some x => return x
  | none => throw (.argumentError "invalid version string")

end JuliaLean.VersionNumbers


/-!
# `VersionBound` and `VersionRange` (`base/version.jl:299-504`, master `bbfa0ce4150`)

Strings are UTF-8 code units (`JuliaLean.ParsePrint.IntParse.Bytes`). Integer
parsing is the shared model of `parse(Int64, s)`. `strip(s)` removes leading and
trailing `isspace` characters (`base/strings/util.jl`); it is the span between
`skipspace` and `skipspace_back` of `base/parse.jl`, which use the same
`isspace`. An `ErrorException` from `error(...)` is represented by
`argumentError` with the message of the `error` call.
-/

namespace JuliaLean.VersionNumbers

open JuliaLean JuliaLean.ParsePrint.IntParse

/-- `struct VersionBound`, `base/version.jl:299-310`: `t` and `n`. -/
structure VersionBound where
  t : JInt .u32 × JInt .u32 × JInt .u32
  n : Nat
  deriving DecidableEq

def VersionBound.get (b : VersionBound) : Nat → JInt .u32
  | 1 => b.t.1
  | 2 => b.t.2.1
  | _ => b.t.2.2

/-- The inner constructor `VersionBound(tin::NTuple{n, Integer})` for `Int64`
components, `base/version.jl:302-309`: `new((tin[1], 0, 0), n)` etc. convert each
component to `UInt32`. -/
def mkBound (tin : List (JInt .i64)) : Jl VersionBound := do
  let z := u32 0
  match tin with
  | [] => return ⟨(z, z, z), 0⟩
  | [a] => return ⟨(← JInt.convert (IntTy.u32.name) .u32 a.val, z, z), 1⟩
  | [a, b] => return ⟨(← JInt.convert (IntTy.u32.name) .u32 a.val, ← JInt.convert (IntTy.u32.name) .u32 b.val, z), 2⟩
  | [a, b, c] => return ⟨(← JInt.convert (IntTy.u32.name) .u32 a.val, ← JInt.convert (IntTy.u32.name) .u32 b.val, ← JInt.convert (IntTy.u32.name) .u32 c.val), 3⟩
  | _ => throw (.argumentError "VersionBound: you can only specify major, minor and patch versions")

/-- `VersionBound()`. -/
def boundStar : VersionBound := ⟨(u32 0, u32 0, u32 0), 0⟩

/-- `v ≲ b`, `base/version.jl:316-321`. -/
def leBound (v : VersionNumber) (b : VersionBound) : Bool :=
  if b.n == 0 then true
  else if b.n == 1 then v.major.val ≤ (b.get 1).val
  else if b.n == 2 then
    v.major.val < (b.get 1).val ∨ (v.major.val = (b.get 1).val ∧ v.minor.val ≤ (b.get 2).val)
  else
    v.major.val < (b.get 1).val ∨ (v.major.val = (b.get 1).val ∧ (v.minor.val < (b.get 2).val ∨
      (v.minor.val = (b.get 2).val ∧ v.patch.val ≤ (b.get 3).val)))

/-- `b ≲ v`, `base/version.jl:323-328`. -/
def geBound (b : VersionBound) (v : VersionNumber) : Bool :=
  if b.n == 0 then true
  else if b.n == 1 then v.major.val ≥ (b.get 1).val
  else if b.n == 2 then
    v.major.val > (b.get 1).val ∨ (v.major.val = (b.get 1).val ∧ v.minor.val ≥ (b.get 2).val)
  else
    v.major.val > (b.get 1).val ∨ (v.major.val = (b.get 1).val ∧ (v.minor.val > (b.get 2).val ∨
      (v.minor.val = (b.get 2).val ∧ v.patch.val ≥ (b.get 3).val)))

def dotByte : Byte := byte 46

/-- `strip(s)`. -/
def stripBytes (s : Bytes) : Bytes :=
  let i := skipspace s 1 s.length
  let j := skipspaceBack s i s.length
  (s.drop (i - 1).toNat).take (j - i + 1).toNat

/-- `findnext('.', s, a)` as the remaining pieces: `s` split at the first dot. -/
def splitDot (s : Bytes) : Bytes × Option Bytes :=
  match s.span (· != dotByte) with
  | (a, _ :: rest) => (a, some rest)
  | (a, []) => (a, none)

/-- `VersionBound(s::AbstractString)`, `base/version.jl:381-405`. -/
def parseBound (s : Bytes) : Jl VersionBound := do
  let s := stripBytes s
  if s == [byte 42] then return boundStar
  let s ← match s with
    | [] => throw .boundsError
    | c :: rest => pure (if c == byte 118 then rest else c :: rest)
  let (a, r1) := splitDot s
  let i ← JuliaLean.ParsePrint.IntParse.parse .i64 a
  match r1 with
  | none => mkBound [i]
  | some s1 =>
    let (b, r2) := splitDot s1
    let j ← JuliaLean.ParsePrint.IntParse.parse .i64 b
    match r2 with
    | none => mkBound [i, j]
    | some s2 =>
      let (c, r3) := splitDot s2
      let k ← JuliaLean.ParsePrint.IntParse.parse .i64 c
      match r3 with
      | none => mkBound [i, j, k]
      | some _ => throw (.argumentError "invalid VersionBound string")

/-- `struct VersionRange` and its inner constructor, `base/version.jl:410-421`. -/
structure VersionRange where
  lower : VersionBound
  upper : VersionBound
  deriving DecidableEq

def mkRange (lo hi : VersionBound) : VersionRange :=
  if lo.t = hi.t then ⟨hi, hi⟩ else ⟨lo, hi⟩

/-- `split(s, "-")` (`keepempty = true`). -/
def splitHyphen : Bytes → List Bytes
  | [] => [[]]
  | c :: cs =>
    match splitHyphen cs with
    | [] => [[c]]
    | w :: ws => if c == byte 45 then [] :: w :: ws else (c :: w) :: ws

/-- `VersionRange(s::AbstractString)`, `base/version.jl:428-438`; `VersionRange_1`
is `VersionRange(VersionBound("1"), VersionBound("1"))`. -/
def parseRange (s : Bytes) : Jl VersionRange := do
  let p := splitHyphen s
  if p.length != 1 && p.length != 2 then throw (.argumentError "invalid version range")
  let lower ← parseBound (p.headD [])
  let upper ← if p.length == 1 then pure lower else parseBound (p.getD 1 [])
  return mkRange lower upper

/-- Decimal digits of a `UInt32`, as bytes. -/
def showU32 (x : JInt .u32) : Bytes := (showNat x.val.toNat).map (fun c => byte c.toNat)

/-- `join(io, xs, '.')`. -/
def joinDots : List (JInt .u32) → Bytes
  | [] => []
  | [a] => showU32 a
  | a :: as => showU32 a ++ [dotByte] ++ joinDots as

def VersionBound.all (b : VersionBound) : List (JInt .u32) := [b.t.1, b.t.2.1, b.t.2.2]

def ascii (s : String) : Bytes := s.toList.map (fun c => byte c.toNat)

/-- `print(io, r::VersionRange)` (`string(r)`), `base/version.jl:448-465`. -/
def printRange (r : VersionRange) : Bytes :=
  let m := r.lower.n
  let n := r.upper.n
  if m == 0 && n == 0 then ascii "*"
  else if m == 0 then ascii "0 -" ++ joinDots r.upper.all
  else if n == 0 then joinDots r.lower.all ++ ascii " - *"
  else
    joinDots (r.lower.all.take m) ++
      (if r.lower != r.upper then ascii " - " ++ joinDots (r.upper.all.take n) else [])

/-- `in(v::VersionNumber, r::VersionRange)`, `base/version.jl:468`. -/
def inRange (v : VersionNumber) (r : VersionRange) : Bool := geBound r.lower v && leBound v r.upper

end JuliaLean.VersionNumbers


/-!
# Source-mirrored model of `base/version.jl`

Version components and numeric identifiers retain their Julia `UInt32` and `UInt64` types.
Abstract integer and string arguments carry their source conversions; regular-expression matching,
string splitting, parsing, and display are typed interfaces to methods loaded elsewhere in Base.
-/

namespace JuliaLean.base.version

open JuliaLean

abbrev VInt := JInt .u32

inductive VersionIdentifier where
  | integer (value : JInt .u64)
  | text (value : String)
  deriving DecidableEq

abbrev VerTuple := List VersionIdentifier

/-- The `VersionNumber` fields are `VInt` and `VerTuple`. -/
/-
Julia source: base/version.jl:49-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VersionNumber
    major::VInt
    minor::VInt
    patch::VInt
    prerelease::VerTuple
    build::VerTuple

```
-/

structure VersionNumber where
  major : VInt
  minor : VInt
  patch : VInt
  prerelease : VerTuple
  build : VerTuple
  deriving DecidableEq

structure IntegerValue where
  carrier : Type
  value : carrier
  toInt : carrier → Int

structure StringValue where
  carrier : Type
  value : carrier
  toString : carrier → String

inductive VersionArgument where
  | integer (value : IntegerValue)
  | string (value : StringValue)

structure VersionCaptures where
  major : String
  minor : Option String
  patch : Option String
  minus : Option String
  prerelease : Option String
  plus : Option String
  build : Option String

/-
Julia source: base/version.jl:115-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const VERSION_REGEX = r"^
    v?                                      # prefix        (optional)
    (\d+)                                   # major         (required)
    (?:\.(\d+))?                            # minor         (optional)
    (?:\.(\d+))?                            # patch         (optional)
    (?:(-)|                                 # pre-release   (optional)
    ([a-z][0-9a-z-]*(?:\.[0-9a-z-]+)*|-(?:[0-9a-z-]+\.)*[0-9a-z-]+)?
    (?:(\+)|
    (?:\+((?:[0-9a-z-]+\.)*[0-9a-z-]+))?    # build         (optional)
    ))
$"ix
```
-/

structure VersionRegexOps (Re : Type) where
  identifierRegex : Re
  digitsRegex : Re
  versionRegex : Re
  occursin : Re → String → Jl Bool
  matchVersion : Re → String → Jl (Option VersionCaptures)
  split : String → Char → List String
  parseUInt32 : String → Jl (JInt .u32)
  parseUInt64 : String → Jl (JInt .u64)
  showUInt32 : JInt .u32 → String
  showUInt64 : JInt .u64 → String
  reprString : String → String
  isEmptyIdentifier : VersionIdentifier → Bool
  showString : StringValue → String
  isInfinity : StringValue → Bool

structure RefValue (α : Type) where
  value : α

def intValue (n : Int) : IntegerValue := ⟨Int, n, id⟩

def stringValue (s : String) : StringValue := ⟨String, s, id⟩

def compareInt (a b : Int) : Int := if a < b then -1 else if a > b then 1 else 0

def compareStringChars : List Char → List Char → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs =>
      if a.val < b.val then -1 else if a.val > b.val then 1 else compareStringChars as bs

def compareString (a b : String) : Int := compareStringChars a.toList b.toList

/- Source: Julia constructors and their typed integer conversions. -/

/-
Julia source: base/version.jl:56-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function VersionNumber(major::VInt, minor::VInt, patch::VInt,
                           @nospecialize(pre::VerTuple), @nospecialize(bld::VerTuple))
        major >= 0 || throw(ArgumentError("invalid negative major version: $major"))
        minor >= 0 || throw(ArgumentError("invalid negative minor version: $minor"))
        patch >= 0 || throw(ArgumentError("invalid negative patch version: $patch"))
        for ident in pre
            if ident isa Integer
                ident >= 0 || throw(ArgumentError("invalid negative pre-release identifier: $ident"))
            else
                if !occursin(r"^(?:|[0-9a-z-]*[a-z-][0-9a-z-]*)$"i, ident) ||
                    isempty(ident) && !(length(pre)==1 && isempty(bld))
                    throw(ArgumentError("invalid pre-release identifier: $(repr(ident))"))
                end
            end
        end
        for ident in bld
            if ident isa Integer
                ident >= 0 || throw(ArgumentError("invalid negative build identifier: $ident"))
            else
                if !occursin(r"^(?:|[0-9a-z-]*[a-z-][0-9a-z-]*)$"i, ident) ||
                    isempty(ident) && length(bld)!=1
                    throw(ArgumentError("invalid build identifier: $(repr(ident))"))
                end
            end
        end
        new(major, minor, patch, pre, bld)
    end
end
```
-/

/-- The inner `VersionNumber` constructor validates components and identifiers. -/
def newVersionNumber {Re : Type} (ops : VersionRegexOps Re)
    (major minor patch : VInt) (pre : VerTuple := []) (build : VerTuple := []) : Jl VersionNumber := do
  if major.val < 0 then throw (.argumentError s!"invalid negative major version: {major.val}")
  if minor.val < 0 then throw (.argumentError s!"invalid negative minor version: {minor.val}")
  if patch.val < 0 then throw (.argumentError s!"invalid negative patch version: {patch.val}")
  checkPre ops pre build pre
  checkBuild ops build build
  return ⟨major, minor, patch, pre, build⟩
where
  checkPre (ops : VersionRegexOps Re) (pre build : VerTuple) : VerTuple → Jl Unit
    | [] => pure ()
    | .integer n :: rest =>
        if n.val < 0 then throw (.argumentError s!"invalid negative pre-release identifier: {n.val}")
        else checkPre ops pre build rest
    | .text s :: rest => do
        let matched ← ops.occursin ops.identifierRegex s
        if !matched || (s.isEmpty && !(pre.length == 1 && build.isEmpty)) then
          throw (.argumentError ("invalid pre-release identifier: " ++ ops.reprString s))
        else checkPre ops pre build rest
  checkBuild (ops : VersionRegexOps Re) (build : VerTuple) : VerTuple → Jl Unit
    | [] => pure ()
    | .integer n :: rest =>
        if n.val < 0 then throw (.argumentError s!"invalid negative build identifier: {n.val}")
        else checkBuild ops build rest
    | .text s :: rest => do
        let matched ← ops.occursin ops.identifierRegex s
        if !matched || (s.isEmpty && build.length != 1) then
          throw (.argumentError ("invalid build identifier: " ++ ops.reprString s))
        else checkBuild ops build rest

/-- `UInt64(x)` or `String(x)` for one outer-constructor identifier. -/
def convertVersionArgument (arg : VersionArgument) : Jl VersionIdentifier :=
  match arg with
  | .integer i => do
      return .integer (← JInt.convert (IntTy.u64.name) .u64 (i.toInt i.value))
  | .string s => pure (.text (s.toString s.value))

/-
Julia source: base/version.jl:84-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionNumber(major::Integer, minor::Integer = 0, patch::Integer = 0,
        pre::Tuple{Vararg{Union{Integer,AbstractString}}} = (),
        bld::Tuple{Vararg{Union{Integer,AbstractString}}} = ()) =
    VersionNumber(VInt(major), VInt(minor), VInt(patch),
        map(x->x isa Integer ? UInt64(x) : String(x), pre),
        map(x->x isa Integer ? UInt64(x) : String(x), bld))
```
-/

/-- The generic `VersionNumber(major, minor, patch, pre, bld)` constructor. -/
def versionNumber {Re : Type} (ops : VersionRegexOps Re) (major : IntegerValue)
    (minor : IntegerValue := intValue 0) (patch : IntegerValue := intValue 0)
    (pre build : List VersionArgument := []) : Jl VersionNumber := do
  let major ← JInt.convert (IntTy.u32.name) .u32 (major.toInt major.value)
  let minor ← JInt.convert (IntTy.u32.name) .u32 (minor.toInt minor.value)
  let patch ← JInt.convert (IntTy.u32.name) .u32 (patch.toInt patch.value)
  let pre ← pre.mapM convertVersionArgument
  let build ← build.mapM convertVersionArgument
  newVersionNumber ops major minor patch pre build

/-
Julia source: base/version.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionNumber(v::Tuple) = VersionNumber(v...)
```
-/

structure TupleArguments where
  carrier : Type
  value : carrier
  splatConstructor : carrier → Jl VersionNumber

/-- `VersionNumber(v::Tuple)`, with tuple splatting delegated to Julia dispatch. -/
def versionNumberTuple (arguments : TupleArguments) : Jl VersionNumber :=
  arguments.splatConstructor arguments.value

/-
Julia source: base/version.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionNumber(v::VersionNumber) = v
```
-/

/-- `VersionNumber(v::VersionNumber)`. -/
def versionNumberIdentity (v : VersionNumber) : VersionNumber := v

/-
Julia source: base/version.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ident_cmp(a::Integer, b::Integer) = cmp(a, b)
```
-/

/-- `ident_cmp(a::Integer,b::Integer)`. -/
def identCmpIntegerInteger (a b : IntegerValue) : Int :=
  compareInt (a.toInt a.value) (b.toInt b.value)

/-
Julia source: base/version.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ident_cmp(a::Integer, b::String ) = isempty(b) ? +1 : -1
```
-/

/-- `ident_cmp(a::Integer,b::String)`. -/
def identCmpIntegerString (_a : IntegerValue) (b : String) : Int :=
  if b.isEmpty then 1 else -1

/-
Julia source: base/version.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ident_cmp(a::String,  b::Integer) = isempty(a) ? -1 : +1
```
-/

/-- `ident_cmp(a::String,b::Integer)`. -/
def identCmpStringInteger (a : String) (_b : IntegerValue) : Int :=
  if a.isEmpty then -1 else 1

/-
Julia source: base/version.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ident_cmp(a::String,  b::String ) = cmp(a, b)
```
-/

/-- `ident_cmp(a::String,b::String)`. -/
def identCmpStringString (a b : String) : Int := compareString a b

def integerFromUInt64 (n : JInt .u64) : IntegerValue := ⟨JInt .u64, n, fun x => x.val⟩

def compareIdentifier : VersionIdentifier → VersionIdentifier → Int
  | .integer a, .integer b => identCmpIntegerInteger (integerFromUInt64 a) (integerFromUInt64 b)
  | .integer a, .text b => identCmpIntegerString (integerFromUInt64 a) b
  | .text a, .integer b => identCmpStringInteger a (integerFromUInt64 b)
  | .text a, .text b => identCmpStringString a b

def compareVerTuple : VerTuple → VerTuple → Int
  | a :: as, b :: bs =>
      let c := compareIdentifier a b
      if c != 0 then c else compareVerTuple as bs
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1

/-- The zipped `ident_cmp` loop and its length tie-break. -/
/-
Julia source: base/version.jl:185-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ident_cmp(@nospecialize(A::VerTuple), @nospecialize(B::VerTuple))
    for (a, b) in Iterators.Zip{Tuple{VerTuple,VerTuple}}((A, B))
        c = ident_cmp(a, b)
        (c != 0) && return c
    end
    length(A) < length(B) ? -1 :
    length(B) < length(A) ? +1 : 0
end
```
-/

def identCmpTuple (a b : VerTuple) : Int := compareVerTuple a b

/-
Julia source: base/version.jl:194-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::VersionNumber, b::VersionNumber)
    (a.major != b.major) && return false
    (a.minor != b.minor) && return false
    (a.patch != b.patch) && return false
    (ident_cmp(a.prerelease, b.prerelease) != 0) && return false
    (ident_cmp(a.build, b.build) != 0) && return false
    return true
end
```
-/

/-- `==(a::VersionNumber, b::VersionNumber)`. -/
def versionEqual (a b : VersionNumber) : Bool :=
  if a.major.val != b.major.val then false
  else if a.minor.val != b.minor.val then false
  else if a.patch.val != b.patch.val then false
  else if identCmpTuple a.prerelease b.prerelease != 0 then false
  else if identCmpTuple a.build b.build != 0 then false
  else true

/-
Julia source: base/version.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issupbuild(v::VersionNumber) = length(v.build)==1 && isempty(v.build[1])
```
-/

/-- `issupbuild(v)`. A numeric build identifier is nonempty. -/
def isSupplementaryBuild {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Bool :=
  match v.build with
  | [ident] => ops.isEmptyIdentifier ident
  | _ => false

/-
Julia source: base/version.jl:205-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless(a::VersionNumber, b::VersionNumber)
    (a.major < b.major) && return true
    (a.major > b.major) && return false
    (a.minor < b.minor) && return true
    (a.minor > b.minor) && return false
    (a.patch < b.patch) && return true
    (a.patch > b.patch) && return false
    (!isempty(a.prerelease) && isempty(b.prerelease)) && return true
    (isempty(a.prerelease) && !isempty(b.prerelease)) && return false
    c = ident_cmp(a.prerelease,b.prerelease)
    (c < 0) && return true
    (c > 0) && return false
    (!issupbuild(a) && issupbuild(b)) && return true
    (issupbuild(a) && !issupbuild(b)) && return false
    c = ident_cmp(a.build,b.build)
    (c < 0) && return true
    return false
end
```
-/

/-- `isless(a::VersionNumber, b::VersionNumber)`. -/
def versionLess {Re : Type} (ops : VersionRegexOps Re) (a b : VersionNumber) : Bool :=
  if a.major.val < b.major.val then true
  else if a.major.val > b.major.val then false
  else if a.minor.val < b.minor.val then true
  else if a.minor.val > b.minor.val then false
  else if a.patch.val < b.patch.val then true
  else if a.patch.val > b.patch.val then false
  else if !a.prerelease.isEmpty && b.prerelease.isEmpty then true
  else if a.prerelease.isEmpty && !b.prerelease.isEmpty then false
  else
    let c := identCmpTuple a.prerelease b.prerelease
    if c < 0 then true
    else if c > 0 then false
    else if !isSupplementaryBuild ops a && isSupplementaryBuild ops b then true
    else if isSupplementaryBuild ops a && !isSupplementaryBuild ops b then false
    else identCmpTuple a.build b.build < 0

/-
Julia source: base/version.jl:224-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(v::VersionNumber, h::UInt)
    h ⊻= 0x8ff4ffdb75f9fede % UInt
    h = hash(v.major, h)
    h = hash(v.minor, h)
    h = hash(v.patch, h)
    h = hash(v.prerelease, ~h)
    h = hash(v.build, ~h)
end
```
-/

/-- `hash(v::VersionNumber, h::UInt)` with the source's field-hash callees. -/
def hashVersionNumber (xor : JInt .u64 → JInt .u64 → JInt .u64)
    (bitNot : JInt .u64 → JInt .u64) (hashInteger : JInt .u32 → JInt .u64 → JInt .u64)
    (hashIdentifiers : VerTuple → JInt .u64 → JInt .u64)
    (v : VersionNumber) (seed : JInt .u64) : JInt .u64 := Id.run do
  let h := xor seed (JInt.lit .u64 0x8ff4ffdb75f9fede)
  let h := hashInteger v.major h
  let h := hashInteger v.minor h
  let h := hashInteger v.patch h
  let h := hashIdentifiers v.prerelease (bitNot h)
  return hashIdentifiers v.build (bitNot h)

/-
Julia source: base/version.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowerbound(v::VersionNumber) = VersionNumber(v.major, v.minor, v.patch, ("",), ())
```
-/

/-- `lowerbound(v)`. -/
def lowerbound {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber :=
  newVersionNumber ops v.major v.minor v.patch [.text ""] []

/-
Julia source: base/version.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
upperbound(v::VersionNumber) = VersionNumber(v.major, v.minor, v.patch, (), ("",))
```
-/

/-- `upperbound(v)`. -/
def upperbound {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber :=
  newVersionNumber ops v.major v.minor v.patch [] [.text ""]

/-
Julia source: base/version.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
thispatch(v::VersionNumber) = VersionNumber(v.major, v.minor, v.patch)
```
-/

/-- `thispatch(v)`. -/
def thispatch {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber :=
  newVersionNumber ops v.major v.minor v.patch

/-
Julia source: base/version.jl:237-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
thisminor(v::VersionNumber) = VersionNumber(v.major, v.minor, 0)
```
-/

/-- `thisminor(v)`. -/
def thisminor {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber :=
  newVersionNumber ops v.major (JInt.lit .u32 0) (JInt.lit .u32 0)

/-
Julia source: base/version.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
thismajor(v::VersionNumber) = VersionNumber(v.major, 0, 0)
```
-/

/-- `thismajor(v)`. -/
def thismajor {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber :=
  newVersionNumber ops v.major (JInt.lit .u32 0) (JInt.lit .u32 0)

/-
Julia source: base/version.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextpatch(v::VersionNumber) = v < thispatch(v) ? thispatch(v) : VersionNumber(v.major, v.minor, v.patch+1)
```
-/

/-- `nextpatch(v)`, preserving the checked `UInt32` conversion of `patch + 1`. -/
def nextpatch {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber := do
  let t ← thispatch ops v
  if versionLess ops v t then return t
  let patch ← JInt.convert (IntTy.u32.name) .u32 (v.patch.val + 1)
  newVersionNumber ops v.major v.minor patch

/-
Julia source: base/version.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextminor(v::VersionNumber) = v < thisminor(v) ? thisminor(v) : VersionNumber(v.major, v.minor+1, 0)
```
-/

/-- `nextminor(v)`, preserving the checked `UInt32` conversion of `minor + 1`. -/
def nextminor {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber := do
  let t ← thisminor ops v
  if versionLess ops v t then return t
  let minor ← JInt.convert (IntTy.u32.name) .u32 (v.minor.val + 1)
  newVersionNumber ops v.major minor (JInt.lit .u32 0)

/-
Julia source: base/version.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextmajor(v::VersionNumber) = v < thismajor(v) ? thismajor(v) : VersionNumber(v.major+1, 0, 0)
```
-/

/-- `nextmajor(v)`, preserving the checked `UInt32` conversion of `major + 1`. -/
def nextmajor {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : Jl VersionNumber := do
  let t ← thismajor ops v
  if versionLess ops v t then return t
  let major ← JInt.convert (IntTy.u32.name) .u32 (v.major.val + 1)
  newVersionNumber ops major (JInt.lit .u32 0) (JInt.lit .u32 0)

/- Source-mirrored printing and parsing methods. -/

def joinStrings : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ "." ++ joinStrings xs

def printIdentifier {Re : Type} (ops : VersionRegexOps Re) : VersionIdentifier → String
  | .integer n => ops.showUInt64 n
  | .text s => s

def printVersionNumber {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : String :=
  if versionEqual v (typemaxValue) then "∞"
  else
    ops.showUInt32 v.major ++ "." ++ ops.showUInt32 v.minor ++ "." ++ ops.showUInt32 v.patch ++
      (if v.prerelease.isEmpty then "" else "-" ++ joinStrings (v.prerelease.map (printIdentifier ops))) ++
      (if v.build.isEmpty then "" else "+" ++ joinStrings (v.build.map (printIdentifier ops)))
where
  typemaxValue : VersionNumber :=
    ⟨JInt.typemax .u32, JInt.typemax .u32, JInt.typemax .u32, [], [.text ""]⟩

/-
Julia source: base/version.jl:94-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print(io::IO, v::VersionNumber)
    v == typemax(VersionNumber) && return print(io, "∞")
    print(io, v.major)
    print(io, '.')
    print(io, v.minor)
    print(io, '.')
    print(io, v.patch)
    if !isempty(v.prerelease)
        print(io, '-')
        # inline join to make call resolvable for --trim
        @inline join(io, v.prerelease,'.')
    end
    if !isempty(v.build)
        print(io, '+')
        @inline join(io, v.build,'.')
    end
end
```
-/

/-- `print(io, v::VersionNumber)`, represented by the emitted string. -/
def printVersion {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : String :=
  printVersionNumber ops v

/-
Julia source: base/version.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, v::VersionNumber) = print(io, "v\"", v, "\"")
```
-/

/-- `show(io, v::VersionNumber)`. -/
def showVersion {Re : Type} (ops : VersionRegexOps Re) (v : VersionNumber) : String :=
  "v\"" ++ printVersionNumber ops v ++ "\""

/-
Julia source: base/version.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Broadcast.broadcastable(v::VersionNumber) = Ref(v)
```
-/

/-- `Broadcast.broadcastable(v::VersionNumber)`. -/
def broadcastableVersion (v : VersionNumber) : RefValue VersionNumber := ⟨v⟩

/-
Julia source: base/version.jl:127-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function split_idents(s::AbstractString)
    idents = eachsplit(s, '.')
    pidents = Union{UInt64,String}[occursin(r"^\d+$", ident) ? parse(UInt64, ident) : String(ident) for ident in idents]
    return tuple(pidents...)::VerTuple
end
```
-/

/-- `split_idents(s)`, with `eachsplit`, regex matching and integer parsing as callees. -/
def splitIdents {Re : Type} (ops : VersionRegexOps Re) (s : String) : Jl VerTuple := do
  let parts := ops.split s '.'
  parts.mapM fun ident => do
    if ← ops.occursin ops.digitsRegex ident then
      return .integer (← ops.parseUInt64 ident)
    else
      return .text ident

/-
Julia source: base/version.jl:133-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse(::Type{VersionNumber}, v::AbstractString)
    v == "∞" && return typemax(VersionNumber)
    m = match(VERSION_REGEX, String(v)::String)
    m === nothing && return nothing
    major, minor, patch, minus, prerl, plus, build = m.captures
    major = parse(VInt, major::AbstractString)
    minor = minor !== nothing ? parse(VInt, minor) : VInt(0)
    patch = patch !== nothing ? parse(VInt, patch) : VInt(0)
    if prerl !== nothing && !isempty(prerl) && prerl[1] == '-'
        prerl = prerl[2:end] # strip leading '-'
    end
    prerl = prerl !== nothing ? split_idents(prerl) : minus !== nothing ? ("",) : ()
    build = build !== nothing ? split_idents(build) : plus  !== nothing ? ("",) : ()
    return VersionNumber(major, minor, patch, prerl::VerTuple, build::VerTuple)
end
```
-/

/-- The `VERSION_REGEX` captures used by `tryparse(VersionNumber, v)`. -/
def tryparseVersion {Re : Type} (ops : VersionRegexOps Re)
    (typemax : Unit → Jl VersionNumber) (v : StringValue) : Jl (Option VersionNumber) := do
  if ops.isInfinity v then return some (← typemax ())
  match ← ops.matchVersion ops.versionRegex (v.toString v.value) with
  | none => return none
  | some m => do
      let major ← ops.parseUInt32 m.major
      let minor ← match m.minor with
        | some s => ops.parseUInt32 s
        | none => pure (JInt.lit .u32 0)
      let patch ← match m.patch with
        | some s => ops.parseUInt32 s
        | none => pure (JInt.lit .u32 0)
      let prerelease := match m.prerelease with
        | some s =>
            match s.toList with
            | '-' :: rest => some (String.ofList rest)
            | _ => some s
        | none => none
      let pre ← match prerelease with
        | some s => splitIdents ops s
        | none => pure (if m.minus.isSome then [.text ""] else [])
      let build ← match m.build with
        | some s => splitIdents ops s
        | none => pure (if m.plus.isSome then [.text ""] else [])
      return some (← newVersionNumber ops major minor patch pre build)

/-
Julia source: base/version.jl:149-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse(::Type{VersionNumber}, v::AbstractString)
    ver = tryparse(VersionNumber, v)
    ver === nothing && throw(ArgumentError("invalid version string: $v"))
    return ver
end
```
-/

/-- `parse(::Type{VersionNumber}, v)`. -/
def parseVersion {Re : Type} (ops : VersionRegexOps Re)
    (typemax : Unit → Jl VersionNumber) (v : StringValue) : Jl VersionNumber := do
  match ← tryparseVersion ops typemax v with
  | some ver => pure ver
  | none => throw (.argumentError ("invalid version string: " ++ ops.showString v))

/-
Julia source: base/version.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionNumber(v::AbstractString) = parse(VersionNumber, v)
```
-/

/-- `VersionNumber(v::AbstractString)`. -/
def versionNumberString (parse : StringValue → Jl VersionNumber) (v : StringValue) : Jl VersionNumber :=
  parse v

/-
Julia source: base/version.jl:173-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typemax(::Type{VersionNumber})
    ∞ = typemax(VInt)
    VersionNumber(∞, ∞, ∞, (), ("",))
end
```
-/

/-- `typemax(VersionNumber)`. -/
def typemaxVersion {Re : Type} (ops : VersionRegexOps Re) : Jl VersionNumber :=
  newVersionNumber ops (JInt.typemax .u32) (JInt.typemax .u32) (JInt.typemax .u32) [] [.text ""]

/-
Julia source: base/version.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{VersionNumber}) = v"0-"
```
-/

/-- `typemin(VersionNumber) = v"0-"`. -/
def typeminVersion (parse : StringValue → Jl VersionNumber) : Jl VersionNumber :=
  parse (stringValue "0-")

-- Reason: `macro v_str` builds a compiler expression rather than a runtime value.
-- UNTRANSLATED
-- Source: base/version.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro v_str(v); VersionNumber(v); end
-- /Source


/- Runtime build information is supplied as typed inputs. -/

structure GitVersionInfo where
  taggedCommit : Bool
  buildNumber : JInt .i64

/-- `VERSION` initialization with version_git.jl state and diagnostic output as callees. -/
/-
Julia source: base/version.jl:246-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    VERSION

A [`VersionNumber`](@ref) object describing which version of Julia is in use. See also
[Version Number Literals](@ref man-version-number-literals).
"""
const VERSION = try
    ver = VersionNumber(VERSION_STRING)
    if !isempty(ver.prerelease) && !GIT_VERSION_INFO.tagged_commit
        if GIT_VERSION_INFO.build_number >= 0
            ver = VersionNumber(ver.major, ver.minor, ver.patch, (ver.prerelease..., GIT_VERSION_INFO.build_number), ver.build)
        else
            println("WARNING: no build number found for pre-release version")
            ver = VersionNumber(ver.major, ver.minor, ver.patch, (ver.prerelease..., "unknown"), ver.build)
        end
    elseif GIT_VERSION_INFO.build_number > 0
        println("WARNING: ignoring non-zero build number for VERSION")
    end
    ver
catch e
    println("while creating Base.VERSION, ignoring error $e")
    VersionNumber(0)
end
```
-/

def initializeVersion {Re : Type} (ops : VersionRegexOps Re)
    (parseVersion : StringValue → Jl VersionNumber) (zeroVersion : Unit → Jl VersionNumber)
    (println : String → Jl Unit) (versionString : StringValue)
    (showError : JlError → String) (gitInfo : GitVersionInfo) : Jl VersionNumber := do
  let result : Jl VersionNumber := do
    let ver ← parseVersion versionString
    if !ver.prerelease.isEmpty && !gitInfo.taggedCommit then
      if gitInfo.buildNumber.val ≥ 0 then
        let id ← JInt.convert (IntTy.u64.name) .u64 gitInfo.buildNumber.val
        newVersionNumber ops ver.major ver.minor ver.patch
          (ver.prerelease ++ [.integer id]) ver.build
      else do
        println "WARNING: no build number found for pre-release version"
        newVersionNumber ops ver.major ver.minor ver.patch
          (ver.prerelease ++ [.text "unknown"]) ver.build
    else if gitInfo.buildNumber.val > 0 then do
      println "WARNING: ignoring non-zero build number for VERSION"
      pure ver
    else
      pure ver
  match result with
  | .ok ver => pure ver
  | .error e => do
      println ("while creating Base.VERSION, ignoring error " ++ showError e)
      zeroVersion ()

/-- `version_with_build_variant()` with build and runtime flags as inputs. -/
/-
Julia source: base/version.jl:273-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function version_with_build_variant()
    tags = String[]
    isempty(BUILD_VARIANT) || push!(tags, BUILD_VARIANT)
    if isdebugbuild()
        push!(tags, "debug")
    elseif ccall(:jl_is_assertsbuild, Int8, ()) != 0
        push!(tags, "assert")
    end
    isempty(tags) && return VERSION
    return VersionNumber(VERSION.major, VERSION.minor, VERSION.patch, VERSION.prerelease, (VERSION.build..., tags...))
end
```
-/

def versionWithBuildVariant {Re : Type} (ops : VersionRegexOps Re)
    (isDebugBuild hasAssertions : Unit → Bool) (buildVariant : String)
    (version : VersionNumber) : Jl VersionNumber := do
  let mut tags := if buildVariant.isEmpty then [] else [buildVariant]
  if isDebugBuild () then
    tags := tags ++ ["debug"]
  else if hasAssertions () then
    tags := tags ++ ["assert"]
  if tags.isEmpty then return version
  newVersionNumber ops version.major version.minor version.patch version.prerelease
    (version.build ++ tags.map VersionIdentifier.text)

/-- `libllvm_version`, with the global library version string and string slicing as inputs. -/
/-
Julia source: base/version.jl:285-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const libllvm_version = if endswith(libllvm_version_string, "jl")
    # strip the "jl" SONAME suffix (JuliaLang/julia#33058)
    # (LLVM does never report a prerelease version anyway)
    VersionNumber(libllvm_version_string[1:end-2])
else
    VersionNumber(libllvm_version_string)
end
```
-/

def libllvmVersion {E : Type} (endsWith : String → String → Bool)
    (removeSuffix : String → Nat → String)
    (parseVersion : StringValue → Except E VersionNumber) (versionString : String) : Except E VersionNumber :=
  parseVersion (stringValue (if endsWith versionString "jl" then removeSuffix versionString 2 else versionString))

/- `jl_get_libllvm` returns `jl_nothing` when the LLVM module path cannot be resolved, and a symbol containing the path otherwise (`src/codegen.cpp:11766-11787`). -/
structure LibLLVMRuntime where
  path : Option String

/--
Julia source: base/version.jl:293-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
libllvm_path() = ccall(:jl_get_libllvm, Any, ())
```
-/
def libllvmPath (runtime : LibLLVMRuntime) : Option String := runtime.path


/-! ## Version bounds -/

/-
Julia source: base/version.jl:299-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VersionBound
    t::NTuple{3, UInt32}
    n::Int
```
-/

structure VersionBound where
  t : VInt × VInt × VInt
  n : Nat
  deriving DecidableEq

def versionBoundParts (b : VersionBound) : List VInt := [b.t.1, b.t.2.1, b.t.2.2]

def sameBoundTuple (a b : VersionBound) : Bool :=
  a.t.1.val == b.t.1.val && a.t.2.1.val == b.t.2.1.val && a.t.2.2.val == b.t.2.2.val

def int64Value (n : Int) : JInt .i64 := JInt.lit .i64 n

def integerFromInt64 (n : JInt .i64) : IntegerValue := ⟨JInt .i64, n, fun x => x.val⟩

def integerFromUInt32 (n : VInt) : IntegerValue := ⟨JInt .u32, n, fun x => x.val⟩

/-- `VersionBound(tin::NTuple{n,Integer})`, including its `n ≤ 3` check. -/
/-
Julia source: base/version.jl:302-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function VersionBound(tin::NTuple{n, Integer}) where {n}
        n <= 3 || throw(ArgumentError("VersionBound: you can only specify major, minor and patch versions"))
        n == 0 && return new((0, 0, 0), n)
        n == 1 && return new((tin[1], 0, 0), n)
        n == 2 && return new((tin[1], tin[2], 0), n)
        n == 3 && return new((tin[1], tin[2], tin[3]), n)
        error("invalid $n")
    end
```
-/

def makeVersionBound (tin : List IntegerValue) : Jl VersionBound := do
  if tin.length > 3 then
    throw (.argumentError "VersionBound: you can only specify major, minor and patch versions")
  let values ← tin.mapM fun x => JInt.convert (IntTy.u32.name) .u32 (x.toInt x.value)
  let zero := JInt.lit .u32 0
  match values with
  | [] => pure ⟨(zero, zero, zero), 0⟩
  | [a] => pure ⟨(a, zero, zero), 1⟩
  | [a, b] => pure ⟨(a, b, zero), 2⟩
  | [a, b, c] => pure ⟨(a, b, c), 3⟩
  | _ => throw (.argumentError "invalid VersionBound")

/-- `VersionBound(t::Integer...)`. -/
/-
Julia source: base/version.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionBound(t::Integer...) = VersionBound(t)
```
-/

def versionBoundVararg (construct : List IntegerValue → Jl VersionBound)
    (values : List IntegerValue) : Jl VersionBound := construct values

/-- `VersionBound(v::VersionNumber)`. -/
/-
Julia source: base/version.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionBound(v::VersionNumber) = VersionBound(v.major, v.minor, v.patch)
```
-/

def versionBoundFromVersion (v : VersionNumber) : Jl VersionBound :=
  versionBoundVararg makeVersionBound [integerFromUInt32 v.major, integerFromUInt32 v.minor, integerFromUInt32 v.patch]

/-- `Base.getindex(b::VersionBound, i::Int) = b.t[i]`. -/
/-
Julia source: base/version.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.getindex(b::VersionBound, i::Int) = b.t[i]
```
-/

def versionBoundGet (b : VersionBound) (i : JInt .i64) : Jl VInt :=
  if i.val < 1 || i.val > 3 then .error .boundsError
  else match (versionBoundParts b)[(i.val - 1).toNat]? with
    | some value => .ok value
    | none => .error .boundsError

/-- Lexicographic comparison of equal-length `UInt32` component prefixes. -/
def compareBoundParts : List VInt → List VInt → Int
  | a :: as, b :: bs =>
      if a.val < b.val then -1 else if a.val > b.val then 1 else compareBoundParts as bs
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1

def boundLength (b : VersionBound) : Nat := b.n

def boundPrefix (b : VersionBound) : List VInt := (versionBoundParts b).take (boundLength b)

/-- `v ≲ b`, comparing only the significant components of the bound. -/
/-
Julia source: base/version.jl:316-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ≲(v::VersionNumber, b::VersionBound)
    b.n == 0 && return true
    b.n == 1 && return v.major <= b[1]
    b.n == 2 && return (v.major, v.minor) <= (b[1], b[2])
    return (v.major, v.minor, v.patch) <= (b[1], b[2], b[3])
end
```
-/

def versionAtMostBound (v : VersionNumber) (b : VersionBound) : Bool :=
  boundLength b == 0 || compareBoundParts
    ([v.major, v.minor, v.patch].take (boundLength b)) (boundPrefix b) ≤ 0

/-- `b ≲ v`, comparing only the significant components of the bound. -/
/-
Julia source: base/version.jl:323-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ≲(b::VersionBound, v::VersionNumber)
    b.n == 0 && return true
    b.n == 1 && return v.major >= b[1]
    b.n == 2 && return (v.major, v.minor) >= (b[1], b[2])
    return (v.major, v.minor, v.patch) >= (b[1], b[2], b[3])
end
```
-/

def versionBoundAtMost (b : VersionBound) (v : VersionNumber) : Bool :=
  boundLength b == 0 || compareBoundParts (boundPrefix b)
    ([v.major, v.minor, v.patch].take (boundLength b)) ≤ 0

/-- `isless_ll(a,b)`: lexicographic comparison of lower bounds. -/
/-
Julia source: base/version.jl:330-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless_ll(a::VersionBound, b::VersionBound)
    m, n = a.n, b.n
    for i in 1:min(m, n)
        a[i] < b[i] && return true
        a[i] > b[i] && return false
    end
    return m < n
end
```
-/

def islessLowerBound (a b : VersionBound) : Bool :=
  compareBoundParts (boundPrefix a) (boundPrefix b) < 0

/-- `stricterlower(a,b)`. -/
/-
Julia source: base/version.jl:339-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stricterlower(a::VersionBound, b::VersionBound) = isless_ll(a, b) ? b : a
```
-/

def stricterLowerBound (a b : VersionBound) : VersionBound :=
  if islessLowerBound a b then b else a

/-- `isless_uu(a,b)`, preferring the more significant bound after equal components. -/
/-
Julia source: base/version.jl:342-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isless_uu(a::VersionBound, b::VersionBound)
    m, n = a.n, b.n
    for i in 1:min(m, n)
        a[i] < b[i] && return true
        a[i] > b[i] && return false
    end
    return m > n
end
```
-/

def islessUpperBound (a b : VersionBound) : Bool :=
  let shared := min (boundLength a) (boundLength b)
  let c := compareBoundParts ((versionBoundParts a).take shared) ((versionBoundParts b).take shared)
  if c < 0 then true else if c > 0 then false else boundLength a > boundLength b

/-- `stricterupper(a,b)`. -/
/-
Julia source: base/version.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stricterupper(a::VersionBound, b::VersionBound) = isless_uu(a, b) ? a : b
```
-/

def stricterUpperBound (a b : VersionBound) : VersionBound :=
  if islessUpperBound a b then a else b

/-- `isjoinable(up,lo)`, including the adjacent final-component test. -/
/-
Julia source: base/version.jl:353-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `isjoinable` compares an upper bound of a range with the lower bound of the next range
# to determine if they can be joined, as in [1.5-2.8, 2.5-3] -> [1.5-3]. Used by `union!`.
# The equal-length-bounds case is special since e.g. `1.5` can be joined with `1.6`,
# `2.3.4` can be joined with `2.3.5` etc.

function isjoinable(up::VersionBound, lo::VersionBound)
    up.n == 0 && lo.n == 0 && return true
    if up.n == lo.n
        n = up.n
        for i in 1:(n - 1)
            up[i] > lo[i] && return true
            up[i] < lo[i] && return false
        end
        up[n] < lo[n] - 1 && return false
        return true
    else
        l = min(up.n, lo.n)
        for i in 1:l
            up[i] > lo[i] && return true
            up[i] < lo[i] && return false
        end
    end
    return true
end
```
-/

def isJoinable (up lo : VersionBound) : Bool := Id.run do
  let m := boundLength up
  let n := boundLength lo
  if m == 0 && n == 0 then return true
  if m == n then
    let priorUp := (versionBoundParts up).take (m - 1)
    let priorLo := (versionBoundParts lo).take (n - 1)
    let prior := compareBoundParts priorUp priorLo
    if prior > 0 then return true
    if prior < 0 then return false
    match (versionBoundParts up)[m - 1]?, (versionBoundParts lo)[n - 1]? with
    | some lastUp, some lastLo =>
        if lastUp.val < lastLo.val - 1 then return false
        return true
    | _, _ => return false
  let shared := min m n
  let c := compareBoundParts ((versionBoundParts up).take shared)
    ((versionBoundParts lo).take shared)
  if c > 0 then return true
  if c < 0 then return false
  return true

/-- `Base.hash(r::VersionBound,h::UInt)`. -/
/-
Julia source: base/version.jl:378-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.hash(r::VersionBound, h::UInt) = hash(r.t, hash(r.n, h))
```
-/

def hashVersionBound (hashTuple : VInt × VInt × VInt → JInt .u64 → JInt .u64)
    (hashInt : JInt .i64 → JInt .u64 → JInt .u64) (b : VersionBound) (seed : JInt .u64) : JInt .u64 :=
  hashTuple b.t (hashInt (int64Value (b.n : Int)) seed)

structure VersionBoundStringOps (S : Type) where
  strip : S → S
  isStar : S → Bool
  first : S → Jl Char
  substringFrom : S → JInt .i64 → Jl S
  lastindex : S → JInt .i64
  findnextDot : S → JInt .i64 → Option (JInt .i64)
  substring : S → JInt .i64 → JInt .i64 → Jl S
  parseInt64 : S → Jl (JInt .i64)
  repr : S → String

/-- `VersionBound(s::AbstractString)`, preserving strip, prefix, dot-search and parse order. -/
/-
Julia source: base/version.jl:381-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function VersionBound(s::AbstractString)
    s = strip(s)
    s == "*" && return VersionBound()
    first(s) == 'v' && (s = SubString(s, 2))
    l = lastindex(s)

    p = findnext('.', s, 1)
    b = p === nothing ? l : (p - 1)
    i = parse(Int64, SubString(s, 1, b))
    p === nothing && return VersionBound(i)

    a = p + 1
    p = findnext('.', s, a)
    b = p === nothing ? l : (p - 1)
    j = parse(Int64, SubString(s, a, b))
    p === nothing && return VersionBound(i, j)

    a = p + 1
    p = findnext('.', s, a)
    b = p === nothing ? l : (p - 1)
    k = parse(Int64, SubString(s, a, b))
    p === nothing && return VersionBound(i, j, k)

    error("invalid VersionBound string $(repr(s))")
end
```
-/

def parseVersionBoundString {S : Type} (ops : VersionBoundStringOps S) (original : S) : Jl VersionBound := do
  let s := ops.strip original
  if ops.isStar s then return ⟨(JInt.lit .u32 0, JInt.lit .u32 0, JInt.lit .u32 0), 0⟩
  let first ← ops.first s
  let s ← if first == 'v' then ops.substringFrom s (int64Value 2) else pure s
  let last := ops.lastindex s
  let p := ops.findnextDot s (int64Value 1)
  let b := p.map (fun pos => JInt.wrap .i64 (pos.val - 1)) |>.getD last
  let i ← ops.parseInt64 (← ops.substring s (int64Value 1) b)
  match p with
  | none => versionBoundVararg makeVersionBound [integerFromInt64 i]
  | some dot1 => do
      let a := JInt.wrap .i64 (dot1.val + 1)
      let p2 := ops.findnextDot s a
      let b2 := p2.map (fun pos => JInt.wrap .i64 (pos.val - 1)) |>.getD last
      let j ← ops.parseInt64 (← ops.substring s a b2)
      match p2 with
      | none => versionBoundVararg makeVersionBound [integerFromInt64 i, integerFromInt64 j]
      | some dot2 => do
          let a2 := JInt.wrap .i64 (dot2.val + 1)
          let p3 := ops.findnextDot s a2
          let b3 := p3.map (fun pos => JInt.wrap .i64 (pos.val - 1)) |>.getD last
          let k ← ops.parseInt64 (← ops.substring s a2 b3)
          match p3 with
          | none => versionBoundVararg makeVersionBound [integerFromInt64 i, integerFromInt64 j, integerFromInt64 k]
          | some _ => throw (.argumentError ("invalid VersionBound string " ++ ops.repr s))

/-! ## Version ranges -/

/-
Julia source: base/version.jl:410-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VersionRange
    lower::VersionBound
    upper::VersionBound
    # NOTE: ranges are allowed to be empty; they are ignored by VersionSpec anyway
```
-/

structure VersionRange where
  lower : VersionBound
  upper : VersionBound
  deriving DecidableEq

/-- The inner `VersionRange(lo, hi)` normalization when their component tuples match. -/
/-
Julia source: base/version.jl:414-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function VersionRange(lo::VersionBound, hi::VersionBound)
        # lo.t == hi.t implies that digits past min(lo.n, hi.n) are zero
        # lo.n < hi.n example: 1.2-1.2.0 => 1.2.0
        # lo.n > hi.n example: 1.2.0-1.2 => 1.2
        lo.t == hi.t && (lo = hi)
        return new(lo, hi)
    end
end
```
-/

def makeVersionRange (lo hi : VersionBound) : VersionRange :=
  if sameBoundTuple lo hi then ⟨hi, hi⟩ else ⟨lo, hi⟩

/-- `VersionRange(b::VersionBound = VersionBound())`. -/
/-
Julia source: base/version.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionRange(b::VersionBound = VersionBound()) = VersionRange(b, b)
```
-/

def versionRangeBound (b : VersionBound := ⟨(JInt.lit .u32 0, JInt.lit .u32 0, JInt.lit .u32 0), 0⟩) : VersionRange :=
  makeVersionRange b b

/-- `VersionRange(t::Integer...)`. -/
/-
Julia source: base/version.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionRange(t::Integer...) = VersionRange(VersionBound(t...))
```
-/

def versionRangeIntegers (values : List IntegerValue) : Jl VersionRange := do
  let b ← versionBoundVararg makeVersionBound values
  pure (versionRangeBound b)

/-- `VersionRange(v::VersionNumber)`. -/
/-
Julia source: base/version.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionRange(v::VersionNumber) = VersionRange(VersionBound(v))
```
-/

def versionRangeVersion (v : VersionNumber) : Jl VersionRange := do
  let b ← versionBoundFromVersion v
  pure (versionRangeBound b)

/-- `VersionRange(lo::VersionNumber, hi::VersionNumber)`. -/
/-
Julia source: base/version.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionRange(lo::VersionNumber, hi::VersionNumber) = VersionRange(VersionBound(lo), VersionBound(hi))
```
-/

def versionRangeVersions (lo hi : VersionNumber) : Jl VersionRange := do
  let lower ← versionBoundFromVersion lo
  let upper ← versionBoundFromVersion hi
  pure (makeVersionRange lower upper)

/-- `VersionRange_1`. -/
/-
Julia source: base/version.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const VersionRange_1 = VersionRange(VersionBound("1"), VersionBound("1"))
```
-/

def versionRangeOne : VersionRange :=
  let one := JInt.lit .u32 1
  let zero := JInt.lit .u32 0
  let bound : VersionBound := ⟨(one, zero, zero), 1⟩
  makeVersionRange bound bound

/-- `VersionRange(s::AbstractString)`. -/
/-
Julia source: base/version.jl:429-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function VersionRange(s::AbstractString)
    s == "1" && return VersionRange_1
    p = split(s, "-")
    if length(p) != 1 && length(p) != 2
        throw(ArgumentError("invalid version range: $(repr(s))"))
    end
    lower = VersionBound(p[1])
    upper = length(p) == 1 ? lower : VersionBound(p[2])
    return VersionRange(lower, upper)
end
```
-/

def parseVersionRangeString {S Part : Type} (isOne : S → Bool)
    (split : S → String → List Part) (showValue : S → String)
    (parseBound : Part → Jl VersionBound) (oneRange : VersionRange) (s : S) : Jl VersionRange := do
  if isOne s then return oneRange
  let parts := split s "-"
  if parts.length != 1 && parts.length != 2 then
    throw (.argumentError ("invalid version range: " ++ showValue s))
  let lowerPart ← match parts with
    | first :: _ => pure first
    | [] => throw .boundsError
  let lower ← parseBound lowerPart
  let upper ← match parts with
    | [_] => pure lower
    | _ :: second :: _ => parseBound second
    | [] => throw .boundsError
  return makeVersionRange lower upper

/-- `Base.isempty(r::VersionRange)`. -/
/-
Julia source: base/version.jl:440-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.isempty(r::VersionRange)
    for i in 1:min(r.lower.n, r.upper.n)
        r.lower[i] > r.upper[i] && return true
        r.lower[i] < r.upper[i] && return false
    end
    return false
end
```
-/

def versionRangeIsEmpty (r : VersionRange) : Bool :=
  let shared := min (boundLength r.lower) (boundLength r.upper)
  compareBoundParts ((versionBoundParts r.lower).take shared)
    ((versionBoundParts r.upper).take shared) > 0

/-- Decimal joining for `print(::VersionRange)`. -/
def joinBoundParts (showUInt32 : VInt → String) (xs : List VInt) : String :=
  joinStrings (xs.map showUInt32)

/-- `Base.print(io::IO,r::VersionRange)`, represented by the emitted string. -/
/-
Julia source: base/version.jl:448-465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.print(io::IO, r::VersionRange)
    m, n = r.lower.n, r.upper.n
    return if (m, n) == (0, 0)
        print(io, '*')
    elseif m == 0
        print(io, "0 -")
        join(io, r.upper.t, '.')
    elseif n == 0
        join(io, r.lower.t, '.')
        print(io, " - *")
    else
        join(io, r.lower.t[1:m], '.')
        if r.lower != r.upper
            print(io, " - ")
            join(io, r.upper.t[1:n], '.')
        end
    end
end
```
-/

def printVersionRange (showUInt32 : VInt → String) (r : VersionRange) : String := Id.run do
  let m := boundLength r.lower
  let n := boundLength r.upper
  if m == 0 && n == 0 then return "*"
  if m == 0 then return "0 -" ++ joinBoundParts showUInt32 (versionBoundParts r.upper)
  if n == 0 then return joinBoundParts showUInt32 (versionBoundParts r.lower) ++ " - *"
  let lower := joinBoundParts showUInt32 ((versionBoundParts r.lower).take m)
  if sameBoundTuple r.lower r.upper && boundLength r.lower == boundLength r.upper then return lower
  let upper := joinBoundParts showUInt32 ((versionBoundParts r.upper).take n)
  return lower ++ " - " ++ upper

/-- `Base.show(io::IO,r::VersionRange)`. -/
/-
Julia source: base/version.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, r::VersionRange) = print(io, "VersionRange(\"", r, "\")")
```
-/

def showVersionRange (showUInt32 : VInt → String) (r : VersionRange) : String :=
  "VersionRange(\"" ++ printVersionRange showUInt32 r ++ "\")"

/-- `Base.in(v::VersionNumber,r::VersionRange)`. -/
/-
Julia source: base/version.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.in(v::VersionNumber, r::VersionRange) = r.lower ≲ v ≲ r.upper
```
-/

def versionInRange (v : VersionNumber) (r : VersionRange) : Bool :=
  versionBoundAtMost r.lower v && versionAtMostBound v r.upper

/-- `Base.intersect(a::VersionRange,b::VersionRange)`. -/
/-
Julia source: base/version.jl:470-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.intersect(a::VersionRange, b::VersionRange) = VersionRange(stricterlower(a.lower, b.lower), stricterupper(a.upper, b.upper))
```
-/

def intersectVersionRanges (a b : VersionRange) : VersionRange :=
  makeVersionRange (stricterLowerBound a.lower b.lower) (stricterUpperBound a.upper b.upper)

structure RangeVectorOps (R E : Type) where
  length : R → Except E Nat
  get : R → Nat → Except E VersionRange
  set : R → Nat → VersionRange → Except E Unit
  sort : R → (VersionRange → VersionRange → Bool) → Except E Unit
  findFirst : R → (VersionRange → Bool) → Except E (Option Nat)
  empty : R → Except E R
  resize : R → Nat → Except E R
  values : R → Except E (List VersionRange)
  fromList : List VersionRange → Except E R
  allocate : JInt .i64 → Except E R
  copy : R → Except E R
  append : R → R → Except E Unit
  push : R → VersionRange → Except E Unit
  equal : R → R → Bool
  hash : R → JInt .u64 → JInt .u64
  assertionError : String → E

/-- `Base.union!(ranges::Vector{<:VersionRange})`. Vector reads and writes remain explicit. -/
/-
Julia source: base/version.jl:472-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.union!(ranges::Vector{<:VersionRange})
    l = length(ranges)
    l == 0 && return ranges

    sort!(ranges, lt = (a, b) -> (isless_ll(a.lower, b.lower) || (a.lower == b.lower && isless_uu(a.upper, b.upper))))

    ks = findfirst(!isempty, ranges)
    ks === nothing && return empty!(ranges)

    lo, up, k0 = ranges[ks].lower, ranges[ks].upper, 1
    for k in (ks + 1):l
        isempty(ranges[k]) && continue
        lo1, up1 = ranges[k].lower, ranges[k].upper
        if isjoinable(up, lo1)
            isless_uu(up, up1) && (up = up1)
            continue
        end
        vr = VersionRange(lo, up)
        @assert !isempty(vr) "empty VersionRange"
        ranges[k0] = vr
        k0 += 1
        lo, up = lo1, up1
    end
    vr = VersionRange(lo, up)
    if !isempty(vr)
        ranges[k0] = vr
        k0 += 1
    end
    resize!(ranges, k0 - 1)
    return ranges
end
```
-/

def unionVersionRanges! {R E : Type} (ops : RangeVectorOps R E) (ranges : R) : Except E R := do
  let length ← ops.length ranges
  if length == 0 then return ranges
  ops.sort ranges fun a b =>
    islessLowerBound a.lower b.lower ||
      (sameBoundTuple a.lower b.lower && boundLength a.lower == boundLength b.lower && islessUpperBound a.upper b.upper)
  let first ← ops.findFirst ranges (fun r => !versionRangeIsEmpty r)
  match first with
  | none => ops.empty ranges
  | some ks => do
      let initial ← ops.get ranges ks
      let mut lo := initial.lower
      let mut up := initial.upper
      let mut k0 := 1
      for offset in List.range (length - ks) do
        let k := ks + 1 + offset
        let range ← ops.get ranges k
        if versionRangeIsEmpty range then continue
        let lo1 := range.lower
        let up1 := range.upper
        if isJoinable up lo1 then
          if islessUpperBound up up1 then up := up1
          continue
        let vr := makeVersionRange lo up
        if versionRangeIsEmpty vr then throw (ops.assertionError "empty VersionRange")
        ops.set ranges k0 vr
        k0 := k0 + 1
        lo := lo1
        up := up1
      let vr := makeVersionRange lo up
      if !versionRangeIsEmpty vr then
        ops.set ranges k0 vr
        k0 := k0 + 1
      ops.resize ranges (k0 - 1)

/-- `Base.minimum(r::VersionRange)`. -/
/-
Julia source: base/version.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.minimum(r::VersionRange) = r.lower
```
-/

def minimumVersionRange (r : VersionRange) : VersionBound := r.lower

/-! ## Version specifications -/

/-
Julia source: base/version.jl:509-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VersionSpec
    ranges::Vector{VersionRange}
```
-/

structure VersionSpec (R : Type) where
  ranges : R

/-- `VersionSpec(r::Vector{<:VersionRange})`, including its in-place canonicalization. -/
/-
Julia source: base/version.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    VersionSpec(r::Vector{<:VersionRange}) = new(length(r) == 1 ? r : union!(r))
```
-/

def makeVersionSpec {R E : Type} (ops : RangeVectorOps R E) (ranges : R) : Except E (VersionSpec R) := do
  let ranges ← if (← ops.length ranges) == 1 then pure ranges else unionVersionRanges! ops ranges
  pure ⟨ranges⟩

/-- `VersionSpec(vs::VersionSpec)`. -/
/-
Julia source: base/version.jl:512-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    VersionSpec(vs::VersionSpec) = vs
```
-/

def versionSpecIdentity {R : Type} (vs : VersionSpec R) : VersionSpec R := vs

/-- `VersionSpec(r::VersionRange)`. -/
/-
Julia source: base/version.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionSpec(r::VersionRange) = VersionSpec(VersionRange[r])
```
-/

def versionSpecFromRange {R E : Type} (ops : RangeVectorOps R E) (r : VersionRange) : Except E (VersionSpec R) := do
  makeVersionSpec ops (← ops.fromList [r])

/-- `VersionSpec(v::VersionNumber)`. -/
/-
Julia source: base/version.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionSpec(v::VersionNumber) = VersionSpec(VersionRange(v))
```
-/

def versionSpecFromVersion {R E : Type} (ops : RangeVectorOps R E)
    (rangeFromVersion : VersionNumber → Except E VersionRange) (v : VersionNumber) : Except E (VersionSpec R) := do
  versionSpecFromRange ops (← rangeFromVersion v)

/-- `_all_versionsspec = VersionSpec(VersionRange())` and the default constructor. -/
/-
Julia source: base/version.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _all_versionsspec = VersionSpec(VersionRange())
```
-/

def allVersionsSpec {R E : Type} (ops : RangeVectorOps R E) : Except E (VersionSpec R) := do
  versionSpecFromRange ops (versionRangeBound)

/-
Julia source: base/version.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionSpec() = _all_versionsspec
```
-/

def versionSpecDefault {R : Type} (allVersions : VersionSpec R) : VersionSpec R := allVersions

/-- `VersionSpec(s::AbstractString)`. -/
/-
Julia source: base/version.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionSpec(s::AbstractString) = VersionSpec(VersionRange(s))
```
-/

def versionSpecFromString {R S E : Type} (ops : RangeVectorOps R E)
    (parseRange : S → Except E VersionRange) (s : S) : Except E (VersionSpec R) := do
  let r ← parseRange s
  makeVersionSpec ops (← ops.fromList [r])

/-- `VersionSpec(v::AbstractVector)`, with `map(VersionRange, v)` as a callee. -/
/-
Julia source: base/version.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionSpec(v::AbstractVector) = VersionSpec(map(VersionRange, v))
```
-/

def versionSpecFromVector {R V E : Type} (ops : RangeVectorOps R E)
    (mapRanges : V → Except E R) (values : V) : Except E (VersionSpec R) := do
  makeVersionSpec ops (← mapRanges values)

/-- `Base.in(v::VersionNumber,s::VersionSpec)`. -/
/-
Julia source: base/version.jl:523-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.in(v::VersionNumber, s::VersionSpec)
    for r in s.ranges
        v in r && return true
    end
    return false
end
```
-/

def versionInSpecLoop {E : Type} (ranges : List VersionRange) (v : VersionNumber) : Except E Bool := do
  match ranges with
  | [] => pure false
  | r :: rest => if versionInRange v r then pure true else versionInSpecLoop rest v

def versionInSpec {R E : Type} (ops : RangeVectorOps R E)
    (v : VersionNumber) (spec : VersionSpec R) : Except E Bool := do
  versionInSpecLoop (← ops.values spec.ranges) v

structure MatchSpecOps (Dest Versions R E : Type) where
  linearIndicesEqual : Dest → Versions → Bool
  lengthDest : Dest → Nat
  lengthVersions : Versions → Nat
  fillFalse : Dest → Nat → Except E Unit
  getVersion : Versions → Nat → Except E VersionNumber
  setBit : Dest → Nat → Bool → Except E Unit
  rangesEmpty : R → Except E Bool
  rangeValues : R → Except E (List VersionRange)
  dimensionMismatch : String → E
  assertionError : String → E

def scanVersionRangeStart {Dest Versions R E : Type} (ops : MatchSpecOps Dest Versions R E)
    (range : VersionRange) (versions : Versions) (n : Nat) : Nat → Nat → Except E Nat
  | 0, i => pure i
  | fuel + 1, i => do
      if i > n then return i
      let version ← ops.getVersion versions i
      if versionBoundAtMost range.lower version then return i
      scanVersionRangeStart ops range versions n fuel (i + 1)

def markVersionRangeEnd {Dest Versions R E : Type} (ops : MatchSpecOps Dest Versions R E)
    (range : VersionRange) (versions : Versions) (dest : Dest) (n : Nat) : Nat → Nat → Except E Unit
  | 0, _ => pure ()
  | fuel + 1, i => do
      if i > n then return ()
      let version ← ops.getVersion versions i
      if !versionAtMostBound version range.upper then return ()
      ops.setBit dest i true
      markVersionRangeEnd ops range versions dest n fuel (i + 1)

/-- `matches_spec_range!`, preserving its assertions, clearing, ordered scans and writes. -/
/-
Julia source: base/version.jl:534-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function matches_spec_range!(dest::BitVector, versions::AbstractVector{VersionNumber}, spec::VersionSpec, n::Int)
    @assert length(versions) == n "invalid version list"
    @assert length(dest) >= n "invalid dest length"

    # Initialize to false
    dest[1:n] .= false

    isempty(spec.ranges) && return dest

    # Assumes versions are sorted (as created in Operations.jl:1002)
    # If sorted, this avoids O(n*m) comparisons by scanning linearly
    @inbounds for range in spec.ranges
        # Find first version that could be in range
        i = 1
        while i <= n && !(range.lower ≲ versions[i])
            i += 1
        end

        # Mark all versions in range
        while i <= n && versions[i] ≲ range.upper
            dest[i] = true
            i += 1
        end
    end

    return dest
end
```
-/

def matchesSpecRange! {D V R E : Type} (ops : MatchSpecOps D V R E)
    (dest : D) (versions : V)
    (spec : VersionSpec R) (n : Nat) : Except E D := do
  if !ops.linearIndicesEqual dest versions then
    throw (ops.dimensionMismatch "input and output array sizes and indices must match")
  if ops.lengthVersions versions != n then throw (ops.assertionError "invalid version list")
  if ops.lengthDest dest < n then throw (ops.assertionError "invalid dest length")
  ops.fillFalse dest n
  if ← ops.rangesEmpty spec.ranges then return dest
  let ranges ← ops.rangeValues spec.ranges
  for range in ranges do
    let i ← scanVersionRangeStart ops range versions n (n + 1) 1
    markVersionRangeEnd ops range versions dest n (n + 1) i
  return dest

/-- `Base.copy(vs::VersionSpec)`. -/
/-
Julia source: base/version.jl:562-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.copy(vs::VersionSpec) = VersionSpec(vs)
```
-/

def copyVersionSpec {R : Type} (vs : VersionSpec R) : VersionSpec R := versionSpecIdentity vs

/-- `empty_versionspec` and `_empty_symbol`. -/
/-
Julia source: base/version.jl:564-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const empty_versionspec = VersionSpec(VersionRange[])
const _empty_symbol = "∅"
```
-/

def emptyVersionSpec {R E : Type} (ops : RangeVectorOps R E) : Except E (VersionSpec R) := do
  makeVersionSpec ops (← ops.fromList [])

def emptyVersionSpecSymbol : String := "∅"

/-- `Base.isempty(s::VersionSpec)`. -/
/-
Julia source: base/version.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isempty(s::VersionSpec) = all(isempty, s.ranges)
```
-/

def allEmptyRanges : List VersionRange → Bool
  | [] => true
  | r :: rs => versionRangeIsEmpty r && allEmptyRanges rs

def versionSpecIsEmpty {R E : Type} (ops : RangeVectorOps R E)
    (s : VersionSpec R) : Except E Bool := do
  return allEmptyRanges (← ops.values s.ranges)

/-- The load-time assertion `@assert isempty(empty_versionspec)`. -/
/-
Julia source: base/version.jl:568-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assert isempty(empty_versionspec)
```
-/

def assertEmptyVersionSpec {E : Type} (isEmpty : Except E Bool) (assertionError : E) : Except E Unit := do
  if ← isEmpty then pure () else throw assertionError

/-- `Base.intersect(A::VersionSpec,B::VersionSpec)`, including its product write order. -/
/-
Julia source: base/version.jl:570-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.intersect(A::VersionSpec, B::VersionSpec)
    (isempty(A) || isempty(B)) && return copy(empty_versionspec)
    ranges = Vector{VersionRange}(undef, length(A.ranges) * length(B.ranges))
    i = 1
    @inbounds for a in A.ranges, b in B.ranges
        ranges[i] = intersect(a, b)
        i += 1
    end
    return VersionSpec(ranges)
end
```
-/

def intersectVersionSpecs {R E : Type} (ops : RangeVectorOps R E)
    (emptySpec : VersionSpec R) (a b : VersionSpec R) : Except E (VersionSpec R) := do
  if (← versionSpecIsEmpty ops a) || (← versionSpecIsEmpty ops b) then
    return copyVersionSpec emptySpec
  let leftLength ← ops.length a.ranges
  let rightLength ← ops.length b.ranges
  let capacity := JInt.wrap .i64 ((leftLength : Int) * (rightLength : Int))
  let mut ranges ← ops.allocate capacity
  let left ← ops.values a.ranges
  let right ← ops.values b.ranges
  let mut i := 1
  for x in left do
    for y in right do
      ops.set ranges i (intersectVersionRanges x y)
      i := i + 1
  makeVersionSpec ops ranges

/-- `Base.intersect(a::VersionNumber,B::VersionSpec)`. -/
/-
Julia source: base/version.jl:580-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.intersect(a::VersionNumber, B::VersionSpec) = a in B ? VersionSpec(a) : empty_versionspec
```
-/

def intersectVersionSpecValue {R E : Type} (ops : RangeVectorOps R E)
    (emptySpec : VersionSpec R) (versionSpecOf : VersionNumber → Except E (VersionSpec R))
    (a : VersionNumber) (b : VersionSpec R) : Except E (VersionSpec R) := do
  if ← versionInSpec ops a b then versionSpecOf a else pure emptySpec

/-- `Base.intersect(A::VersionSpec,b::VersionNumber)`. -/
/-
Julia source: base/version.jl:581-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.intersect(A::VersionSpec, b::VersionNumber) = intersect(b, A)
```
-/

def intersectVersionSpecReverse {R E : Type} (ops : RangeVectorOps R E)
    (emptySpec : VersionSpec R) (versionSpecOf : VersionNumber → Except E (VersionSpec R))
    (a : VersionSpec R) (b : VersionNumber) : Except E (VersionSpec R) :=
  intersectVersionSpecValue ops emptySpec versionSpecOf b a

/-- `Base.union(A::VersionSpec,B::VersionSpec)`. -/
/-
Julia source: base/version.jl:583-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.union(A::VersionSpec, B::VersionSpec)
    A == B && return A
    Ar = copy(A.ranges)
    append!(Ar, B.ranges)
    union!(Ar)
    return VersionSpec(Ar)
end
```
-/

def unionVersionSpecs {R E : Type} (ops : RangeVectorOps R E)
    (a b : VersionSpec R) : Except E (VersionSpec R) := do
  if ops.equal a.ranges b.ranges then return a
  let ranges ← ops.copy a.ranges
  ops.append ranges b.ranges
  let _ ← unionVersionRanges! ops ranges
  makeVersionSpec ops ranges

/-- `Base.:(==)(A::VersionSpec,B::VersionSpec)`. -/
/-
Julia source: base/version.jl:591-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:(==)(A::VersionSpec, B::VersionSpec) = A.ranges == B.ranges
```
-/

def versionSpecsEqual {R E : Type} (ops : RangeVectorOps R E)
    (a b : VersionSpec R) : Bool := ops.equal a.ranges b.ranges

/-- `Base.hash(s::VersionSpec,h::UInt)`. -/
/-
Julia source: base/version.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.hash(s::VersionSpec, h::UInt) = hash(s.ranges, h +% (0x2fd2ca6efa023f44 % UInt))
```
-/

def hashVersionSpec {R E : Type} (ops : RangeVectorOps R E)
    (s : VersionSpec R) (seed : JInt .u64) : JInt .u64 :=
  ops.hash s.ranges (JInt.wrap .u64 (seed.val + 0x2fd2ca6efa023f44))

def joinComma : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ ", " ++ joinComma xs

/-- `Base.print(io::IO,s::VersionSpec)`, represented by the emitted string. -/
/-
Julia source: base/version.jl:594-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.print(io::IO, s::VersionSpec)
    isempty(s) && return print(io, _empty_symbol)
    length(s.ranges) == 1 && return print(io, s.ranges[1])
    print(io, '[')
    for i in 1:length(s.ranges)
        1 < i && print(io, ", ")
        print(io, s.ranges[i])
    end
    return print(io, ']')
end
```
-/

def printVersionSpec {R E : Type} (ops : RangeVectorOps R E)
    (showUInt32 : VInt → String) (s : VersionSpec R) : Except E String := do
  if ← versionSpecIsEmpty ops s then return emptyVersionSpecSymbol
  let length ← ops.length s.ranges
  if length == 1 then
    return printVersionRange showUInt32 (← ops.get s.ranges 1)
  let mut rendered := []
  for offset in List.range length do
    rendered := rendered ++ [printVersionRange showUInt32 (← ops.get s.ranges (offset + 1))]
  return "[" ++ joinComma rendered ++ "]"

/-- `Base.show(io::IO,s::VersionSpec)`. -/
/-
Julia source: base/version.jl:605-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, s::VersionSpec)
    print(io, "VersionSpec(")
    if length(s.ranges) == 1
        print(io, '"', s.ranges[1], '"')
    else
        print(io, "[")
        for i in 1:length(s.ranges)
            1 < i && print(io, ", ")
            print(io, '"', s.ranges[i], '"')
        end
        print(io, ']')
    end
    return print(io, ")")
end
```
-/

def showVersionSpec {R E : Type} (ops : RangeVectorOps R E)
    (showUInt32 : VInt → String) (s : VersionSpec R) : Except E String := do
  let length ← ops.length s.ranges
  if length == 1 then
    return "VersionSpec(\"" ++ printVersionRange showUInt32 (← ops.get s.ranges 1) ++ "\")"
  let mut rendered := []
  for offset in List.range length do
    rendered := rendered ++ ["\"" ++ printVersionRange showUInt32
      (← ops.get s.ranges (offset + 1)) ++ "\""]
  return "VersionSpec([" ++ joinComma rendered ++ "])"

/-- `Base.minimum(v::VersionSpec)`. -/
/-
Julia source: base/version.jl:620-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.minimum(v::VersionSpec) = minimum(v.ranges[1])
```
-/

def minimumVersionSpec {R E : Type} (ops : RangeVectorOps R E) (v : VersionSpec R) : Except E VersionBound := do
  let r ← ops.get v.ranges 1
  pure (minimumVersionRange r)

/-! ## Compatibility specifiers -/

/-- A regex alternative in `ver_regs`, with matching and conversion as typed callees. -/
structure SpecifierPattern (Re Match E : Type) where
  regex : Re
  occursin : Re → String → Except E Bool
  matchRegex : Re → String → Except E (Option Match)
  interval : Option Match → Except E VersionRange

structure SemverIntervalOps (Match E : Type) where
  captures : Match → List (Option String)
  parseInt : String → Except E Int
  liftBound : Jl VersionBound → Except E VersionBound
  lessPrefix : String → Except E Bool
  equalPrefix : String → Except E Bool
  greaterEqualPrefix : String → Except E Bool
  assertionError : String → E
  errorException : String → E

def makeSemverBound {Match E : Type} (ops : SemverIntervalOps Match E)
    (values : List Int) : Except E VersionBound :=
  ops.liftBound (versionBoundVararg makeVersionBound (values.map intValue))

def captureAt (captures : List (Option String)) (index : Nat) : Option String :=
  match captures[index - 1]? with
  | some value => value
  | none => none

def requiredCapture {E : Type} (error : E) (captures : List (Option String)) (index : Nat) : Except E String :=
  match captureAt captures index with
  | some value => pure value
  | none => .error error

def parseCapturedInt {Match E : Type} (ops : SemverIntervalOps Match E)
    (captures : List (Option String)) (index : Nat) : Except E Int := do
  ops.parseInt (← requiredCapture (ops.errorException "parse(Int, nothing)") captures index)

def significantCaptureCount (captures : List (Option String)) : Nat :=
  ((captures.filterMap id).length) - 1

/-- `semver_interval(m::RegexMatch)` with capture arity and conversion order. -/
/-
Julia source: base/version.jl:650-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function semver_interval(m::RegexMatch)
    @assert length(m.captures) == 4 "invalid match"
    n_significant = count(x -> x !== nothing, m.captures) - 1
    typ, _major, _minor, _patch = m.captures
    major = parse(Int, _major)
    minor = (n_significant < 2) ? 0 : parse(Int, _minor)
    patch = (n_significant < 3) ? 0 : parse(Int, _patch)
    if n_significant == 3 && major == 0 && minor == 0 && patch == 0
        error("invalid version: \"0.0.0\"")
    end
    # Default type is :caret
    vertyp = (typ == "" || typ == "^") ? :caret : :tilde
    v0 = VersionBound((major, minor, patch))
    return if vertyp === :caret
        if major != 0
            return VersionRange(v0, VersionBound((v0[1],)))
        elseif minor != 0
            return VersionRange(v0, VersionBound((v0[1], v0[2])))
        else
            if n_significant == 1
                return VersionRange(v0, VersionBound((0,)))
            elseif n_significant == 2
                return VersionRange(v0, VersionBound((0, 0)))
            else
                return VersionRange(v0, VersionBound((0, 0, v0[3])))
            end
        end
    else
        if n_significant == 3 || n_significant == 2
            return VersionRange(v0, VersionBound((v0[1], v0[2])))
        else
            return VersionRange(v0, VersionBound((v0[1],)))
        end
    end
end
```
-/

def semverInterval {Match E : Type} (ops : SemverIntervalOps Match E)
    (m : Match) : Except E VersionRange := do
  let captures := ops.captures m
  if captures.length != 4 then throw (ops.assertionError "invalid match")
  let nSignificant := significantCaptureCount captures
  let typ ← requiredCapture (ops.errorException "missing semver type") captures 1
  let major ← parseCapturedInt ops captures 2
  let minor ← if nSignificant < 2 then pure 0 else parseCapturedInt ops captures 3
  let patch ← if nSignificant < 3 then pure 0 else parseCapturedInt ops captures 4
  if nSignificant == 3 && major == 0 && minor == 0 && patch == 0 then
    throw (ops.errorException "invalid version: \"0.0.0\"")
  let vertypCaret := typ == "" || typ == "^"
  let v0 ← makeSemverBound ops [major, minor, patch]
  if vertypCaret then
    if major != 0 then
      return makeVersionRange v0 (← makeSemverBound ops [v0.t.1.val])
    else if minor != 0 then
      return makeVersionRange v0 (← makeSemverBound ops [v0.t.1.val, v0.t.2.1.val])
    else if nSignificant == 1 then
      return makeVersionRange v0 (← makeSemverBound ops [0])
    else if nSignificant == 2 then
      return makeVersionRange v0 (← makeSemverBound ops [0, 0])
    else
      return makeVersionRange v0 (← makeSemverBound ops [0, 0, v0.t.2.2.val])
  else if nSignificant == 3 || nSignificant == 2 then
    return makeVersionRange v0 (← makeSemverBound ops [v0.t.1.val, v0.t.2.1.val])
  else
    return makeVersionRange v0 (← makeSemverBound ops [v0.t.1.val])

/-- `_inf = VersionBound("*")`. -/
/-
Julia source: base/version.jl:686-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _inf = VersionBound("*")
```
-/

def versionBoundInfinity : VersionBound :=
  ⟨(JInt.lit .u32 0, JInt.lit .u32 0, JInt.lit .u32 0), 0⟩

/-- `inequality_interval(m::RegexMatch)`, preserving prefix checks and order. -/
/-
Julia source: base/version.jl:687-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function inequality_interval(m::RegexMatch)
    @assert length(m.captures) == 4 "invalid match"
    typ, _major, _minor, _patch = m.captures
    n_significant = count(x -> x !== nothing, m.captures) - 1
    major = parse(Int, _major)
    minor = (n_significant < 2) ? 0 : parse(Int, _minor)
    patch = (n_significant < 3) ? 0 : parse(Int, _patch)
    if n_significant == 3 && major == 0 && minor == 0 && patch == 0
        error("invalid version: 0.0.0")
    end
    v = VersionBound(major, minor, patch)
    if occursin(r"^<\s*$", typ)
        nil = VersionBound(0, 0, 0)
        if v[3] == 0
            if v[2] == 0
                v1 = VersionBound(v[1] - 1)
            else
                v1 = VersionBound(v[1], v[2] - 1)
            end
        else
            v1 = VersionBound(v[1], v[2], v[3] - 1)
        end
        return VersionRange(nil, v1)
    elseif occursin(r"^=\s*$", typ)
        return VersionRange(v)
    elseif occursin(r"^>=\s*$", typ) || occursin(r"^≥\s*$", typ)
        return VersionRange(v, _inf)
    else
        error("invalid prefix $typ")
    end
end
```
-/

def inequalityInterval {Match E : Type} (ops : SemverIntervalOps Match E)
    (m : Match) : Except E VersionRange := do
  let captures := ops.captures m
  if captures.length != 4 then throw (ops.assertionError "invalid match")
  let typ ← requiredCapture (ops.errorException "missing prefix") captures 1
  let nSignificant := significantCaptureCount captures
  let major ← parseCapturedInt ops captures 2
  let minor ← if nSignificant < 2 then pure 0 else parseCapturedInt ops captures 3
  let patch ← if nSignificant < 3 then pure 0 else parseCapturedInt ops captures 4
  if nSignificant == 3 && major == 0 && minor == 0 && patch == 0 then
    throw (ops.errorException "invalid version: 0.0.0")
  let v ← makeSemverBound ops [major, minor, patch]
  if ← ops.lessPrefix typ then
    let nil ← makeSemverBound ops [0, 0, 0]
    let b ← if v.t.2.2.val == 0 then
      if v.t.2.1.val == 0 then makeSemverBound ops [v.t.1.val - 1]
      else makeSemverBound ops [v.t.1.val, v.t.2.1.val - 1]
    else makeSemverBound ops [v.t.1.val, v.t.2.1.val, v.t.2.2.val - 1]
    return makeVersionRange nil b
  else if ← ops.equalPrefix typ then
    return makeVersionRange v v
  else if ← ops.greaterEqualPrefix typ then
    let inf := versionBoundInfinity
    return makeVersionRange v inf
  else
    throw (ops.errorException ("invalid prefix " ++ typ))

/-- `hyphen_interval(m::RegexMatch)`, parsing lower then upper components. -/
/-
Julia source: base/version.jl:719-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hyphen_interval(m::RegexMatch)
    @assert length(m.captures) == 6 "invalid match"
    _lower_major, _lower_minor, _lower_patch, _upper_major, _upper_minor, _upper_patch = m.captures
    if isnothing(_lower_minor)
        lower_bound = VersionBound(parse(Int, _lower_major))
    elseif isnothing(_lower_patch)
        lower_bound = VersionBound(
            parse(Int, _lower_major),
            parse(Int, _lower_minor)
        )
    else
        lower_bound = VersionBound(
            parse(Int, _lower_major),
            parse(Int, _lower_minor),
            parse(Int, _lower_patch)
        )
    end
    if isnothing(_upper_minor)
        upper_bound = VersionBound(parse(Int, _upper_major))
    elseif isnothing(_upper_patch)
        upper_bound = VersionBound(
            parse(Int, _upper_major),
            parse(Int, _upper_minor)
        )
    else
        upper_bound = VersionBound(
            parse(Int, _upper_major),
            parse(Int, _upper_minor),
            parse(Int, _upper_patch)
        )
    end
    return VersionRange(lower_bound, upper_bound)
end
```
-/

def hyphenInterval {Match E : Type} (ops : SemverIntervalOps Match E)
    (m : Match) : Except E VersionRange := do
  let captures := ops.captures m
  if captures.length != 6 then throw (ops.assertionError "invalid match")
  let lowerMajor ← parseCapturedInt ops captures 1
  let lower ← if (captureAt captures 2).isNone then
      makeSemverBound ops [lowerMajor]
    else if (captureAt captures 3).isNone then
      makeSemverBound ops [lowerMajor, ← parseCapturedInt ops captures 2]
    else
      makeSemverBound ops [lowerMajor, ← parseCapturedInt ops captures 2, ← parseCapturedInt ops captures 3]
  let upperMajor ← parseCapturedInt ops captures 4
  let upper ← if (captureAt captures 5).isNone then
      makeSemverBound ops [upperMajor]
    else if (captureAt captures 6).isNone then
      makeSemverBound ops [upperMajor, ← parseCapturedInt ops captures 5]
    else
      makeSemverBound ops [upperMajor, ← parseCapturedInt ops captures 5, ← parseCapturedInt ops captures 6]
  return makeVersionRange lower upper

structure SemverOps (Re Match R E : Type) where
  patterns : List (SpecifierPattern Re Match E)
  strip : String → String
  splitComma : String → List String
  rangeVectors : RangeVectorOps R E
  errorException : String → E

/-- `version = ...` and `ver_regs`, supplied as the ordered regex alternatives. -/
/-
Julia source: base/version.jl:753-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const version = "v?([0-9]+?)(?:\\.([0-9]+?))?(?:\\.([0-9]+?))?"
const ver_regs =
    Pair{Regex, Any}[
    Regex("^([~^]?)?$version\$") => semver_interval, # 0.5 ^0.4 ~0.3.2
    Regex("^((?:≥\\s*)|(?:>=\\s*)|(?:=\\s*)|(?:<\\s*)|(?:=\\s*))v?$version\$") => inequality_interval, # < 0.2 >= 0.5,2
    Regex("^[\\s]*$version[\\s]*?\\s-\\s[\\s]*?$version[\\s]*\$") => hyphen_interval, # 0.7 - 1.3
```
-/

def firstSpecifierRange {Re Match E : Type} (patterns : List (SpecifierPattern Re Match E))
    (version : String) : Except E (Option VersionRange) := do
  match patterns with
  | [] => pure none
  | pattern :: rest => do
      if ← pattern.occursin pattern.regex version then
        return some (← pattern.interval (← pattern.matchRegex pattern.regex version))
      else firstSpecifierRange rest version

/-- `semver_spec(s::String; throw=true)`. -/
/-
Julia source: base/version.jl:626-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function semver_spec(s::String; throw = true)
    ranges = VersionRange[]
    for ver in strip.(split(strip(s), ','))
        range = nothing
        found_match = false
        for (ver_reg, f) in ver_regs
            if occursin(ver_reg, ver)
                range = f(match(ver_reg, ver))
                found_match = true
                break
            end
        end
        if !found_match
            if throw
                error("invalid version specifier: \"$s\"")
            else
                return nothing
            end
        end
        push!(ranges, range)
    end
    return VersionSpec(ranges)
end
```
-/

def semverSpec {Re Match R E : Type} (ops : SemverOps Re Match R E)
    (s : String) (throwOnInvalid : Bool := true) : Except E (Option (VersionSpec R)) := do
  let ranges ← ops.rangeVectors.fromList []
  let versions := (ops.splitComma (ops.strip s)).map ops.strip
  for version in versions do
    match ← firstSpecifierRange ops.patterns version with
    | some range => ops.rangeVectors.push ranges range
    | none =>
        if throwOnInvalid then
          throw (ops.errorException ("invalid version specifier: \"" ++ s ++ "\""))
        else
          return none
  return some (← makeVersionSpec ops.rangeVectors ranges)

/-- `EditionNumber(v::VersionNumber)`. -/
/-
Julia source: base/version.jl:763-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
EditionNumber(v::VersionNumber) = (Int(v.major), Int(v.minor))
```
-/

def editionNumber (v : VersionNumber) : JInt .i64 × JInt .i64 :=
  (JInt.lit .i64 v.major.val, JInt.lit .i64 v.minor.val)

/-- `VersionedParse(v::VersionNumber)`. -/
/-
Julia source: base/version.jl:764-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
VersionedParse(v::VersionNumber) = VersionedParse(EditionNumber(v))
```
-/

def versionedParse {α : Type} (construct : JInt .i64 × JInt .i64 → α)
    (v : VersionNumber) : α := construct (editionNumber v)

end JuliaLean.base.version

namespace JuliaLean.IntFuncsCov.Version

open JuliaLean
open JuliaLean.VersionNumbers


structure Bound where
  t : Nat × Nat × Nat
  n : Nat
  deriving DecidableEq, Repr

def vnum (major minor patch : Int) : VersionNumber :=
  ⟨JInt.lit .u32 major, JInt.lit .u32 minor, JInt.lit .u32 patch, [], []⟩

def egetD {ε α : Type} (x : Except ε α) (d : α) : α :=
  match x with
  | .ok a => a
  | .error _ => d

def pairLE (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

def tripleLE (a b : Nat × Nat × Nat) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && pairLE a.2 b.2)

def boundOfInts (xs : List Int) : Jl Bound := do
  if 3 < xs.length then .error (.argumentError "VersionBound has at most three components")
  else
    let ys ← xs.mapM fun x => (JInt.convert (IntTy.u32.name) .u32 x).map (·.val.toNat)
    pure ⟨(ys.getD 0 0, ys.getD 1 0, ys.getD 2 0), ys.length⟩

def boundComponent (b : Bound) : Nat → Nat
  | 0 => b.t.1
  | 1 => b.t.2.1
  | _ => b.t.2.2

def prefixCmp (a b : Bound) (n : Nat) : Int :=
  (List.range n).foldl (fun r i =>
    if r ≠ 0 then r
    else if boundComponent a i < boundComponent b i then -1
    else if boundComponent b i < boundComponent a i then 1
    else 0) 0

def islessLL (a b : Bound) : Bool :=
  let c := prefixCmp a b (min a.n b.n)
  if c < 0 then true else if c > 0 then false else decide (a.n < b.n)

def islessUU (a b : Bound) : Bool :=
  let c := prefixCmp a b (min a.n b.n)
  if c < 0 then true else if c > 0 then false else decide (b.n < a.n)

def vparts (v : VersionNumber) : Nat × Nat × Nat :=
  (v.major.val.toNat, v.minor.val.toNat, v.patch.val.toNat)

def lowerAccepts (b : Bound) (v : VersionNumber) : Bool :=
  b.n = 0 ||
  (b.n = 1 && b.t.1 ≤ (vparts v).1) ||
  (b.n = 2 && pairLE (b.t.1, b.t.2.1) ((vparts v).1, (vparts v).2.1)) ||
  (3 ≤ b.n && tripleLE b.t (vparts v))

def upperAccepts (v : VersionNumber) (b : Bound) : Bool :=
  b.n = 0 ||
  (b.n = 1 && (vparts v).1 ≤ b.t.1) ||
  (b.n = 2 && pairLE ((vparts v).1, (vparts v).2.1) (b.t.1, b.t.2.1)) ||
  (3 ≤ b.n && tripleLE (vparts v) b.t)

def isJoinable (up lo : Bound) : Bool :=
  if up.n = 0 ∧ lo.n = 0 then true
  else
    let l := min up.n lo.n
    let c := prefixCmp up lo (if up.n = lo.n then l - 1 else l)
    if c > 0 then true
    else if c < 0 then false
    else if up.n = lo.n ∧ 0 < up.n then
      decide (boundComponent lo (up.n - 1) ≤ boundComponent up (up.n - 1) + 1)
    else true

structure Range where
  lower : Bound
  upper : Bound
  deriving DecidableEq, Repr

def range (lo hi : Bound) : Range := if lo.t = hi.t then ⟨hi, hi⟩ else ⟨lo, hi⟩

def rangeEmpty (r : Range) : Bool :=
  let c := prefixCmp r.lower r.upper (min r.lower.n r.upper.n)
  decide (0 < c)

def rangeMember (v : VersionNumber) (r : Range) : Bool :=
  lowerAccepts r.lower v && upperAccepts v r.upper

def rangeIntersect (a b : Range) : Range :=
  range (if islessLL a.lower b.lower then b.lower else a.lower)
    (if islessUU a.upper b.upper then a.upper else b.upper)

structure Spec where
  ranges : List Range
  deriving DecidableEq, Repr

def specMember (v : VersionNumber) (s : Spec) : Bool :=
  s.ranges.any (rangeMember v)

def scanRange (versions : List VersionNumber) (r : Range) (n : Nat)
    (dest : List Bool) : List Bool :=
  let rec skip (i : Nat) : Nat :=
    if h : i < n then
      if lowerAccepts r.lower (versions.getD i (vnum 0 0 0)) then i else skip (i + 1)
    else i
  termination_by n - i
  decreasing_by omega
  let rec mark (i : Nat) (d : List Bool) : List Bool :=
    if h : i < n then
      if upperAccepts (versions.getD i (vnum 0 0 0)) r.upper then mark (i + 1) (d.set i true)
      else d
    else d
  termination_by n - i
  decreasing_by omega
  mark (skip 0) dest

def matchesSpecRange (dest : List Bool) (versions : List VersionNumber)
    (spec : Spec) (n : Nat) : Jl (List Bool) :=
  if versions.length ≠ n then .error (.argumentError "invalid version list")
  else if dest.length < n then .error (.argumentError "invalid dest length")
  else
    let dest := (List.replicate n false) ++ dest.drop n
    .ok (spec.ranges.foldl (fun d r => scanRange versions r n d) dest)


def scanOne : Range → List VersionNumber → List Bool
  | _, [] => []
  | r, v :: vs =>
    if lowerAccepts r.lower v then
      if upperAccepts v r.upper then true :: scanOne r vs
      else List.replicate (vs.length + 1) false
    else false :: scanOne r vs

def matchesSpecSimple (versions : List VersionNumber) (s : Spec) : List Bool :=
  s.ranges.foldl (fun out r => List.zipWith (· || ·) out (scanOne r versions))
    (List.replicate versions.length false)

def bnd (xs : List Int) : Bound := egetD (boundOfInts xs) ⟨(0, 0, 0), 0⟩


inductive SemverInput where
  | valid
  | unmatched
  | lessZero
  | zeroExact
  deriving DecidableEq

def semverSpec (s : SemverInput) (throw : Bool) : Jl (Option Spec) :=
  match s with
  | .valid => .ok (some ⟨[range (bnd [1]) (bnd [1])]⟩)
  | .unmatched => if throw then .error (.argumentError "invalid version specifier") else .ok none
  | .lessZero => .error (.inexactError "UInt32")
  | .zeroExact => .error (.argumentError "invalid version: 0.0.0")

end JuliaLean.IntFuncsCov.Version
