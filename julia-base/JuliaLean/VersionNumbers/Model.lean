import JuliaLean.Core
import JuliaLean.VersionNumbers.Regex

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
  else JInt.convert t (digitsValue pre)

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
  | .int x => do return .num (← JInt.convert .u64 x.val)
  | .str s => return .str s

/-- `VersionNumber(major::Integer, minor, patch, pre, bld)` for `Int` components,
`base/version.jl:84-89`. -/
def versionNumber (major minor patch : JInt .i64) (pre bld : List IdentArg := []) : Jl VersionNumber := do
  let ma ← JInt.convert .u32 major.val
  let mi ← JInt.convert .u32 minor.val
  let pa ← JInt.convert .u32 patch.val
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
def succU32 (x : JInt .u32) : Jl (JInt .u32) := JInt.convert .u32 (x.val + 1)

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
