import JuliaLean.VersionNumbers.Model
import JuliaLean.ParsePrint.IntParse

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
  | [a] => return ⟨(← JInt.convert .u32 a.val, z, z), 1⟩
  | [a, b] => return ⟨(← JInt.convert .u32 a.val, ← JInt.convert .u32 b.val, z), 2⟩
  | [a, b, c] => return ⟨(← JInt.convert .u32 a.val, ← JInt.convert .u32 b.val, ← JInt.convert .u32 c.val), 3⟩
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

/-- A bound `VersionBound(tin)` can produce: `n ≤ 3` and zeros past `n`. -/
def WellFormed (b : VersionBound) : Prop :=
  b.n ≤ 3 ∧ (b.n < 1 → b.t.1.val = 0) ∧ (b.n < 2 → b.t.2.1.val = 0) ∧ (b.n < 3 → b.t.2.2.val = 0)

/-- `VersionRange(string(r))` reconstructs a range with the same members as `r`
(`show(r)` prints `VersionRange("<string(r)>")`, `base/version.jl:466`). -/
def RangePrintRoundtrip : Prop :=
  ∀ lo hi, WellFormed lo → WellFormed hi →
    ∃ r', parseRange (printRange (mkRange lo hi)) = .ok r' ∧
      ∀ v, inRange v r' = inRange v (mkRange lo hi)

/-- `VersionRange("*-2")`: lower bound `*`, upper bound `2`. -/
def starToTwo : VersionRange := mkRange boundStar ⟨(u32 2, u32 0, u32 0), 1⟩

theorem starToTwo_parse : parseRange (ascii "*-2") = .ok starToTwo := by decide +kernel

theorem starToTwo_print : printRange starToTwo = ascii "0 -2.0.0" := by decide +kernel

theorem starToTwo_reparse :
    parseRange (printRange starToTwo) = .ok ⟨⟨(u32 0, u32 0, u32 0), 1⟩, ⟨(u32 2, u32 0, u32 0), 3⟩⟩ := by
  decide +kernel

/-- `v"2.5.0"`. -/
def v250 : VersionNumber := ⟨u32 2, u32 5, u32 0, [], []⟩

theorem rangePrintRoundtrip_refuted : ¬ RangePrintRoundtrip := by
  intro h
  obtain ⟨r', hp, hin⟩ := h boundStar ⟨(u32 2, u32 0, u32 0), 1⟩ (by unfold WellFormed; decide) (by unfold WellFormed; decide)
  have e : mkRange boundStar ⟨(u32 2, u32 0, u32 0), 1⟩ = starToTwo := rfl
  rw [e, starToTwo_reparse] at hp
  cases hp
  have := hin v250
  revert this
  decide

end JuliaLean.VersionNumbers
