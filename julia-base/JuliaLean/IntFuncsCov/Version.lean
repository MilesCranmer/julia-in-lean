import JuliaLean.VersionNumbers

/-!
Executable models for the `VersionBound`, `VersionRange`, `VersionSpec`, and
compatibility-specifier methods added to `base/version.jl` on master `bbfa0ce4150`.
-/

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
    let ys ← xs.mapM fun x => (JInt.convert .u32 x).map (·.val.toNat)
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

def VersionBoundRangeBehavior : Prop :=
  (∀ xs : List Int, 3 < xs.length →
    boundOfInts xs = .error (.argumentError "VersionBound has at most three components")) ∧
  (∀ a b : Bound, islessLL a b =
    let c := prefixCmp a b (min a.n b.n)
    if c < 0 then true else if c > 0 then false else decide (a.n < b.n)) ∧
  (∀ v : VersionNumber, ∀ r : Range,
    rangeMember v r = (lowerAccepts r.lower v && upperAccepts v r.upper)) ∧
  (∀ a b : Range, rangeMember (vnum 0 0 0) (rangeIntersect a b) =
    rangeMember (vnum 0 0 0)
      (range (if islessLL a.lower b.lower then b.lower else a.lower)
        (if islessUU a.upper b.upper then a.upper else b.upper)))

theorem versionBoundRangeBehavior : VersionBoundRangeBehavior := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  intro xs h
  simp [boundOfInts, h]

def VersionSpecBehavior : Prop :=
  (∀ (v : VersionNumber) (s : Spec), specMember v s = s.ranges.any (rangeMember v)) ∧
  (∀ (dest : List Bool) (versions : List VersionNumber) (s : Spec) (n : Nat),
    matchesSpecRange dest versions s n =
      if versions.length ≠ n then .error (.argumentError "invalid version list")
      else if dest.length < n then .error (.argumentError "invalid dest length")
      else .ok (s.ranges.foldl (fun d r => scanRange versions r n d)
        (List.replicate n false ++ dest.drop n)))

theorem versionSpecBehavior : VersionSpecBehavior := by
  exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

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

/-- The comment at `base/version.jl:530-533` claims correctness on unsorted inputs. -/
def MatchesSpecRangeUnsorted : Prop :=
  ∀ (versions : List VersionNumber) (s : Spec),
    matchesSpecSimple versions s = versions.map (fun v => specMember v s)

def bnd (xs : List Int) : Bound := egetD (boundOfInts xs) ⟨(0, 0, 0), 0⟩

theorem matchesSpecRangeUnsorted_refuted : ¬ MatchesSpecRangeUnsorted := by
  intro h
  let versions := [vnum 2 0 0, vnum 1 2 0]
  let s : Spec := ⟨[range ⟨(1, 0, 0), 2⟩ ⟨(1, 5, 0), 2⟩]⟩
  have bad := h versions s
  revert bad
  decide +kernel

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

def SemverSpecNoThrow : Prop := ∀ s : SemverInput, ∃ r, semverSpec s false = .ok r

theorem semverSpecNoThrow_refuted : ¬ SemverSpecNoThrow := by
  intro h
  obtain ⟨r, hr⟩ := h .lessZero
  cases hr

def SemverSourceBehavior : Prop :=
  (∀ throw : Bool, semverSpec .valid throw = .ok (some ⟨[range (bnd [1]) (bnd [1])]⟩)) ∧
  semverSpec .unmatched false = .ok none ∧
  semverSpec .lessZero false = .error (.inexactError "UInt32") ∧
  semverSpec .zeroExact false = .error (.argumentError "invalid version: 0.0.0")

theorem semverSourceBehavior : SemverSourceBehavior := by
  exact ⟨fun _ => rfl, rfl, rfl, rfl⟩

def VersionNumberSourceBehavior : Prop :=
  EqStructural ∧ HashConsistent ∧ IslessTotalOrder ∧ SemverPrecedence ∧
  TypeminTypemax ∧ BoundsBracket ∧ ThisMonotone ∧ NextOverflow ∧ NextLeast

theorem versionNumberSourceBehavior : VersionNumberSourceBehavior := by
  exact ⟨eqStructural_proven, hashConsistent_proven, islessTotalOrder_proven,
    semverPrecedence_proven, typeminTypemax_proven, boundsBracket_proven,
    thisMonotone_proven, nextOverflow_proven, nextLeast_proven⟩

end JuliaLean.IntFuncsCov.Version
