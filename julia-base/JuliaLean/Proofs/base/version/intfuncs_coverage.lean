import JuliaLean.base.version
import JuliaLean.Proofs.base.version
/-!
Executable models for the `VersionBound`, `VersionRange`, `VersionSpec`, and
compatibility-specifier methods added to `base/version.jl` on master `bbfa0ce4150`.
-/

namespace JuliaLean.IntFuncsCov.Version

open JuliaLean
open JuliaLean.VersionNumbers

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

/-- The comment at `base/version.jl:530-533` claims correctness on unsorted inputs. -/
def MatchesSpecRangeUnsorted : Prop :=
  ∀ (versions : List VersionNumber) (s : Spec),
    matchesSpecSimple versions s = versions.map (fun v => specMember v s)

theorem matchesSpecRangeUnsorted_refuted : ¬ MatchesSpecRangeUnsorted := by
  intro h
  let versions := [vnum 2 0 0, vnum 1 2 0]
  let s : Spec := ⟨[range ⟨(1, 0, 0), 2⟩ ⟨(1, 5, 0), 2⟩]⟩
  have bad := h versions s
  revert bad
  decide +kernel

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
