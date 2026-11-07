import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.public_wrappers
/-! Unsigned order-preserving mappings from `base/sort.jl:2227-2310`
(master `bbfa0ce4150`).  A bit integer is its fixed-width bit pattern. -/

namespace JuliaLean.SortTuplesCov

def UIntMappingCorrect : Prop :=
  (∀ x, uintMapUnsigned x = x ∧ uintUnmapUnsigned x = x) ∧
  (∀ bits x, uintUnmapSigned bits (uintMapSigned bits x) = x) ∧
  (∀ c, uintUnmapChar (uintMapChar c) = c) ∧
  (∀ bits f x, uintMapReverse bits f x = wordMask bits ^^^ f x) ∧
  (∀ bits f x, uintUnmapReverse bits f x = f (wordMask bits ^^^ x)) ∧
  (∀ width reverse, uintMappable (.bits width) reverse = some width) ∧
  (∀ reverse, uintMappable .char reverse = some 32) ∧
  (∀ reverse, uintMappable .unsupported reverse = none)

theorem uintMappingCorrect : UIntMappingCorrect := by
  refine ⟨by simp [uintMapUnsigned, uintUnmapUnsigned], ?_,
    by simp [uintMapChar, uintUnmapChar], by simp [uintMapReverse],
    by simp [uintUnmapReverse], by simp [uintMappable], by simp [uintMappable],
    by simp [uintMappable]⟩
  intro bits x
  simp [uintMapSigned, uintUnmapSigned, Nat.xor_assoc]

def UIntMappingLoopsCorrect : Prop :=
  (∀ map v lo hi, uintMapBang map v lo hi =
    uintMapLoop map lo (hi - lo + 1).toNat v) ∧
  (∀ unmap v u lo hi off io, uintUnmapBang unmap v u lo hi off io =
    uintUnmapLoop unmap off lo io (hi - lo + 1).toNat v u)

theorem uintMappingLoopsCorrect : UIntMappingLoopsCorrect := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

def MaybeApplyInitialOptimizationsCorrect : Prop :=
  ∀ alg, maybeApplyInitialOptimizations alg =
    match alg with
    | .quick | .merge | .insertion => true
    | .other => false

theorem maybeApplyInitialOptimizationsCorrect : MaybeApplyInitialOptimizationsCorrect := by
  intro alg
  cases alg <;> rfl

end JuliaLean.SortTuplesCov
