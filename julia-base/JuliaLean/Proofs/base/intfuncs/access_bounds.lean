import JuliaLean.Proofs.base.abstractarray.common.input_invariants
import JuliaLean.base.intfuncs

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Union of buffer positions stored by all writer branches, after the shared
`IntPrint.string` model computes the allocation from the integer, base, pad,
sign, digit count, and selected writer. -/
def integerStringAccesses (t bty : IntTy) (n : JInt t) (base : JInt bty) (pad : Int) :
    Jl (Nat × List Nat) :=
  (ParsePrint.IntPrint.string n base pad).map fun buf =>
    (buf.length, oneBasedLoop buf.length)

/-- The fixed-width allocation and store union for `bitstring`. -/
def bitstringAccesses (t : IntTy) (x : JInt t) : Nat × List Nat :=
  let buf := ParsePrint.IntPrint.bitstring x
  (buf.length, oneBasedLoop buf.length)

/-- `_dec_d100[1 + remainder]` after `divrem(_, 100)`. -/
def decimalPairIndex (remainder : Nat) : Nat := remainder % 100 + 1

/-- Digit-table index and table length for `_base`, after the documented base
check and `rem`/`mod` computation. -/
def genericBaseDigitAccess (base x : Int) : Option (Nat × Nat) :=
  let magnitude := base.natAbs
  if 2 ≤ magnitude ∧ magnitude ≤ 62 then
    let index := (x % (magnitude : Int)).toNat + 1
    some (index, if magnitude ≤ 36 then 36 else 62)
  else none

/-- Store/table access union for integer formatting plus the `eachindex(x)`
loop of `clamp!`, `base/intfuncs.jl:878-1165,1518-1523`. -/
def IntegerFormattingSafe : Prop :=
  (∀ t bty n base pad result, integerStringAccesses t bty n base pad = .ok result →
    ∀ i ∈ result.2, inOneBased result.1 i) ∧
  (∀ t (x : JInt t) i, i ∈ (bitstringAccesses t x).2 →
    inOneBased (bitstringAccesses t x).1 i) ∧
  (∀ remainder, inOneBased 100 (decimalPairIndex remainder)) ∧
  (∀ base x index length, genericBaseDigitAccess base x = some (index, length) →
    inOneBased length index) ∧
  (∀ (α : Type) (a : LinearArray α) i, i ∈ linearArrayIndices a →
    inAxis a.first a.values.length i)

theorem integerFormattingSafe_proven : IntegerFormattingSafe := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t bty n base pad result hr i hi
    unfold integerStringAccesses at hr
    cases hs : ParsePrint.IntPrint.string n base pad with
    | error e =>
      rw [hs] at hr
      simp only [Except.map] at hr
      cases hr
    | ok buf =>
      rw [hs] at hr
      simp only [Except.map, Except.ok.injEq] at hr
      subst result
      simp only [oneBasedLoop, List.mem_map, List.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      unfold inOneBased
      omega
  · intro t x i hi
    simp only [bitstringAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [bitstringAccesses]
    unfold inOneBased
    omega
  · intro remainder
    unfold decimalPairIndex inOneBased
    have hm := Nat.mod_lt remainder (by decide : 0 < 100)
    omega
  · intro base x index length hi
    unfold genericBaseDigitAccess at hi
    dsimp only at hi
    split at hi
    · rename_i hb
      split at hi <;> cases hi
      all_goals unfold inOneBased
      all_goals have hm := Int.emod_nonneg x (by omega : (base.natAbs : Int) ≠ 0)
      all_goals have hl := Int.emod_lt_of_pos x (by omega : 0 < (base.natAbs : Int))
      all_goals omega
    · contradiction
  · intro α a i hi
    simp only [linearArrayIndices, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inAxis
    omega

end JuliaLean.MemSafety.G3
