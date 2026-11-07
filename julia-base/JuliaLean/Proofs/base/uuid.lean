import JuliaLean.base.uuid
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.uuid.Round1

open JuliaLean JuliaLean.base.uuid

/-!
Equality in the next statement is equality of the immutable single-field
UInt128 representation, used as an independent observable value relation.
UUID has no equality override: generic == falls back to egal, and isequal
falls back to ==. Immutable values of the same type compare their contents
at the bit level (operators.jl:112,156–169,343–350). Thus this relation does
not assume an isless law or introduce an equality-callee correctness axiom.
The actual islessUUID subject calls the concrete source integer comparison.
-/

/-- UUID comparison is a strict total order, consistent with unsigned payload
order and with equality of immutable UUID values.
Julia source: base/uuid.jl:121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:151–170,206–225,343–350
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UUIDStrictOrderCorrect : Prop :=
  (∀ a : UUID, islessUUID a a = false) ∧
  (∀ a b c : UUID,
    islessUUID a b = true → islessUUID b c = true → islessUUID a c = true) ∧
  (∀ a b : UUID,
    (a = b ∧ islessUUID a b = false ∧ islessUUID b a = false) ∨
    (a ≠ b ∧ islessUUID a b = true ∧ islessUUID b a = false) ∨
    (a ≠ b ∧ islessUUID a b = false ∧ islessUUID b a = true)) ∧
  (∀ a b : UUID, islessUUID a b = true ↔ a.value.val < b.value.val)

end JuliaLean.Proofs.base.uuid.Round1

namespace JuliaLean.Proofs.base.uuid

open JuliaLean.Registry

end JuliaLean.Proofs.base.uuid

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean JuliaLean.base.uuid

theorem uuidUnsignedBitsValue (x : JInt .u128) :
    ((JuliaLean.C.fromJInt x).toNat : Int) = x.val := by
  have hx := x.property
  change 0 ≤ x.val ∧ x.val ≤ (2 ^ 128 : Int) - 1 at hx
  have hlt : x.val < (2 ^ 128 : Int) := by omega
  simp only [JuliaLean.C.fromJInt, BitVec.toNat_ofInt, IntTy.bits]
  change ((x.val % (2 ^ 128 : Int)).toNat : Int) = x.val
  rw [Int.emod_eq_of_lt hx.1 hlt, Int.toNat_of_nonneg hx.1]

theorem uuidLessPayload (a b : UUID) :
    islessUUID a b = decide (a.value.val < b.value.val) := by
  have ha := uuidUnsignedBitsValue a.value
  have hb := uuidUnsignedBitsValue b.value
  simp only [islessUUID, JuliaLean.base.operators.islessReal,
    JuliaLean.base.int.lt_BitUnsigned, JuliaLean.base.int.ult_int,
    JuliaLean.C.jlUltInt, decide_eq_decide]
  omega

theorem uuidPayloadExt {a b : UUID} (h : a.value.val = b.value.val) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      apply congrArg UUID.mk
      exact Subtype.ext h

/-- uuid-total-order -/
theorem UuidTotalOrder_proven : JuliaLean.Proofs.base.uuid.Round1.UUIDStrictOrderCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp only [uuidLessPayload, Int.lt_irrefl, decide_false]
  · intro a b c hab hbc
    rw [uuidLessPayload, decide_eq_true_iff] at hab hbc ⊢
    exact Int.lt_trans hab hbc
  · intro a b
    by_cases heq : a.value.val = b.value.val
    · have hab := uuidPayloadExt heq
      subst b
      left
      refine ⟨rfl, ?_, ?_⟩ <;>
        simp only [uuidLessPayload, Int.lt_irrefl, decide_false]
    · have hne : a ≠ b := by
        intro hab
        exact heq (congrArg (fun u : UUID => u.value.val) hab)
      by_cases hlt : a.value.val < b.value.val
      · right
        left
        refine ⟨hne, ?_, ?_⟩
        · simp only [uuidLessPayload, hlt, decide_true]
        · have hrev : ¬ b.value.val < a.value.val := by omega
          simp only [uuidLessPayload, hrev, decide_false]
      · right
        right
        refine ⟨hne, ?_, ?_⟩
        · simp only [uuidLessPayload, hlt, decide_false]
        · have hrev : b.value.val < a.value.val := by omega
          simp only [uuidLessPayload, hrev, decide_true]
  · intro a b
    simp only [uuidLessPayload, decide_eq_true_iff]

end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.Proofs.base.uuid

open JuliaLean.Registry
def entries : List Entry := [
  { id := "uuid-total-order",
    juliaFile := "base/uuid.jl",
    juliaFns := ["isless(a::UUID,b::UUID)"],
    statement := "UUID isless is irreflexive and transitive, exactly one of equality, a<b and b<a holds for every pair, and the order agrees with unsigned 128-bit payload order.",
    source := "base/uuid.jl:121; base/operators.jl:151-170,206-225,343-350",
    status := .proven,
    prop := ``Round1.UUIDStrictOrderCorrect,
    thm := some ``JuliaLean.ChatGPT.Batch4.Group22.UuidTotalOrder_proven }
]

end JuliaLean.Proofs.base.uuid
