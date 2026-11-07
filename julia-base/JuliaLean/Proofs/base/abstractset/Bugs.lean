import JuliaLean.Proofs.base.dict.Bugs
import JuliaLean.Proofs.base.abstractset.Claims

namespace JuliaLean.Dicts

/-! ## `union!` stops before converting the remaining elements -/

def boolOps : KeyOps Bool where
  hash := fun b => JInt.wrap .u64 (if b then 1 else 0)
  eq := fun a b => a == b
  maxValues := JInt.lit .i64 2

theorem boolOps_lawful : boolOps.Lawful where
  refl := by intro a; simp [boolOps]
  symm := by intro a b h; simp [boolOps] at h ⊢; exact h.symm
  trans := by intro a b c h1 h2; simp [boolOps] at h1 h2 ⊢; exact h1.trans h2
  hash_eq := by intro a b h; simp [boolOps] at h; rw [h]

theorem boolOps_maxValues : MaxValuesOK boolOps := by
  right
  have hmv : boolOps.maxValues.val = 2 := by decide
  intro xs hxs
  rw [hmv]
  match xs, hxs with
  | [], _ => simp
  | [_], _ => simp
  | [_, _], _ => simp
  | a :: b :: c :: _, hxs =>
    simp only [List.pairwise_cons, List.mem_cons] at hxs
    cases a <;> cases b <;> cases c <;> simp [boolOps] at hxs

/-- `convert(Bool, x::Int)`: `0`, `1`, otherwise `InexactError`. -/
def intToBool : Conv Nat Bool where
  isa := fun _ => none
  convert := fun q =>
    if q = 0 then pure false else if q = 1 then pure true
    else throw (.jl (.inexactError "Bool"))
  hash := fun q => JInt.wrap .u64 q
  iseq := fun q b => q == (if b then 1 else 0)

theorem intToBool_lawful : ConvLawful boolOps intToBool where
  hash_eq := by
    intro q k h
    cases k <;> simp [intToBool] at h <;> simp [intToBool, boolOps, h]
  iseq_eq := by intro q k k' h1 h2; simp [boolOps] at h2; subst h2; exact h1
  isa_convert := by intro q k h; simp [intToBool] at h
  subtype_isa := by intro h; simp [intToBool] at h

def HistoricalUnionPushEquiv : Prop :=
  ∀ (K Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → MaxValuesOK o →
  ∀ (s : SetT K) ms, Reach o s ms → ∀ itr : List Q, itr.length ≤ 2 ^ 30 →
    SameOutcome (do
      let s ← sizehint o s (JInt.lit .i64 (s.count + itr.length)) false
      unionLoopHistorical o c s itr) (itr.foldlM (pushConv o c) s)
      (fun s₁ s₂ => ∀ y, setIn o s₁ y = setIn o s₂ y)

theorem unionPushEquiv_refuted : ¬ HistoricalUnionPushEquiv := by
  intro h
  have hp := h Bool Nat boolOps intToBool boolOps_lawful intToBool_lawful boolOps_maxValues
    Table.empty [] (reach_empty boolOps) [1, 0, 2] (by decide)
  have h1 := hp.okB_eq
  revert h1
  decide +kernel


/-! ## `issubset` of vectors switches from `==` to `isequal` above 70 elements -/

/-- `0.0`, `-0.0` and `1.0`: `0.0 == -0.0` but `!isequal(0.0, -0.0)`. -/
inductive Z3 where
  | pz | nz | one
  deriving DecidableEq

def z3Ops : KeyOps Z3 where
  hash := fun z => JInt.wrap .u64 (match z with | .pz => 0 | .nz => 1 | .one => 2)
  eq := fun a b => a == b

/-- `==` on the three floats. -/
def z3Eqeq : Z3 → Z3 → Bool
  | .one, .one => true
  | .one, _ => false
  | _, .one => false
  | _, _ => true

theorem z3Ops_lawful : z3Ops.Lawful where
  refl := by intro a; simp [z3Ops]
  symm := by intro a b h; simp [z3Ops] at h ⊢; exact h.symm
  trans := by intro a b c h1 h2; simp [z3Ops] at h1 h2 ⊢; exact h1.trans h2
  hash_eq := by intro a b h; simp [z3Ops] at h; rw [h]

theorem issubsetVecUsesIn_refuted : ¬ IssubsetVecUsesIn := by
  intro h
  have hp := h Z3 z3Ops z3Eqeq z3Ops_lawful rfl (by intro a b; cases a <;> cases b <;> rfl)
    [.pz] (.nz :: List.replicate 70 .one)
  have hd : (match issubsetVec z3Ops z3Eqeq [.pz] (.nz :: List.replicate 70 .one) with
      | .ok b => b | .error _ => true) = false := by decide +kernel
  rw [hp] at hd
  revert hd
  decide

/-- With 70 elements (no `Set` conversion) the same call returns `true`. -/
theorem issubsetVec_short :
    (match issubsetVec z3Ops z3Eqeq [.pz] (.nz :: List.replicate 69 .one) with
      | .ok b => b | .error _ => false) = true := by
  decide +kernel

end JuliaLean.Dicts
