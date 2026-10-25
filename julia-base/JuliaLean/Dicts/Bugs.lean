import JuliaLean.Dicts.Props

/-!
# Refutations

Each counterexample is evaluated by the kernel (`decide +kernel`) on a
concrete table built by API calls from `Dict()`.
-/

namespace JuliaLean.Dicts

/-- The value of a successful call, `d` otherwise. -/
def getOkD {ε α : Type} (e : Except ε α) (d : α) : α :=
  match e with
  | .ok a => a
  | .error _ => d

theorem eq_ok_of_okB {ε α : Type} (e : Except ε α) (d : α) (h : okB e = true) :
    e = .ok (getOkD e d) := by
  cases e with
  | ok a => rfl
  | error _ => simp [okB] at h

/-- `Int` keys hashed by their value (any lawful hash shows the bugs). -/
def natOps : KeyOps Nat := { hash := fun x => JInt.wrap .u64 x, eq := fun a b => a == b }

theorem natOps_lawful : natOps.Lawful where
  refl := by intro a; simp [natOps]
  symm := by intro a b h; simp [natOps] at h ⊢; exact h.symm
  trans := by intro a b c h1 h2; simp [natOps] at h1 h2 ⊢; exact h1.trans h2
  hash_eq := by intro a b h; simp [natOps] at h; rw [h]

theorem natOps_generic : GenericMax natOps := rfl

theorem natOps_maxValues : MaxValuesOK natOps := Or.inl (by decide)

theorem reach_of_ok {K V : Type} (o : KeyOps K) (ops : List (DOp K V)) (hs : OpsSmall ops)
    (h1 : okB (runOps o ops) = true) (h2 : okB (rrun o ops) = true) :
    Reach o (getOkD (runOps o ops) Table.empty) (getOkD (rrun o ops) []) :=
  ⟨ops, hs, eq_ok_of_okB _ _ h1, eq_ok_of_okB _ _ h2⟩

theorem reach_empty {K V : Type} (o : KeyOps K) : Reach o (Table.empty : Table K V) [] :=
  ⟨[], ⟨by simp, rfl⟩, rfl, rfl⟩

/-! ## `sizehint!` with a hint whose `3n` overflows hangs -/

/-- `d = Dict(i => i for i in 0:16)`. -/
def opsHang : List (DOp Nat Nat) := (List.range 17).map fun i => .base (.set i i)

theorem sizehintAgrees_refuted : ¬ SizehintAgrees := by
  intro h
  have hr := reach_of_ok natOps opsHang ⟨by decide, by decide⟩ (by decide +kernel) (by decide +kernel)
  obtain ⟨t', ht', -⟩ := h Nat Nat natOps natOps_lawful natOps_maxValues _ _ hr
    (JInt.lit .i64 (2 ^ 62)) true
  have hd : okB (sizehint natOps (getOkD (runOps natOps opsHang) Table.empty)
      (JInt.lit .i64 (2 ^ 62)) true) = false := by decide +kernel
  rw [ht'] at hd
  simp [okB] at hd

/-- The model's outcome is non-termination, not an error. -/
theorem sizehint_hang_diverges :
    (match sizehint natOps (getOkD (runOps natOps opsHang) Table.empty) (JInt.lit .i64 (2 ^ 62)) true with
     | .error .diverges => true
     | _ => false) = true := by decide +kernel

/-! ## `in!` skips the `isequal` check of `push!` -/

/-- A narrower element type (`Float32` in the reproducer): converting rounds to
an even number, and a value is `isequal` only to itself (`0.1 != 0.1f0`). -/
def roundConv : Conv Nat Nat where
  isa := fun _ => none
  convert := fun q => pure (q / 2 * 2)
  hash := fun q => JInt.wrap .u64 q
  iseq := fun q k => q == k

theorem roundConv_lawful : ConvLawful natOps roundConv where
  hash_eq := by intro q k h; simp [roundConv] at h; simp [roundConv, natOps, h]
  iseq_eq := by intro q k k' h1 h2; simp [roundConv, natOps] at h1 h2 ⊢; exact h1.trans h2
  isa_convert := by intro q k h; simp [roundConv] at h

theorem SameOutcome.okB_eq {α β : Type} {A : DR α} {B : DR β} {R : α → β → Prop}
    (h : SameOutcome A B R) : okB A = okB B := by
  cases A <;> cases B <;> simp_all [SameOutcome, okB]

theorem inBangEquiv_refuted : ¬ InBangEquiv := by
  intro h
  have hp := (h Nat Nat natOps roundConv natOps_lawful roundConv_lawful natOps_generic
    Table.empty [] (reach_empty natOps) 1).okB_eq
  revert hp
  decide +kernel

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

theorem unionPushEquiv_refuted : ¬ UnionPushEquiv := by
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
