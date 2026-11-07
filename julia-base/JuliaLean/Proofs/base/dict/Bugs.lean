import JuliaLean.Proofs.base.dict.Props
import JuliaLean.Proofs.base.set.Claims

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

theorem SameOutcome.okB_eq {α β : Type} {A : DR α} {B : DR β} {R : α → β → Prop}
    (h : SameOutcome A B R) : okB A = okB B := by
  cases A <;> cases B <;> simp_all [SameOutcome, okB]

end JuliaLean.Dicts
