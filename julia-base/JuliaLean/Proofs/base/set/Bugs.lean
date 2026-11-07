import JuliaLean.Proofs.base.dict.Bugs
import JuliaLean.Proofs.base.set.Claims

namespace JuliaLean.Dicts

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
  subtype_isa := by intro h; simp [roundConv] at h

theorem inBangEquiv_refuted : ¬ InBangEquiv := by
  intro h
  have hp := (h Nat Nat natOps roundConv natOps_lawful roundConv_lawful natOps_generic
    Table.empty [] (reach_empty natOps) 1).okB_eq
  revert hp
  decide +kernel

end JuliaLean.Dicts
