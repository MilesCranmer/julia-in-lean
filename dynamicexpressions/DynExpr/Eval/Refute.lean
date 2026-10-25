import DynExpr.Eval.Props
import DynExpr.Eval.Scalars

/-!
Concrete counterexamples for the refuted evaluator properties. Each mirrors a
Julia reproducer in `repro/eval-*.jl`.
-/

namespace DynExpr.Eval.Ex
open DynExpr.Eval

/-- `inv(x) = one(x) / x`. -/
def inv1 : List JF → JF
  | [x] => JF.div (.fin 1) x
  | _ => .nan
/-- Unary `-`. -/
def neg1 : List JF → JF
  | [x] => JF.neg x
  | _ => .nan
/-- Binary `+`. -/
def add2 : List JF → JF
  | [x, y] => JF.add x y
  | _ => .nan
/-- Binary `/`. -/
def div2 : List JF → JF
  | [x, y] => JF.div x y
  | _ => .nan

/-- `OperatorEnum(1 => (inv, -), 2 => (+, /))`. -/
def ops : OpEnum JF := ⟨[[inv1, neg1], [add2, div2]]⟩

/-- Extensions are never called in these examples. -/
def noImpl {T : Type} : ExtImpl T := ⟨fun _ _ => .error .boundsError⟩

/-- `is_valid_array` on `JF` arrays holds exactly for all-finite arrays. -/
theorem jf_exact : ArrayValidExact JF := by
  intro a
  rw [jf_isValidArray, Array.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hx)
    exact h i hi
  · intro h i hi
    exact h _ (by simp)

/-- One sample with `x1 = 0`. -/
def XZero : JMat JF := ⟨1, 1, #[.fin 0], rfl⟩

/-- The constant tree `inv(inv(0.0))`, whose value is `0`. -/
def tConstInvInv : Tree JF := .branch 1 [.branch 1 [.const (.fin 0)]]

/-- The non-constant tree `x1 + inv(inv(0.0))`, whose value is `x1`. -/
def tXPlusConst : Tree JF := .branch 1 [.feature 1, tConstInvInv]

theorem tXPlusConst_wf : tXPlusConst.WF 2 ops.nops 1 := by
  simp [tXPlusConst, tConstInvInv, Tree.WF, OpEnum.nops, ops]

/-- With `early_exit=false`, the constant subtree still stops evaluation
(`dispatch_constant_tree` exits on `inv(0.0) = Inf`, src/Evaluate.jl:1001-1039). -/
example : (evalTreeArray {} noImpl 2 tXPlusConst XZero ops (plainCtx false false .none)).map
    Prod.snd = .ok false := by decide +kernel

theorem evalNoEarlyDenote_refuted : ¬ evalNoEarlyDenote := by
  intro h
  obtain ⟨out, h1, _⟩ := h JF {} noImpl 2 ops XZero tXPlusConst (by decide) tXPlusConst_wf
    (by decide)
  have h2 : (evalTreeArray {} noImpl 2 tXPlusConst XZero ops (plainCtx false false .none)).map
      Prod.snd = .ok false := by decide +kernel
  rw [h1] at h2
  cases h2

/-- `differentiable_eval_tree_array` on the constant leaf `NaN`. -/
example : obs (differentiableEvalTreeArray ops XZero (.const .nan)) = .ok ([.nan], true) := by
  decide +kernel

/-- `one(T) * v == v` for `JF`. -/
theorem jf_one_mul (v : JF) : JlScalar.mul JlScalar.one v = v := by
  cases v with
  | fin x => show JF.mul (.fin 1) (.fin x) = .fin x; simp [JF.mul]
  | nan => rfl
  | posInf => decide
  | negInf => decide

theorem evalDiffFlag_refuted : ¬ evalDiffFlag := by
  intro h
  have := h JF ops XZero (.const .nan) [.nan] (by simp [Tree.WF]) jf_one_mul (by decide +kernel)
    .nan (by simp)
  exact absurd this (by decide)

end DynExpr.Eval.Ex
