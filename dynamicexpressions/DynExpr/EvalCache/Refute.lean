import DynExpr.EvalCache.Props
import DynExpr.Eval.Refute

/-!
Concrete counterexamples for the refuted cache properties. Each mirrors a
Julia reproducer `repro/evalcache-*.jl` run against PR #219.
-/

namespace DynExpr.EvalCache.Ex
open DynExpr.Eval DynExpr.EvalCache

/-- `inv(x1)` with `OperatorEnum(1 => (inv, -), 2 => (+, /))`. -/
def tInv : Tree JF := .branch 1 [.feature 1]

theorem tInv_wf : tInv.WF 2 Eval.Ex.ops.nops 1 := by
  simp [tInv, Tree.WF, OpEnum.nops, Eval.Ex.ops]

/-- The same operator slots with `-` first: unary operator 1 is now `-`. -/
def opsSwapped : OpEnum JF := ⟨[[Eval.Ex.neg1, Eval.Ex.inv1], [Eval.Ex.add2, Eval.Ex.div2]]⟩

theorem tInv_wf' : tInv.WF 2 opsSwapped.nops 1 := by
  simp [tInv, Tree.WF, OpEnum.nops, opsSwapped]

/-- `EvalContext(; early_exit=ee)`. -/
def ctxE (ee : Bool) : EvalContext JF := ⟨false, false, ee, .none, true⟩

/-- One sample, `x1 = v`. -/
def X1 (v : JF) : JMat JF := ⟨1, 1, #[v], rfl⟩

/-- Observable form of a run. -/
def obsRun (r : Jl (List (JVec JF × Bool))) : Jl (List (List JF × Bool)) :=
  r.map (List.map fun p => (p.1.toList, p.2))

/-! In-place mutation of `X`: the same identity `0` with `x1 = 1`, then `x1 = 2`. -/

def callsMutX : List (Call JF) :=
  [⟨tInv, X1 (.fin 1), 0, Eval.Ex.ops, 0, ctxE true⟩, ⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩]

/-- The second call returns the stale `inv(1) = 1`; uncached gives `inv(2) = 1/2`. -/
example : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsMutX UCache.empty) =
    .ok [([.fin 1], true), ([.fin 1], true)] := by decide +kernel
example : obsRun (runPlain {} Eval.Ex.noImpl 2 callsMutX) =
    .ok [([.fin 1], true), ([JF.div (.fin 1) (.fin 2)], true)] := by decide +kernel

theorem evalCacheMutateX_refuted : ¬ evalCacheMutateX := by
  intro h
  have he := h JF {} Eval.Ex.noImpl 2 8 true callsMutX (by decide)
    (by
      intro k hk
      simp only [callsMutX, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> exact ⟨tInv_wf, rfl⟩)
    (by
      intro k hk k' hk' _
      simp only [callsMutX, List.mem_cons, List.not_mem_nil, or_false] at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> rfl)
  have hne : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsMutX UCache.empty) ≠
      obsRun (runPlain {} Eval.Ex.noImpl 2 callsMutX) := by decide +kernel
  exact hne (by rw [he])

/-! Operators that change behaviour behind the same identity `0`. -/

def callsMutOp : List (Call JF) :=
  [⟨tInv, X1 (.fin 1), 0, Eval.Ex.ops, 0, ctxE true⟩, ⟨tInv, X1 (.fin 1), 0, opsSwapped, 0, ctxE true⟩]

/-- The second call returns the stale `inv(1) = 1`; uncached gives `-1`. -/
example : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsMutOp UCache.empty) =
    .ok [([.fin 1], true), ([.fin 1], true)] := by decide +kernel
example : obsRun (runPlain {} Eval.Ex.noImpl 2 callsMutOp) =
    .ok [([.fin 1], true), ([.fin (-1)], true)] := by decide +kernel

theorem evalCacheMutateOp_refuted : ¬ evalCacheMutateOp := by
  intro h
  have he := h JF {} Eval.Ex.noImpl 2 8 true callsMutOp (by decide)
    (by
      intro k hk
      simp only [callsMutOp, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact ⟨tInv_wf, rfl⟩
      · exact ⟨tInv_wf', rfl⟩)
    (by
      intro k hk k' hk' _
      simp only [callsMutOp, List.mem_cons, List.not_mem_nil, or_false] at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> rfl)
  have hne : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsMutOp UCache.empty) ≠
      obsRun (runPlain {} Eval.Ex.noImpl 2 callsMutOp) := by decide +kernel
  exact hne (by rw [he])

/-! One cache shared by an early_exit=false and an early_exit=true context. -/

def callsShared : List (Call JF) :=
  [⟨tInv, X1 .posInf, 0, Eval.Ex.ops, 0, ctxE false⟩,
    ⟨tInv, X1 .posInf, 0, Eval.Ex.ops, 0, ctxE true⟩]

/-- The strict call hits the entry `inv(Inf) = 0` and reports success;
uncached strict evaluation stops at the non-finite feature. -/
example : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsShared UCache.empty) =
    .ok [([.fin 0], true), ([.fin 0], true)] := by decide +kernel
example : obsRun (runPlain {} Eval.Ex.noImpl 2 callsShared) =
    .ok [([.fin 0], true), ([.posInf], false)] := by decide +kernel

theorem evalCacheSharedEarly_refuted : ¬ evalCacheSharedEarly := by
  intro h
  have stab : ∀ k ∈ callsShared, ∀ k' ∈ callsShared, k.X = k'.X ∧ k.o = k'.o := by
    intro k hk k' hk'
    simp only [callsShared, List.mem_cons, List.not_mem_nil, or_false] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have he := h JF {} Eval.Ex.noImpl 2 8 callsShared (by decide)
    (by
      intro k hk
      simp only [callsShared, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> exact tInv_wf)
    (fun k hk k' hk' _ => (stab k hk k' hk').1) (fun k hk k' hk' _ => (stab k hk k' hk').2)
  have hne : obsRun (runCached {} Eval.Ex.noImpl 2 8 callsShared UCache.empty) ≠
      obsRun (runPlain {} Eval.Ex.noImpl 2 callsShared) := by decide +kernel
  exact hne (by rw [he])

/-! Two threads on different inputs. Thread A (`X = [1]`, identity 1) passes
the identity check; thread B (`X = [2]`, identity 2) resets, misses and stores
`inv(2)`; thread A then reads B's entry. -/

def jobA : Job JF := ⟨⟨1, 0, 8, false⟩, X1 (.fin 1), Eval.Ex.ops, 1, 1, {}⟩
def jobB : Job JF := ⟨⟨2, 0, 8, false⟩, X1 (.fin 2), Eval.Ex.ops, 1, 1, {}⟩

/-- A: check; B: check, read (miss), store; A: read (hit on B's entry). -/
def badSchedule : List Bool := [true, false, false, false, true]

/-- Observable form of a thread result. -/
def obsRes (r : Jl (ResultOk JF)) : Jl (List JF × Bool × Ident) :=
  r.map fun x => (x.x.toList, x.ok, x.id)

/-- Whether some finished thread's result differs from its uncached result. -/
def raceBad (ja jb : Job JF) (sched : List Bool) : Bool :=
  match race ja jb sched (.start, .start, UCache.empty) with
  | (.done ra, .done rb, _) => obsRes ra != obsRes ja.plain || obsRes rb != obsRes jb.plain
  | _ => false

example : (match race jobA jobB badSchedule (.start, .start, UCache.empty) with
    | (.done ra, _, _) => obsRes ra
    | _ => .error .boundsError) = .ok ([JF.div (.fin 1) (.fin 2)], true, .fresh) := by
  decide +kernel
example : obsRes jobA.plain = .ok ([.fin 1], true, .fresh) := by decide +kernel

theorem raceBad_true : raceBad jobA jobB badSchedule = true := by decide +kernel

theorem not_raceOK (ja jb : Job JF) (sched : List Bool) (h : raceBad ja jb sched = true) :
    ¬ RaceOK ja jb (race ja jb sched (.start, .start, UCache.empty)) := by
  unfold raceBad at h
  intro hok
  split at h
  · rename_i ra rb c heq
    rw [heq] at hok
    obtain ⟨h1, h2⟩ := hok
    rw [h1, h2] at h
    simp at h
  · simp at h

theorem evalCacheRace_refuted : ¬ evalCacheRace := by
  intro h
  have hwf : (Tree.branch 1 [.feature 1] : Tree JF).WF 2 Eval.Ex.ops.nops 1 := tInv_wf
  exact not_raceOK jobA jobB badSchedule raceBad_true
    (h JF jobA jobB badSchedule UCache.empty ⟨hwf, by decide⟩ ⟨hwf, by decide⟩ rfl
      (fun h => absurd h (by decide)) (fun _ => rfl)
      (fun h => by simp [UCache.empty] at h) (fun h => by simp [UCache.empty] at h))

end DynExpr.EvalCache.Ex
