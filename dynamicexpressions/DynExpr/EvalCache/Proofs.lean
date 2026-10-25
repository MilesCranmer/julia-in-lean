import DynExpr.EvalCache.Sim
import DynExpr.EvalCache.Refute

/-!
Proofs of the proven cache properties from the simulation `evalTC_sim`.
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

variable {T : Type} [JlScalar T]

theorem evalArrC_sim (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (b : Buf T) (c0 c : UCache T) (hsz : 0 < ce.szT) (hw : t.WF cx.D o.nops X.nrows)
    (hc : CInv cx.earlyExit ce X o c0 c) :
    ∃ c', CInv cx.earlyExit ce X o c0 c' ∧
      evalArrC cx ce o X t b c = (evalArr cx o X t b).map (fun r => (r, c')) := by
  obtain ⟨c', hc', he⟩ := evalTC_sim cx ce o X c0 hsz t hw b c hc
  refine ⟨c', hc', ?_⟩
  unfold evalArrC evalArr
  rw [he]
  cases evalT cx o X t b <;> rfl

theorem evalTreeArrayC_sim (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T) (X : JMat T)
    (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c0 c : UCache T) (hsz : 0 < szT)
    (hw : t.WF D o.nops X.nrows) (hc : CInv ec.earlyExit ⟨xid, oid, szT, ec.bumper⟩ X o c0 c) :
    ∃ c', CInv ec.earlyExit ⟨xid, oid, szT, ec.bumper⟩ X o c0 c' ∧
      evalTreeArrayC ext impl D t X o ec xid oid szT c =
        (evalTreeArray ext impl D t X o ec).map (fun r => (r, c')) := by
  unfold evalTreeArrayC evalTreeArray
  by_cases ht : ec.turbo = true
  · refine ⟨c, hc, ?_⟩
    simp only [ht, Bool.true_and]
    split
    · rfl
    · split
      · rfl
      · cases impl.turboEval t X <;> rfl
  · simp only [ht, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact evalArrC_sim ⟨ec.earlyExit, ec.useFused, D⟩ ⟨xid, oid, szT, ec.bumper⟩ o X t ec.buffer
      c0 c hsz hw hc

theorem cacheOK_empty (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T) :
    CacheOK ee szT xid oid X o (UCache.empty : UCache T) := fun h => by simp [UCache.empty] at h

theorem evalCacheSingle_proof : evalCacheSingle := by
  intro T _ ext impl D t X o ec xid oid szT c hsz hw hc
  obtain ⟨c', _, he⟩ := evalTreeArrayC_sim ext impl D t X o ec xid oid szT c c hsz hw ⟨Or.inl rfl, hc⟩
  exact ⟨c', he⟩

theorem evalCacheNode_proof : evalCacheNode := by
  intro T _ cx ce o X t b c hsz hw hc
  obtain ⟨c', _, he⟩ := evalTC_sim cx ce o X c hsz t hw b c ⟨Or.inl rfl, hc⟩
  exact ⟨c', he⟩

theorem evalCacheStored_proof : evalCacheStored := by
  intro T _ ext impl D t X o ec xid oid szT c hsz hw hc r c' he
  obtain ⟨c'', hinv, he2⟩ := evalTreeArrayC_sim ext impl D t X o ec xid oid szT c c hsz hw
    ⟨Or.inl rfl, hc⟩
  rw [he2] at he
  cases hp : evalTreeArray ext impl D t X o ec with
  | error e => rw [hp] at he; cases he
  | ok r0 =>
    rw [hp] at he
    cases he
    exact ⟨hinv.2, hinv.1⟩

theorem evalCacheLimit_proof : evalCacheLimit := by
  intro T _ ext impl D t X o ec xid oid szT c hsz hw hc hlim
  obtain ⟨c', hinv, he⟩ := evalTreeArrayC_sim ext impl D t X o ec xid oid szT c c hsz hw
    ⟨Or.inl rfl, hc⟩
  refine ⟨c', he, fun hk => ?_⟩
  have hcons := hinv.2 hk
  have hdims : c'.nu = 0 ∧ c'.nf = 0 := by
    have h1 := hcons.1
    simp only [resetDims, show ¬ ((opsOf o 1).length * X.nrows ≤ maxEntries szT X.ncols) by omega,
      ↓reduceIte, Prod.mk.injEq] at h1
    exact h1
  refine ⟨by simp [UCache.isEmpty, hdims.1], fun i f => ?_⟩
  cases hg : c'.get i f with
  | none => rfl
  | some v =>
    have := (hcons.2 i f v hg)
    omega

theorem evalCacheTurbo_proof : evalCacheTurbo := by
  intro T _ ext impl D t X o ec xid oid szT c ht
  unfold evalTreeArrayC evalTreeArray
  simp only [ht, Bool.true_and]
  split
  · rfl
  · split
    · rfl
    · cases impl.turboEval t X <;> rfl

theorem evalCacheCopy_proof : evalCacheCopy := by
  intro T _ ext impl D t X o ec xid oid szT c hsz hw
  refine ⟨rfl, ?_⟩
  obtain ⟨c', _, he⟩ := evalTreeArrayC_sim ext impl D t X o ec xid oid szT UCache.empty
    UCache.empty hsz hw ⟨Or.inl rfl, cacheOK_empty _ _ _ _ _ _⟩
  exact ⟨c', he⟩

omit [JlScalar T] in
theorem xStable_tail (k : Call T) (ks : List (Call T)) (h : XStable (k :: ks)) : XStable ks :=
  fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

omit [JlScalar T] in
theorem opsStable_tail (k : Call T) (ks : List (Call T)) (h : OpsStable (k :: ks)) : OpsStable ks :=
  fun a ha b hb => h a (by simp [ha]) b (by simp [hb])

theorem runCached_eq (ext : Ext) (impl : ExtImpl T) (D szT : Nat) (hsz : 0 < szT) (ee : Bool) :
    ∀ (ks : List (Call T)) (c : UCache T),
      (∀ k ∈ ks, k.t.WF D k.o.nops k.X.nrows ∧ k.ec.earlyExit = ee) → XStable ks → OpsStable ks →
      (∀ k ∈ ks, CacheOK ee szT k.xid k.oid k.X k.o c) →
      runCached ext impl D szT ks c = runPlain ext impl D ks
  | [], _, _, _, _, _ => rfl
  | k :: ks, c, hw, hx, ho, hc => by
    have hk := hw k (by simp)
    have hck : CInv k.ec.earlyExit ⟨k.xid, k.oid, szT, k.ec.bumper⟩ k.X k.o c c :=
      ⟨Or.inl rfl, by rw [hk.2]; exact hc k (by simp)⟩
    obtain ⟨c', hinv, he⟩ := evalTreeArrayC_sim ext impl D k.t k.X k.o k.ec k.xid k.oid szT c c
      hsz hk.1 hck
    have hrest : ∀ k' ∈ ks, CacheOK ee szT k'.xid k'.oid k'.X k'.o c' := by
      intro k' hk' hkey
      rcases hinv.1 with heq | hkk
      · subst heq
        exact hc k' (by simp [hk']) hkey
      · rw [hkey] at hkk
        simp only [Option.some.injEq, Prod.mk.injEq] at hkk
        rw [hx k' (by simp [hk']) k (by simp) hkk.1, ho k' (by simp [hk']) k (by simp) hkk.2]
        have := hinv.2 (by rw [hkey, hkk.1, hkk.2])
        rw [hk.2] at this
        exact this
    have ih := runCached_eq ext impl D szT hsz ee ks c' (fun k' hk' => hw k' (by simp [hk']))
      (xStable_tail k ks hx) (opsStable_tail k ks ho) hrest
    simp only [runCached, runPlain, he]
    cases evalTreeArray ext impl D k.t k.X k.o k.ec with
    | error e => rfl
    | ok r =>
      simp only [Except.map, jl_ok_bind]
      rw [ih]

theorem evalCacheSequence_proof : evalCacheSequence := by
  intro T _ ext impl D szT ee ks hsz hw hx ho
  exact runCached_eq ext impl D szT hsz ee ks UCache.empty hw hx ho
    (fun _ _ => cacheOK_empty _ _ _ _ _ _)

section examples
open DynExpr.EvalCache.Ex

/-- The hypotheses of evalcache-single, -node, -stored and -copy hold for
`inv(x1)` on one sample with a fresh cache. -/
example : 0 < 8 ∧ tInv.WF 2 Eval.Ex.ops.nops (X1 (.fin 1)).nrows ∧
    CacheOK true 8 0 0 (X1 (.fin 1)) Eval.Ex.ops UCache.empty :=
  ⟨by decide, tInv_wf, cacheOK_empty _ _ _ _ _ _⟩

/-- evalcache-limit: `sizeof(T) = 16 MiB` leaves room for one entry, below the
two unary operators times one feature. -/
example : maxEntries (16 * 1024 ^ 2) (X1 (.fin 1)).ncols <
    (opsOf Eval.Ex.ops 1).length * (X1 (.fin 1)).nrows := by decide

/-- evalcache-turbo: a turbo context. -/
example : (⟨true, false, true, .none, true⟩ : EvalContext JF).turbo = true := rfl

/-- evalcache-sequence: the same tree twice on one input satisfies the
hypotheses, and the second call reads the stored entry. -/
example : ∀ k ∈ ([⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩,
      ⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩] : List (Call JF)),
    k.t.WF 2 k.o.nops k.X.nrows ∧ k.ec.earlyExit = true := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> exact ⟨tInv_wf, rfl⟩

example : XStable ([⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩,
      ⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩] : List (Call JF)) ∧
    OpsStable ([⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩,
      ⟨tInv, X1 (.fin 2), 0, Eval.Ex.ops, 0, ctxE true⟩] : List (Call JF)) := by
  constructor <;>
  · intro k hk k' hk' _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> rfl

example : (do
    let (_, c) ← evalTreeArrayC {} Eval.Ex.noImpl 2 tInv (X1 (.fin 2)) Eval.Ex.ops (ctxE true) 0 0 8
      UCache.empty
    pure ((c.get 1 1).map Array.toList)) = Except.ok (some [JF.div (.fin 1) (.fin 2)]) := by
  decide +kernel

end examples

end DynExpr.EvalCache
