import DynExpr.EvalCache.Proofs

/-!
What a single node `op(x_f)` stores in a fresh cache (evalcache-store-rule).
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- `cached_deg1_eval` on a fresh cache within the size limit: reset, miss,
evaluate, and store under the early-exit rule. -/
theorem cachedDeg1_fresh (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (op feat : Nat)
    (g : List T → T) (b : Buf T) (hsz : 0 < ce.szT) (hop1 : 1 ≤ op)
    (hop2 : op ≤ (opsOf o 1).length) (hf1 : 1 ≤ feat) (hf2 : feat ≤ X.nrows)
    (hlim : (opsOf o 1).length * X.nrows ≤ maxEntries ce.szT X.ncols) (row : JVec T)
    (hrow : X.row feat = .ok row) :
    cachedDeg1 cx ce o X op g feat (b, UCache.empty) =
      (getArray b X.ncols).bind (fun p =>
        if cx.earlyExit && !isValidArray row then
          .ok (some (⟨row, false, nextId b⟩, p.2),
            ⟨some (ce.xid, ce.oid), (opsOf o 1).length, X.nrows, fun _ _ => none⟩)
        else (degnEval g [row]).bind (fun out => .ok (some (⟨out, true, nextId b⟩, p.2),
          if !cx.earlyExit || isValidArray out then
            (⟨some (ce.xid, ce.oid), (opsOf o 1).length, X.nrows, fun _ _ => none⟩ : UCache T).store
              op feat out
          else ⟨some (ce.xid, ce.oid), (opsOf o 1).length, X.nrows, fun _ _ => none⟩))) := by
  have hne : (opsOf o 1).length ≠ 0 := by omega
  have hnr : X.nrows ≠ 0 := by omega
  have hemp : ((opsOf o 1).length == 0 || X.nrows == 0) = false := by simp [hne, hnr]
  simp only [cachedDeg1, UCache.empty, resetIfNew, resetDims, hlim, ↓reduceIte, UCache.isEmpty,
    beq_iff_eq, hne, hnr, Bool.or_self, decide_false, Bool.false_eq_true, ne_eq,
    reduceCtorEq, not_false_eq_true, true_and, show ce.szT ≠ 0 by omega, and_false]
  simp only [hop1, hop2, hf1, hf2, and_self, not_true_eq_false, ↓reduceIte, hemp,
    Bool.false_eq_true]
  rw [evalT_feature cx o X feat b row hf1 hf2 hrow]
  cases getArray b X.ncols with
  | error e => rfl
  | ok p =>
    simp only [Except.map, Except.bind, jl_ok_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hx : (cx.earlyExit && !isValidArray row) = true
    · simp only [hx, ↓reduceIte]; rfl
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      cases degnEval g [row] <;> rfl

theorem evalCacheStoreRule_proof : evalCacheStoreRule := by
  intro T _ ext impl D op f X o ec xid oid szT hsz hw hturbo hbump hlim
  have hw' := hw
  simp only [Tree.WF] at hw'
  have hfw := hw'.2.2 (.feature f) (by simp)
  simp only [Tree.WF] at hfw
  have hop1 : 1 ≤ op := hw'.2.1.1
  have hop2 : op ≤ o.nops 1 := by simpa using hw'.2.1.2.1
  have hnops : o.nops 1 = (opsOf o 1).length := by simp [OpEnum.nops, opsOf]
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 1 op (by omega) hop1 hop2
  have hidx := idxOp_lookup o 1 op g (by omega) hg
  obtain ⟨row, hrow, _⟩ := JMat.row_exists X f hfw.1 hfw.2.1
  refine ⟨g, row, _, hg, hrow, degnEval_one g row, ?_⟩
  intro r c' he
  let cx : Ctx := ⟨ec.earlyExit, ec.useFused, D⟩
  let ce : CEnv := ⟨xid, oid, szT, ec.bumper⟩
  have hfresh := cachedDeg1_fresh cx ce o X op f g ec.buffer hsz hop1 (by omega) hfw.1 hfw.2.1
    hlim row hrow
  -- every dispatch branch reaches `viaCache` for this feature child
  have hdisp : ∃ fb, evalTC cx ce o X (.branch op [.feature f]) (ec.buffer, UCache.empty) =
      viaCache cx ce o X op g f fb (ec.buffer, UCache.empty) := by
    simp only [evalTC, isConstantL, isConstant, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      deg1DispatchC]
    split
    · simp only [hidx, jl_ok_bind]; exact ⟨_, rfl⟩
    · simp only [hnif, jl_ok_bind]; exact ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ := hdisp
  simp only [evalTreeArrayC, hturbo, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    evalArrC] at he
  change (do
    let (r, s) ← evalTC cx ce o X (.branch op [.feature f]) (ec.buffer, UCache.empty)
    pure ((r.x, r.ok && (!cx.earlyExit || isValidArray r.x)), s.2)) = Except.ok (r, c') at he
  rw [hfb] at he
  simp only [viaCache, show ce.bumper = false from hbump, Bool.false_eq_true, ↓reduceIte,
    hfresh] at he
  cases hga : getArray ec.buffer X.ncols with
  | error e => rw [hga] at he; cases he
  | ok p =>
    rw [hga] at he
    simp only [Except.bind, jl_ok_bind] at he
    by_cases hx : (ec.earlyExit && !isValidArray row) = true
    · have hx' : (cx.earlyExit && !isValidArray row) = true := hx
      simp only [hx', ↓reduceIte] at he
      simp only [Except.bind, jl_ok_bind, emb] at he
      cases he
      have hee : ec.earlyExit = true := by simp_all
      have hrv : isValidArray row = false := by simp_all
      simp [hee, hrv]
    · have hx' : ¬ (cx.earlyExit && !isValidArray row) = true := hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte, degnEval_one, Except.bind, jl_ok_bind,
        emb] at he
      cases he
      by_cases hee : ec.earlyExit = true
      · have hrv : isValidArray row = true := by simp_all
        simp only [cx, hee, hrv, Bool.not_true, Bool.false_or, Bool.true_and]
        split <;> simp [UCache.store]
      · simp [cx, hee, UCache.store]

/-- The hypotheses of evalcache-store-rule hold for `inv(x1)` on one sample. -/
example : 0 < 8 ∧ (Tree.branch 1 [.feature 1] : Tree JF).WF 2 Eval.Ex.ops.nops (Ex.X1 (.fin 1)).nrows ∧
    (Ex.ctxE true).turbo = false ∧ (Ex.ctxE true).bumper = false ∧
    (opsOf Eval.Ex.ops 1).length * (Ex.X1 (.fin 1)).nrows ≤ maxEntries 8 (Ex.X1 (.fin 1)).ncols :=
  ⟨by decide, Ex.tInv_wf, rfl, rfl, by decide⟩

end DynExpr.EvalCache
