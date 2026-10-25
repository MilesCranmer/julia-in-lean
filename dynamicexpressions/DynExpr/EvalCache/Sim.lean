import DynExpr.EvalCache.Props
import DynExpr.Eval.Lemmas

/-!
Simulation of the uncached evaluator by the cached one: every cached step
returns the uncached result with some cache state attached, and that state
satisfies an invariant. The combinators are proved for any invariant; the
cache step `viaCache` for `CInv`.
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

variable {T : Type} [JlScalar T]

section sim
variable (Inv : UCache T → Prop)

/-- `v` is `u` with a cache state satisfying `Inv` attached. -/
def SimR (u : Jl (ResultOk T × Buf T)) (v : Jl (ResultOk T × St T)) : Prop :=
  ∃ c, Inv c ∧ v = u.map (emb c)

/-- Step `v` simulates step `u` from every state satisfying `Inv`. -/
def SimF (u : Buf T → Jl (ResultOk T × Buf T)) (v : St T → Jl (ResultOk T × St T)) : Prop :=
  ∀ b c, Inv c → SimR Inv (u b) (v (b, c))

/-- Children-loop version of `SimR`. -/
def SimRCh (u : Jl ((ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)))
    (v : Jl ((ResultOk T × St T) ⊕ (List (JVec T × Ident) × St T))) : Prop :=
  ∃ c, Inv c ∧ v = u.map (Sum.map (emb c) (fun p => (p.1, (p.2, c))))

theorem simR_error (e : JlError) (c : UCache T) (hc : Inv c) :
    SimR Inv (.error e) (.error e) := ⟨c, hc, rfl⟩

theorem liftB_sim (k : Buf T → Jl (ResultOk T × Buf T)) : SimF Inv k (liftB k) :=
  fun _ c hc => ⟨c, hc, rfl⟩

theorem bind_sim {α : Type} (G : Jl α) (K : α → Jl (ResultOk T × Buf T))
    (K' : α → Jl (ResultOk T × St T)) (c : UCache T) (hc : Inv c)
    (hK : ∀ g, G = .ok g → SimR Inv (K g) (K' g)) :
    SimR Inv (G >>= K) (G >>= K') := by
  cases hG : G with
  | error e => exact ⟨c, hc, rfl⟩
  | ok g => exact hK g hG

theorem checked_sim (cx : Ctx) (ev : Buf T → Jl (ResultOk T × Buf T))
    (ev' : St T → Jl (ResultOk T × St T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T))
    (k' : JVec T → Ident → St T → Jl (ResultOk T × St T))
    (hev : SimF Inv ev ev') (hk : ∀ x i, SimF Inv (k x i) (k' x i)) :
    SimF Inv (checked cx ev k) (checkedC cx ev' k') := by
  intro b c hc
  obtain ⟨c1, hc1, he⟩ := hev b c hc
  unfold checked checkedC
  rw [he]
  rcases hu : ev b with e | ⟨r, b1⟩
  · exact ⟨c1, hc1, rfl⟩
  · simp only [Except.map, emb, jl_ok_bind]
    by_cases h1 : r.ok = true
    · by_cases h2 : (cx.earlyExit && !isValidArray r.x) = true
      · simp only [h1, h2, Bool.not_true, ↓reduceIte]
        exact ⟨c1, hc1, rfl⟩
      · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hk _ _ b1 c1 hc1
    · simp only [h1, Bool.not_false, ↓reduceIte]
      exact ⟨c1, hc1, rfl⟩

theorem unfused1_sim (cx : Ctx) (fop : Jl (List T → T)) (evC : Buf T → Jl (ResultOk T × Buf T))
    (evC' : St T → Jl (ResultOk T × St T)) (h : SimF Inv evC evC') :
    SimF Inv (unfused1 cx fop evC) (unfused1C cx fop evC') :=
  checked_sim Inv cx _ _ _ _ h (fun _ _ => liftB_sim Inv _)

theorem unfused2_sim (cx : Ctx) (fop : Jl (List T → T))
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (evL' evR' : St T → Jl (ResultOk T × St T))
    (hL : SimF Inv evL evL') (hR : SimF Inv evR evR') :
    SimF Inv (unfused2 cx fop evL evR) (unfused2C cx fop evL' evR') :=
  checked_sim Inv cx _ _ _ _ hL (fun _ _ => checked_sim Inv cx _ _ _ _ hR
    (fun _ _ => liftB_sim Inv _))

theorem deg2Dispatch_sim (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat) (l r : Tree T)
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (evL' evR' : St T → Jl (ResultOk T × St T))
    (hL : SimF Inv evL evL') (hR : SimF Inv evR evR') :
    SimF Inv (deg2Dispatch cx o X op l r evL evR) (deg2DispatchC cx o X op l r evL' evR') := by
  intro b c hc
  unfold deg2Dispatch deg2DispatchC
  by_cases hlim : operatorLimit < (opsOf o 2).length
  · simp only [hlim, ↓reduceIte]
    exact unfused2_sim Inv cx _ _ _ _ _ hL hR b c hc
  simp only [hlim, ↓reduceIte]
  apply bind_sim Inv _ _ _ c hc
  intro f _
  have r0 := checked_sim Inv cx evL evL' _ _ hL (fun xl cid => liftB_sim Inv (deg2R0 cx X f r xl cid)) b c hc
  have l0 := checked_sim Inv cx evR evR' _ _ hR (fun xr cid => liftB_sim Inv (deg2L0 cx X f l xr cid)) b c hc
  by_cases hA : (cx.useFused && isLeaf l && isLeaf r) = true
  · simp only [hA, ↓reduceIte]
    exact liftB_sim Inv _ b c hc
  simp only [hA, Bool.false_eq_true, ↓reduceIte]
  by_cases hB : (cx.useFused && isLeaf r) = true
  · simp only [hB, ↓reduceIte]
    rcases l with _ | _ | ⟨lop, _ | ⟨ll, _ | ⟨lr, _ | ⟨_, _⟩⟩⟩⟩ <;> try exact r0
    by_cases hC : (isNum T && isLeaf ll && isLeaf lr) = true
    · simp only [hC, ↓reduceIte]
      exact bind_sim Inv _ _ _ c hc (fun g _ => liftB_sim Inv _ b c hc)
    · simp only [hC, Bool.false_eq_true, ↓reduceIte]
      exact r0
  simp only [hB, Bool.false_eq_true, ↓reduceIte]
  by_cases hD : (cx.useFused && isLeaf l) = true
  · simp only [hD, ↓reduceIte]
    rcases r with _ | _ | ⟨rop, _ | ⟨rl, _ | ⟨rr, _ | ⟨_, _⟩⟩⟩⟩ <;> try exact l0
    by_cases hC : (isNum T && isLeaf rl && isLeaf rr) = true
    · simp only [hC, ↓reduceIte]
      exact bind_sim Inv _ _ _ c hc (fun g _ => liftB_sim Inv _ b c hc)
    · simp only [hC, Bool.false_eq_true, ↓reduceIte]
      exact l0
  simp only [hD, Bool.false_eq_true, ↓reduceIte]
  exact unfused2_sim Inv cx _ _ _ _ _ hL hR b c hc

theorem finish_sim (o : OpEnum T) (d op : Nat)
    (u : Jl ((ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)))
    (v : Jl ((ResultOk T × St T) ⊕ (List (JVec T × Ident) × St T))) (h : SimRCh Inv u v) :
    SimR Inv (u >>= degnFinish o d op) (v >>= degnFinishC o d op) := by
  obtain ⟨c, hc, rfl⟩ := h
  rcases u with e | (⟨r, b⟩ | ⟨xs, b⟩)
  · exact ⟨c, hc, rfl⟩
  · exact ⟨c, hc, rfl⟩
  · exact ⟨c, hc, rfl⟩

end sim

/-! The cache invariant and the cache step. -/

/-- Invariant of the cache state during one call with identities `ce.xid`,
`ce.oid` and contents `X`, `o`: the state is the initial `c0` or carries this
call's identities, and is consistent when it carries them. -/
def CInv (ee : Bool) (ce : CEnv) (X : JMat T) (o : OpEnum T) (c0 c : UCache T) : Prop :=
  (c = c0 ∨ c.key = some (ce.xid, ce.oid)) ∧ CacheOK ee ce.szT ce.xid ce.oid X o c

theorem getArray_size (b : Buf T) (n : Nat) (a : JVec T) (b' : Buf T)
    (h : getArray b n = .ok (a, b')) : a.size = n := by
  cases b with
  | none => simp [getArray] at h; rw [← h.1]; simp [JVec.fill]
  | mat A i =>
    simp only [getArray] at h
    cases hr : A.row (i + 1) with
    | error e => simp [hr] at h
    | ok row =>
      have hrl := JMat.row_length A (i + 1) row hr
      simp only [hr, jl_ok_bind] at h
      split at h
      · cases h; simp; omega
      · cases h
  | vec arrs i =>
    simp only [getArray] at h
    split at h
    · split at h
      · cases h; assumption
      · cases h; simp [JVec.fill]
    · cases h; simp [JVec.fill]

theorem degnEval_one (f : List T → T) (x : JVec T) :
    degnEval f [x] = .ok ((List.range x.size).map (fun j => f [x.getD j JlScalar.undef])).toArray := by
  have hm := mapM_jl_eq (fun j => do
      let args ← [x].mapM (fun c => getInb c j)
      pure (f args)) (fun j => f [x.getD j JlScalar.undef]) (List.range x.size) (by
    intro j hj
    have hj' : j < x.size := List.mem_range.mp hj
    simp [getInb, hj', Array.getD])
  show (do
    let vs ← (List.range x.size).mapM (fun j => do
      let args ← [x].mapM (fun c => getInb c j)
      pure (f args))
    pure vs.toArray) = _
  rw [hm]
  rfl

theorem degnEval_one_size (f : List T → T) (x v : JVec T) (h : degnEval f [x] = .ok v) :
    v.size = x.size := by
  rw [degnEval_one] at h
  cases h
  simp

theorem copyTo_same (a v : JVec T) (h : a.size = v.size) : copyTo a v = .ok v := by
  simp [copyTo, h]

theorem getFeature_eq (b : Buf T) (X : JMat T) (f : Nat) :
    getFeature b X f = (getArray b X.ncols).bind (fun p => (rowInb X f).map (fun r => (r, p.2))) := by
  cases b with
  | none =>
    simp only [getFeature, getArray, Except.bind]
    cases rowInb X f <;> rfl
  | mat A i =>
    simp only [getFeature]
    cases getArray (.mat A i) X.ncols with
    | error e => rfl
    | ok p => obtain ⟨a, b'⟩ := p; simp only [jl_ok_bind]; cases rowInb X f <;> rfl
  | vec arrs i =>
    simp only [getFeature]
    cases getArray (.vec arrs i) X.ncols with
    | error e => rfl
    | ok p => obtain ⟨a, b'⟩ := p; simp only [jl_ok_bind]; cases rowInb X f <;> rfl

/-- A feature leaf in range reads its row into the next slot. -/
theorem evalT_feature (cx : Ctx) (o : OpEnum T) (X : JMat T) (f : Nat) (b : Buf T)
    (row : JVec T) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows) (hrow : X.row f = .ok row) :
    evalT cx o X (.feature f) b =
      (getArray b X.ncols).map (fun p => (⟨row, true, nextId b⟩, p.2)) := by
  have hchk : chk X f = .ok () := by simp [chk, hf1, hf2]
  have hr : rowInb X f = .ok row := by simp [rowInb, hf1, hf2, hrow]
  simp only [evalT, hchk, jl_ok_bind, getFeature_eq, hr]
  cases getArray b X.ncols <;> rfl

theorem resetIfNew_spec (ee : Bool) (ce : CEnv) (X : JMat T) (o : OpEnum T) (c0 c : UCache T)
    (hc : CInv ee ce X o c0 c) :
    CInv ee ce X o c0 (resetIfNew ce o X c) ∧ (resetIfNew ce o X c).key = some (ce.xid, ce.oid) ∧
      Consistent ee ce.szT X o (resetIfNew ce o X c) := by
  unfold resetIfNew
  split
  · rename_i hk
    exact ⟨hc, hk, hc.2 hk⟩
  · refine ⟨⟨Or.inr rfl, fun _ => ?_⟩, rfl, ?_⟩ <;>
      exact ⟨rfl, fun _ _ _ h => by simp at h⟩

theorem store_spec (ee : Bool) (ce : CEnv) (X : JMat T) (o : OpEnum T) (c0 c : UCache T)
    (hc : CInv ee ce X o c0 c) (hk : c.key = some (ce.xid, ce.oid)) (op f : Nat) (g : List T → T)
    (row out : JVec T) (hb : 1 ≤ op ∧ op ≤ c.nu ∧ 1 ≤ f ∧ f ≤ c.nf)
    (hg : o.lookup 1 op = some g) (hrow : X.row f = .ok row) (hout : degnEval g [row] = .ok out)
    (hv : ee = true → isValidArray row = true ∧ isValidArray out = true) :
    CInv ee ce X o c0 (c.store op f out) := by
  have hcons := hc.2 hk
  refine ⟨Or.inr hk, fun _ => ⟨hcons.1, ?_⟩⟩
  intro i f' v hv'
  simp only [UCache.store] at hv'
  split at hv'
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    cases hv'
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, g, row, hg, hrow, hout, hv⟩
  · exact hcons.2 i f' v hv'

/-- The cache step simulates the uncached code for a node `op(x_feat)`. -/
theorem via_sim (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (c0 : UCache T)
    (hsz : 0 < ce.szT) (op feat : Nat) (g : List T → T) (fop : Jl (List T → T))
    (hg : o.lookup 1 op = some g) (hfop : fop = .ok g) (hf1 : 1 ≤ feat) (hf2 : feat ≤ X.nrows) :
    SimF (CInv cx.earlyExit ce X o c0) (unfused1 cx fop (evalT cx o X (.feature feat)))
      (viaCache cx ce o X op g feat (unfused1C cx fop (liftB (evalT cx o X (.feature feat))))) := by
  intro b c hc
  have hsim := unfused1_sim (CInv cx.earlyExit ce X o c0) cx fop _ _
    (liftB_sim (CInv cx.earlyExit ce X o c0) (evalT cx o X (.feature feat)))
  unfold viaCache
  by_cases hbump : ce.bumper = true
  · simp only [hbump, ↓reduceIte]
    exact hsim b c hc
  simp only [hbump, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hc1, hk1, hcons⟩ := resetIfNew_spec cx.earlyExit ce X o c0 c hc
  have hop := (OpEnum.lookup_some_iff o 1 op).mp ⟨g, hg⟩
  obtain ⟨row, hrow, hrowlen⟩ := JMat.row_exists X feat hf1 hf2
  unfold cachedDeg1
  have hdiv : ¬ (c.key ≠ some (ce.xid, ce.oid) ∧ ce.szT = 0) := fun h => by omega
  simp only [hdiv, ↓reduceIte]
  generalize hc1def : resetIfNew ce o X c = c1 at hc1 hk1 hcons
  by_cases he : c1.isEmpty = true
  · simp only [he, ↓reduceIte, jl_ok_bind]
    exact hsim b c1 hc1
  simp only [he, Bool.false_eq_true, ↓reduceIte]
  have hdims : c1.nu = (opsOf o 1).length ∧ c1.nf = X.nrows := by
    have h1 := hcons.1
    unfold resetDims at h1
    split at h1
    · simp only [Prod.mk.injEq] at h1; exact h1
    · simp only [Prod.mk.injEq] at h1
      simp [UCache.isEmpty, h1.1] at he
  have hnops : o.nops 1 = (opsOf o 1).length := by simp [OpEnum.nops, opsOf]
  have hb : 1 ≤ op ∧ op ≤ c1.nu ∧ 1 ≤ feat ∧ feat ≤ c1.nf := by omega
  simp only [hb, and_self, not_true_eq_false, ↓reduceIte]
  -- uncached side, unfolded
  have hunc : unfused1 cx fop (evalT cx o X (.feature feat)) b =
      checked cx (evalT cx o X (.feature feat)) (fun x cid b => do
        let f ← fop
        let out ← degnEval f [x]
        pure (⟨out, true, cid⟩, b)) b := rfl
  rw [hunc]
  cases hget : c1.get op feat with
  | some v =>
    obtain ⟨_, _, _, _, g', row', hg', hrow', hv, hvalid⟩ := hcons.2 op feat v hget
    have hgg : g' = g := by rw [hg] at hg'; exact (Option.some.inj hg').symm
    subst hgg
    have hrr : row' = row := by rw [hrow] at hrow'; exact (Except.ok.inj hrow').symm
    subst hrr
    simp only [checked]
    rw [evalT_feature cx o X feat b row' hf1 hf2 hrow]
    cases hga : getArray b X.ncols with
    | error e => exact ⟨c1, hc1, rfl⟩
    | ok p =>
      obtain ⟨a, b'⟩ := p
      have ha := getArray_size b X.ncols a b' hga
      have hvs := degnEval_one_size g' row' v hv
      simp only [Except.map, checked, jl_ok_bind, hfop]
      have hnoexit : (cx.earlyExit && !isValidArray row') = false := by
        cases hee : cx.earlyExit
        · rfl
        · simp [(hvalid hee).1]
      simp only [hnoexit, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv, jl_ok_bind,
        copyTo_same a v (by rw [ha, hvs, hrowlen])]
      exact ⟨c1, hc1, rfl⟩
  | none =>
    simp only
    cases hev : evalT cx o X (.feature feat) b with
    | error e => simp [checked, hev]; exact ⟨c1, hc1, rfl⟩
    | ok p =>
      obtain ⟨r, b1⟩ := p
      have hrx : r.x = row := by
        rw [evalT_feature cx o X feat b row hf1 hf2 hrow] at hev
        cases hga : getArray b X.ncols <;> simp [hga, Except.map] at hev
        rw [← hev.1]
      simp only [checked, hev, jl_ok_bind]
      by_cases h1 : r.ok = true
      · by_cases h2 : (cx.earlyExit && !isValidArray r.x) = true
        · simp only [h1, h2, Bool.not_true, ↓reduceIte]
          exact ⟨c1, hc1, rfl⟩
        · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfop, jl_ok_bind]
          cases hd : degnEval g [r.x] with
          | error e => exact ⟨c1, hc1, rfl⟩
          | ok out =>
            simp only [jl_ok_bind]
            by_cases hs : (!cx.earlyExit || isValidArray out) = true
            · simp only [hs, ↓reduceIte]
              refine ⟨_, store_spec cx.earlyExit ce X o c0 c1 hc1 hk1 op feat g row out hb hg hrow
                (hrx ▸ hd) (fun hee => ?_), rfl⟩
              refine ⟨?_, ?_⟩
              · rw [← hrx]; simpa [hee] using h2
              · simpa [hee] using hs
            · simp only [hs, Bool.false_eq_true, ↓reduceIte]
              exact ⟨c1, hc1, rfl⟩
      · simp only [h1, Bool.not_false, ↓reduceIte]
        exact ⟨c1, hc1, rfl⟩

theorem deg1Dispatch_sim (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (c0 : UCache T)
    (hsz : 0 < ce.szT) (op : Nat) (ch : Tree T) (evC : Buf T → Jl (ResultOk T × Buf T))
    (evC' : St T → Jl (ResultOk T × St T))
    (hop : 1 ≤ op ∧ op ≤ o.nops 1) (hw : ch.WF cx.D o.nops X.nrows)
    (hC : SimF (CInv cx.earlyExit ce X o c0) evC evC')
    (hfe : ∀ feat, ch = .feature feat →
      evC = evalT cx o X (.feature feat) ∧ evC' = liftB (evalT cx o X (.feature feat))) :
    SimF (CInv cx.earlyExit ce X o c0) (deg1Dispatch cx o X op ch evC)
      (deg1DispatchC cx ce o X op ch evC') := by
  intro b c hc
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 1 op (by omega) hop.1 hop.2
  have hidx := idxOp_lookup o 1 op g (by omega) hg
  unfold deg1Dispatch deg1DispatchC
  by_cases hlim : operatorLimit < (opsOf o 1).length
  · simp only [hlim, ↓reduceIte]
    cases ch with
    | feature feat =>
      obtain ⟨rfl, rfl⟩ := hfe feat rfl
      simp only [Tree.WF] at hw
      simp only [hidx, jl_ok_bind]
      exact via_sim cx ce o X c0 hsz op feat g _ hg rfl hw.1 hw.2.1 b c hc
    | const v => exact unfused1_sim _ cx _ _ _ hC b c hc
    | branch lop cs => exact unfused1_sim _ cx _ _ _ hC b c hc
  simp only [hlim, ↓reduceIte, hnif, jl_ok_bind]
  rcases ch with v | feat | ⟨lop, _ | ⟨ll, _ | ⟨lr, _ | ⟨_, _⟩⟩⟩⟩
  · exact unfused1_sim _ cx _ _ _ hC b c hc
  · obtain ⟨rfl, rfl⟩ := hfe feat rfl
    simp only [Tree.WF] at hw
    exact via_sim cx ce o X c0 hsz op feat g _ hg rfl hw.1 hw.2.1 b c hc
  · exact unfused1_sim _ cx _ _ _ hC b c hc
  · simp only
    by_cases hA : (cx.useFused && isLeaf ll) = true
    · simp only [hA, ↓reduceIte]
      exact bind_sim _ _ _ _ c hc (fun _ _ => liftB_sim _ _ b c hc)
    · simp only [hA, Bool.false_eq_true, ↓reduceIte]
      exact unfused1_sim _ cx _ _ _ hC b c hc
  · simp only
    by_cases hA : (cx.useFused && isLeaf ll && isLeaf lr) = true
    · simp only [hA, ↓reduceIte]
      exact bind_sim _ _ _ _ c hc (fun _ _ => liftB_sim _ _ b c hc)
    · simp only [hA, Bool.false_eq_true, ↓reduceIte]
      exact unfused1_sim _ cx _ _ _ hC b c hc
  · exact unfused1_sim _ cx _ _ _ hC b c hc

theorem children_sim (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (c0 : UCache T) :
    ∀ cs : List (Tree T),
      (∀ t ∈ cs, SimF (CInv cx.earlyExit ce X o c0) (evalT cx o X t) (evalTC cx ce o X t)) →
      ∀ b c, CInv cx.earlyExit ce X o c0 c →
        SimRCh (CInv cx.earlyExit ce X o c0) (evalChildren cx o X cs b)
          (evalChildrenC cx ce o X cs (b, c))
  | [], _, b, c, hc => ⟨c, hc, rfl⟩
  | t :: ts, h, b, c, hc => by
    obtain ⟨c1, hc1, he⟩ := h t (by simp) b c hc
    have ih := children_sim cx ce o X c0 ts (fun t' ht' => h t' (by simp [ht']))
    simp only [evalChildren, evalChildrenC]
    rw [he]
    rcases hu : evalT cx o X t b with e | ⟨r, b1⟩
    · exact ⟨c1, hc1, rfl⟩
    · simp only [Except.map, emb, jl_ok_bind]
      by_cases h1 : r.ok = true
      · by_cases h2 : (cx.earlyExit && !isValidArray r.x) = true
        · simp only [h1, h2, Bool.not_true, ↓reduceIte]
          exact ⟨c1, hc1, rfl⟩
        · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨c2, hc2, he2⟩ := ih b1 c1 hc1
          rw [he2]
          rcases evalChildren cx o X ts b1 with e | (⟨r', b'⟩ | ⟨xs, b'⟩)
          · exact ⟨c2, hc2, rfl⟩
          · exact ⟨c2, hc2, rfl⟩
          · exact ⟨c2, hc2, rfl⟩
      · simp only [h1, Bool.not_false, ↓reduceIte]
        exact ⟨c1, hc1, rfl⟩

/-- Main simulation: the cached evaluator returns the uncached result. -/
theorem evalTC_sim (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (c0 : UCache T)
    (hsz : 0 < ce.szT) (t : Tree T) (hw : t.WF cx.D o.nops X.nrows) :
    SimF (CInv cx.earlyExit ce X o c0) (evalT cx o X t) (evalTC cx ce o X t) := by
  induction t using Tree.induction with
  | hc v => intro b c hc; exact ⟨c, hc, rfl⟩
  | hf f => intro b c hc; exact ⟨c, hc, rfl⟩
  | hb op cs ih =>
    intro b c hc
    simp only [Tree.WF] at hw
    have hchild : ∀ t ∈ cs, SimF (CInv cx.earlyExit ce X o c0) (evalT cx o X t) (evalTC cx ce o X t) :=
      fun t ht => ih t ht (hw.2.2 t ht)
    unfold evalT evalTC
    by_cases hconst : isConstantL cs = true
    · simp only [hconst, ↓reduceIte]
      exact ⟨c, hc, rfl⟩
    simp only [hconst, Bool.false_eq_true, ↓reduceIte]
    rcases cs with _ | ⟨ch, _ | ⟨d, _ | ⟨e, es⟩⟩⟩
    · exact ⟨c, hc, rfl⟩
    · simp only
      refine deg1Dispatch_sim cx ce o X c0 hsz op ch _ _ ⟨hw.2.1.1, by simpa using hw.2.1.2.1⟩
        (hw.2.2 ch (by simp)) (hchild ch (by simp)) ?_ b c hc
      intro feat hfeat
      subst hfeat
      exact ⟨rfl, rfl⟩
    · exact deg2Dispatch_sim _ cx o X op ch d _ _ _ _ (hchild ch (by simp)) (hchild d (by simp)) b c hc
    · simp only
      split
      · exact deg2Dispatch_sim _ cx o X op ch d _ _ _ _ (hchild ch (by simp)) (hchild d (by simp)) b c hc
      · exact finish_sim _ o _ op _ _ (children_sim cx ce o X c0 _ hchild b c hc)

end DynExpr.EvalCache
