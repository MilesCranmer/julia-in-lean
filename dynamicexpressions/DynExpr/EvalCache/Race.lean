import DynExpr.EvalCache.StoreRule

/-!
evalcache-threads-same: threads sharing one cache and one input never read a
wrong entry, under every interleaving of the modelled cache steps.
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

variable {T : Type} [JlScalar T]

theorem deg1Dispatch_feature (cx : Ctx) (o : OpEnum T) (X : JMat T) (op feat : Nat)
    (g : List T → T) (hg : o.lookup 1 op = some g) (evC : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) :
    deg1Dispatch cx o X op (.feature feat) evC b = unfused1 cx (.ok g) evC b := by
  have hop := (OpEnum.lookup_some_iff o 1 op).mp ⟨g, hg⟩
  obtain ⟨g', hg', hnif⟩ := nifOp_lookup o 1 op (by omega) hop.1 hop.2
  rw [hg] at hg'
  cases hg'
  have hidx := idxOp_lookup o 1 op g (by omega) hg
  unfold deg1Dispatch
  by_cases hlim : operatorLimit < (opsOf o 1).length
  · simp only [hlim, ↓reduceIte, hidx]
  · simp only [hlim, ↓reduceIte, hnif, jl_ok_bind]
    rfl

/-- The uncached result of a job's node. -/
theorem plain_eq (j : Job T) (g : List T → T) (row : JVec T) (hg : j.o.lookup 1 j.op = some g)
    (hf1 : 1 ≤ j.feat) (hf2 : j.feat ≤ j.X.nrows) (hrow : j.X.row j.feat = .ok row) :
    j.plain = if j.cx.earlyExit && !isValidArray row then .ok ⟨row, false, .fresh⟩
      else (degnEval g [row]).map fun out => ⟨out, true, .fresh⟩ := by
  unfold Job.plain
  have h1 : evalT j.cx j.o j.X (.branch j.op [.feature j.feat]) .none =
      deg1Dispatch j.cx j.o j.X j.op (.feature j.feat) (evalT j.cx j.o j.X (.feature j.feat)) .none := by
    simp [evalT, isConstantL, isConstant]
  rw [h1, deg1Dispatch_feature _ _ _ _ _ g hg]
  unfold unfused1 checked
  rw [evalT_feature j.cx j.o j.X j.feat .none row hf1 hf2 hrow]
  simp only [getArray, Except.map, jl_ok_bind, nextId, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hx : (j.cx.earlyExit && !isValidArray row) = true
  · simp only [hx, ↓reduceIte]
    rfl
  · simp only [hx, Bool.false_eq_true, ↓reduceIte]
    cases degnEval g [row] <;> rfl

/-- A job reads the shared input `X`, `o` with identities `xid`, `oid`. -/
def Job.Same (j : Job T) (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T) : Prop :=
  j.WF ∧ j.ce.xid = xid ∧ j.ce.oid = oid ∧ j.ce.szT = szT ∧ j.X = X ∧ j.o = o ∧ j.cx.earlyExit = ee

/-- Thread invariant: past the identity check the cache carries the shared
identities and is non-empty while a store is pending; a pending store holds
the uncached result; a finished thread returned the uncached result. -/
def TOK (j : Job T) (xid oid : Nat) (c : UCache T) : TState T → Prop
  | .start => True
  | .checked => c.key = some (xid, oid)
  | .pending r => c.key = some (xid, oid) ∧ c.isEmpty = false ∧ j.plain = .ok r ∧
      ∃ g row, j.o.lookup 1 j.op = some g ∧ j.X.row j.feat = .ok row ∧ degnEval g [row] = .ok r.x ∧
        (j.cx.earlyExit = true → isValidArray row = true ∧ isValidArray r.x = true)
  | .done r => r = j.plain

/-- A step keeps the key once it is the shared one, and keeps the entry size. -/
theorem tstep_frame (j : Job T) (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T)
    (hj : j.Same ee szT xid oid X o) (s : TState T) (c : UCache T)
    (hk : c.key = some (xid, oid)) :
    (tstep j (s, c)).2.key = some (xid, oid) ∧ (tstep j (s, c)).2.nu = c.nu ∧
      (tstep j (s, c)).2.nf = c.nf := by
  obtain ⟨_, hx, ho, _, _, _, _⟩ := hj
  cases s with
  | start =>
    simp only [tstep]
    split
    · exact ⟨hk, rfl, rfl⟩
    · simp [resetIfNew, hx, ho, hk]
  | checked =>
    simp only [tstep]
    split
    · exact ⟨hk, rfl, rfl⟩
    · split
      · exact ⟨hk, rfl, rfl⟩
      · split
        · exact ⟨hk, rfl, rfl⟩
        · split
          · exact ⟨hk, rfl, rfl⟩
          · split
            · exact ⟨hk, rfl, rfl⟩
            · split
              · exact ⟨hk, rfl, rfl⟩
              · split
                · exact ⟨hk, rfl, rfl⟩
                · split
                  · exact ⟨hk, rfl, rfl⟩
                  · split <;> exact ⟨hk, rfl, rfl⟩
  | pending r =>
    simp only [tstep]
    split
    · exact ⟨hk, rfl, rfl⟩
    · exact ⟨hk, rfl, rfl⟩
  | done r => exact ⟨hk, rfl, rfl⟩

/-- Another thread's step preserves this thread's invariant. -/
theorem tok_other (j j' : Job T) (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T)
    (hj : j.Same ee szT xid oid X o) (s s' : TState T) (c : UCache T)
    (h' : TOK j' xid oid c s') : TOK j' xid oid (tstep j (s, c)).2 s' := by
  cases s' with
  | start => trivial
  | done r => exact h'
  | checked => exact (tstep_frame j ee szT xid oid X o hj s c h').1
  | pending r =>
    obtain ⟨hk, he, rest⟩ := h'
    obtain ⟨hk', hnu, hnf⟩ := tstep_frame j ee szT xid oid X o hj s c hk
    refine ⟨hk', ?_, rest⟩
    simp only [UCache.isEmpty] at he ⊢
    rw [hnu, hnf]
    exact he

/-- A thread's own step preserves its invariant and the cache invariant. -/
theorem tok_self (j : Job T) (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T)
    (hj : j.Same ee szT xid oid X o) (s : TState T) (c : UCache T)
    (hc : CacheOK ee szT xid oid X o c) (hs : TOK j xid oid c s) :
    TOK j xid oid (tstep j (s, c)).2 (tstep j (s, c)).1 ∧
      CacheOK ee szT xid oid X o (tstep j (s, c)).2 := by
  obtain ⟨⟨hw, hsz⟩, hx, ho, hszT, hX, hO, hee⟩ := hj
  subst hx ho hszT hX hO hee
  simp only [Tree.WF] at hw
  have hfw := hw.2.2 (.feature j.feat) (by simp)
  simp only [Tree.WF] at hfw
  have hop1 : 1 ≤ j.op := hw.2.1.1
  have hop2 : j.op ≤ j.o.nops 1 := by simpa using hw.2.1.2.1
  have hnops : j.o.nops 1 = (opsOf j.o 1).length := by simp [OpEnum.nops, opsOf]
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup j.o 1 j.op (by omega) hop1 hop2
  obtain ⟨row, hrow, hrowlen⟩ := JMat.row_exists j.X j.feat hfw.1 hfw.2.1
  have hplain := plain_eq j g row hg hfw.1 hfw.2.1 hrow
  have hinv0 : CInv j.cx.earlyExit j.ce j.X j.o c c := ⟨Or.inl rfl, hc⟩
  cases s with
  | start =>
    have hdiv : ¬ (c.key ≠ some (j.ce.xid, j.ce.oid) ∧ j.ce.szT = 0) := fun h => by omega
    simp only [tstep, hdiv, ↓reduceIte]
    obtain ⟨hc1, hk1, _⟩ := resetIfNew_spec j.cx.earlyExit j.ce j.X j.o c c hinv0
    exact ⟨hk1, hc1.2⟩
  | checked =>
    have hk : c.key = some (j.ce.xid, j.ce.oid) := hs
    have hcons := hc hk
    simp only [tstep, hnif]
    by_cases he : c.isEmpty = true
    · simp only [he, ↓reduceIte]
      exact ⟨rfl, hc⟩
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    have hdims : c.nu = (opsOf j.o 1).length ∧ c.nf = j.X.nrows := by
      have h1 := hcons.1
      unfold resetDims at h1
      split at h1
      · simp only [Prod.mk.injEq] at h1; exact h1
      · simp only [Prod.mk.injEq] at h1
        simp [UCache.isEmpty, h1.1] at he
    have hb : 1 ≤ j.op ∧ j.op ≤ c.nu ∧ 1 ≤ j.feat ∧ j.feat ≤ c.nf := by omega
    simp only [hb, and_self, not_true_eq_false, ↓reduceIte]
    cases hget : c.get j.op j.feat with
    | some v =>
      obtain ⟨_, _, _, _, g', row', hg', hrow', hv, hvalid⟩ := hcons.2 j.op j.feat v hget
      rw [hg] at hg'
      cases hg'
      rw [hrow] at hrow'
      cases hrow'
      have hvs := degnEval_one_size g row v hv
      have hcp : copyTo (JVec.fill j.X.ncols JlScalar.undef) v = .ok v :=
        copyTo_same _ _ (by simp [JVec.fill, hvs, hrowlen])
      refine ⟨?_, hc⟩
      show (copyTo (JVec.fill j.X.ncols JlScalar.undef) v).map (fun out => ⟨out, true, .fresh⟩) = j.plain
      rw [hcp, hplain]
      have hnoexit : (j.cx.earlyExit && !isValidArray row) = false := by
        cases hee : j.cx.earlyExit
        · rfl
        · simp [(hvalid hee).1]
      simp only [hnoexit, Bool.false_eq_true, ↓reduceIte, hv]
    | none =>
      simp only
      rw [evalT_feature j.cx j.o j.X j.feat .none row hfw.1 hfw.2.1 hrow]
      simp only [getArray, Except.map, Bool.not_true, Bool.false_eq_true, ↓reduceIte, nextId]
      by_cases hx : (j.cx.earlyExit && !isValidArray row) = true
      · simp only [hx, ↓reduceIte]
        refine ⟨?_, hc⟩
        show Except.ok _ = j.plain
        rw [hplain, if_pos hx]
      · simp only [hx, Bool.false_eq_true, ↓reduceIte, degnEval_one]
        have hplain' : j.plain = .ok ⟨((List.range row.size).map
            (fun i => g [row.getD i JlScalar.undef])).toArray, true, .fresh⟩ := by
          rw [hplain, if_neg hx, degnEval_one]
          rfl
        split
        · rename_i hst
          refine ⟨⟨hk, by simpa using he, hplain', g, row, hg, hrow, degnEval_one g row, ?_⟩, hc⟩
          intro hee
          refine ⟨by simpa [hee] using hx, by simpa [hee] using hst⟩
        · exact ⟨hplain'.symm, hc⟩
  | pending r =>
    obtain ⟨hk, he, hpl, g', row', hg', hrow', hv, hvalid⟩ := hs
    have hcons := hc hk
    have hdims : c.nu = (opsOf j.o 1).length ∧ c.nf = j.X.nrows := by
      have h1 := hcons.1
      unfold resetDims at h1
      split at h1
      · simp only [Prod.mk.injEq] at h1; exact h1
      · simp only [Prod.mk.injEq] at h1
        simp [UCache.isEmpty, h1.1] at he
    have hb : 1 ≤ j.op ∧ j.op ≤ c.nu ∧ 1 ≤ j.feat ∧ j.feat ≤ c.nf := by omega
    simp only [tstep, hb, and_self, ↓reduceIte]
    exact ⟨hpl.symm, (store_spec j.cx.earlyExit j.ce j.X j.o c c hinv0 hk j.op j.feat g' row' r.x
      hb hg' hrow' hv hvalid).2⟩
  | done r => exact ⟨hs, hc⟩

theorem race_ok (ja jb : Job T) (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T)
    (ha : ja.Same ee szT xid oid X o) (hb : jb.Same ee szT xid oid X o) :
    ∀ (sched : List Bool) (a b : TState T) (c : UCache T),
      CacheOK ee szT xid oid X o c → TOK ja xid oid c a → TOK jb xid oid c b →
      CacheOK ee szT xid oid X o (race ja jb sched (a, b, c)).2.2 ∧
        TOK ja xid oid (race ja jb sched (a, b, c)).2.2 (race ja jb sched (a, b, c)).1 ∧
        TOK jb xid oid (race ja jb sched (a, b, c)).2.2 (race ja jb sched (a, b, c)).2.1
  | [], a, b, c, hc, h1, h2 => ⟨hc, h1, h2⟩
  | true :: rest, a, b, c, hc, h1, h2 => by
    obtain ⟨h1', hc'⟩ := tok_self ja ee szT xid oid X o ha a c hc h1
    have h2' := tok_other ja jb ee szT xid oid X o ha a b c h2
    exact race_ok ja jb ee szT xid oid X o ha hb rest _ b _ hc' h1' h2'
  | false :: rest, a, b, c, hc, h1, h2 => by
    obtain ⟨h2', hc'⟩ := tok_self jb ee szT xid oid X o hb b c hc h2
    have h1' := tok_other jb ja ee szT xid oid X o hb b a c h1
    exact race_ok ja jb ee szT xid oid X o ha hb rest a _ _ hc' h1' h2'

theorem evalCacheRaceSame_proof : evalCacheRaceSame := by
  intro T _ ja jb sched c hwa hwb hsz hx ho hX hO hee hc
  have ha : ja.Same ja.cx.earlyExit ja.ce.szT ja.ce.xid ja.ce.oid ja.X ja.o :=
    ⟨hwa, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hb : jb.Same ja.cx.earlyExit ja.ce.szT ja.ce.xid ja.ce.oid ja.X ja.o :=
    ⟨hwb, hx.symm, ho.symm, hsz.symm, hX.symm, hO.symm, hee.symm⟩
  obtain ⟨_, h1, h2⟩ := race_ok ja jb _ _ _ _ _ _ ha hb sched .start .start c hc trivial trivial
  generalize race ja jb sched (.start, .start, c) = st at h1 h2
  obtain ⟨a, b, c'⟩ := st
  cases a <;> cases b <;> simp only [RaceOK] <;> try trivial

/-- The hypotheses of evalcache-threads-same hold for two copies of one job on a
fresh cache. -/
example : Ex.jobA.WF ∧ CacheOK Ex.jobA.cx.earlyExit Ex.jobA.ce.szT Ex.jobA.ce.xid Ex.jobA.ce.oid
    Ex.jobA.X Ex.jobA.o UCache.empty :=
  ⟨⟨Ex.tInv_wf, by decide⟩, cacheOK_empty _ _ _ _ _ _⟩

end DynExpr.EvalCache
