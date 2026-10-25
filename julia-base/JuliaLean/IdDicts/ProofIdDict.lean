import JuliaLean.IdDicts.ProofTable

/-!
# Proofs for `IdDict`

A wrapper invariant (`DInv`: keys pairwise non-`===`, `count` is the number
of live pairs, every key `isa K` and value `isa V`) holds after every call;
every mutator moves the table exactly like the reference map.
-/

namespace JuliaLean.IdDicts

/-- Every key has type `K` and every value type `V`. -/
def Typed (K V : JTy) (t : Tab) : Prop := ∀ p ∈ t, isa p.1 K = true ∧ isa p.2 V = true

/-- The wrapper invariant of `IdDict`. -/
def DInv (d : IdDict) : Prop := keysDistinct d.ht ∧ d.count = d.ht.length ∧ Typed d.K d.V d.ht

theorem cast_ok {x : JVal} {T : JTy} (h : isa x T = true) : cast x T = .ok x := by
  simp [cast, h]

theorem convert_self {x : JVal} {T : JTy} (h : isa x T = true) : convert T x = .ok x := by
  simp [convert, h]

theorem valConv (V : JTy) (v : JVal) :
    (if isa v V = true then Except.ok v else (convert V v).bind (cast · V)) = convert V v := by
  by_cases h : isa v V = true
  · simp [h, convert]
  · simp only [h]
    cases hc : convert V v with
    | error e => rfl
    | ok w => simp [Except.bind, cast_ok (convert_isa hc)]

theorem valConv' (V : JTy) (v : JVal) :
    (if (!isa v V) = true then (convert V v).bind (cast · V) else Except.ok v) = convert V v := by
  conv => rhs; rw [← valConv V v]
  by_cases h : isa v V = true <;> simp [h]

/-! ## `setindex!` -/

theorem setindex_spec (d : IdDict) (v k : JVal) :
    (d.setindex v k).1.K = d.K ∧ (d.setindex v k).1.V = d.V ∧
    (isa k d.K = true → ∀ w, convert d.V v = .ok w →
      (d.setindex v k).1.ht = (eqtablePut d.ht k w).1 ∧
      (d.setindex v k).1.count = d.count + (eqtablePut d.ht k w).2 ∧
      (d.setindex v k).2 = .ok ()) ∧
    (isa k d.K = true → ∀ e, convert d.V v = .error e → (d.setindex v k).1 = d) ∧
    (isa k d.K = false → (d.setindex v k).1 = d) := by
  unfold IdDict.setindex
  simp only [valConv]
  by_cases hk : isa k d.K = true
  · cases hc : convert d.V v with
    | error e => simp [hk]
    | ok w =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, if_false]
      by_cases hr : d.ndel ≥ 3 * d.sz / 4 <;> simp [hr, IdDict.rehash]
  · have hk' : isa k d.K = false := by simpa using hk
    simp [hk']

theorem setindex_inv {d : IdDict} (h : DInv d) (v k : JVal) :
    DInv (d.setindex v k).1 ∧ (d.setindex v k).1.K = d.K ∧ (d.setindex v k).1.V = d.V := by
  obtain ⟨hK, hV, hok, herr, hbad⟩ := setindex_spec d v k
  refine ⟨?_, hK, hV⟩
  by_cases hk : isa k d.K = true
  · cases hc : convert d.V v with
    | error e => rw [herr hk e hc]; exact h
    | ok w =>
      obtain ⟨hht, hcount, -⟩ := hok hk w hc
      refine ⟨?_, ?_, ?_⟩
      · rw [hht]; exact put_distinct h.1 k w
      · rw [hht, hcount, put_length, h.2.1]
      · intro p hp
        rw [hht] at hp
        rw [hK, hV]
        rcases put_mem hp with hp | hp
        · exact h.2.2 p hp
        · subst hp; exact ⟨hk, convert_isa hc⟩
  · rw [hbad (by simpa using hk)]; exact h

/-! ## `pop!` and `delete!` -/

theorem pop3_spec {d : IdDict} (h : DInv d) (k dflt : JVal) :
    (d.pop3 k dflt).1.K = d.K ∧ (d.pop3 k dflt).1.V = d.V ∧
    (d.pop3 k dflt).1.ht = rDel d.ht k ∧
    (d.pop3 k dflt).1.count = (if (rLookup d.ht k).isSome then d.count - 1 else d.count) := by
  unfold IdDict.pop3
  rw [pop_eq h.1]
  by_cases hs : (rLookup d.ht k).isSome = true <;> simp [hs]

theorem pop3_inv {d : IdDict} (h : DInv d) (k dflt : JVal) :
    DInv (d.pop3 k dflt).1 ∧ (d.pop3 k dflt).1.K = d.K ∧ (d.pop3 k dflt).1.V = d.V := by
  obtain ⟨hK, hV, hht, hc⟩ := pop3_spec h k dflt
  refine ⟨⟨?_, ?_, ?_⟩, hK, hV⟩
  · rw [hht]; exact rDel_distinct h.1 k
  · have := rDel_length h.1 k
    rw [hc, hht, h.2.1]
    by_cases hs : (rLookup d.ht k).isSome = true <;> simp [hs] at this ⊢ <;> omega
  · intro p hp; rw [hht] at hp; rw [hK, hV]; exact h.2.2 p (rDel_mem hp)

theorem pop_fst (d : IdDict) (k : JVal) : (d.pop k).1 = (d.pop3 k token).1 := by
  unfold IdDict.pop; dsimp only; split <;> (try split) <;> rfl

theorem delete_fst (d : IdDict) (k : JVal) : (d.delete k).1 = (d.pop3 k token).1 := rfl

/-! ## `get!` -/

theorem getBang_inv {d : IdDict} (h : DInv d) (k dflt : JVal) :
    DInv (d.getBang k dflt).1 ∧ (d.getBang k dflt).1.K = d.K ∧ (d.getBang k dflt).1.V = d.V := by
  unfold IdDict.getBang
  simp only [valConv]
  split
  · cases convert d.V dflt with
    | error e => exact ⟨h, rfl, rfl⟩
    | ok w => exact setindex_inv h w k
  · exact ⟨h, rfl, rfl⟩

theorem getBangF_inv {d : IdDict} (h : DInv d) (fv k : JVal) :
    DInv (d.getBangF fv k).1 ∧ (d.getBangF fv k).1.K = d.K ∧ (d.getBangF fv k).1.V = d.V := by
  unfold IdDict.getBangF
  simp only [valConv']
  split
  · cases convert d.V fv with
    | error e => exact ⟨h, rfl, rfl⟩
    | ok w => exact setindex_inv h w k
  · exact ⟨h, rfl, rfl⟩

/-! ## Whole calls -/

theorem sizehint_fields (d : IdDict) (n : JInt .i64) :
    (d.sizehint n).K = d.K ∧ (d.sizehint n).V = d.V ∧ (d.sizehint n).ht = d.ht ∧
    (d.sizehint n).count = d.count := by
  unfold IdDict.sizehint; dsimp only; split <;> simp [IdDict.rehash]

theorem step_inv {d : IdDict} (h : DInv d) (op : DOp) :
    DInv (op.run d) ∧ (op.run d).K = d.K ∧ (op.run d).V = d.V := by
  cases op with
  | set k v => exact setindex_inv h v k
  | delete k => rw [DOp.run, delete_fst]; exact pop3_inv h k token
  | pop3 k dflt => exact pop3_inv h k dflt
  | pop k => rw [DOp.run, pop_fst]; exact pop3_inv h k token
  | empty => exact ⟨⟨List.nodup_nil, rfl, fun p hp => by simp [DOp.run, IdDict.empty] at hp⟩, rfl, rfl⟩
  | sizehint n =>
    obtain ⟨hK, hV, hht, hc⟩ := sizehint_fields d n
    show DInv (d.sizehint n) ∧ (d.sizehint n).K = d.K ∧ (d.sizehint n).V = d.V
    exact ⟨⟨hht ▸ h.1, hc ▸ hht ▸ h.2.1, hK ▸ hV ▸ hht ▸ h.2.2⟩, hK, hV⟩
  | getBang k dflt => exact getBang_inv h k dflt
  | getBangF fv k => exact getBangF_inv h fv k

theorem step_agree {d : IdDict} {m : Tab} (h : DInv d) (ha : Agree d.ht m) (op : DOp)
    (hop : op.mutator = true) : Agree (op.run d).ht (op.ref d.K d.V m) := by
  cases op with
  | set k v =>
    obtain ⟨-, -, hok, herr, hbad⟩ := setindex_spec d v k
    simp only [DOp.run, DOp.ref]
    by_cases hk : isa k d.K = true
    · simp only [hk, if_true]
      cases hc : convert d.V v with
      | error e => rw [herr hk e hc]; exact ha
      | ok w => rw [(hok hk w hc).1]; exact ha.put k w
    · have hk' : isa k d.K = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, if_false]
      rw [hbad hk']; exact ha
  | delete k => simp only [DOp.run, DOp.ref, delete_fst]; rw [(pop3_spec h k token).2.2.1]; exact ha.del k
  | pop3 k dflt => simp only [DOp.run, DOp.ref]; rw [(pop3_spec h k dflt).2.2.1]; exact ha.del k
  | pop k => simp only [DOp.run, DOp.ref, pop_fst]; rw [(pop3_spec h k token).2.2.1]; exact ha.del k
  | empty => exact ⟨List.nodup_nil, List.nodup_nil, fun _ => rfl, rfl⟩
  | sizehint n => simp only [DOp.run, DOp.ref]; rw [(sizehint_fields d n).2.2.1]; exact ha
  | getBang _ _ => simp [DOp.mutator] at hop
  | getBangF _ _ => simp [DOp.mutator] at hop

theorem fold_inv (ops : List DOp) : ∀ d : IdDict, DInv d →
    DInv (ops.foldl DOp.run d) ∧ (ops.foldl DOp.run d).K = d.K ∧ (ops.foldl DOp.run d).V = d.V := by
  induction ops with
  | nil => intro d h; exact ⟨h, rfl, rfl⟩
  | cons op ops ih =>
    intro d h
    obtain ⟨h1, hK, hV⟩ := step_inv h op
    obtain ⟨h2, hK2, hV2⟩ := ih _ h1
    exact ⟨h2, hK2.trans hK, hV2.trans hV⟩

theorem fold_agree (ops : List DOp) (hm : ∀ op ∈ ops, op.mutator = true) :
    ∀ (d : IdDict) (m : Tab), DInv d → Agree d.ht m →
      Agree (ops.foldl DOp.run d).ht (ops.foldl (DOp.ref d.K d.V) m) := by
  induction ops with
  | nil => intro d m _ ha; exact ha
  | cons op ops ih =>
    intro d m h ha
    obtain ⟨h1, hK, hV⟩ := step_inv h op
    have ha1 := step_agree h ha op (hm op List.mem_cons_self)
    have := ih (fun o ho => hm o (List.mem_cons_of_mem _ ho)) _ _ h1 ha1
    simp only [List.foldl_cons]
    rw [hK, hV] at this
    exact this

theorem new_inv (K V : JTy) : DInv (IdDict.new K V) :=
  ⟨List.nodup_nil, rfl, fun p hp => by simp [IdDict.new] at hp⟩

theorem runD_inv (K V : JTy) (ops : List DOp) :
    DInv (runD K V ops) ∧ (runD K V ops).K = K ∧ (runD K V ops).V = V :=
  fold_inv ops _ (new_inv K V)

/-! ## Observations -/

theorem iterate_ok {d : IdDict} (h : DInv d) : d.iterate = .ok d.ht := by
  unfold IdDict.iterate
  have ht := h.2.2
  generalize d.ht = t at ht ⊢
  induction t with
  | nil => rfl
  | cons p t ih =>
    have hp := ht p List.mem_cons_self
    have ih := ih (fun q hq => ht q (List.mem_cons_of_mem _ hq))
    rw [List.mapM_cons, ih]
    simp [cast_ok hp.1, cast_ok hp.2, bind, Except.bind, pure, Except.pure]

theorem get_eq {d : IdDict} (h : DInv d) (q dflt : JVal) :
    d.get q dflt = .ok ((rLookup d.ht q).getD dflt) := by
  unfold IdDict.get
  rw [eqtableGet_eq]
  cases hl : rLookup d.ht q with
  | none => simp
  | some v =>
    by_cases hv : v = dflt
    · subst hv; simp
    · have := (h.2.2 _ (rLookup_mem hl)).2
      simp [hv, cast_ok this]

/-! ## Registry theorems -/

theorem idDictOpsAgree_proven : IdDictOpsAgree := by
  intro K V ops hm
  dsimp only
  obtain ⟨h, hK, hV⟩ := runD_inv K V ops
  have ha := fold_agree ops hm (IdDict.new K V) [] (new_inv K V) ⟨List.nodup_nil, List.nodup_nil, fun _ => rfl, rfl⟩
  change Agree (runD K V ops).ht (refD K V ops) at ha
  refine ⟨fun q dflt => ?_, ?_, (runD K V ops).ht, iterate_ok h, ha.1, ha.2.2.1⟩
  · rw [get_eq h, ha.2.2.1]
  · rw [IdDict.length, h.2.1, ha.2.2.2]

theorem idDictLengthLive_proven : IdDictLengthLive := by
  intro K V ops
  dsimp only
  have h := (runD_inv K V ops).1
  exact ⟨_, iterate_ok h, h.2.1, h.1⟩

theorem idDictGetBangAbsent_proven : IdDictGetBangAbsent := by
  intro K V ops k dflt w
  dsimp only
  intro habs hk hc
  have h := (runD_inv K V ops).1
  have hK := (runD_inv K V ops).2.1
  have hV := (runD_inv K V ops).2.2
  rw [← hK] at hk
  rw [← hV] at hc
  generalize runD K V ops = d at h habs hk hc ⊢
  have hval : eqtableGet d.ht k token = token := by rw [eqtableGet_eq, habs]; rfl
  have hw : isa w d.V = true := convert_isa hc
  have hcw : convert d.V w = .ok w := convert_self hw
  obtain ⟨hht, hcount, hres⟩ := (setindex_spec d w k).2.2.1 hk w hcw
  have hgb : d.getBang k dflt = ((d.setindex w k).1, ((d.setindex w k).2.map fun _ => w)) := by
    unfold IdDict.getBang
    dsimp only
    rw [hval, valConv, hc]
    simp
  have hinv := (setindex_inv h w k).1
  rw [hgb]
  refine ⟨?_, ?_, ?_⟩
  · rw [hres]; rfl
  · rw [get_eq hinv, hht, put_lookup]; simp
  · simp only [IdDict.length]; rw [hcount, put_ins, habs]; rfl

end JuliaLean.IdDicts
