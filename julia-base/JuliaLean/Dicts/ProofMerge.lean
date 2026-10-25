import JuliaLean.Dicts.ProofBulk

/-!
# `Dict()` from pairs, `merge!` and `mergewith!`

`merge!` and `mergewith!` insert the pairs of the other dictionary in its slot
order. For pairwise non-`isequal` keys the reference updates `rset` and
`rcombine` commute up to the order of the association list, so any order gives
the same map.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

theorem Rep.perm {o : KeyOps K} {t : Table K V} {m m' : RMap K V} (h : Rep o t m)
    (hp : List.Perm m m') : Rep o t m' := ⟨h.1, h.2.trans hp⟩

theorem Rep.distinct {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m) :
    Distinct o m := (tlist_pairwise h.1).perm h.2 (fun h => eq_false_symm hl h)

theorem Rep.count_eq {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) :
    t.count = m.length := by rw [h.1.count, h.2.length_eq]

theorem empty_rep (o : KeyOps K) : Rep o (Table.empty : Table K V) [] :=
  ⟨⟨Or.inl rfl, Nat.zero_le _, fun _ _ _ => Or.inl rfl,
    fun _ _ _ _ _ h2 _ _ _ _ _ => absurd h2 (by show ¬ _ ≤ 0; omega), rfl, Or.inl rfl,
    Nat.le_refl _, fun _ _ h2 _ => absurd h2 (by show ¬ _ ≤ 0; omega), Nat.le_refl _⟩,
    List.Perm.nil⟩

theorem rset_length_le (o : KeyOps K) (m : RMap K V) (k : K) (v : V) :
    (rset o m k v).length ≤ m.length + 1 := by
  show (List.filter _ m).length + 1 ≤ m.length + 1
  have := List.length_filter_le (fun e : K × V => !o.eq k e.1) m
  omega

/-! ## Folding `setindex!` -/

theorem Rep.setFold {o : KeyOps K} (hl : o.Lawful) (B : Nat) :
    ∀ (ps : List (K × V)) (t : Table K V) (m : RMap K V), Rep o t m →
      t.count + ps.length ≤ 2 ^ 32 → 2 * (t.count + ps.length) + 21 ≤ B →
      ∃ t', ps.foldlM (fun t kv => JuliaLean.Dicts.setindex o t kv.2 kv.1) t = .ok t' ∧
        Rep o t' (ps.foldl (fun m kv => rset o m kv.1 kv.2) m) ∧ t'.count ≤ t.count + ps.length ∧
        ∃ n, n ≤ ps.length * B ∧ AgeStep t t' n
  | [], t, _, h, _, _ => ⟨t, rfl, h, by simp, 0, Nat.zero_le _, AgeStep.refl t⟩
  | kv :: ps, t, m, h, hc, hB => by
    simp only [List.length_cons] at hc hB
    obtain ⟨t1, h1, hr1, n1, -, hn1, ha1⟩ := h.setindex hl (by omega) kv.1 kv.2
    have hc1 : t1.count ≤ t.count + 1 := by
      rw [hr1.count_eq, h.count_eq]
      exact rset_length_le o m kv.1 kv.2
    obtain ⟨t2, h2, hr2, hc2, n2, hn2, ha2⟩ :=
      Rep.setFold hl B ps t1 _ hr1 (by omega) (by omega)
    refine ⟨t2, ?_, hr2, by simp only [List.length_cons]; omega, n1 + n2, ?_, ha1.trans ha2⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem buildDict_spec {o : KeyOps K} (hl : o.Lawful) (ps : List (K × V)) (hps : ps.length ≤ 2 ^ 32) :
    ∃ d2, buildDict o ps = .ok d2 ∧ Rep o d2 (rbuild o ps) ∧ d2.count ≤ ps.length := by
  obtain ⟨d2, h1, h2, h3, -⟩ := Rep.setFold hl (2 * (0 + ps.length) + 21) ps Table.empty []
    (empty_rep o) (by show 0 + ps.length ≤ 2 ^ 32; omega) (Nat.le_refl _)
  exact ⟨d2, h1, h2, by have : (Table.empty : Table K V).count = 0 := rfl; omega⟩

/-! ## Reordering `rset` -/

theorem rset_perm {o : KeyOps K} {m1 m2 : RMap K V} (hp : List.Perm m1 m2) (k : K) (v : V) :
    List.Perm (rset o m1 k v) (rset o m2 k v) := (hp.filter _).cons _

theorem foldl_rset_perm_init {o : KeyOps K} :
    ∀ (l : List (K × V)) {m1 m2 : RMap K V}, List.Perm m1 m2 →
      List.Perm (l.foldl (fun m kv => rset o m kv.1 kv.2) m1) (l.foldl (fun m kv => rset o m kv.1 kv.2) m2)
  | [], _, _, hp => hp
  | kv :: l, _, _, hp => foldl_rset_perm_init l (rset_perm hp kv.1 kv.2)

theorem rdel_comm (o : KeyOps K) (m : RMap K V) (a b : K) :
    rdel o (rdel o m a) b = rdel o (rdel o m b) a := by
  unfold rdel
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro x _
  rw [Bool.and_comm]

theorem rdel_cons_ne {o : KeyOps K} {m : RMap K V} {a : K} {e : K × V} (h : o.eq a e.1 = false) :
    rdel o (e :: m) a = e :: rdel o m a := by
  unfold rdel
  rw [List.filter_cons_of_pos (by simp [h])]

theorem rset_swap {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (x y : K × V)
    (hxy : o.eq x.1 y.1 = false) :
    List.Perm (rset o (rset o m y.1 y.2) x.1 x.2) (rset o (rset o m x.1 x.2) y.1 y.2) := by
  unfold rset
  rw [rdel_cons_ne (e := (y.1, y.2)) hxy, rdel_cons_ne (e := (x.1, x.2)) (eq_false_symm hl hxy),
    rdel_comm]
  exact List.Perm.swap _ _ _

theorem foldl_rset_perm {o : KeyOps K} (hl : o.Lawful) {l l' : List (K × V)} (hp : List.Perm l l') :
    Distinct o l → ∀ m : RMap K V,
      List.Perm (l.foldl (fun m kv => rset o m kv.1 kv.2) m) (l'.foldl (fun m kv => rset o m kv.1 kv.2) m) := by
  induction hp with
  | nil => exact fun _ m => List.Perm.refl _
  | cons x _ ih => exact fun hd m => ih (List.pairwise_cons.1 hd).2 _
  | swap x y l =>
    intro hd m
    have hyx : o.eq y.1 x.1 = false := (List.pairwise_cons.1 hd).1 x List.mem_cons_self
    exact foldl_rset_perm_init l (rset_swap hl m y x hyx).symm
  | trans p1 _ ih1 ih2 => exact fun hd m => (ih1 hd m).trans (ih2 (hd.perm hl p1) m)

/-! ## Reordering `rcombine` -/

/-- The pair `rcombine` puts in front. -/
def rcHead (o : KeyOps K) (f : V → V → V) (m : RMap K V) (kv : K × V) : K × V :=
  match rfind o m kv.1 with
  | some (k0, w) => (k0, f w kv.2)
  | none => (kv.1, kv.2)

theorem rcombine_eq (o : KeyOps K) (f : V → V → V) (m : RMap K V) (kv : K × V) :
    rcombine o f m kv = rcHead o f m kv :: rdel o m kv.1 := by
  unfold rcombine rcHead
  cases rfind o m kv.1 with
  | some e => obtain ⟨k0, w⟩ := e; rfl
  | none => rfl

theorem rcHead_eq {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) (m : RMap K V) (kv : K × V) :
    o.eq kv.1 (rcHead o f m kv).1 = true := by
  unfold rcHead
  cases h : rfind o m kv.1 with
  | some e =>
    obtain ⟨k0, w⟩ := e
    exact (rfind_some h).2
  | none => exact hl.refl _

theorem rfind_rcombine_ne {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) (m : RMap K V)
    (kv : K × V) {q : K} (hq : o.eq q kv.1 = false) :
    rfind o (rcombine o f m kv) q = rfind o m q := by
  rw [rcombine_eq]
  have hne : o.eq q (rcHead o f m kv).1 = false := by
    cases h : o.eq q (rcHead o f m kv).1
    · rfl
    · rw [hl.trans q _ kv.1 h (hl.symm _ _ (rcHead_eq hl f m kv))] at hq
      cases hq
  unfold rfind
  rw [List.find?_cons_of_neg (p := fun e : K × V => o.eq q e.1) (a := rcHead o f m kv)
    (by simp [hne])]
  exact rfind_rdel_ne hl m hq

theorem rcHead_rcombine {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) (m : RMap K V)
    (x y : K × V) (hxy : o.eq x.1 y.1 = false) :
    rcHead o f (rcombine o f m y) x = rcHead o f m x := by
  unfold rcHead
  rw [rfind_rcombine_ne hl f m y hxy]

theorem rcombine_swap {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) (m : RMap K V) (x y : K × V)
    (hxy : o.eq x.1 y.1 = false) :
    List.Perm (rcombine o f (rcombine o f m y) x) (rcombine o f (rcombine o f m x) y) := by
  have hyx := eq_false_symm hl hxy
  have hx : o.eq x.1 (rcHead o f m y).1 = false := by
    cases h : o.eq x.1 (rcHead o f m y).1
    · rfl
    · rw [hl.trans x.1 _ y.1 h (hl.symm _ _ (rcHead_eq hl f m y))] at hxy
      cases hxy
  have hy : o.eq y.1 (rcHead o f m x).1 = false := by
    cases h : o.eq y.1 (rcHead o f m x).1
    · rfl
    · rw [hl.trans y.1 _ x.1 h (hl.symm _ _ (rcHead_eq hl f m x))] at hyx
      cases hyx
  rw [rcombine_eq, rcombine_eq o f (rcombine o f m x), rcHead_rcombine hl f m x y hxy,
    rcHead_rcombine hl f m y x hyx, rcombine_eq, rcombine_eq, rdel_cons_ne hx, rdel_cons_ne hy,
    rdel_comm]
  exact List.Perm.swap _ _ _

theorem distinct_rcombine {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) {m : RMap K V}
    (h : Distinct o m) (kv : K × V) : Distinct o (rcombine o f m kv) := by
  rw [rcombine_eq]
  refine List.Pairwise.cons (fun b hb => ?_) (distinct_rdel h kv.1)
  rw [mem_rdel] at hb
  rw [eq_congr_left hl (hl.symm _ _ (rcHead_eq hl f m kv))]
  exact hb.2

theorem rcombine_perm_init {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) {m1 m2 : RMap K V}
    (hd : Distinct o m1) (hp : List.Perm m1 m2) (kv : K × V) :
    List.Perm (rcombine o f m1 kv) (rcombine o f m2 kv) := by
  rw [rcombine_eq, rcombine_eq]
  have : rcHead o f m1 kv = rcHead o f m2 kv := by
    unfold rcHead
    rw [rfind_perm hl hd hp]
  rw [this]
  exact (hp.filter _).cons _

theorem foldl_rcombine_perm_init {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) :
    ∀ (l : List (K × V)) {m1 m2 : RMap K V}, Distinct o m1 → List.Perm m1 m2 →
      List.Perm (l.foldl (rcombine o f) m1) (l.foldl (rcombine o f) m2)
  | [], _, _, _, hp => hp
  | kv :: l, _, _, hd, hp =>
    foldl_rcombine_perm_init hl f l (distinct_rcombine hl f hd kv) (rcombine_perm_init hl f hd hp kv)

theorem distinct_foldl_rcombine {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) :
    ∀ (l : List (K × V)) {m : RMap K V}, Distinct o m → Distinct o (l.foldl (rcombine o f) m)
  | [], _, hd => hd
  | kv :: l, _, hd => distinct_foldl_rcombine hl f l (distinct_rcombine hl f hd kv)

theorem foldl_rcombine_perm {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) {l l' : List (K × V)}
    (hp : List.Perm l l') :
    Distinct o l → ∀ m : RMap K V, Distinct o m →
      List.Perm (l.foldl (rcombine o f) m) (l'.foldl (rcombine o f) m) := by
  induction hp with
  | nil => exact fun _ m _ => List.Perm.refl _
  | cons x _ ih => exact fun hd m hm => ih (List.pairwise_cons.1 hd).2 _ (distinct_rcombine hl f hm x)
  | swap x y l =>
    intro hd m hm
    have hyx : o.eq y.1 x.1 = false := (List.pairwise_cons.1 hd).1 x List.mem_cons_self
    exact foldl_rcombine_perm_init hl f l
      (distinct_rcombine hl f (distinct_rcombine hl f hm y) x)
      (rcombine_swap hl f m x y (eq_false_symm hl hyx))
  | trans p1 _ ih1 ih2 => exact fun hd m hm => (ih1 hd m hm).trans (ih2 (hd.perm hl p1) m hm)

theorem rcombine_length_le (o : KeyOps K) (f : V → V → V) (m : RMap K V) (kv : K × V) :
    (rcombine o f m kv).length ≤ m.length + 1 := by
  rw [rcombine_eq, List.length_cons]
  have := List.length_filter_le (fun e : K × V => !o.eq kv.1 e.1) m
  unfold rdel
  omega

/-! ## `merge!` -/

theorem dictMerge_eq (o : KeyOps K) (d other : Table K V) :
    dictMerge o d other = (sizehint o d (JInt.lit .i64 ((d.count + other.count : Nat) : Int)) false >>=
      fun d => iterList other >>= fun items =>
        items.foldlM (fun d kv => setindex o d kv.2 kv.1) d) := rfl

/-- The size hint of `merge!`/`mergewith!` keeps the pairs. -/
theorem merge_hint {o : KeyOps K} (hmv : MaxValuesOK o) {d : Table K V} {m : RMap K V}
    (h : Rep o d m) (c : Nat) (hc : d.count + c ≤ 2 ^ 32) :
    ∃ d1, sizehint o d (JInt.lit .i64 ((d.count + c : Nat) : Int)) false = .ok d1 ∧ Rep o d1 m ∧
      d1.count = d.count ∧ ∃ k, k ≤ 2 ∧ AgeStep d d1 k := by
  obtain ⟨d1, h1, hi1, hp1, hc1, k, hk, ha⟩ := sizehint_spec hmv h.1 (by omega)
    (JInt.lit .i64 ((d.count + c : Nat) : Int))
    (by rw [lit_i64_val (by omega) (by omega)]; omega) false
  exact ⟨d1, h1, ⟨hi1, hp1.trans h.2⟩, hc1, k, hk, ha⟩

theorem Rep.dictMerge {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) {d d2 : Table K V}
    {m m2 : RMap K V} (h : Rep o d m) (h2 : Rep o d2 m2) (hc : d.count + d2.count ≤ 2 ^ 32) :
    ∃ t', dictMerge o d d2 = .ok t' ∧
      Rep o t' (m2.foldl (fun m kv => rset o m kv.1 kv.2) m) ∧ t'.count ≤ d.count + d2.count ∧
      ∃ n, n ≤ (1 + d2.count) * (2 * (d.count + d2.count) + 21) ∧ AgeStep d t' n := by
  obtain ⟨d1, h1, hr1, hc1, k, hk, ha1⟩ := merge_hint hmv h d2.count hc
  have hlen : (tlist d2).length = d2.count := h2.1.count.symm
  obtain ⟨t', h3, hr3, hc3, n, hn, ha3⟩ := Rep.setFold hl (2 * (d.count + d2.count) + 21) (tlist d2)
    d1 m hr1 (by omega) (by omega)
  refine ⟨t', ?_, hr3.perm (foldl_rset_perm hl h2.2 (tlist_pairwise h2.1) m), by omega, k + n, ?_,
    ha1.trans ha3⟩
  · simp only [dictMerge_eq, h1, except_ok_bind, iterList_eq h2.1]
    exact h3
  · rw [hlen] at hn
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-! ## `mergewith!` -/

/-- One iteration of the `mergewith!` loop. -/
def mstep (o : KeyOps K) (combine : V → V → V) (d1 : Table K V) (kv : K × V) : DR (Table K V) := do
  let (k, v) := kv
  let (i, sh, d1) ← keyindex2 o d1 (o.hash k) (o.eq k)
  if i > 0 then
    let w ← valAt d1 i.toNat
    pure { d1 with vals := upd d1.vals i.toNat (some (combine w v)) }
  else setindexAt o d1 v k (-i).toNat sh

theorem mergewith_eq (o : KeyOps K) (f : V → V → V) (d1 d2 : Table K V) :
    mergewith o f d1 d2 = (sizehint o d1 (JInt.lit .i64 ((d1.count + d2.count : Nat) : Int)) false >>=
      fun d1 => iterList d2 >>= fun items => items.foldlM (mstep o f) d1) := rfl

theorem mstep_of {o : KeyOps K} {f : V → V → V} {d t1 : Table K V} {k : K} {v : V} {idx : Int}
    {sh : Nat} (h : keyindex2 o d (o.hash k) (o.eq k) = .ok (idx, sh, t1)) :
    mstep o f d (k, v) = if idx > 0 then
      (valAt t1 idx.toNat >>= fun w => pure { t1 with vals := upd t1.vals idx.toNat (some (f w v)) })
      else setindexAt o t1 v k (-idx).toNat sh := by
  unfold mstep
  dsimp only
  rw [h]
  rfl

/-- Replacing the value of the entry at slot `i`. -/
theorem valUpdate_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {i : Nat}
    {k0 : K} {w : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some (k0, w)) (x : V) :
    Inv o { t with vals := upd t.vals i (some x) } ∧
      List.Perm (tlist { t with vals := upd t.vals i (some x) })
        ((k0, x) :: (tlist t).filter (fun b => !o.eq k0 b.1)) := by
  obtain ⟨hI, hP, -⟩ := overwrite_spec hl hi h1 h2 he (hl.refl k0) x
  have hk : upd t.keys i (some k0) = t.keys := by
    funext p
    by_cases hp : p = i
    · rw [hp, upd_same, (ent_some he).2.1]
    · rw [upd_ne _ _ hp]
  have hT : ({ t with vals := upd t.vals i (some x) } : Table K V) =
      { overwriteAt t x k0 i with age := t.age } := by
    unfold overwriteAt
    rw [hk] <;> rfl
  rw [hT]
  exact ⟨⟨hI.size, hI.sizeLe, hI.slot, hI.distinct, hI.count, hI.maxprobe, hI.idxfloor, hI.floorLe,
    hI.popcursor⟩, hP⟩

theorem Rep.mstep {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) {d : Table K V} {m : RMap K V}
    (h : Rep o d m) (hc : d.count < 2 ^ 33) (kv : K × V) :
    ∃ d', mstep o f d kv = .ok d' ∧ Rep o d' (rcombine o f m kv) ∧
      ∃ n, n ≤ 2 * d.count + 21 ∧ AgeStep d d' n := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨idx, t1, n1, hk2, hn1, hout⟩ := keyindex2_spec hl h.1 hc k
  rw [mstep_of hk2]
  rcases present_or_absent o d k with ⟨i, ⟨k0, w⟩, h1, h2, he, hq⟩ | habs
  · obtain ⟨hidx, ht1⟩ := hout.found i (k0, w) h1 h2 he hq
    rw [hidx, ht1, if_pos (by omega), Int.toNat_natCast, valAt_of_ent he]
    obtain ⟨hI, hP⟩ := valUpdate_spec hl h.1 h1 h2 he (f w v)
    have hrf : rfind o m k = some (k0, w) :=
      rfind_of_mem hl (h.distinct hl) (h.2.mem_iff.1 (mem_tlist.2 ⟨i, h1, h2, he⟩)) hq
    have hrc : rcombine o f m (k, v) = (k0, f w v) :: rdel o m k := by
      unfold rcombine
      rw [hrf] <;> rfl
    have hfilt : (tlist d).filter (fun b => !o.eq k0 b.1) = (tlist d).filter (fun b => !o.eq k b.1) :=
      List.filter_congr (fun b _ => by
        show (!o.eq k0 b.1) = (!o.eq k b.1)
        rw [eq_congr_left hl hq])
    refine ⟨_, rfl, ⟨hI, ?_⟩, 0, Nat.zero_le _,
      ⟨(ageAdd_zero _).symm, fun _ => ⟨rfl, rfl, rfl, Nat.le_refl _⟩⟩⟩
    rw [hrc]
    refine hP.trans (List.Perm.cons _ ?_)
    rw [hfilt]
    exact h.2.filter _
  · obtain ⟨hneg, hslot⟩ := hout.absent habs
    rw [if_neg (by omega)]
    have habs1 : Absent o t1 k := fun b hb => habs b (hout.perm.mem_iff.1 hb)
    obtain ⟨t', h1', hi', hp', -, n2, -, hn2b, hage⟩ :=
      setindexAt_spec hl hout.inv v hslot habs1 (by rw [hout.count]; exact hc)
    have hrf : rfind o m k = none := rfind_none fun b hb => habs b (h.2.mem_iff.2 hb)
    have hm : rdel o m k = m := rdel_of_absent fun b hb => habs b (h.2.mem_iff.2 hb)
    have hrc : rcombine o f m (k, v) = (k, v) :: m := by
      unfold rcombine
      rw [hrf]
      show (k, v) :: rdel o m k = _
      rw [hm]
    refine ⟨t', h1', ⟨hi', ?_⟩, n1 + n2, by omega, hout.age.trans hage⟩
    rw [hrc]
    exact hp'.trans (List.Perm.cons _ (hout.perm.trans h.2))

theorem Rep.mergeFold {o : KeyOps K} (hl : o.Lawful) (f : V → V → V) (B : Nat) :
    ∀ (ps : List (K × V)) (t : Table K V) (m : RMap K V), Rep o t m →
      t.count + ps.length ≤ 2 ^ 32 → 2 * (t.count + ps.length) + 21 ≤ B →
      ∃ t', ps.foldlM (JuliaLean.Dicts.mstep o f) t = .ok t' ∧ Rep o t' (ps.foldl (rcombine o f) m) ∧
        t'.count ≤ t.count + ps.length ∧ ∃ n, n ≤ ps.length * B ∧ AgeStep t t' n
  | [], t, _, h, _, _ => ⟨t, rfl, h, by simp, 0, Nat.zero_le _, AgeStep.refl t⟩
  | kv :: ps, t, m, h, hc, hB => by
    simp only [List.length_cons] at hc hB
    obtain ⟨t1, h1, hr1, n1, hn1, ha1⟩ := h.mstep hl f (by omega) kv
    have hc1 : t1.count ≤ t.count + 1 := by
      rw [hr1.count_eq, h.count_eq]
      exact rcombine_length_le o f m kv
    obtain ⟨t2, h2, hr2, hc2, n2, hn2, ha2⟩ :=
      Rep.mergeFold hl f B ps t1 _ hr1 (by omega) (by omega)
    refine ⟨t2, ?_, hr2, by simp only [List.length_cons]; omega, n1 + n2, ?_, ha1.trans ha2⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem Rep.mergewith {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) (f : V → V → V)
    {d d2 : Table K V} {m m2 : RMap K V} (h : Rep o d m) (h2 : Rep o d2 m2)
    (hc : d.count + d2.count ≤ 2 ^ 32) :
    ∃ t', mergewith o f d d2 = .ok t' ∧ Rep o t' (m2.foldl (rcombine o f) m) ∧
      t'.count ≤ d.count + d2.count ∧
      ∃ n, n ≤ (1 + d2.count) * (2 * (d.count + d2.count) + 21) ∧ AgeStep d t' n := by
  obtain ⟨d1, h1, hr1, hc1, k, hk, ha1⟩ := merge_hint hmv h d2.count hc
  have hlen : (tlist d2).length = d2.count := h2.1.count.symm
  obtain ⟨t', h3, hr3, hc3, n, hn, ha3⟩ := Rep.mergeFold hl f (2 * (d.count + d2.count) + 21)
    (tlist d2) d1 m hr1 (by omega) (by omega)
  refine ⟨t', ?_, hr3.perm (foldl_rcombine_perm hl f h2.2 (tlist_pairwise h2.1) m (h.distinct hl)),
    by omega, k + n, ?_, ha1.trans ha3⟩
  · simp only [mergewith_eq, h1, except_ok_bind, iterList_eq h2.1]
    exact h3
  · rw [hlen] at hn
    rw [Nat.add_mul, Nat.one_mul]
    omega

end JuliaLean.Dicts
