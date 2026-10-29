import JuliaLean.MultidimCov.ArrayV2Delete

/-!
Properties of deletion by index collections, `splice!` and `keepat!`
(`ArrayV2Delete.lean`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-! ### Specification vocabulary -/

/-- `inds` is sorted and unique when every element is greater than the one before it,
`lo` included. -/
def IncrFrom (lo : Int) : List Int → Prop
  | [] => True
  | i :: l => lo < i ∧ IncrFrom i l

/-- `inds` is sorted and unique (each index less than the next). -/
def Incr : List Int → Prop
  | [] => True
  | i :: l => IncrFrom i l

/-- The positions `1..m` that `del` does not mark, in increasing order. -/
def keepBy (m : Int) (del : Int → Bool) : List Int :=
  ((List.range m.toNat).map fun k : Nat => (k : Int) + 1).filter fun k => !del k

/-- The indices `1..n` not in `inds`, in increasing order. -/
def keepIdx (n : Int) (inds : List Int) : List Int := keepBy n fun k => decide (k ∈ inds)

/-- The positions `k` (1-based) with `mask[k] == b`, in increasing order. -/
def maskIdx (mask : List Bool) (b : Bool) : List Int :=
  ((List.range mask.length).filter fun k => mask.getD k false == b).map fun k : Nat => (k : Int) + 1

/-! ### Helper lemmas -/

theorem m239_in {a : Arr α} {q : Int} (h1 : 1 ≤ q) (h2 : q ≤ length a) : m239 a q = (a.at q).isSome := by
  unfold m239 assignedU
  rw [if_neg (by rw [inBounds_iff]; simp; omega)]

theorem m1961_ok {a : Arr α} {p q : Int} (h1 : 1 ≤ q) (h2 : q ≤ length a) :
    m1961 a p q = .ok (setU a p (a.at q)) := by
  unfold m1961
  rw [m239_in h1 h2]
  cases h : a.at q <;> simp [getU, h]

theorem m1952_ok {a : Arr α} {i : Int} (d : Option (List (Option α))) (h1 : 1 ≤ i) (h2 : i ≤ length a) :
    m1952 d a i = .ok (dltdPush d (a.at i)) := by
  unfold m1952
  rw [m239_in h1 h2]
  cases h : a.at i <;> simp [getU, h]

theorem keepBy_succ (del : Int → Bool) {m : Int} (hm : 0 ≤ m) :
    keepBy (m + 1) del = keepBy m del ++ (if del (m + 1) then [] else [m + 1]) := by
  unfold keepBy
  rw [show (m + 1).toNat = m.toNat + 1 by omega, List.range_succ, List.map_append, List.filter_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  rw [show ((m.toNat : Nat) : Int) + 1 = m + 1 by omega]
  cases del (m + 1) <;> simp

theorem keepBy_length_le (del : Int → Bool) (m : Int) : ((keepBy m del).length : Int) ≤ max m 0 := by
  unfold keepBy
  have := List.length_filter_le (fun k => !del k) ((List.range m.toNat).map fun k : Nat => (k : Int) + 1)
  simp only [List.length_map, List.length_range] at this
  omega

theorem keepBy_none (del : Int → Bool) {m : Int} (h : ∀ k, 1 ≤ k → k ≤ m → del k = false) :
    keepBy m del = (List.range m.toNat).map fun k : Nat => (k : Int) + 1 := by
  unfold keepBy
  rw [List.filter_eq_self]
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [h _ (by omega) (by omega)]; rfl

/-- The state of the compaction loops of `_deleteat!` and `deleteat!(a, mask)`: `q` is the
next position to read, slots `q..` are the original ones, and slots `1..p-1` hold the
kept original slots before `q`. -/
structure DInv (o a : Arr α) (del : Int → Bool) (p q : Int) : Prop where
  dims : a.dims = o.dims
  off : a.off = o.off
  mlen : a.mem.len = o.mem.len
  hi : ∀ k, q ≤ k → a.at k = o.at k
  lo : ∀ (k : Nat) x, (keepBy (q - 1) del)[k]? = some x → a.at ((k : Int) + 1) = o.at x
  plen : p - 1 = ((keepBy (q - 1) del).length : Int)
  pq : p ≤ q
  q1 : 1 ≤ q

theorem DInv.length_eq {o a : Arr α} {del p q} (h : DInv o a del p q) : length a = length o := by
  simp [length, h.dims]

theorem dinv_copy {o a : Arr α} {del p q} (h : DInv o a del p q) (hq : del q = false) :
    DInv o (setU a p (o.at q)) del (p + 1) (q + 1) := by
  have hK : keepBy (q + 1 - 1) del = keepBy (q - 1) del ++ [q] := by
    rw [show q + 1 - 1 = q - 1 + 1 by omega, keepBy_succ del (by have := h.q1; omega),
      show q - 1 + 1 = q by omega, hq]; rfl
  have hp := h.plen; have hpq := h.pq
  refine ⟨by simp [h.dims], by simp [h.off], by simp [h.mlen], fun k hk => ?_, fun k x hx => ?_, ?_,
    by omega, by have := h.q1; omega⟩
  · rw [setU_at, if_neg (by omega)]; exact h.hi k (by omega)
  · rw [hK] at hx
    rw [setU_at]
    by_cases hk : k < (keepBy (q - 1) del).length
    · rw [List.getElem?_append_left hk] at hx
      rw [if_neg (by omega)]; exact h.lo k x hx
    · rw [List.getElem?_append_right (by omega)] at hx
      by_cases hk2 : k - (keepBy (q - 1) del).length = 0
      · rw [hk2] at hx; simp at hx; subst hx
        rw [if_pos (by omega)]
      · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
  · rw [hK]; simp; omega

theorem dinv_skip {o a : Arr α} {del p q} (h : DInv o a del p q) (hq : del q = true) :
    DInv o a del p (q + 1) := by
  have hK : keepBy (q + 1 - 1) del = keepBy (q - 1) del := by
    rw [show q + 1 - 1 = q - 1 + 1 by omega, keepBy_succ del (by have := h.q1; omega),
      show q - 1 + 1 = q by omega, hq]; simp
  exact ⟨h.dims, h.off, h.mlen, fun k hk => h.hi k (by omega), fun k x hx => h.lo k x (by rwa [hK] at hx),
    by rw [hK]; exact h.plen, by have := h.pq; omega, by have := h.q1; omega⟩

theorem dinv_write_skip {o a : Arr α} {del p q} (h : DInv o a del p q) (hq : del q = true) (x : Option α) :
    DInv o (setU a p x) del p (q + 1) := by
  have h2 := dinv_skip h hq
  have hp := h2.plen; have hpq := h.pq
  refine ⟨by simp [h.dims], by simp [h.off], by simp [h.mlen], fun k hk => ?_, fun k y hy => ?_, h2.plen,
    h2.pq, h2.q1⟩
  · rw [setU_at, if_neg (by omega)]; exact h2.hi k hk
  · have hk : k < (keepBy (q + 1 - 1) del).length := by
      rcases Nat.lt_or_ge k (keepBy (q + 1 - 1) del).length with hc | hc
      · exact hc
      · rw [List.getElem?_eq_none hc] at hy; cases hy
    rw [setU_at, if_neg (by omega)]; exact h2.lo k y hy

theorem copyWhile_spec {o : Arr α} {del : Int → Bool} {i : Int} :
    ∀ (m : Nat) (a : Arr α) (p q : Int), (i - q).toNat = m → DInv o a del p q → q ≤ i →
    i ≤ length o + 1 → (∀ k, q ≤ k → k < i → del k = false) →
    ∃ a', copyWhile a p q i = .ok (a', p + (i - q), i) ∧ DInv o a' del (p + (i - q)) i
  | 0, a, p, q, hm, h, hqi, hi, _ => by
    have : q = i := by omega
    subst this
    rw [copyWhile]; rw [if_neg (by omega)]
    exact ⟨a, by simp, by simpa using h⟩
  | m + 1, a, p, q, hm, h, hqi, hi, hd => by
    rw [copyWhile, if_pos (by omega), m1961_ok h.q1 (by rw [h.length_eq]; omega), bind_ok,
      h.hi q (Int.le_refl q)]
    have h2 := dinv_copy h (hd q (Int.le_refl q) (by omega))
    obtain ⟨a', e, h3⟩ := copyWhile_spec m _ (p + 1) (q + 1) (by omega) h2 (by omega) hi
      (fun k h1 h2 => hd k (by omega) h2)
    refine ⟨a', ?_, ?_⟩
    · rw [e]; congr 3; omega
    · rw [show p + (i - q) = p + 1 + (i - (q + 1)) by omega]; exact h3

theorem IncrFrom_gt : ∀ {lo : Int} {l : List Int}, IncrFrom lo l → ∀ x ∈ l, lo < x
  | _, [], _, x, hx => by simp at hx
  | lo, i :: l, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · have := IncrFrom_gt h2 x hx; omega

theorem delLoop_spec {o : Arr α} {inds : List Int} :
    ∀ (rest : List Int) (a : Arr α) (d : Option (List (Option α))) (p q : Int),
    DInv o a (fun k => decide (k ∈ inds)) p q → IncrFrom (q - 1) rest → (∀ i ∈ rest, i ≤ length o) →
    q ≤ length o + 1 → (∀ m, q ≤ m → (m ∈ inds ↔ m ∈ rest)) →
    ∃ a' p' q', delLoop (length o) a d p q rest = .ok (a', (rest.map o.at).foldl dltdPush d, p', q') ∧
      DInv o a' (fun k => decide (k ∈ inds)) p' q' ∧ q' ≤ length o + 1 ∧ ∀ m, q' ≤ m → m ∉ inds
  | [], a, d, p, q, h, _, _, hq, hiff => ⟨a, p, q, by simp [delLoop], h, hq,
      fun m hm hmem => by simpa using (hiff m hm).1 hmem⟩
  | i :: rest, a, d, p, q, h, ⟨hq1, hinc⟩, hle, hq, hiff => by
    have hi : i ≤ length o := hle i (by simp)
    unfold delLoop
    rw [if_neg (fun hc => hc ⟨by omega, hi⟩)]
    obtain ⟨a1, e1, h1⟩ := copyWhile_spec (i - q).toNat a p q rfl h (by omega) (by omega) (by
      intro k hk1 hk2
      simp only [decide_eq_false_iff_not]
      intro hk
      rcases List.mem_cons.mp ((hiff k hk1).1 hk) with rfl | h3
      · omega
      · have := IncrFrom_gt hinc k h3; omega)
    rw [e1, bind_ok]
    simp only []
    rw [m1952_ok d (by have := h.q1; omega) (by rw [h1.length_eq]; exact hi), bind_ok, h1.hi i (by omega)]
    have h2 := dinv_skip h1 (by simpa using (hiff i (by omega)).2 (by simp))
    obtain ⟨a', p', q', e, h3, h4, h5⟩ := delLoop_spec rest a1 (dltdPush d (o.at i)) (p + (i - q)) (i + 1) h2
      (by rw [show i + 1 - 1 = i by omega]; exact hinc) (fun x hx => hle x (by simp [hx])) (by omega)
      (fun m hm => ⟨fun hmi => ((List.mem_cons.mp ((hiff m (by omega)).1 hmi)).resolve_left (by omega)),
        fun hmr => (hiff m (by omega)).2 (by simp [hmr])⟩)
    exact ⟨a', p', q', by rw [e]; simp, h3, h4, h5⟩

theorem vecOK_of_same {a b : Arr α} {n : Int} (ha : VecOK a n) (hd : b.dims = a.dims) (ho : b.off = a.off)
    (hm : b.mem.len = a.mem.len) : VecOK b n := by
  obtain ⟨hv, ⟨h1, h2, h3⟩, h4⟩ := ha
  have hl : length b = length a := by simp [length, hd]
  exact ⟨by unfold IsVec; rw [hd]; exact hv, ⟨by rw [ho]; exact h1, by rw [hl]; exact h2,
    by rw [ho, hl, hm]; exact h3⟩, by unfold Small; rw [hm]; exact h4⟩

/-- The end of the compaction: `_deleteend!(a, n-p+1)` keeps exactly the kept slots. -/
theorem finish_spec {o a : Arr α} {n : Int} {del : Int → Bool} {p : Int} (ho : VecOK o n)
    (h : DInv o a del p (n + 1)) :
    ∃ a', m1296 a (n - p + 1) = .ok a' ∧ VecOK a' (keepBy n del).length ∧
      contents a' = (keepBy n del).map o.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ho
  have ha : VecOK a n := vecOK_of_same ho h.dims h.off h.mlen
  have hK : keepBy (n + 1 - 1) del = keepBy n del := by rw [show n + 1 - 1 = n by omega]
  have hp := h.plen; rw [hK] at hp
  have hL := keepBy_length_le del n
  obtain ⟨a', e, hv, hval, hml, hpt⟩ := m1296_spec ha (delta := n - p + 1) (by omega) (by omega)
  refine ⟨a', e, ⟨by unfold IsVec at *; rw [hv]; congr 1; omega, hval,
    by unfold Small; rw [hml]; exact ha.2.2⟩, ?_⟩
  apply contents_ext
  · rw [length_vec a' _ hv]; simp; omega
  · intro k hk
    simp only [List.length_map] at hk
    rw [hpt _ (by omega) (by omega), List.getElem_map]
    exact h.lo k _ (by rw [hK]; exact List.getElem?_eq_getElem hk)

theorem dinv_start {o : Arr α} {n : Int} {del : Int → Bool} (ho : VecOK o n) {p : Int} (hp1 : 1 ≤ p)
    (hdel : ∀ k, 1 ≤ k → k < p → del k = false) : DInv o o del p p := by
  have hK := keepBy_none del (m := p - 1) (fun k h1 h2 => hdel k h1 (by omega))
  refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun k x hx => ?_, by rw [hK]; simp; omega, Int.le_refl p, hp1⟩
  rw [hK, List.getElem?_map] at hx
  rcases Nat.lt_or_ge k (p - 1).toNat with hk | hk
  · rw [List.getElem?_range hk] at hx; simp at hx; rw [hx]
  · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx

/-- `_deleteat!(a, inds, dltd)` for sorted, unique, in-range indices. -/
theorem m1970_spec {a : Arr α} {n : Int} (ha : VecOK a n) {inds : List Int} (hinc : Incr inds)
    (hin : ∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) (d : Option (List (Option α))) :
    ∃ a', m1970 a inds d = .ok (a', (inds.map a.at).foldl dltdPush d) ∧
      VecOK a' (keepIdx n inds).length ∧ contents a' = (keepIdx n inds).map a.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  match inds, hinc, hin with
  | [], _, _ =>
    refine ⟨a, by simp [m1970], ?_, ?_⟩
    · have : (keepIdx n []).length = n := by
        unfold keepIdx; rw [keepBy_none _ (fun k _ _ => by simp)]; simp; omega
      rw [this]; exact ha
    · unfold keepIdx; rw [keepBy_none _ (fun k _ _ => by simp)]
      unfold contents; rw [List.map_map, hn]; rfl
  | p :: rest, hinc, hin =>
    have hp := hin p (by simp)
    have hgt := IncrFrom_gt hinc
    unfold m1970
    simp only []
    rw [if_neg (by rw [inBounds_iff, hn]; simp; omega), m1952_ok d hp.1 (by omega), bind_ok]
    have h0 := dinv_start ha (del := fun k => decide (k ∈ p :: rest)) hp.1 (by
      intro k h1 h2; simp only [decide_eq_false_iff_not, List.mem_cons, not_or]
      exact ⟨by omega, fun hk => by have := hgt k hk; omega⟩)
    have h1 := dinv_skip h0 (by simp)
    obtain ⟨a1, p1, q1, e1, h2, h3, h4⟩ := delLoop_spec (o := a) rest a (dltdPush d (a.at p)) p (p + 1) h1
      (by rw [show p + 1 - 1 = p by omega]; exact hinc) (fun x hx => by have := hin x (by simp [hx]); omega)
      (by omega) (fun m hm => ⟨fun hmi => (List.mem_cons.mp hmi).resolve_left (by omega), fun hmr => by simp [hmr]⟩)
    rw [e1, bind_ok]
    simp only []
    obtain ⟨a2, e2, h5⟩ := copyWhile_spec (length a + 1 - q1).toNat a1 p1 q1 rfl h2 h3 (Int.le_refl _)
      (fun k hk1 _ => by simpa using h4 k hk1)
    rw [e2, bind_ok]
    simp only []
    rw [hn] at h5 ⊢
    obtain ⟨a3, e3, hv3, hc3⟩ := finish_spec ha h5
    exact ⟨a3, by rw [e3]; simp, hv3, hc3⟩

theorem copyWhile_ok {i : Int} : ∀ (m : Nat) (a : Arr α) (p q : Int), (i - q).toNat = m → 1 ≤ q → q ≤ i →
    i ≤ length a + 1 → ∃ a', copyWhile a p q i = .ok (a', p + (i - q), i) ∧ a'.dims = a.dims
  | 0, a, p, q, hm, _, hqi, _ => by
    have : q = i := by omega
    subst this
    rw [copyWhile, if_neg (by omega)]
    exact ⟨a, by simp, rfl⟩
  | m + 1, a, p, q, hm, hq, hqi, hi => by
    rw [copyWhile, if_pos (by omega), m1961_ok (a := a) (p := p) hq (by omega), bind_ok]
    obtain ⟨a', e, hd⟩ := copyWhile_ok (i := i) m (setU a p (a.at q)) (p + 1) (q + 1) (by omega) (by omega) (by omega)
      (by simpa using hi)
    exact ⟨a', by rw [e]; congr 3; omega, by rw [hd]; rfl⟩

theorem delLoop_arg {n : Int} : ∀ (rest : List Int) (a : Arr α) (d : Option (List (Option α))) (p q : Int),
    length a = n → 1 ≤ q → (∀ i ∈ rest, 1 ≤ i ∧ i ≤ n) → ¬ IncrFrom (q - 1) rest →
    delLoop n a d p q rest = .error .argument
  | [], _, _, _, _, _, _, _, h => absurd trivial h
  | i :: rest, a, d, p, q, hn, hq, hin, hinc => by
    have hi := hin i (by simp)
    unfold delLoop
    by_cases hiq : i < q
    · rw [if_pos (fun hc => by omega), if_pos hiq]; rfl
    · rw [if_neg (fun hc => hc ⟨by omega, hi.2⟩)]
      obtain ⟨a1, e1, hd⟩ := copyWhile_ok (i - q).toNat a p q rfl hq (by omega) (by omega)
      have hl : length a1 = n := by simp [length, hd] at hn ⊢; exact hn
      rw [e1, bind_ok]
      simp only []
      rw [m1952_ok d hi.1 (by omega), bind_ok]
      exact delLoop_arg rest a1 _ _ (i + 1) hl (by omega) (fun x hx => hin x (by simp [hx]))
        (by rw [show i + 1 - 1 = i by omega]; exact fun hc => hinc ⟨by omega, hc⟩)

theorem delLoop_bounds {n : Int} : ∀ (rest : List Int) (a : Arr α) (d : Option (List (Option α))) (p q : Int),
    length a = n → 1 ≤ q → IncrFrom (q - 1) rest → (∃ i ∈ rest, n < i) →
    delLoop n a d p q rest = .error .bounds
  | [], _, _, _, _, _, _, _, h => by simp at h
  | i :: rest, a, d, p, q, hn, hq, ⟨hq1, hinc⟩, hex => by
    unfold delLoop
    by_cases hin : n < i
    · rw [if_pos (fun hc => by omega), if_neg (by omega)]
    · rw [if_neg (fun hc => hc ⟨by omega, by omega⟩)]
      obtain ⟨a1, e1, hd⟩ := copyWhile_ok (i - q).toNat a p q rfl hq (by omega) (by omega)
      have hl : length a1 = n := by simp [length, hd] at hn ⊢; exact hn
      rw [e1, bind_ok]
      simp only []
      rw [m1952_ok d (by omega) (by omega), bind_ok]
      obtain ⟨j, hj, hjn⟩ := hex
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      exact delLoop_bounds rest a1 _ _ (i + 1) hl (by omega) (by rw [show i + 1 - 1 = i by omega]; exact hinc)
        ⟨j, hj, hjn⟩

/-- `_deleteat!` throws `ArgumentError` for in-range indices that are not sorted and unique. -/
theorem m1970_arg {a : Arr α} {n : Int} (hn : length a = n) {inds : List Int}
    (hin : ∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) (hinc : ¬ Incr inds) (d : Option (List (Option α))) :
    m1970 a inds d = .error .argument := by
  match inds, hin, hinc with
  | [], _, h => exact absurd trivial h
  | p :: rest, hin, hinc =>
    have hp := hin p (by simp)
    unfold m1970
    simp only []
    rw [if_neg (by rw [inBounds_iff]; simp; omega), m1952_ok d hp.1 (by omega), bind_ok, hn,
      delLoop_arg rest a _ p (p + 1) hn (by omega) (fun x hx => hin x (by simp [hx]))
        (by rw [show p + 1 - 1 = p by omega]; exact hinc)]
    rfl

/-- `_deleteat!` throws `BoundsError` for sorted, unique indices reaching outside `1:n`. -/
theorem m1970_bounds {a : Arr α} {n : Int} (hn : length a = n) {inds : List Int}
    (hinc : Incr inds) (hout : ∃ i ∈ inds, i < 1 ∨ n < i) (d : Option (List (Option α))) :
    m1970 a inds d = .error .bounds := by
  match inds, hinc, hout with
  | [], _, h => simp at h
  | p :: rest, hinc, ⟨j, hj, hjb⟩ =>
    have hgt := IncrFrom_gt hinc
    unfold m1970
    simp only []
    by_cases hp : 1 ≤ p ∧ p ≤ n
    · rw [if_neg (by rw [inBounds_iff]; simp; omega), m1952_ok d hp.1 (by omega), bind_ok, hn,
        delLoop_bounds rest a _ p (p + 1) hn (by omega) (by rw [show p + 1 - 1 = p by omega]; exact hinc)]
      · rfl
      · rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · have := hgt j hj; exact ⟨j, hj, by omega⟩
    · rw [if_pos (by rw [inBounds_iff]; omega)]

/-- The mask loop of `deleteat!(a, mask)`. -/
theorem maskLoop_spec {o : Arr α} {mask : List Bool} :
    ∀ (rest : List Bool) (a : Arr α) (p q : Int),
    DInv o a (fun k => mask.getD (k - 1).toNat false) p q → rest = mask.drop (q - 1).toNat →
    q - 1 + rest.length = length o →
    ∃ a' p', maskLoop a p q rest = .ok (a', p') ∧
      DInv o a' (fun k => mask.getD (k - 1).toNat false) p' (length o + 1)
  | [], a, p, q, h, _, hl => ⟨a, p, rfl, by rw [show length o + 1 = q by simp at hl; omega]; exact h⟩
  | b :: rest, a, p, q, h, hr, hl => by
    have hq := h.q1
    have hb : mask.getD (q - 1).toNat false = b := by
      rw [List.getD_eq_getElem?_getD, show (q - 1).toNat = (q - 1).toNat + 0 by rfl, ← List.getElem?_drop,
        ← hr]; rfl
    have hr' : rest = mask.drop (q + 1 - 1).toNat := by
      rw [show (q + 1 - 1).toNat = (q - 1).toNat + 1 by omega, ← List.tail_drop, ← hr]; rfl
    simp only [List.length_cons] at hl
    unfold maskLoop
    rw [m1961_ok hq (by rw [h.length_eq]; omega), bind_ok, h.hi q (Int.le_refl q)]
    cases b with
    | true =>
      have h2 := dinv_write_skip h (by simpa using hb) (o.at q)
      obtain ⟨a', p', e, h3⟩ := maskLoop_spec rest _ p (q + 1) h2 hr' (by omega)
      exact ⟨a', p', by simpa using e, h3⟩
    | false =>
      have h2 := dinv_copy h (by simpa using hb)
      obtain ⟨a', p', e, h3⟩ := maskLoop_spec rest _ (p + 1) (q + 1) h2 hr' (by omega)
      exact ⟨a', p', by simpa using e, h3⟩

theorem keepBy_mask {mask : List Bool} {n : Int} (hn : 0 ≤ n) (hl : (mask.length : Int) = n) (b : Bool) :
    keepBy n (fun k => (mask.getD (k - 1).toNat false) == !b) = maskIdx mask b := by
  unfold keepBy maskIdx
  rw [List.filter_map, show n.toNat = mask.length by omega]
  congr 1
  apply List.filter_congr
  intro k _
  simp only [Function.comp, show ((k : Int) + 1 - 1).toNat = k by omega]
  cases mask.getD k false <;> cases b <;> rfl

/-- `deleteat!(a, mask)` on a vector of the same length. -/
theorem m2005_spec {a : Arr α} {n : Int} (ha : VecOK a n) {mask : List Bool} (hl : (mask.length : Int) = n) :
    ∃ a', m2005 a mask = .ok a' ∧ VecOK a' (maskIdx mask false).length ∧
      contents a' = (maskIdx mask false).map a.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  unfold m2005
  simp only []
  rw [if_neg (by rw [hn]; omega)]
  have h0 := dinv_start ha (del := fun k => mask.getD (k - 1).toNat false) (p := 1) (Int.le_refl 1)
    (fun k h1 h2 => by omega)
  obtain ⟨a1, p1, e1, h1⟩ := maskLoop_spec mask a 1 1 h0 (by simp) (by simp; omega)
  rw [e1, bind_ok]
  simp only []
  rw [hn] at h1
  obtain ⟨a2, e2, hv2, hc2⟩ := finish_spec ha h1
  have hK : keepBy n (fun k => mask.getD (k - 1).toNat false) = maskIdx mask false := by
    rw [← keepBy_mask hn0 hl false]; congr 1; funext k; cases mask.getD (k - 1).toNat false <;> rfl
  rw [hn]
  exact ⟨a2, e2, by rw [← hK]; exact hv2, by rw [← hK]; exact hc2⟩

/-! ### `keepat!` -/

/-- The state of the `_keepat!` loops: slots `r..` are the original ones and slots
`1..j-1` hold the original slots at the kept positions `done`. -/
structure KInv (o a : Arr α) (done : List Int) (j r : Int) : Prop where
  dims : a.dims = o.dims
  off : a.off = o.off
  mlen : a.mem.len = o.mem.len
  hi : ∀ m, r ≤ m → a.at m = o.at m
  lo : ∀ (k : Nat) x, done[k]? = some x → a.at ((k : Int) + 1) = o.at x
  jlen : j = done.length + 1
  jr : j ≤ r

theorem KInv.length_eq {o a : Arr α} {done j r} (h : KInv o a done j r) : length a = length o := by
  simp [length, h.dims]

theorem kinv_keep {o a : Arr α} {done j r t r'} (h : KInv o a done j r) (ht : r ≤ t) (hr' : r ≤ r')
    (hj : j + 1 ≤ r') : KInv o (if j ≠ t then setU a j (o.at t) else a) (done ++ [t]) (j + 1) r' := by
  have hjl := h.jlen
  have hw : ∀ m, m ≠ j → (if j ≠ t then setU a j (o.at t) else a).at m = a.at m := by
    intro m hm; split <;> simp [setU_at, hm]
  refine ⟨by split <;> simp [h.dims], by split <;> simp [h.off], by split <;> simp [h.mlen],
    fun m hm => by rw [hw m (by omega)]; exact h.hi m (by omega), fun k x hx => ?_, by simp; omega, hj⟩
  by_cases hk : k < done.length
  · rw [List.getElem?_append_left hk] at hx
    rw [hw _ (by omega)]; exact h.lo k x hx
  · rw [List.getElem?_append_right (by omega)] at hx
    by_cases hk2 : k - done.length = 0
    · rw [hk2] at hx; simp at hx; subst hx
      have : ((k : Int) + 1) = j := by omega
      rw [this]
      split
      · simp
      · rename_i hjt; simp at hjt; rw [hjt]; exact h.hi t ht
    · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx

theorem kinv_skip {o a : Arr α} {done j r r'} (h : KInv o a done j r) (hr' : r ≤ r') : KInv o a done j r' :=
  ⟨h.dims, h.off, h.mlen, fun m hm => h.hi m (by omega), h.lo, h.jlen, by have := h.jr; omega⟩

theorem IncrFrom_length : ∀ {lo n : Int} {l : List Int}, IncrFrom lo l → (∀ x ∈ l, x ≤ n) → lo ≤ n →
    (l.length : Int) ≤ n - lo
  | _, _, [], _, _, h => by simp; omega
  | lo, n, k :: l, ⟨h1, h2⟩, hle, _ => by
    have hk := hle k (by simp)
    have := IncrFrom_length h2 (fun x hx => hle x (by simp [hx])) hk
    simp; omega

theorem keepLoop_spec {o : Arr α} :
    ∀ (rest : List Int) (a : Arr α) (prev : Option Int) (i lo : Int) (done : List Int),
    KInv o a done i i → (prev = some lo ∨ (prev = none ∧ lo = 0)) → i - 1 ≤ lo → IncrFrom lo rest →
    (∀ k ∈ rest, k ≤ length o ∧ (o.at k).isSome) →
    ∃ a', keepLoop a prev i rest = .ok (a', i + rest.length) ∧
      KInv o a' (done ++ rest) (i + rest.length) (i + rest.length)
  | [], a, prev, i, lo, done, h, _, _, _, _ => ⟨a, by simp [keepLoop], by simpa using h⟩
  | k :: rest, a, prev, i, lo, done, h, hprev, hlo, ⟨hk1, hinc⟩, hok => by
    obtain ⟨hkn, hks⟩ := hok k (by simp)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hks
    have hi1 : 1 ≤ i := by have := h.jlen; omega
    have hg : getL a k = .ok x := by
      unfold getL
      rw [if_pos (by rw [inBounds_iff, h.length_eq]; omega), h.hi k (by omega), hx]
    have h2 := kinv_keep h (t := k) (r' := i + 1) (by omega) (by omega) (Int.le_refl _)
    rw [hx] at h2
    obtain ⟨a', e, h3⟩ := keepLoop_spec rest _ (some k) (i + 1) k (done ++ [k]) h2 (Or.inl rfl) (by omega)
      hinc (fun k' hk' => hok k' (by simp [hk']))
    refine ⟨a', ?_, ?_⟩
    · unfold keepLoop
      rcases hprev with rfl | ⟨rfl, rfl⟩
      · simp only [if_pos hk1, pure_ok, bind_ok, hg]
        rw [e]; simp; omega
      · simp only [pure_ok, bind_ok, hg]
        rw [e]; simp; omega
    · have : i + 1 + (rest.length : Int) = i + ((k :: rest).length : Int) := by simp; omega
      rw [← this]; simpa using h3

theorem keepLoop_arg {o : Arr α} :
    ∀ (rest : List Int) (a : Arr α) (prev : Option Int) (i lo : Int) (done : List Int),
    KInv o a done i i → (prev = some lo ∨ (prev = none ∧ lo = 0)) → i - 1 ≤ lo → ¬ IncrFrom lo rest →
    (∀ k ∈ rest, 1 ≤ k ∧ k ≤ length o ∧ (o.at k).isSome) →
    keepLoop a prev i rest = .error .argument
  | [], _, _, _, _, _, _, _, _, h, _ => absurd trivial h
  | k :: rest, a, prev, i, lo, done, h, hprev, hlo, hinc, hok => by
    obtain ⟨hk0, hkn, hks⟩ := hok k (by simp)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hks
    have hi1 : 1 ≤ i := by have := h.jlen; omega
    unfold keepLoop
    by_cases hk1 : lo < k
    · have hinc' : ¬ IncrFrom k rest := fun hc => hinc ⟨hk1, hc⟩
      have hg : getL a k = .ok x := by
        unfold getL
        rw [if_pos (by rw [inBounds_iff, h.length_eq]; omega), h.hi k (by omega), hx]
      have h2 := kinv_keep h (t := k) (r' := i + 1) (by omega) (by omega) (Int.le_refl _)
      rw [hx] at h2
      have e := keepLoop_arg rest _ (some k) (i + 1) k (done ++ [k]) h2 (Or.inl rfl) (by omega) hinc'
        (fun k' hk' => hok k' (by simp [hk']))
      rcases hprev with rfl | ⟨rfl, rfl⟩
      · simp only [if_pos hk1, pure_ok, bind_ok, hg]; exact e
      · simp only [pure_ok, bind_ok, hg]; exact e
    · rcases hprev with rfl | ⟨rfl, rfl⟩
      · simp only [if_neg hk1, bind_error]
      · omega

theorem keepLoop_bounds {o : Arr α} :
    ∀ (rest : List Int) (a : Arr α) (prev : Option Int) (i lo : Int) (done : List Int),
    KInv o a done i i → (prev = some lo ∨ (prev = none ∧ lo = 0)) → i - 1 ≤ lo →
    (prev = none → ∀ k ∈ rest.head?, 1 ≤ k) → IncrFrom lo rest →
    (∀ k ∈ rest, 1 ≤ k → k ≤ length o → (o.at k).isSome) → (∃ k ∈ rest, length o < k) →
    keepLoop a prev i rest = .error .bounds
  | [], _, _, _, _, _, _, _, _, _, _, _, h => by simp at h
  | k :: rest, a, prev, i, lo, done, h, hprev, hlo, hfirst, ⟨hk1, hinc⟩, hok, hex => by
    have hi1 : 1 ≤ i := by have := h.jlen; omega
    have hk0 : 1 ≤ k := by
      rcases hprev with rfl | ⟨rfl, rfl⟩
      · omega
      · exact hfirst rfl k (by simp)
    unfold keepLoop
    by_cases hkn : length o < k
    · have hg : getL a k = .error .bounds := by
        unfold getL; rw [if_neg (by rw [inBounds_iff, h.length_eq]; omega)]
      rcases hprev with rfl | ⟨rfl, rfl⟩
      · simp only [if_pos hk1, hg, bind_error]
      · simp only [hg, bind_error]
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hok k (by simp) hk0 (by omega))
      have hg : getL a k = .ok x := by
        unfold getL
        rw [if_pos (by rw [inBounds_iff, h.length_eq]; omega), h.hi k (by omega), hx]
      have h2 := kinv_keep h (t := k) (r' := i + 1) (by omega) (by omega) (Int.le_refl _)
      rw [hx] at h2
      obtain ⟨j, hj, hjn⟩ := hex
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      have e := keepLoop_bounds rest _ (some k) (i + 1) k (done ++ [k]) h2 (Or.inl rfl) (by omega)
        (fun hc => by cases hc) hinc (fun k' hk' => hok k' (by simp [hk'])) ⟨j, hj, hjn⟩
      rcases hprev with rfl | ⟨rfl, rfl⟩
      · simp only [if_pos hk1, hg, bind_ok]; exact e
      · simp only [hg, bind_ok]; exact e

/-- The end of `_keepat!`: `deleteat!(a, j:lastindex(a))` keeps exactly the slots `1..j-1`. -/
theorem keep_finish {o a : Arr α} {n : Int} {done : List Int} {j r : Int} (ho : VecOK o n)
    (h : KInv o a done j r) (hlen : (done.length : Int) ≤ n) :
    ∃ a', m1905 pure a j (length a) false = .ok a' ∧ IsVec a' done.length ∧ contents a' = done.map o.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ho
  have ha : VecOK a n := vecOK_of_same ho h.dims h.off h.mlen
  have hla : length a = n := by rw [h.length_eq, hn]
  have hj := h.jlen
  have hpre : ∀ k (hk : k < done.length), a.at ((k : Int) + 1) = o.at done[k] :=
    fun k hk => h.lo k _ (List.getElem?_eq_getElem hk)
  unfold m1905
  simp only [Bool.false_eq_true, if_false]
  rw [hla]
  by_cases hjn : j > n
  · rw [if_pos hjn]
    refine ⟨a, rfl, by unfold IsVec; rw [ha.1]; congr 1; omega, ?_⟩
    apply contents_ext
    · simp; omega
    · intro k hk; simp only [List.length_map] at hk; rw [List.getElem_map]; exact hpre k hk
  · rw [if_neg hjn, wrap64_id (by have := ha.2.2; unfold Small at this; omega) (by omega)]
    obtain ⟨a', e, hv, _, hc⟩ := m1312_spec ha (i := j) (delta := 1 + (n - j)) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨a', e, by unfold IsVec at *; rw [hv]; congr 1; omega, ?_⟩
    rw [hc, List.drop_eq_nil_of_le (by simp; omega), List.append_nil]
    apply List.ext_getElem
    · simp; omega
    · intro k h1 h2
      simp only [List.length_map] at h2
      rw [List.getElem_take, getElem_contents, List.getElem_map]; exact hpre k h2

/-- `keepat!(a, inds)` for sorted, unique, in-range indices whose slots are assigned. -/
theorem m3134_spec {a : Arr α} {n : Int} (ha : VecOK a n) {inds : List Int} (hinc : Incr inds)
    (hin : ∀ k ∈ inds, 1 ≤ k ∧ k ≤ n ∧ (a.at k).isSome) :
    ∃ a', m3134 a inds = .ok a' ∧ IsVec a' inds.length ∧ contents a' = inds.map a.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  have h0 : KInv a a [] 1 1 := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun k x hx => by simp at hx, rfl, Int.le_refl 1⟩
  have hinc0 : IncrFrom 0 inds := by
    match inds, hinc, hin with
    | [], _, _ => trivial
    | k :: l, h1, h2 => exact ⟨by have := h2 k (by simp); omega, h1⟩
  obtain ⟨a1, e1, h1⟩ := keepLoop_spec inds a none 1 0 [] h0 (Or.inr ⟨rfl, rfl⟩) (by omega) hinc0
    (fun k hk => by have := hin k hk; rw [hn]; exact ⟨this.2.1, this.2.2⟩)
  have hlen := IncrFrom_length hinc0 (fun x hx => (hin x hx).2.1) hn0
  unfold m3134 keepatIdx
  rw [e1, bind_ok]
  simp only []
  obtain ⟨a2, e2, hv2, hc2⟩ := keep_finish ha (by simpa using h1) (by omega)
  exact ⟨a2, e2, by simpa using hv2, by simpa using hc2⟩

theorem m3134_arg {a : Arr α} {n : Int} (ha : VecOK a n) {inds : List Int} (hinc : ¬ Incr inds)
    (hin : ∀ k ∈ inds, 1 ≤ k ∧ k ≤ n ∧ (a.at k).isSome) : m3134 a inds = .error .argument := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  have h0 : KInv a a [] 1 1 := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun k x hx => by simp at hx, rfl, Int.le_refl 1⟩
  have hinc0 : ¬ IncrFrom 0 inds := by
    match inds, hinc, hin with
    | [], h, _ => exact absurd trivial h
    | k :: l, h1, _ => exact fun hc => h1 hc.2
  unfold m3134 keepatIdx
  rw [keepLoop_arg inds a none 1 0 [] h0 (Or.inr ⟨rfl, rfl⟩) (by omega) hinc0
    (fun k hk => by have := hin k hk; rw [hn]; exact this), bind_error]

theorem m3134_bounds {a : Arr α} {n : Int} (ha : VecOK a n) {inds : List Int} (hinc : Incr inds)
    (hout : ∃ k ∈ inds, k < 1 ∨ n < k) (hok : ∀ k ∈ inds, 1 ≤ k → k ≤ n → (a.at k).isSome) :
    m3134 a inds = .error .bounds := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  unfold m3134 keepatIdx
  match inds, hinc, hout, hok with
  | [], _, h, _ => simp at h
  | k :: l, hinc, hout, hok =>
    by_cases hk : k < 1
    · have hg : getL a k = .error .bounds := by
        unfold getL; rw [if_neg (by rw [inBounds_iff]; omega)]
      simp only [keepLoop, pure_ok, bind_ok, hg, bind_error]
    · have h0 : KInv a a [] 1 1 :=
        ⟨rfl, rfl, rfl, fun _ _ => rfl, fun k x hx => by simp at hx, rfl, Int.le_refl 1⟩
      have hgt := IncrFrom_gt hinc
      rw [keepLoop_bounds (k :: l) a none 1 0 [] h0 (Or.inr ⟨rfl, rfl⟩) (by omega)
        (fun _ k' hk' => by simp at hk'; omega) ⟨by omega, hinc⟩ (fun k' hk' h1 h2 => hok k' hk' h1 (by omega))
        (by
          obtain ⟨j, hj, hjb⟩ := hout
          rcases List.mem_cons.mp hj with rfl | hj'
          · exact ⟨j, hj, by omega⟩
          · have := hgt j hj'; exact ⟨j, hj, by omega⟩), bind_error]

theorem maskIdx_cons (b c : Bool) (rest : List Bool) :
    maskIdx (b :: rest) c = (if b == c then [1] else []) ++ (maskIdx rest c).map (· + 1) := by
  unfold maskIdx
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.getD_cons_zero, List.filter_map]
  have hf : (fun k => (b :: rest).getD k false == c) ∘ Nat.succ = fun k => rest.getD k false == c := by
    funext k; simp [Function.comp]
  rw [hf]
  cases b == c <;> simp [List.map_map, Function.comp] <;> (funext k; omega)

theorem keepMaskLoop_spec {o : Arr α} {mask : List Bool} :
    ∀ (rest : List Bool) (a : Arr α) (j i : Int) (done : List Int),
    KInv o a done j i → done ++ (maskIdx rest true).map (· + (i - 1)) = maskIdx mask true →
    i - 1 + rest.length = length o → 1 ≤ i →
    (∀ t ∈ (maskIdx rest true).map (· + (i - 1)), (o.at t).isSome) →
    ∃ a' j', keepMaskLoop a j i rest = .ok (a', j') ∧ KInv o a' (maskIdx mask true) j' (length o + 1)
  | [], a, j, i, done, h, hd, hl, _, _ => by
    have e : maskIdx ([] : List Bool) true = [] := rfl
    rw [e, List.map_nil, List.append_nil] at hd
    refine ⟨a, j, rfl, ?_⟩
    rw [← hd, show length o + 1 = i by simp at hl; omega]; exact h
  | b :: rest, a, j, i, done, h, hd, hl, hi1, hok => by
    simp only [List.length_cons] at hl
    have hcomp : ((· + (i - 1)) ∘ (· + 1) : Int → Int) = (· + (i + 1 - 1)) := by funext x; simp; omega
    unfold keepMaskLoop
    cases b with
    | false =>
      have e : maskIdx (false :: rest) true = (maskIdx rest true).map (· + 1) := by rw [maskIdx_cons]; rfl
      rw [e, List.map_map, hcomp] at hd hok
      simp only [Bool.false_eq_true, if_false]
      exact keepMaskLoop_spec rest a j (i + 1) done (kinv_skip h (by omega)) hd (by omega) (by omega) hok
    | true =>
      have e : maskIdx (true :: rest) true = 1 :: (maskIdx rest true).map (· + 1) := by rw [maskIdx_cons]; rfl
      rw [e, List.map_cons, List.map_map, hcomp, show 1 + (i - 1) = i by omega] at hd hok
      simp only [if_true]
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hok i (by simp))
      have hjl := h.jlen; have hjr := h.jr
      have h2 := kinv_keep h (t := i) (r' := i + 1) (Int.le_refl _) (by omega) (by omega)
      rw [hx] at h2
      obtain ⟨a', j', e', h3⟩ := keepMaskLoop_spec rest _ (j + 1) (i + 1) (done ++ [i]) h2
        (by simpa using hd) (by omega) (by omega) (fun t ht => hok t (List.mem_cons_of_mem _ ht))
      refine ⟨a', j', ?_, h3⟩
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl]; simp only [pure_ok, bind_ok]; rw [← e']; simp
      · rw [if_neg hij]
        simp only [getU, h.hi i (Int.le_refl i), hx, pure_ok, bind_ok]
        rw [← e', if_pos (Ne.symm hij)]

/-- `keepat!(a, mask)` on a vector of the same length whose kept slots are assigned. -/
theorem m3159_spec {a : Arr α} {n : Int} (ha : VecOK a n) {mask : List Bool} (hl : (mask.length : Int) = n)
    (hok : ∀ t ∈ maskIdx mask true, (a.at t).isSome) :
    ∃ a', m3159 a mask = .ok a' ∧ IsVec a' (maskIdx mask true).length ∧
      contents a' = (maskIdx mask true).map a.at := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  have h0 : KInv a a [] 1 1 := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun k x hx => by simp at hx, rfl, Int.le_refl 1⟩
  have hz : (fun x : Int => x + (1 - 1)) = id := by funext x; simp
  obtain ⟨a1, j1, e1, h1⟩ := keepMaskLoop_spec (mask := mask) mask a 1 1 [] h0
    (by rw [hz, List.map_id, List.nil_append]) (by simp; omega)
    (Int.le_refl 1) (by rw [hz, List.map_id]; exact hok)
  have hlen : ((maskIdx mask true).length : Int) ≤ n := by
    unfold maskIdx; simp only [List.length_map]
    have := List.length_filter_le (fun k => mask.getD k false == true) (List.range mask.length)
    rw [List.length_range] at this; omega
  unfold m3159 keepatMask
  rw [if_neg (by rw [hn]; omega), e1, bind_ok]
  simp only []
  exact keep_finish ha h1 hlen

/-! ### `splice!` -/

theorem writeFrom_safe (conv : β → R α) : ∀ (ins : List β) (a : Arr α) (start : Int) (ys : List α),
    convList conv ins = .ok ys → 1 ≤ start → start - 1 + ins.length ≤ length a →
    writeFrom conv a start ins = .ok (safeWrites a start ys)
  | [], a, start, ys, h, _, _ => by simp [convList] at h; subst h; rfl
  | x :: xs, a, start, ys, h, h1, h2 => by
    simp only [convList] at h
    cases hx : conv x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx, bind_ok] at h
      cases hxs : convList conv xs with
      | error e => rw [hxs] at h; cases h
      | ok ys' =>
        rw [hxs, bind_ok] at h
        simp only [pure_ok, Except.ok.injEq] at h; subst h
        simp only [writeFrom, m1031, hx, bind_ok, m1036]
        rw [if_neg (by rw [inBounds_iff]; simp at h2 ⊢; omega), bind_ok]
        exact writeFrom_safe conv xs _ (start + 1) ys' hxs (by omega) (by simp at h2 ⊢; omega)

theorem writeFrom_err (conv : β → R α) : ∀ (ins : List β) (a : Arr α) (start : Int) (e : Err),
    convList conv ins = .error e → 1 ≤ start → start - 1 + ins.length ≤ length a →
    writeFrom conv a start ins = .error e
  | [], _, _, _, h, _, _ => by simp [convList] at h
  | x :: xs, a, start, e, h, h1, h2 => by
    simp only [convList] at h
    cases hx : conv x with
    | error e' => rw [hx, bind_error] at h; cases h; simp [writeFrom, m1031, hx]
    | ok y =>
      rw [hx, bind_ok] at h
      cases hxs : convList conv xs with
      | ok ys' => rw [hxs, bind_ok] at h; cases h
      | error e' =>
        rw [hxs, bind_error] at h; cases h
        simp only [writeFrom, m1031, hx, bind_ok, m1036]
        rw [if_neg (by rw [inBounds_iff]; simp at h2 ⊢; omega), bind_ok]
        exact writeFrom_err conv xs _ (start + 1) _ hxs (by omega) (by simp at h2 ⊢; omega)

/-- A vector whose slots are `a[1:s]`, then `ys`, then `a[s+d+1:n]` has those contents. -/
theorem contents_replace {a a' : Arr α} {n s d : Int} (ys : List (Option α)) (hn : length a = n)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d) (hs1 : s + d ≤ n) (hl : length a' = n - d + ys.length)
    (hA : ∀ k, 1 ≤ k → k ≤ s → a'.at k = a.at k)
    (hB : ∀ j : Nat, (hj : j < ys.length) → a'.at (s + j + 1) = ys[j])
    (hC : ∀ k, s + d < k → k ≤ n → a'.at (k - d + ys.length) = a.at k) :
    contents a' = (contents a).take s.toNat ++ ys ++ (contents a).drop (s + d).toNat := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [contents_length] at h1
    rw [getElem_contents]
    by_cases ja : j < s.toNat
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_take, getElem_contents]
      exact hA _ (by omega) (by omega)
    · by_cases jb : j < s.toNat + ys.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        have hj : j - (List.take s.toNat (contents a)).length < ys.length := by simp; omega
        have := hB (j - (List.take s.toNat (contents a)).length) hj
        rw [show s + ((j - (List.take s.toNat (contents a)).length : Nat) : Int) + 1 = (j : Int) + 1 by
          simp; omega] at this
        exact this
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_drop, getElem_contents, List.length_append, List.length_take,
          contents_length]
        have := hC (((s + d).toNat + (j - (min s.toNat (length a).toNat + ys.length)) : Nat) + 1)
          (by omega) (by omega)
        rw [← this]; congr 1; omega

/-- Pointwise reading of `take s ++ drop (s + d)`. -/
theorem at_of_contents_del {a a1 : Arr α} {n s d : Int} (hn : length a = n) (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hs1 : s + d ≤ n) (hl : length a1 = n - d)
    (hc : contents a1 = (contents a).take s.toNat ++ (contents a).drop (s + d).toNat) :
    (∀ k, 1 ≤ k → k ≤ s → a1.at k = a.at k) ∧ (∀ k, s < k → k ≤ n - d → a1.at k = a.at (k + d)) := by
  have key : ∀ k : Nat, (hk : k < (n - d).toNat) → a1.at ((k : Int) + 1) =
      ((contents a).take s.toNat ++ (contents a).drop (s + d).toNat)[k]'(by simp; omega) := by
    intro k hk
    rw [← getElem_contents a1 k (by simp; omega)]
    simp only [hc]
  refine ⟨fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · have := key (k - 1).toNat (by omega)
    rw [show (((k - 1).toNat : Nat) : Int) + 1 = k by omega, List.getElem_append_left (by simp; omega),
      List.getElem_take, getElem_contents] at this
    rw [this]; congr 1; omega
  · have := key (k - 1).toNat (by omega)
    rw [show (((k - 1).toNat : Nat) : Int) + 1 = k by omega, List.getElem_append_right (by simp; omega),
      List.getElem_drop, getElem_contents] at this
    rw [this]; congr 1; simp; omega

theorem getL_ok_of {a : Arr α} {i : Int} {v : α} (h1 : 1 ≤ i) (h2 : i ≤ length a) (hv : a.at i = some v) :
    getL a i = .ok v := by
  unfold getL; rw [if_pos (by rw [inBounds_iff]; omega), hv]

/-- After the size change of `splice!(a, i, ins)` (for `length(ins) ≥ 2`), the vector
has room for the replacements at `i` and keeps the other slots around them. -/
theorem m2070_grow {a : Arr α} {n i : Int} (ha : VecOK a n) (hi1 : 1 ≤ i) (hi2 : i ≤ n) {m : Int}
    (hm1 : 2 ≤ m) (hm2 : m ≤ 2 ^ 58) :
    ∃ a1, m1230 a i (m - 1) = .ok a1 ∧ a1.dims = [n + m - 1] ∧
      (∀ k, 1 ≤ k → k ≤ i - 1 → a1.at k = a.at k) ∧
      (∀ k, i + m ≤ k → k ≤ n + m - 1 → a1.at k = a.at (k - m + 1)) := by
  obtain ⟨a1, e, hv, _, hA, hC⟩ := m1230_spec ha (i := i) (delta := m - 1) (by omega) (by omega) hi1 (by omega)
  refine ⟨a1, e, by rw [hv]; congr 1; omega, hA, fun k h1 h2 => ?_⟩
  have := hC (k - (i - 1) - (m - 1)) (by omega) (by omega)
  rw [show i - 1 + (m - 1) + (k - (i - 1) - (m - 1)) = k by omega] at this
  rw [this]; congr 1; omega

/-- `splice!(a, i, ins)`: the removed item and the vector with the replacements in its place. -/
theorem m2070_spec (conv : β → R α) {a : Arr α} {n i : Int} (ha : VecOK a n) (hi1 : 1 ≤ i) (hi2 : i ≤ n)
    {v : α} (hv : a.at i = some v) {ins : List β} (hm : ins.length ≤ 2 ^ 58) :
    (∀ ys, convList conv ins = .ok ys → ∃ a', m2070 conv a i ins = .ok (v, a') ∧
      IsVec a' (n - 1 + ys.length) ∧
      contents a' = (contents a).take (i - 1).toNat ++ ys.map some ++ (contents a).drop i.toNat) ∧
    (∀ e, convList conv ins = .error e → m2070 conv a i ins = .error e) := by
  obtain ⟨hn, _, hn0, _, _, hdims⟩ := vecOK_unpack ha
  have hg := getL_ok_of hi1 (by omega) hv
  unfold m2070
  rw [hg, bind_ok]
  match ins, hm with
  | [], _ =>
    refine ⟨fun ys hys => ?_, fun e he => by simp [convList] at he⟩
    simp [convList] at hys; subst hys
    obtain ⟨a', e, hv', _, hc⟩ := m1312_spec ha (i := i) (delta := 1) hi1 hi2 (by omega) (by omega)
    refine ⟨a', by simp only [e, bind_ok]; rfl, by simpa using hv', ?_⟩
    rw [hc, show (i - 1 + 1) = i by omega]; simp
  | [x], _ =>
    have hw : (m1031 conv a x i >>= fun a => pure (v, a)) =
        (writeFrom conv a i [x] >>= fun a => pure (v, a)) := by
      simp only [writeFrom]; cases m1031 conv a x i <;> rfl
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · have hyl := convList_length conv _ ys hys
      dsimp only; rw [hw, writeFrom_safe conv [x] a i ys hys hi1 (by simp; omega), bind_ok]
      obtain ⟨h1, h2, h3, h4⟩ := safeWrites_spec ys a i
      refine ⟨_, rfl, by unfold IsVec; rw [h1, hdims]; simp at hyl; rw [hyl]; congr 1; omega, ?_⟩
      rw [show (contents a).take (i - 1).toNat ++ ys.map some ++ (contents a).drop i.toNat =
        (contents a).take (i - 1).toNat ++ ys.map some ++ (contents a).drop (i - 1 + 1).toNat by
        rw [show i - 1 + 1 = i by omega]]
      apply contents_replace (ys.map some) hn (by omega) (by omega) (by omega)
        (by simp [length, h1, hdims] at hyl ⊢; omega)
      · intro k k1 k2; rw [h4]; rw [if_neg (by omega)]
      · intro j hj
        have hj' : j < ys.length := by simpa using hj
        rw [h4, if_pos (by omega), List.getElem_map, show (i - 1 + (j : Int) + 1 - i).toNat = j by omega]
        exact List.getElem?_eq_getElem hj'
      · intro k k1 k2
        have hy1 : ys.length = 1 := by simpa using hyl
        simp only [List.length_map, hy1]
        rw [h4, hy1, if_neg (by omega)]; congr 1; omega
    · dsimp only; rw [hw, writeFrom_err conv [x] a i e he hi1 (by simp; omega), bind_error]
  | x1 :: x2 :: rest, hm =>
    obtain ⟨a1, e1, hd1, hA, hC⟩ := m2070_grow ha hi1 hi2 (m := ((x1 :: x2 :: rest).length : Int))
      (by simp; omega) (by omega)
    have hl1 : length a1 = n + ((x1 :: x2 :: rest).length : Int) - 1 := length_vec a1 _ hd1
    simp only []
    rw [e1, bind_ok]
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · have hyl := convList_length conv _ ys hys
      rw [writeFrom_safe conv _ a1 i ys hys hi1 (by rw [hl1]; omega), bind_ok]
      obtain ⟨h1, h2, h3, h4⟩ := safeWrites_spec ys a1 i
      have hl' : length (safeWrites a1 i ys) = n + ys.length - 1 := by
        simp only [length, h1]; simp only [length] at hl1; rw [hl1, hyl]
      refine ⟨_, rfl, by unfold IsVec; rw [h1, hd1, hyl]; congr 1; omega, ?_⟩
      rw [show (contents a).drop i.toNat = (contents a).drop (i - 1 + 1).toNat by
        rw [show i - 1 + 1 = i by omega]]
      apply contents_replace (ys.map some) hn (by omega) (by omega) (by omega) (by simp; omega)
      · intro k k1 k2; rw [h4, if_neg (by omega)]; exact hA k k1 k2
      · intro j hj
        have hj' : j < ys.length := by simpa using hj
        rw [h4, if_pos (by omega), List.getElem_map, show (i - 1 + (j : Int) + 1 - i).toNat = j by omega]
        exact List.getElem?_eq_getElem hj'
      · intro k k1 k2; rw [h4]; simp only [List.length_map]
        rw [if_neg (by omega), hC _ (by rw [hyl]; omega) (by rw [hyl]; omega)]; congr 1; rw [hyl]; omega
    · rw [writeFrom_err conv _ a1 i e he hi1 (by rw [hl1]; omega), bind_error]

/-- The size change of `splice!(a, f:l, ins)` for nonempty `ins`: the slots before `f` stay,
the slots after `l` move to just after the `m` replacement slots. -/
theorem m2125_resize {a : Arr α} {n f l m : Int} (ha : VecOK a n) (hf : 1 ≤ f) (hfl : f ≤ l + 1) (hl : l ≤ n)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ 58) :
    ∃ a1, spliceResize a f l m (l - f + 1) = .ok a1 ∧ IsVec a1 (n - (l - f + 1) + m) ∧
      (∀ k, 1 ≤ k → k ≤ f - 1 → a1.at k = a.at k) ∧
      (∀ k, l < k → k ≤ n → a1.at (k - (l - f + 1) + m) = a.at k) := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  unfold spliceResize
  simp only []
  rw [hn]
  by_cases c1 : m < l - f + 1
  · rw [if_pos c1]
    generalize hp : (if f - 1 < n - l then f else l - (l - f + 1 - m) + 1) = pos
    have hp1 : f ≤ pos ∧ pos ≤ f + m := by split at hp <;> omega
    have hp2 : pos - 1 + (l - f + 1 - m) ≤ l := by split at hp <;> omega
    obtain ⟨a1, e, hv, _, hc⟩ := m1312_spec ha (i := pos) (delta := l - f + 1 - m) (by omega) (by omega)
      (by omega) (by omega)
    obtain ⟨hA, hB⟩ := at_of_contents_del (a := a) (s := pos - 1) (d := l - f + 1 - m) hn (by omega) (by omega)
      (by omega) (length_vec a1 _ hv) (by rw [hc])
    refine ⟨a1, e, by unfold IsVec at *; rw [hv]; congr 1; omega, fun k k1 k2 => hA k k1 (by omega),
      fun k k1 k2 => ?_⟩
    rw [hB _ (by omega) (by omega)]; congr 1; omega
  · rw [if_neg c1]
    by_cases c2 : m > l - f + 1
    · rw [if_pos c2]
      generalize hp : (if f - 1 < n - l then f else l + 1) = pos
      have hp1 : f ≤ pos ∧ pos ≤ l + 1 := by split at hp <;> omega
      obtain ⟨a1, e, hv, _, hA, hC⟩ := m1230_spec ha (i := pos) (delta := m - (l - f + 1)) (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨a1, e, by unfold IsVec at *; rw [hv]; congr 1; omega, fun k k1 k2 => hA k k1 (by omega),
        fun k k1 k2 => ?_⟩
      have := hC (k - pos + 1) (by omega) (by omega)
      rw [show pos - 1 + (m - (l - f + 1)) + (k - pos + 1) = k - (l - f + 1) + m by omega,
        show pos - 1 + (k - pos + 1) = k by omega] at this
      exact this
    · rw [if_neg c2]
      exact ⟨a, rfl, by unfold IsVec; rw [ha.1]; congr 1; omega, fun _ _ _ => rfl,
        fun k _ _ => by congr 1; omega⟩

/-- `splice!(a, f:l, ins)`: the removed items `a[f:l]` and the vector with `ins` in their place. -/
theorem m2125_spec (conv : β → R α) {a : Arr α} {n f l : Int} (ha : VecOK a n) (hn58 : n ≤ 2 ^ 58)
    (hf : 1 ≤ f) (hfl : f ≤ l + 1) (hl : l ≤ n) {ins : List β} (hm : ins.length ≤ 2 ^ 58) :
    ∃ v, IsVec v (l - f + 1) ∧ contents v = ((contents a).drop (f - 1).toNat).take (l - f + 1).toNat ∧
    (∀ ys, convList conv ins = .ok ys → ∃ a', m2125 conv a f l ins = .ok (v, a') ∧
      IsVec a' (n - (l - f + 1) + ys.length) ∧
      contents a' = (contents a).take (f - 1).toNat ++ ys.map some ++ (contents a).drop l.toNat) ∧
    (∀ e, convList conv ins = .error e → m2125 conv a f l ins = .error e) := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  have hw : wrap64 (1 + (l - f)) = l - f + 1 := by rw [wrap64_id (by omega) (by omega)]; omega
  have hr : rangeIn a f (l - f + 1) := by unfold rangeIn; right; omega
  obtain ⟨v, ev, hvv, hcv⟩ := (p981 a f (l - f + 1) ha.2.1 (by omega) (by omega)).1 hr
  refine ⟨v, hvv, hcv, ?_⟩
  unfold m2125
  rw [hw, ev, bind_ok]
  simp only []
  by_cases hm0 : ins.length = 0
  · have hins : ins = [] := List.eq_nil_of_length_eq_zero hm0
    subst hins
    refine ⟨fun ys hys => ?_, fun e he => by simp [convList] at he⟩
    simp [convList] at hys; subst hys
    rw [if_pos (by simp)]
    unfold m1905
    simp only [Bool.false_eq_true, if_false]
    by_cases hfl' : f > l
    · rw [if_pos hfl']
      refine ⟨a, rfl, by unfold IsVec; rw [ha.1]; congr 1; simp; omega, ?_⟩
      rw [show l.toNat = (f - 1).toNat by omega]; simp
    · rw [if_neg hfl', hw]
      obtain ⟨a', e, hv', _, hc⟩ := m1312_spec ha (i := f) (delta := l - f + 1) hf (by omega) (by omega) (by omega)
      refine ⟨a', by rw [e]; rfl, by unfold IsVec at *; rw [hv']; congr 1; simp, ?_⟩
      rw [hc, show f - 1 + (l - f + 1) = l by omega]; simp
  · rw [if_neg (by omega)]
    obtain ⟨a1, e1, hv1, hA, hC⟩ := m2125_resize ha hf hfl hl (m := (ins.length : Int)) (by omega) (by omega)
    rw [e1, bind_ok]
    have hl1 := length_vec a1 _ hv1
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · have hyl := convList_length conv _ ys hys
      rw [writeFrom_safe conv _ a1 f ys hys hf (by rw [hl1]; omega), bind_ok]
      obtain ⟨h1, h2, h3, h4⟩ := safeWrites_spec ys a1 f
      refine ⟨_, rfl, by unfold IsVec at *; rw [h1, hv1, hyl], ?_⟩
      rw [show (contents a).drop l.toNat = (contents a).drop (f - 1 + (l - f + 1)).toNat by
        rw [show f - 1 + (l - f + 1) = l by omega]]
      apply contents_replace (ys.map some) hn (by omega) (by omega) (by omega)
        (by simp only [length, h1]; simp only [length] at hl1; rw [hl1, List.length_map, hyl])
      · intro k k1 k2; rw [h4, if_neg (by omega)]; exact hA k k1 k2
      · intro j hj
        have hj' : j < ys.length := by simpa using hj
        rw [h4, if_pos (by omega), List.getElem_map, show (f - 1 + (j : Int) + 1 - f).toNat = j by omega]
        exact List.getElem?_eq_getElem hj'
      · intro k k1 k2
        simp only [List.length_map]
        rw [h4, if_neg (by omega), hyl]; exact hC k (by omega) k2
    · rw [writeFrom_err conv _ a1 f e he hf (by rw [hl1]; omega), bind_error]

theorem dltdPush_foldl : ∀ (xs : List (Option α)) (l : List (Option α)),
    xs.foldl dltdPush (some l) = some (l ++ xs) ∧ xs.foldl dltdPush none = none
  | [], l => by simp
  | x :: xs, l => by
    obtain ⟨h1, _⟩ := dltdPush_foldl xs (l ++ [x])
    obtain ⟨_, h2⟩ := dltdPush_foldl xs l
    simp only [List.foldl_cons, dltdPush]
    exact ⟨by rw [h1]; simp, h2⟩

/-! ### Properties -/

/-- The `deleteat!(a, inds)` contract (docstring base/array.jl:1916-1944): for sorted, unique
indices in `1:n` the result holds exactly the slots whose index is not in `inds`, in order
(an `#undef` slot stays `#undef`); in-range indices that are not sorted and unique throw
`ArgumentError` (the docstring's `(2, 2)` example); sorted indices reaching outside `1:n`
throw `BoundsError`. -/
def DeleteatContract {α : Type} (del : Arr α → List Int → R (Arr α)) : Prop :=
  ∀ (a : Arr α) (n : Int) (inds : List Int), VecOK a n →
    (Incr inds → (∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ∃ a', del a inds = .ok a' ∧
      IsVec a' (keepIdx n inds).length ∧ contents a' = (keepIdx n inds).map a.at) ∧
    ((∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ¬ Incr inds → del a inds = .error .argument) ∧
    (Incr inds → (∃ i ∈ inds, i < 1 ∨ n < i) → del a inds = .error .bounds)

theorem deleteat_contract_of {α : Type} (del : Arr α → List Int → R (Arr α))
    (h : ∀ a inds, del a inds = (do let (a, _) ← m1970 a inds none; pure a)) : DeleteatContract del := by
  intro a n inds ha
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨a', e, hv, hc⟩ := m1970_spec ha h1 h2 none
    exact ⟨a', by rw [h, e]; rfl, hv.1, hc⟩
  · rw [h, m1970_arg hn h1 h2 none]; rfl
  · rw [h, m1970_bounds hn h1 h2 none]; rfl

/-- `deleteat!(a::Vector, inds)` for an index iterator satisfies the `deleteat!` contract. -/
def P1945 : Prop := ∀ {α : Type}, DeleteatContract (α := α) m1945
theorem p1945 : P1945 := fun {_} => deleteat_contract_of m1945 fun _ _ => rfl

/-- `deleteat!(a::Vector, inds::AbstractVector)` satisfies the `deleteat!` contract. -/
def P1946 : Prop := ∀ {α : Type}, DeleteatContract (α := α) m1946
theorem p1946 : P1946 := fun {_} => deleteat_contract_of m1946 fun _ _ => rfl

/-- `_deleteat!(a, inds, dltd)`: on sorted, unique, in-range indices it leaves the kept
slots in order and appends the removed slots, in order, to a vector `dltd` (nothing for
`Nowhere()`); otherwise it throws as `deleteat!` does. -/
def P1970 : Prop := ∀ {α : Type} (a : Arr α) (n : Int) (inds : List Int) (d : Option (List (Option α))),
    VecOK a n →
    (Incr inds → (∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ∃ a', m1970 a inds d =
      .ok (a', d.map (· ++ inds.map a.at)) ∧ IsVec a' (keepIdx n inds).length ∧
      contents a' = (keepIdx n inds).map a.at) ∧
    ((∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ¬ Incr inds → m1970 a inds d = .error .argument) ∧
    (Incr inds → (∃ i ∈ inds, i < 1 ∨ n < i) → m1970 a inds d = .error .bounds)

theorem p1970 : P1970 := by
  intro α a n inds d ha
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => m1970_arg hn h1 h2 d, fun h1 h2 => m1970_bounds hn h1 h2 d⟩
  obtain ⟨a', e, hv, hc⟩ := m1970_spec ha h1 h2 d
  refine ⟨a', ?_, hv.1, hc⟩
  rw [e]
  cases d with
  | none => rw [(dltdPush_foldl _ []).2]; rfl
  | some l => rw [(dltdPush_foldl _ l).1]; rfl

/-- `deleteat!(a, mask)` (docstring base/array.jl:1922-1923: "a boolean vector of the same
length as `a` with `true` indicating entries to delete"): the slots where `mask` is false,
in order; a mask of another length throws `BoundsError`. -/
def P2005 : Prop := ∀ {α : Type} (a : Arr α) (n : Int) (mask : List Bool), VecOK a n →
    ((mask.length : Int) = n → ∃ a', m2005 a mask = .ok a' ∧ IsVec a' (maskIdx mask false).length ∧
      contents a' = (maskIdx mask false).map a.at) ∧
    ((mask.length : Int) ≠ n → m2005 a mask = .error .bounds)

theorem p2005 : P2005 := by
  intro α a n mask ha
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a', e, hv, hc⟩ := m2005_spec ha h
    exact ⟨a', e, hv.1, hc⟩
  · unfold m2005; simp only []; rw [if_pos (by rw [hn]; exact h)]

/-- `splice!(a, i, ins)` (docstring base/array.jl:2018-2025): an index outside `1:n` throws
`BoundsError` and an `#undef` item `UndefRefError`; otherwise it returns the item at `i`
and leaves `a[1:i-1]`, the replacements converted to `eltype(a)`, then `a[i+1:n]`; a
failing conversion throws that error. -/
def P2070 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n i : Int) (ins : List β), VecOK a n →
    ins.length ≤ 2 ^ 58 →
    (¬ (1 ≤ i ∧ i ≤ n) → m2070 conv a i ins = .error .bounds) ∧
    (1 ≤ i → i ≤ n → a.at i = none → m2070 conv a i ins = .error .undefRef) ∧
    (1 ≤ i → i ≤ n → ∀ v, a.at i = some v →
      (∀ ys, convList conv ins = .ok ys → ∃ a', m2070 conv a i ins = .ok (v, a') ∧
        IsVec a' (n - 1 + ys.length) ∧
        contents a' = (contents a).take (i - 1).toNat ++ ys.map some ++ (contents a).drop i.toNat) ∧
      (∀ e, convList conv ins = .error e → m2070 conv a i ins = .error e))

theorem p2070 : P2070 := by
  intro α β conv a n i ins ha hm
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h => ?_, fun h1 h2 h3 => ?_, fun h1 h2 v hv => m2070_spec conv ha h1 h2 hv hm⟩
  · unfold m2070; unfold getL; rw [if_neg (by rw [inBounds_iff, hn]; exact h), bind_error]
  · unfold m2070; unfold getL; rw [if_pos (by rw [inBounds_iff, hn]; omega), h3]; rfl

/-- `splice!(a, f:l, ins)` (docstring base/array.jl:2073-2084): a nonempty range outside
`1:n` throws `BoundsError`, and so does an insertion point `f:f-1` outside `1:n+1` with
replacements; otherwise it returns `a[f:l]` and leaves `a[1:f-1]`, the replacements
converted to `eltype(a)`, then `a[l+1:n]`; a failing conversion throws that error. -/
def P2125 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n f l : Int) (ins : List β), VecOK a n →
    n ≤ 2 ^ 58 → ins.length ≤ 2 ^ 58 → -2 ^ 60 ≤ f → l ≤ 2 ^ 60 → f ≤ l + 1 →
    (f ≤ l → (f < 1 ∨ n < l) → m2125 conv a f l ins = .error .bounds) ∧
    (l = f - 1 → ins ≠ [] → (f < 1 ∨ n + 1 < f) → m2125 conv a f l ins = .error .bounds) ∧
    (1 ≤ f → l ≤ n → ∃ v, IsVec v (l - f + 1) ∧ contents v = ((contents a).drop (f - 1).toNat).take (l - f + 1).toNat ∧
      (∀ ys, convList conv ins = .ok ys → ∃ a', m2125 conv a f l ins = .ok (v, a') ∧
        IsVec a' (n - (l - f + 1) + ys.length) ∧
        contents a' = (contents a).take (f - 1).toNat ++ ys.map some ++ (contents a).drop l.toNat) ∧
      (∀ e, convList conv ins = .error e → m2125 conv a f l ins = .error e))

theorem p2125 : P2125 := by
  intro α β conv a n f l ins ha hn58 hm hf0 hl0 hfl
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  have hw : wrap64 (1 + (l - f)) = l - f + 1 := by rw [wrap64_id (by omega) (by omega)]; omega
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 => m2125_spec conv ha hn58 h1 hfl h2 hm⟩
  · unfold m2125; rw [hw]; unfold m981
    rw [if_pos (by unfold rangeIn; omega), bind_error]
  · have hr : rangeIn a f (l - f + 1) := by unfold rangeIn; left; omega
    obtain ⟨v, ev, _, _⟩ := (p981 a f (l - f + 1) ha.2.1 (by omega) (by omega)).1 hr
    unfold m2125; rw [hw, ev, bind_ok]
    simp only []
    have hm0 : (ins.length : Int) ≠ 0 := by
      intro hc; exact h2 (List.eq_nil_of_length_eq_zero (by omega))
    rw [if_neg hm0]
    unfold spliceResize
    simp only []
    rw [if_neg (by omega), if_pos (by omega)]
    have hp : (if f - 1 < length a - l then f else l + 1) = f := by split <;> omega
    rw [hp, ((p1230 a n f _ ha).2.1 (by omega) (by omega) (by unfold typeminInt; omega)
      (by unfold typemaxInt; omega) (by omega)), bind_error]

/-- `splice!(a, inds)` (docstring base/array.jl:2054-2056): for sorted, unique, in-range
indices it returns the removed slots in order and leaves the other slots; otherwise it
throws as `deleteat!` does. -/
def P2153 : Prop := ∀ {α : Type} (a : Arr α) (n : Int) (inds : List Int), VecOK a n →
    (Incr inds → (∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ∃ a', m2153 a inds = .ok (inds.map a.at, a') ∧
      IsVec a' (keepIdx n inds).length ∧ contents a' = (keepIdx n inds).map a.at) ∧
    ((∀ i ∈ inds, 1 ≤ i ∧ i ≤ n) → ¬ Incr inds → m2153 a inds = .error .argument) ∧
    (Incr inds → (∃ i ∈ inds, i < 1 ∨ n < i) → m2153 a inds = .error .bounds)

theorem p2153 : P2153 := by
  intro α a n inds ha
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨a', e, hv, hc⟩ := m1970_spec ha h1 h2 (some [])
    refine ⟨a', ?_, hv.1, hc⟩
    unfold m2153; rw [e, (dltdPush_foldl _ []).1]; rfl
  · unfold m2153; rw [m1970_arg hn h1 h2 (some [])]; rfl
  · unfold m2153; rw [m1970_bounds hn h1 h2 (some [])]; rfl

/-- `keepat!(a, inds)` (docstring base/array.jl:3110-3121) when the kept slots are assigned:
for sorted, unique, in-range indices the result is `a[inds]`; in-range indices that are not
sorted and unique throw `ArgumentError`; sorted indices reaching outside `1:n` throw
`BoundsError`. -/
def P3134 : Prop := ∀ {α : Type} (a : Arr α) (n : Int) (inds : List Int), VecOK a n →
    (Incr inds → (∀ k ∈ inds, 1 ≤ k ∧ k ≤ n ∧ (a.at k).isSome) → ∃ a', m3134 a inds = .ok a' ∧
      IsVec a' inds.length ∧ contents a' = inds.map a.at) ∧
    (¬ Incr inds → (∀ k ∈ inds, 1 ≤ k ∧ k ≤ n ∧ (a.at k).isSome) → m3134 a inds = .error .argument) ∧
    (Incr inds → (∃ k ∈ inds, k < 1 ∨ n < k) → (∀ k ∈ inds, 1 ≤ k → k ≤ n → (a.at k).isSome) →
      m3134 a inds = .error .bounds)

theorem p3134 : P3134 := fun a _ _ ha =>
  ⟨fun h1 h2 => m3134_spec ha h1 h2, fun h1 h2 => m3134_arg ha h1 h2, fun h1 h2 h3 => m3134_bounds ha h1 h2 h3⟩

/-- `keepat!(a, m::AbstractVector{Bool})` (docstring base/array.jl:3137-3142: "the in-place
version of logical indexing `a = a[m]`") when the kept slots are assigned: the slots where
`m` is true, in order; a mask of another length throws `BoundsError`. -/
def P3159 : Prop := ∀ {α : Type} (a : Arr α) (n : Int) (mask : List Bool), VecOK a n →
    ((mask.length : Int) = n → (∀ t ∈ maskIdx mask true, (a.at t).isSome) → ∃ a', m3159 a mask = .ok a' ∧
      IsVec a' (maskIdx mask true).length ∧ contents a' = (maskIdx mask true).map a.at) ∧
    ((mask.length : Int) ≠ n → m3159 a mask = .error .bounds)

theorem p3159 : P3159 := by
  intro α a n mask ha
  obtain ⟨hn, _, _, _, _, _⟩ := vecOK_unpack ha
  refine ⟨fun h1 h2 => m3159_spec ha h1 h2, fun h => ?_⟩
  unfold m3159 keepatMask; rw [if_pos (by rw [hn]; exact h)]

/-- `keepat!` keeps the items at `inds` (docstring base/array.jl:3113-3115, "Items which are
kept are shifted to fill the resulting gaps") and is the in-place `a = a[m]` for a mask, for
every vector, as `deleteat!` of the complement does: an `#undef` kept slot stays `#undef`. -/
def PKeepat : Prop := ∀ {α : Type} (a : Arr α) (n : Int), VecOK a n →
    (∀ inds : List Int, Incr inds → (∀ k ∈ inds, 1 ≤ k ∧ k ≤ n) → ∃ a', m3134 a inds = .ok a' ∧
      IsVec a' inds.length ∧ contents a' = inds.map a.at) ∧
    (∀ mask : List Bool, (mask.length : Int) = n → ∃ a', m3159 a mask = .ok a' ∧
      IsVec a' (maskIdx mask true).length ∧ contents a' = (maskIdx mask true).map a.at)

/-- A vector of length 3 whose second slot is `#undef` (the reproducer uses a `Vector{String}`). -/
def undefMid : Arr Int := ⟨⟨3, fun k => if k = 2 then none else some k⟩, 1, [3]⟩

theorem pKeepat_refuted : ¬ PKeepat := by
  intro h
  have hv : VecOK undefMid 3 := ⟨rfl, ⟨by decide, by decide, by decide⟩, show (3 : Int) ≤ 2 ^ 60 by decide⟩
  obtain ⟨a', e, _⟩ := (h undefMid 3 hv).1 [1, 2] ⟨by decide, trivial⟩
    (fun k hk => by simp at hk; omega)
  have : m3134 undefMid [1, 2] = .error .undefRef := by rfl
  rw [this] at e; cases e

end JuliaLean.MultidimCov.ArrayV2
