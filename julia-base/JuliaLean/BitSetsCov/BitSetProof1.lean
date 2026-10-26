import JuliaLean.BitSetsCov.BitSetProps

/-!
# Proofs of the elementwise `BitSet` properties
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem toInt_ok {x : Int} (h : inIntRange x) : toInt x = .ok ⟨x, (inIntRange_iff x).mp h⟩ := by
  simp [toInt, h]

theorem toInt_err {x : Int} (h : ¬ inIntRange x) : toInt x = .error .inexactError := by
  simp [toInt, h]

theorem push_ok {s : BitSetS} {x : Int} (h : inIntRange x) :
    push s x = .ok (s.setint ⟨x, (inIntRange_iff x).mp h⟩ true) := by
  simp [push, toInt_ok h]; rfl

theorem unionItr_spec : ∀ (xs : List Int) (s : BitSetS), WF s → (∀ x ∈ xs, inIntRange x) →
    ∃ s', unionItr s xs = .ok s' ∧ WF s' ∧ ∀ x, mem s' x = (mem s x || decide (x ∈ xs))
  | [], s, h, _ => ⟨s, rfl, h, fun x => by simp⟩
  | y :: ys, s, h, hr => by
    have hy : inIntRange y := hr y (List.mem_cons_self ..)
    have hys : ∀ x ∈ ys, inIntRange x := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    have hw := wf_setint h ⟨y, (inIntRange_iff y).mp hy⟩ true
    obtain ⟨s', h1, h2, h3⟩ := unionItr_spec ys _ hw hys
    refine ⟨s', ?_, h2, fun x => ?_⟩
    · show List.foldlM push s (y :: ys) = _
      rw [List.foldlM_cons, push_ok hy]
      exact h1
    · rw [h3, mem_setint h]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy]

theorem unionItr_err : ∀ (xs : List Int) (s : BitSetS), (∃ x ∈ xs, ¬ inIntRange x) →
    unionItr s xs = .error .inexactError
  | [], _, ⟨_, hx, _⟩ => absurd hx (List.not_mem_nil)
  | y :: ys, s, ⟨x, hx, hnx⟩ => by
    show List.foldlM push s (y :: ys) = _
    rw [List.foldlM_cons]
    by_cases hy : inIntRange y
    · rw [push_ok hy]
      have hxs : x ∈ ys := by
        rcases List.mem_cons.mp hx with h | h
        · subst h; exact absurd hy hnx
        · exact h
      exact unionItr_err ys _ ⟨x, hxs, hnx⟩
    · simp [push, toInt_err hy]; rfl

end BS

theorem bitSetBuildSpec : BitSetBuildSpec := by
  refine ⟨BS.wf_new, BS.mem_new, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro s xs h hr
    obtain ⟨s', h1, h2, h3⟩ := BS.unionItr_spec xs s h hr
    exact ⟨s', h1, h1, h2, h3⟩
  · intro s xs he
    exact BS.unionItr_err xs s he
  · intro xs hr
    obtain ⟨s', h1, h2, h3⟩ := BS.unionItr_spec xs BS.new BS.wf_new hr
    exact ⟨s', h1, h2, fun x => by rw [h3, BS.mem_new]; rfl⟩

theorem length_vresize (v : List U64) (n : Nat) (d : U64) : (vresize v n d).length = n := by
  unfold vresize
  split
  · simp; omega
  · simp; omega

theorem bitSetCopySpec : BitSetCopySpec := by
  intro dest src dirty
  have hc : ∀ d : BitSetS, BS.copyBang d src dirty = .ok src := by
    intro d
    simp only [BS.copyBang, vcopyto, length_vresize, gt_iff_lt, Nat.lt_irrefl, if_false]
    show (Except.ok (src.bits ++ List.drop src.bits.length (vresize d.bits src.bits.length dirty)) >>=
      fun bits => pure ⟨bits, src.offset⟩ : R BitSetS) = _
    rw [List.drop_eq_nil_of_le (by rw [length_vresize]; exact Nat.le_refl _)]
    simp; rfl
  exact ⟨hc dest, hc BS.new, hc BS.new⟩

theorem bitSetSizehintSpec : BitSetSizehintSpec := by
  intro t s n
  have hb := wrapInt_bounds t (n.val + (JInt.lit t 63).val)
  have hn := n.property
  have hv : (n + JInt.lit t 63).val = wrapInt t (n.val + (JInt.lit t 63).val) := rfl
  by_cases h128 : t.bits = 128
  · by_cases hr : inIntRange (wrapInt t (n.val + (JInt.lit t 63).val) / 64)
    · left
      simp only [BS.sizehint, BS.vsizehint, hv, BS.toInt_ok hr]
      rfl
    · right
      refine ⟨h128, ?_⟩
      simp only [BS.sizehint, BS.vsizehint, hv, BS.toInt_err hr]
      rfl
  · left
    have hr : inIntRange (wrapInt t (n.val + (JInt.lit t 63).val) / 64) := by
      unfold inIntRange
      cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb h128 ⊢ <;> omega
    simp only [BS.sizehint, BS.vsizehint, hv, BS.toInt_ok hr]
    rfl

theorem bitSetInSpec : BitSetInSpec := by
  refine ⟨fun b m off => BS.mem_contains _ m, fun n => rfl, ?_⟩
  intro s h n
  unfold BS.inInteger BS.inInt BS.bitsGetindex
  by_cases hr : inIntRange n
  · rw [dif_pos hr, BS.mem_contains]
  · rw [dif_neg hr, BS.mem_out h hr]

theorem deleteInteger_spec {s : BitSetS} (h : BS.WF s) (n : Int) :
    BS.WF (BS.deleteInteger s n) ∧
    ∀ x, BS.mem (BS.deleteInteger s n) x = (BS.mem s x && decide (x ≠ n)) := by
  unfold BS.deleteInteger BS.deleteInt
  by_cases hr : inIntRange n
  · rw [dif_pos hr]
    refine ⟨BS.wf_setint h _ false, fun x => ?_⟩
    rw [BS.mem_setint h]
    by_cases hx : x = n
    · simp [hx]
    · simp [hx]
  · rw [dif_neg hr]
    refine ⟨h, fun x => ?_⟩
    by_cases hx : x = n
    · subst hx; simp [BS.mem_out h hr]
    · simp [hx]

theorem bitSetDeleteSpec : BitSetDeleteSpec := by
  refine ⟨?_, ?_⟩
  · intro s h n
    refine ⟨BS.wf_setint h n false, fun x => ?_⟩
    unfold BS.deleteInt
    rw [BS.mem_setint h]
    by_cases hx : x = n.val <;> simp [hx]

  intro s h n
  have hin := bitSetInSpec.2.2 s h n
  obtain ⟨h1, h2⟩ := deleteInteger_spec h n
  refine ⟨h1, h2, ?_, ?_⟩
  · unfold BS.popKey; rw [hin]
  · unfold BS.popDefault; rw [hin]

theorem check0_iff (a : List U64) (b e : Int) (hb : 1 ≤ b) :
    BS.check0 a b e = true ↔ ∀ i : Int, b ≤ i → i ≤ e → a.getD (i - 1).toNat 0 = 0 := by
  unfold BS.check0 vget
  rw [List.all_eq_true]
  constructor
  · intro hall i h1 h2
    have := hall (i - b).toNat (List.mem_range.mpr (by omega))
    rw [show b + ((i - b).toNat : Int) = i by omega] at this
    have h3 : ((i).toNat - 1) = (i - 1).toNat := by omega
    rw [← h3]
    simpa using this
  · intro hall k hk
    have hk' := List.mem_range.mp hk
    have := hall (b + k) (by omega) (by omega)
    rw [show (b + (k : Int) - 1).toNat = (b + (k : Int)).toNat - 1 by omega] at this
    simpa using this

theorem chunk_zero_of_mem (s : BitSetS) (hall : ∀ x, BS.mem s x = false) (p : Nat) :
    s.bits.getD p 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := hall (64 * (s.offset + p) + j)
  unfold BS.mem G at this
  rw [show (64 * (s.offset + p) + j) / 64 = s.offset + p by omega,
    show ((64 * (s.offset + p) + (j : Int)) % 64).toNat = j by omega,
    if_pos (by omega), show (s.offset + p - s.offset).toNat = p by omega] at this
  rw [this]; simp

theorem bitSetEmptySpec : BitSetEmptySpec := by
  refine ⟨check0_iff, ?_⟩
  intro s h
  refine ⟨⟨fun _ => rfl, fun h => absurd rfl h⟩, fun x => G_nil _ _ _, rfl, ?_⟩
  unfold BS.isempty
  rw [check0_iff _ _ _ (by omega)]
  constructor
  · intro hall x
    unfold BS.mem G
    split
    · rename_i hc
      by_cases hl : (x / 64 - s.offset).toNat < s.bits.length
      · have := hall ((x / 64 - s.offset).toNat + 1) (by omega) (by omega)
        have e : (((x / 64 - s.offset).toNat : Int) + 1 - 1).toNat = (x / 64 - s.offset).toNat := by omega
        rw [e] at this
        rw [this]; simp
      · rw [getD_ge _ _ (by omega)]; simp
    · rfl
  · intro hall i h1 h2
    exact chunk_zero_of_mem s hall _

theorem symdiffSet_spec : ∀ (ns : List Int) (s : BitSetS), BS.WF s → ns.Nodup →
    (∀ x ∈ ns, inIntRange x) →
    ∃ s', BS.symdiffSet s ns = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s x ^^ decide (x ∈ ns))
  | [], s, h, _, _ => ⟨s, rfl, h, fun x => by simp⟩
  | y :: ys, s, h, hnd, hr => by
    have hy : inIntRange y := hr y (List.mem_cons_self ..)
    have hys : ∀ x ∈ ys, inIntRange x := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    have hyn : y ∉ ys := (List.nodup_cons.mp hnd).1
    have hw := BS.wf_setint h ⟨y, (inIntRange_iff y).mp hy⟩ (!(BS.inInt ⟨y, (inIntRange_iff y).mp hy⟩ s))
    obtain ⟨s', h1, h2, h3⟩ := symdiffSet_spec ys _ hw (List.nodup_cons.mp hnd).2 hys
    refine ⟨s', ?_, h2, fun x => ?_⟩
    · show List.foldlM BS.intSymdiff s (y :: ys) = _
      rw [List.foldlM_cons]
      simp only [BS.intSymdiff, BS.toInt_ok hy]
      exact h1
    · rw [h3, BS.mem_setint h]
      unfold BS.inInt BS.bitsGetindex
      rw [BS.mem_contains]
      by_cases hxy : x = y
      · subst hxy; simp [hyn]
      · simp [hxy]

theorem bitSetSymdiffSetSpec : BitSetSymdiffSetSpec :=
  fun s ns h hnd hr => symdiffSet_spec ns s h hnd hr

/-! ## `_growend0!` and `_growbeg0!` -/

theorem set_mid (pre post : List U64) (j r : Nat) (d : U64) :
    (pre ++ List.replicate j 0 ++ List.replicate (r + 1) d ++ post).set (pre.length + j) 0 =
      pre ++ List.replicate (j + 1) 0 ++ List.replicate r d ++ post := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_set, List.length_append, List.length_replicate] at h1
    rw [List.getElem_set]
    simp only [List.getElem_append, List.getElem_replicate, List.length_append, List.length_replicate]
    simp only [show pre.length + (j + 1) + r = pre.length + j + (r + 1) by omega]
    repeat' split
    all_goals first | rfl | omega

theorem fold_zero_at (pre post : List U64) (d : U64) : ∀ (k j : Nat), j ≤ k →
    (List.range j).foldl (fun b' (i : Nat) => vset b' (pre.length + 1 + i) 0)
      (pre ++ List.replicate k d ++ post) =
      pre ++ List.replicate j 0 ++ List.replicate (k - j) d ++ post := by
  intro k j hj
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, vset]
    obtain ⟨r, hr⟩ : ∃ r, k - j = r + 1 := ⟨k - j - 1, by omega⟩
    rw [hr, show pre.length + 1 + j - 1 = pre.length + j by omega, set_mid,
      show k - (j + 1) = r by omega]

theorem growend0_eq (b : List U64) (k : Nat) (d : U64) : BS.growend0 b k d = b ++ List.replicate k 0 := by
  unfold BS.growend0 growend
  simp only [List.length_append, List.length_replicate, Nat.add_sub_cancel_left]
  have := fold_zero_at b [] d k k (Nat.le_refl _)
  simp only [List.append_nil, Nat.sub_self, List.replicate_zero] at this
  exact this

theorem growbeg0_eq (b : List U64) (k : Nat) (d : U64) : BS.growbeg0 b k d = List.replicate k 0 ++ b := by
  unfold BS.growbeg0 growbeg
  have := fold_zero_at [] b d k k (Nat.le_refl _)
  simp only [List.nil_append, Nat.sub_self, List.replicate_zero, List.append_nil, List.length_nil,
    Nat.zero_add] at this
  exact this

theorem bitSetGrowSpec : BitSetGrowSpec :=
  fun b k d => ⟨growend0_eq b k d, growbeg0_eq b k d⟩

end JuliaLean.BitSetsCov
