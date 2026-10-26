import JuliaLean.BitSetsCov.BitSetIter
import JuliaLean.BitSetsCov.BitSetRange

/-!
# Iteration, `first`, `last`, `length` and `show` of a `BitSet`

`_bits_findnext` and `_bits_findprev` are the `BitVector` searches of
`base/bitarray.jl` on the chunk vector, which is the packing of its own bits;
iteration lists the set positions in order (`elems_eq`), so the extreme
elements, the count and the printed text all follow from that list.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem pack_unpack (cs : List U64) : pack (unpack cs (64 * cs.length)) = cs := by
  apply List.ext_getElem
  · rw [pack_length, RangeSpec.length_unpack, numBitChunks_eq]; omega
  · intro c h1 h2
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have e : (pack (unpack cs (64 * cs.length)))[c] = chunkAt (unpack cs (64 * cs.length)) c := by
      simp [pack]
    rw [e, getLsbD_chunkAt, if_pos hj, RangeSpec.getD_unpack, if_pos (by omega), bitOf_def,
      show (64 * c + j) / 64 = c by omega, show (64 * c + j) % 64 = j by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem find_congr (f g : Nat → Bool) (n : Nat) (h : ∀ p, p < n → f p = g p) :
    (List.range n).find? f = (List.range n).find? g := by
  rcases hg : (List.range n).find? g with _ | p
  · rw [FindProof.find_none] at hg ⊢
    intro q hq; rw [h q hq]; exact hg q hq
  · rw [FindProof.find_some] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    exact ⟨h1, by rw [h p h1]; exact h2, fun q hq => by rw [h q (by omega)]; exact h3 q hq⟩

theorem find_rev_congr (f g : Nat → Bool) (n : Nat) (h : ∀ p, p < n → f p = g p) :
    (List.range n).reverse.find? f = (List.range n).reverse.find? g := by
  rcases hg : (List.range n).reverse.find? g with _ | p
  · rw [FindProof.find_rev_none] at hg ⊢
    intro q hq; rw [h q hq]; exact hg q hq
  · rw [FindProof.find_rev_some] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    exact ⟨h1, by rw [h p h1]; exact h2, fun q hq hq2 => by rw [h q hq2]; exact h3 q hq hq2⟩

theorem bitsFindnext_spec (b : List U64) (start : Nat) : bitsFindnext b start =
    match (List.range (64 * b.length)).find? (fun p => decide (start ≤ p) && bitOf b p) with
    | some p => (p : Int) | none => -1 := by
  unfold bitsFindnext
  by_cases h : start / 64 + 1 > b.length
  · rw [if_pos h]
    have : (List.range (64 * b.length)).find? (fun p => decide (start ≤ p) && bitOf b p) = none := by
      rw [FindProof.find_none]
      intro q hq
      have : ¬ start ≤ q := by omega
      simp [this]
    rw [this]
  · rw [if_neg h]
    have hl := RangeSpec.length_unpack b (64 * b.length)
    have e : unsafeBitfindnext b (start + 1) = unsafeBitfindnext (pack (unpack b (64 * b.length))) (start + 1) := by
      rw [pack_unpack]
    rw [e, FindProof.next_unsafe _ _ (by omega) (by rw [hl]; omega), hl,
      find_congr _ (fun p => decide (start ≤ p) && bitOf b p)]
    · rcases (List.range (64 * b.length)).find? (fun p => decide (start ≤ p) && bitOf b p) with _ | p
      · rfl
      · show ((p + 1 : Nat) : Int) - 1 = p; omega
    · intro p hp
      rw [RangeSpec.getD_unpack, if_pos hp]
      congr 1
      apply decide_eq_decide.mpr; omega

theorem bitsFindprev_spec (b : List U64) (start : Int) (hs : start < 64 * b.length) : bitsFindprev b start =
    match (List.range (64 * b.length)).reverse.find? (fun (p : Nat) => decide ((p : Int) ≤ start) && bitOf b p) with
    | some p => (p : Int) | none => -1 := by
  unfold bitsFindprev
  by_cases h : ¬ start ≥ 0
  · rw [if_pos h]
    have : (List.range (64 * b.length)).reverse.find? (fun (p : Nat) => decide ((p : Int) ≤ start) && bitOf b p) = none := by
      rw [FindProof.find_rev_none]
      intro q hq
      have : ¬ (q : Int) ≤ start := by omega
      simp [this]
    rw [this]
  · rw [if_neg h]
    have hl := RangeSpec.length_unpack b (64 * b.length)
    have e : unsafeBitfindprev b (start + 1).toNat = unsafeBitfindprev (pack (unpack b (64 * b.length))) (start + 1).toNat := by
      rw [pack_unpack]
    rw [e, FindProof.prev_unsafe _ _ (by omega) (by rw [hl]; omega), hl,
      find_rev_congr _ (fun (p : Nat) => decide ((p : Int) ≤ start) && bitOf b p)]
    · rcases (List.range (64 * b.length)).reverse.find? (fun (p : Nat) => decide ((p : Int) ≤ start) && bitOf b p) with _ | p
      · rfl
      · show ((p + 1 : Nat) : Int) - 1 = p; omega
    · intro p hp
      rw [RangeSpec.getD_unpack, if_pos hp]
      congr 1
      apply decide_eq_decide.mpr; omega

/-! ## Values of positions -/

theorem wrap_val (x : Int) (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

theorem mem_pos (bits : List U64) (p : Nat) : p ∈ pos bits ↔ p < 64 * bits.length ∧ bitOf bits p = true := by
  unfold pos; simp

theorem pos_nil_of (s : BitSetS) (h : WF s) (ho : s.offset = noOffset) : pos s.bits = [] := by
  rw [h.1 ho]; unfold pos; simp

theorem elemAt_val (s : BitSetS) (h : WF s) (p : Nat) (hp : p ∈ pos s.bits) :
    (elemAt s.offset p).val = p + 64 * s.offset := by
  have hpl := ((mem_pos _ _).mp hp).1
  by_cases ho : s.offset = noOffset
  · rw [pos_nil_of s h ho] at hp; simp at hp
  · have := h.2 ho
    exact wrap_val _ (by omega)

theorem mem_iff_pos (s : BitSetS) (h : WF s) (x : Int) :
    mem s x = true ↔ ∃ p ∈ pos s.bits, (p : Int) + 64 * s.offset = x := by
  rw [mem_Cg, Cg_def]
  constructor
  · intro hm
    split at hm
    · rename_i hc
      have hlt : (x / 64 - s.offset).toNat < s.bits.length := by
        by_cases hlt : (x / 64 - s.offset).toNat < s.bits.length
        · exact hlt
        · rw [getD_ge _ _ (by omega)] at hm; simp at hm
      refine ⟨(x - 64 * s.offset).toNat, (mem_pos _ _).mpr ⟨by omega, ?_⟩, by omega⟩
      rw [bitOf_def, show (x - 64 * s.offset).toNat / 64 = (x / 64 - s.offset).toNat by omega,
        show (x - 64 * s.offset).toNat % 64 = (x % 64).toNat by omega]
      exact hm
    · simp at hm
  · intro ⟨p, hp, hx⟩
    obtain ⟨hpl, hb⟩ := (mem_pos _ _).mp hp
    rw [if_pos (by omega)]
    rw [bitOf_def] at hb
    rw [show (x / 64 - s.offset).toNat = p / 64 by omega, show (x % 64).toNat = p % 64 by omega]
    exact hb

theorem pos_pairwise (bits : List U64) : (pos bits).Pairwise (· < ·) := by
  unfold pos
  exact List.Pairwise.filter _ List.pairwise_lt_range

theorem elems_vals (s : BitSetS) (h : WF s) :
    (elems s).map (·.val) = (pos s.bits).map (fun (p : Nat) => (p : Int) + 64 * s.offset) := by
  rw [elems_eq, List.map_map]
  apply List.map_congr_left
  intro p hp
  exact elemAt_val s h p hp

/-! ## `length` -/

theorem countOnes_le (x : U64) : countOnes x ≤ 64 := by
  unfold countOnes
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem bitcount_val : ∀ (bc : List U64) (n : JInt64), 0 ≤ n.val → n.val + 64 * bc.length < 2 ^ 63 →
    (bitcount bc n).val = n.val + (bc.map countOnes).sum
  | [], n, _, _ => by simp [bitcount]
  | c :: rest, n, h1, h2 => by
    have hc := countOnes_le c
    have hb := wrap_val (n.val + countOnes c) (by simp at h2; omega)
    have ih := bitcount_val rest (JInt.wrap .i64 (n.val + countOnes c)) (by rw [hb]; omega)
      (by rw [hb]; simp at h2; omega)
    show (bitcount rest (JInt.wrap .i64 (n.val + countOnes c))).val = _
    rw [ih, hb, List.map_cons, List.sum_cons]
    push_cast; omega

theorem pos_length (bits : List U64) : (pos bits).length = (bits.map countOnes).sum := by
  unfold pos
  rw [pos_eq, List.length_flatMap]
  simp only [List.length_map]
  have : (List.range bits.length).map (fun c => (cpos (bits.getD c 0)).length) = bits.map countOnes := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]
      rfl
  rw [this]

theorem length_spec (s : BitSetS) (hl : s.bits.length < 2 ^ 57) : (length s).val = (pos s.bits).length := by
  unfold length
  have h0 : (JInt.lit .i64 0).val = 0 := rfl
  rw [bitcount_val _ _ (by rw [h0]; omega) (by rw [h0]; omega), h0, pos_length]
  simp

/-! ## `first` and `last` -/

theorem head_filter (l : List Nat) (f : Nat → Bool) : (l.filter f).head? = l.find? f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, List.find?_cons]
    cases f x
    · simpa using ih
    · rfl

theorem last_filter (l : List Nat) (f : Nat → Bool) : (l.filter f).getLast? = l.reverse.find? f := by
  rw [List.getLast?_eq_head?_reverse, ← List.filter_reverse, head_filter]

theorem first_spec (s : BitSetS) (h : WF s) :
    first s = (match (elems s).head? with | some x => .ok x | none => .error .argumentError) := by
  unfold first
  rw [bitsFindnext_spec, elems_eq, List.head?_map]
  have e : (List.range (64 * s.bits.length)).find? (fun p => decide (0 ≤ p) && bitOf s.bits p) = (pos s.bits).head? := by
    unfold pos
    rw [head_filter]
    simp
  rw [e]
  rcases hp : (pos s.bits).head? with _ | p
  · rfl
  · have hm : p ∈ pos s.bits := List.mem_of_mem_head? hp
    simp only [Option.map_some]
    rw [if_neg (by omega)]
    show Except.ok (JInt.wrap .i64 ((p : Int) + (shl6 s.offset).val)) = _
    unfold shl6 elemAt
    rw [wrap_add_wrap, show (p : Int) + s.offset * 64 = p + 64 * s.offset by omega]

theorem last_spec (s : BitSetS) (h : WF s) (hl : s.bits.length < 2 ^ 57) :
    last s = (match (elems s).getLast? with | some x => .ok x | none => .error .argumentError) := by
  unfold last
  have hs : (shl6 s.bits.length).val = 64 * s.bits.length := by
    unfold shl6; rw [wrap_val _ (by omega)]; omega
  rw [hs, bitsFindprev_spec _ _ (by omega), elems_eq, List.getLast?_map]
  have e : (List.range (64 * s.bits.length)).reverse.find?
      (fun (p : Nat) => decide ((p : Int) ≤ 64 * s.bits.length - 1) && bitOf s.bits p) = (pos s.bits).getLast? := by
    unfold pos; rw [last_filter]
    apply find_rev_congr
    intro p hp
    have : (p : Int) ≤ 64 * s.bits.length - 1 := by omega
    simp [this]
  rw [e]
  rcases hp : (pos s.bits).getLast? with _ | p
  · rfl
  · simp only [Option.map_some]
    rw [if_neg (by omega)]
    show Except.ok (JInt.wrap .i64 ((p : Int) + (shl6 s.offset).val)) = _
    unfold shl6 elemAt
    rw [wrap_add_wrap, show (p : Int) + s.offset * 64 = p + 64 * s.offset by omega]

/-! ## `show` -/

def step (acc : String × Bool) (n : JInt64) : String × Bool :=
  ((if !acc.2 then acc.1 ++ ", " else acc.1) ++ toString n.val, false)

theorem fold_false : ∀ (ys : List JInt64) (a : String), ys ≠ [] →
    ys.foldl step (a, false) = (a ++ ", " ++ joinComma (ys.map (fun n => toString n.val)), false)
  | [], _, h => absurd rfl h
  | [y], a, _ => by simp [step, joinComma]
  | y :: z :: zs, a, _ => by
    rw [List.foldl_cons, show step (a, false) y = (a ++ ", " ++ toString y.val, false) by simp [step],
      fold_false (z :: zs) _ (by simp)]
    simp [joinComma, String.append_assoc]

theorem show_spec (s : BitSetS) :
    showStr s = "BitSet([" ++ joinComma ((elems s).map (fun n => toString n.val)) ++ "])" := by
  unfold showStr
  show "BitSet([" ++ ((elems s).foldl step ("", true)).1 ++ "])" = _
  rcases elems s with _ | ⟨y, ys⟩
  · rfl
  · rw [List.foldl_cons, show step ("", true) y = (toString y.val, false) by simp [step]]
    by_cases hy : ys = []
    · subst hy; simp [joinComma]
    · rw [fold_false ys _ hy]
      rcases ys with _ | ⟨z, zs⟩
      · exact absurd rfl hy
      · simp [joinComma]

end BS

theorem bitSetFindSpec : BitSetFindSpec := ⟨BS.bitsFindnext_spec, BS.bitsFindprev_spec⟩

theorem bitSetIterSpec : BitSetIterSpec := by
  intro s h hl
  simp only []
  have hf := BS.first_spec s h
  have hla := BS.last_spec s h hl
  have hv := BS.elems_vals s h
  have hlen : (BS.elems s).length = (BS.pos s.bits).length := by
    rw [← List.length_map (f := (·.val)), hv, List.length_map]
  have hmem : ∀ x, x ∈ (BS.elems s).map (·.val) ↔ BS.mem s x = true := by
    intro x; rw [hv, BS.mem_iff_pos s h, List.mem_map]
  have hpop : ∀ x : JInt64, x ∈ BS.elems s → BS.popKey s x.val = .ok (x.val, BS.deleteInteger s x.val) := by
    intro x hx
    have hm : BS.mem s x.val = true := (hmem x.val).mp (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hin := (bitSetInSpec.2.2 s h x.val)
    unfold BS.popKey; rw [hin, hm]; rfl
  refine ⟨?_, hmem, ?_, ?_, hf, hla, hf, hla, ?_, rfl, ?_, ?_, BS.show_spec s⟩
  · intro _
    rfl
  · rw [hv]
    exact List.Pairwise.map _ (fun a b hab => by omega) (BS.pos_pairwise _)
  · rw [BS.length_spec s hl, hlen]
  · unfold BS.extrema
    rw [hf, hla]
    rcases hh : (BS.elems s).head? with _ | x
    · rfl
    · have : (BS.elems s) ≠ [] := fun he => by rw [he] at hh; simp at hh
      rcases hg : (BS.elems s).getLast? with _ | y
      · rw [List.getLast?_eq_none_iff] at hg; exact absurd hg this
      · rfl
  · unfold BS.pop
    rw [hla]
    rcases hg : (BS.elems s).getLast? with _ | y
    · rfl
    · exact hpop y (List.mem_of_getLast? hg)
  · unfold BS.popfirst
    rw [hf]
    rcases hh : (BS.elems s).head? with _ | x
    · rfl
    · exact hpop x (List.mem_of_mem_head? hh)

end JuliaLean.BitSetsCov
