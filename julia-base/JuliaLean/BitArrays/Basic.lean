import JuliaLean.BitArrays.Properties

/-!
# Foundation lemmas for the `BitArrays` proofs

Bit-level descriptions of the chunk helpers of `Chunks.lean` and `Vector.lean`
through `bitOf cs k` (0-based bit `k` of a chunk vector), the packing `pack`,
and the extensionality lemma `eq_ofList_of_bits` that reduces an equation
`B = BV.ofList l` to a length check and a bitwise comparison.

Most bit lemmas are stated with `if` on the right-hand side, so that a chain of
`simp only` rewrites followed by `split` and `omega` decides the resulting
goals (tactics `bitsimp` and `bfin` at the end of the file).
-/

namespace JuliaLean.BitArrays

open BV

/-! ## Arithmetic of chunk indices -/

theorem numBitChunks_eq (n : Nat) : numBitChunks n = (n + 63) / 64 := by
  unfold numBitChunks div64 mod64; split <;> omega

theorem getChunksId_fst (i : Nat) : (getChunksId i).1 = (i - 1) / 64 + 1 := rfl
theorem getChunksId_snd (i : Nat) : (getChunksId i).2 = (i - 1) % 64 := rfl

theorem ofList_len (l : List Bool) : (BV.ofList l).len = l.length := rfl
theorem ofList_chunks (l : List Bool) : (BV.ofList l).chunks = pack l := rfl

/-! ## `List Bool` positions -/

theorem getD_ge {l : List Bool} {k : Nat} (h : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]; rfl

theorem getD_lt {l : List Bool} {k : Nat} (h : k < l.length) : l.getD k false = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem getD_set (l : List Bool) (p : Nat) (x : Bool) (k : Nat) :
    (l.set p x).getD k false = if k = p ∧ p < l.length then x else l.getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : p = k
  · subst h1
    by_cases h2 : p < l.length
    · rw [if_pos rfl, if_pos h2, if_pos ⟨rfl, h2⟩]; rfl
    · rw [if_pos rfl, if_neg h2, if_neg (fun h => h2 h.2), List.getElem?_eq_none_iff.mpr (by omega)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]

theorem getD_append (a b : List Bool) (k : Nat) :
    (a ++ b).getD k false = if k < a.length then a.getD k false else b.getD (k - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

theorem getD_cons (x : Bool) (l : List Bool) (k : Nat) :
    (x :: l).getD k false = if k = 0 then x else l.getD (k - 1) false := by
  cases k <;> simp

theorem getD_insertIdx (l : List Bool) (q : Nat) (x : Bool) (k : Nat) :
    (l.insertIdx q x).getD k false =
      if k < q then l.getD k false else if k = q then (if q ≤ l.length then x else false)
      else l.getD (k - 1) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
  by_cases h1 : k < q
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : k = q
    · subst h2
      by_cases h3 : k ≤ l.length
      · rw [if_pos rfl, if_pos h3, if_pos rfl, if_pos h3]; rfl
      · rw [if_pos rfl, if_neg h3, if_pos rfl, if_neg h3]; rfl
    · rw [if_neg h2, if_neg h2]

theorem getD_eraseIdx (l : List Bool) (q k : Nat) :
    (l.eraseIdx q).getD k false = if k < q then l.getD k false else l.getD (k + 1) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split <;> rfl

theorem getD_dropLast (l : List Bool) (k : Nat) :
    l.dropLast.getD k false = if k < l.length - 1 then l.getD k false else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_dropLast]
  split <;> rfl

theorem getD_tail (l : List Bool) (k : Nat) : l.tail.getD k false = l.getD (k + 1) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_tail]

theorem getD_replicate (n : Nat) (x : Bool) (k : Nat) :
    (List.replicate n x).getD k false = if k < n then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getLastD_eq (l : List Bool) : l.getLastD false = l.getD (l.length - 1) false := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem headD_eq (l : List Bool) : l.headD false = l.getD 0 false := by
  cases l <;> rfl

/-! ## Bits of a `UInt64` -/

theorem getLsbD_zero64 (j : Nat) : (0 : U64).getLsbD j = false := by simp

theorem getLsbD_msk64 (j : Nat) : msk64.getLsbD j = if j < 64 then true else false := by
  unfold msk64; rw [BitVec.getLsbD_allOnes]
  by_cases h : j < 64
  · rw [decide_eq_true h, if_pos h]
  · rw [decide_eq_false h, if_neg h]

theorem getLsbD_one_shl (m j : Nat) :
    ((1 : U64) <<< m).getLsbD j = (decide (m < 64) && decide (m = j)) :=
  BitVec.getLsbD_twoPow m j

theorem getLsbD_shl (x : U64) (n j : Nat) :
    (x <<< n).getLsbD j = if j < 64 ∧ n ≤ j then x.getLsbD (j - n) else false := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h1 : j < 64
  · by_cases h2 : j < n
    · rw [if_neg (by omega)]; simp [h2]
    · rw [if_pos ⟨h1, by omega⟩]; simp [h1, h2]
  · rw [if_neg (by omega)]; simp [h1]

theorem getLsbD_not64 (x : U64) (j : Nat) :
    (~~~x).getLsbD j = if j < 64 then !x.getLsbD j else false := by
  rw [BitVec.getLsbD_not]
  by_cases h : j < 64
  · rw [decide_eq_true h, if_pos h]; rfl
  · rw [decide_eq_false h, if_neg h]; rfl

theorem getLsbD_ge64 (x : U64) {j : Nat} (h : 64 ≤ j) : x.getLsbD j = false :=
  BitVec.getLsbD_of_ge x j h

theorem one_eq_twoPow : (1 : U64) = BitVec.twoPow 64 0 := by decide

theorem getLsbD_ofBool (b : Bool) (j : Nat) : (ofBool b).getLsbD j = if j = 0 then b else false := by
  cases b
  · show (0 : U64).getLsbD j = if j = 0 then false else false
    rw [getLsbD_zero64, ite_self]
  · show (1 : U64).getLsbD j = if j = 0 then true else false
    rw [one_eq_twoPow, BitVec.getLsbD_twoPow]
    by_cases h : j = 0
    · subst h; rfl
    · rw [if_neg h]; simp [Ne.symm h]

/-- `_msk_end(l)` has exactly the bits `0:(l-1) % 64` set (all bits when `64 ∣ l`). -/
theorem getLsbD_mskEnd (l j : Nat) :
    (mskEnd l).getLsbD j = decide (j < 64 ∧ (l % 64 = 0 ∨ j < l % 64)) := by
  unfold mskEnd msk64
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem getLsbD_mskEnd_ite (l j : Nat) :
    (mskEnd l).getLsbD j = if j < 64 ∧ (l % 64 = 0 ∨ j < l % 64) then true else false := by
  rw [getLsbD_mskEnd]
  by_cases h : j < 64 ∧ (l % 64 = 0 ∨ j < l % 64)
  · rw [decide_eq_true h, if_pos h]
  · rw [decide_eq_false h, if_neg h]

/-- `(x & (1 << m)) != 0` reads bit `m`. -/
theorem and_one_shl_ne (x : U64) (m : Nat) (hm : m < 64) :
    ((x &&& ((1 : U64) <<< m)) != 0) = x.getLsbD m := by
  by_cases h : x.getLsbD m = true
  · rw [h]
    have hne : (x &&& ((1 : U64) <<< m)) ≠ 0 := by
      intro he
      have := congrArg (fun y : U64 => y.getLsbD m) he
      simp only [BitVec.getLsbD_and, getLsbD_one_shl, h, getLsbD_zero64] at this
      simp [hm] at this
    simpa using hne
  · rw [Bool.not_eq_true] at h
    rw [h]
    have he : (x &&& ((1 : U64) <<< m)) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      rw [BitVec.getLsbD_and, getLsbD_one_shl, getLsbD_zero64]
      by_cases him : m = i
      · subst him; simp [h]
      · simp [him]
    rw [he]; decide

/-- The bit pattern written by `_unsafe_bitsetindex!`. -/
theorem getLsbD_setBit (c : U64) (x : Bool) (m j : Nat) (hm : m < 64) (hj : j < 64) :
    (if x then c ||| ((1 : U64) <<< m) else c &&& ~~~((1 : U64) <<< m)).getLsbD j =
      if j = m then x else c.getLsbD j := by
  cases x
  · show (c &&& ~~~((1 : U64) <<< m)).getLsbD j = _
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_one_shl]
    by_cases hjm : j = m
    · subst hjm; rw [if_pos rfl]; simp [hj]
    · have hmj : ¬ m = j := fun h => hjm h.symm
      rw [if_neg hjm]; simp [hmj, hj]
  · show (c ||| ((1 : U64) <<< m)).getLsbD j = _
    rw [BitVec.getLsbD_or, getLsbD_one_shl]
    by_cases hjm : j = m
    · subst hjm; rw [if_pos rfl]; simp [hj]
    · have hmj : ¬ m = j := fun h => hjm h.symm
      rw [if_neg hjm]; simp [hmj]

/-- One step of the `pushfirst!`/`insert!` carry loop on a single chunk. -/
theorem getLsbD_shlCarry (a b : U64) {j : Nat} (hj : j < 64) :
    ((a <<< 1) ||| (b >>> 63)).getLsbD j = if j = 0 then b.getLsbD 63 else a.getLsbD (j - 1) := by
  rw [BitVec.getLsbD_or, getLsbD_shl, BitVec.getLsbD_ushiftRight]
  by_cases h0 : j = 0
  · subst h0; rw [if_neg (by omega), if_pos rfl]; rfl
  · rw [if_pos ⟨hj, by omega⟩, if_neg h0, getLsbD_ge64 b (by omega : 64 ≤ 63 + j)]
    simp

/-- One step of the `popfirst!`/`deleteat!` carry loop on a single chunk. -/
theorem getLsbD_shrCarry (a b : U64) {j : Nat} (hj : j < 64) :
    ((a >>> 1) ||| (b <<< 63)).getLsbD j = if j = 63 then b.getLsbD 0 else a.getLsbD (j + 1) := by
  rw [BitVec.getLsbD_or, getLsbD_shl, BitVec.getLsbD_ushiftRight]
  by_cases h0 : j = 63
  · subst h0; rw [if_pos ⟨hj, by omega⟩, if_pos rfl, getLsbD_ge64 a (by omega : 64 ≤ 1 + 63)]; simp
  · rw [if_neg (by omega), if_neg h0, Nat.add_comm 1 j]; simp

/-- The chunk computed by `insert!`: bits below `j` stay, bits from `j` on move up one. -/
theorem getLsbD_insChunk (c : U64) (j j' : Nat) :
    ((~~~(msk64 <<< j) &&& c) ||| ((msk64 <<< j &&& c) <<< 1)).getLsbD j' =
      if j' < 64 ∧ j' < j then c.getLsbD j' else if j' < 64 ∧ j < j' then c.getLsbD (j' - 1) else false := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, getLsbD_not64, getLsbD_shl, getLsbD_msk64]
  (repeat' split) <;>
    (try simp only [Bool.or_false, Bool.false_or, Bool.and_true, Bool.true_and, Bool.and_false,
      Bool.false_and, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false]) <;>
    first | rfl | omega | (congr 1; omega)

/-- The chunk computed by `deleteat!`: bits below `j` stay, bits above `j` move down one. -/
theorem getLsbD_delChunk (c : U64) (j j' : Nat) (hj : j < 64) :
    (((msk64 >>> (63 - j)) >>> 1 &&& c) ||| ((~~~(msk64 >>> (63 - j)) &&& c) >>> 1)).getLsbD j' =
      if j' < j then c.getLsbD j' else if j' + 1 < 64 then c.getLsbD (j' + 1) else false := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, getLsbD_not64, BitVec.getLsbD_ushiftRight,
    getLsbD_msk64]
  (repeat' split) <;>
    (try simp only [Bool.or_false, Bool.false_or, Bool.and_true, Bool.true_and, Bool.and_false,
      Bool.false_and, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false]) <;>
    first | rfl | omega | (congr 1; omega) | (rw [getLsbD_ge64 c (by omega)])

/-! ## Bits of a chunk vector -/

theorem bitOf_def (cs : List U64) (k : Nat) : bitOf cs k = (cs.getD (k / 64) 0).getLsbD (k % 64) := rfl

theorem bitOf_ge {cs : List U64} {k : Nat} (h : cs.length ≤ k / 64) : bitOf cs k = false := by
  rw [bitOf_def, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  exact getLsbD_zero64 _

theorem bitOf_eq_getElem (cs : List U64) (c j : Nat) (hc : c < cs.length) (hj : j < 64) :
    bitOf cs (64 * c + j) = cs[c].getLsbD j := by
  rw [bitOf_def, show (64 * c + j) / 64 = c by omega, show (64 * c + j) % 64 = j by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
  rfl

/-- Two chunk vectors of the same length with the same bits are equal. -/
theorem chunks_ext {cs ds : List U64} (hl : cs.length = ds.length)
    (h : ∀ k, bitOf cs k = bitOf ds k) : cs = ds := by
  apply List.ext_getElem hl
  intro c h1 h2
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [← bitOf_eq_getElem cs c j h1 hj, ← bitOf_eq_getElem ds c j h2 hj]
  exact h _

theorem getLsbD_cget (cs : List U64) (c j : Nat) :
    (cget cs c).getLsbD j = if j < 64 then bitOf cs (64 * (c - 1) + j) else false := by
  by_cases hj : j < 64
  · rw [if_pos hj, bitOf_def, show (64 * (c - 1) + j) / 64 = c - 1 by omega,
      show (64 * (c - 1) + j) % 64 = j by omega]
    rfl
  · rw [if_neg hj]; exact getLsbD_ge64 _ (by omega)

theorem getLsbD_cget_lt (cs : List U64) (c : Nat) {j : Nat} (hj : j < 64) :
    (cget cs c).getLsbD j = bitOf cs (64 * (c - 1) + j) := by
  rw [getLsbD_cget, if_pos hj]

/-- `cget cs c = v` exactly when chunk `c` has the bits of `v`. -/
theorem cget_eq_iff (cs : List U64) (c : Nat) (v : U64) :
    cget cs c = v ↔ ∀ j, j < 64 → bitOf cs (64 * (c - 1) + j) = v.getLsbD j := by
  constructor
  · intro h j hj; rw [← getLsbD_cget_lt cs c hj, h]
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro j hj; rw [getLsbD_cget_lt cs c hj]; exact h j hj

/-! ## `chunkAt` and `pack` -/

theorem getLsbD_chunkAt_fold (l : List Bool) (c j : Nat) :
    ∀ (m : Nat) (acc : U64),
    ((List.range m).foldl (fun acc j => if l.getD (64 * c + j) false then acc ||| BitVec.twoPow 64 j else acc)
        acc).getLsbD j
      = (acc.getLsbD j || (decide (j < m) && decide (j < 64) && l.getD (64 * c + j) false)) := by
  intro m
  induction m with
  | zero => intro acc; simp
  | succ m ih =>
    intro acc
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hb : l.getD (64 * c + m) false = true
    · rw [if_pos hb, BitVec.getLsbD_or, ih, BitVec.getLsbD_twoPow]
      by_cases hjm : j = m
      · subst hjm; rw [hb]; simp
      · have hmj : ¬ m = j := fun h => hjm h.symm
        have e : decide (j < m + 1) = decide (j < m) := decide_eq_decide.mpr (by omega)
        rw [e]; simp [hmj]
    · rw [if_neg hb, ih]
      by_cases hjm : j = m
      · subst hjm; rw [Bool.not_eq_true] at hb; rw [hb]; simp
      · have e : decide (j < m + 1) = decide (j < m) := decide_eq_decide.mpr (by omega)
        rw [e]

theorem getLsbD_chunkAt (l : List Bool) (c j : Nat) :
    (chunkAt l c).getLsbD j = if j < 64 then l.getD (64 * c + j) false else false := by
  unfold chunkAt
  rw [getLsbD_chunkAt_fold l c j 64 0, getLsbD_zero64]
  by_cases hj : j < 64
  · rw [if_pos hj]; simp [hj]
  · rw [if_neg hj]; simp [hj]

theorem pack_length (l : List Bool) : (pack l).length = numBitChunks l.length := by simp [pack]

theorem getD_pack (l : List Bool) (c : Nat) :
    (pack l).getD c 0 = if c < numBitChunks l.length then chunkAt l c else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : c < numBitChunks l.length
  · rw [if_pos h]; unfold pack; rw [List.getElem?_map, List.getElem?_range h]; rfl
  · rw [if_neg h, List.getElem?_eq_none_iff.mpr (by rw [pack_length]; omega)]; rfl

/-- Bit `k` of the packing of `l` is `l[k]`, and `false` beyond the end. -/
theorem bitOf_pack (l : List Bool) (k : Nat) : bitOf (pack l) k = l.getD k false := by
  rw [bitOf_def, getD_pack]
  by_cases h : k / 64 < numBitChunks l.length
  · rw [if_pos h, getLsbD_chunkAt, if_pos (Nat.mod_lt _ (by omega)),
      show 64 * (k / 64) + k % 64 = k by omega]
  · rw [if_neg h, getLsbD_zero64]
    rw [numBitChunks_eq] at h
    rw [getD_ge (by omega)]

theorem cget_pack (l : List Bool) (c : Nat) :
    cget (pack l) c = if c - 1 < numBitChunks l.length then chunkAt l (c - 1) else 0 := getD_pack l (c - 1)

theorem toList_ofList (l : List Bool) : (BV.ofList l).toList = l := by
  apply List.ext_getElem?
  intro i
  simp only [BV.toList, BV.ofList, unpack, List.getElem?_map]
  by_cases h : i < l.length
  · rw [List.getElem?_range h, List.getElem?_eq_getElem h]
    simp only [Option.map_some, bitOf_pack, getD_lt h]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega),
      List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-- Extensionality: a `BV` with the length, the chunk count and the bits of the
valid packing of `l` is `BV.ofList l`. -/
theorem eq_ofList_of_bits (B : BV) (l : List Bool) (hlen : B.len = l.length)
    (hc : B.chunks.length = numBitChunks l.length) (hb : ∀ k, bitOf B.chunks k = l.getD k false) :
    B = BV.ofList l := by
  have h1 : B.chunks = pack l :=
    chunks_ext (by rw [hc, pack_length]) (fun k => by rw [hb, bitOf_pack])
  show B = ⟨pack l, l.length⟩
  rw [← h1, ← hlen]

theorem ofList_eq_of_bits (B : BV) (l : List Bool) (hlen : B.len = l.length)
    (hc : B.chunks.length = numBitChunks l.length) (hb : ∀ k, bitOf B.chunks k = l.getD k false) :
    B = BV.ofList l := eq_ofList_of_bits B l hlen hc hb

/-! ## Chunk vector updates -/

theorem length_cset (cs : List U64) (c : Nat) (v : U64) : (cset cs c v).length = cs.length := by
  simp [cset]

theorem bitOf_cset (cs : List U64) (c : Nat) (v : U64) (k : Nat) :
    bitOf (cset cs c v) k =
      if k / 64 = c - 1 ∧ k / 64 < cs.length then v.getLsbD (k % 64) else bitOf cs k := by
  simp only [bitOf, cset, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : c - 1 = k / 64
  · rw [if_pos h1]
    by_cases h2 : c - 1 < cs.length
    · rw [if_pos h2, if_pos ⟨h1.symm, by omega⟩]; rfl
    · rw [if_neg h2, if_neg (by omega), List.getElem?_eq_none_iff.mpr (by omega)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]

theorem length_csetEnd (cs : List U64) (v : U64) : (csetEnd cs v).length = cs.length :=
  length_cset _ _ _

theorem bitOf_csetEnd (cs : List U64) (v : U64) (k : Nat) :
    bitOf (csetEnd cs v) k = if k / 64 + 1 = cs.length then v.getLsbD (k % 64) else bitOf cs k := by
  unfold csetEnd
  rw [bitOf_cset]
  by_cases h : k / 64 + 1 = cs.length
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem cgetEnd_eq (cs : List U64) : cgetEnd cs = cget cs cs.length := rfl

theorem length_growend (cs : List U64) (m : Nat) (d : U64) :
    (growend cs m d).length = cs.length + m := by simp [growend]

theorem bitOf_growend (cs : List U64) (m : Nat) (d : U64) (k : Nat) :
    bitOf (growend cs m d) k =
      if k / 64 < cs.length then bitOf cs k
      else if k / 64 < cs.length + m then d.getLsbD (k % 64) else false := by
  simp only [bitOf, growend, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  by_cases h1 : k / 64 < cs.length
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : k / 64 - cs.length < m
    · rw [if_pos h2, if_pos (by omega)]; rfl
    · rw [if_neg h2, if_neg (by omega)]; exact getLsbD_zero64 _

theorem length_deleteend (cs : List U64) (m : Nat) : (deleteend cs m).length = cs.length - m := by
  simp only [deleteend, List.length_take]; omega

theorem bitOf_deleteend (cs : List U64) (m k : Nat) :
    bitOf (deleteend cs m) k = if k / 64 + m < cs.length then bitOf cs k else false := by
  simp only [bitOf, deleteend, List.getD_eq_getElem?_getD, List.getElem?_take]
  by_cases h : k / 64 < cs.length - m
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]; exact getLsbD_zero64 _

theorem length_map_const (cs : List U64) (v : U64) : (cs.map fun _ => v).length = cs.length :=
  List.length_map _

theorem bitOf_map_const (cs : List U64) (v : U64) (k : Nat) :
    bitOf (cs.map fun _ => v) k = if k / 64 < cs.length then v.getLsbD (k % 64) else false := by
  simp only [bitOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k / 64 < cs.length
  · rw [List.getElem?_eq_getElem h, if_pos h]; rfl
  · rw [List.getElem?_eq_none_iff.mpr (by omega), if_neg h]; exact getLsbD_zero64 _

theorem bitOf_ite (c : Prop) {d : Decidable c} (a b : List U64) (k : Nat) :
    bitOf (@ite _ c d a b) k = @ite _ c d (bitOf a k) (bitOf b k) := by
  cases d <;> rfl

theorem length_ite (c : Prop) {d : Decidable c} (a b : List U64) :
    (@ite _ c d a b).length = @ite _ c d a.length b.length := by
  cases d <;> rfl

/-! ## Scalar indexing -/

/-- `unsafe_bitgetindex(Bc, i)` reads element `i`, i.e. bit `i - 1`. -/
theorem unsafeBitget_eq (cs : List U64) (i : Nat) : unsafeBitget cs i = bitOf cs (i - 1) := by
  simp only [unsafeBitget, getChunksId, cget, div64, mod64, Nat.add_sub_cancel]
  rw [and_one_shl_ne _ _ (Nat.mod_lt _ (by omega))]
  rfl

theorem length_unsafeBitset (cs : List U64) (x : Bool) (i : Nat) :
    (unsafeBitset cs x i).length = cs.length := length_cset _ _ _

/-- `unsafe_bitsetindex!(Bc, x, i)` writes element `i`, i.e. bit `i - 1`. -/
theorem bitOf_unsafeBitset (cs : List U64) (x : Bool) (i k : Nat) :
    bitOf (unsafeBitset cs x i) k = if k = i - 1 ∧ k / 64 < cs.length then x else bitOf cs k := by
  simp only [unsafeBitset, unsafeBitsetAt, getChunksId, div64, mod64]
  rw [bitOf_cset, Nat.add_sub_cancel]
  by_cases h1 : k / 64 = (i - 1) / 64 ∧ k / 64 < cs.length
  · rw [if_pos h1, getLsbD_setBit _ _ _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    by_cases h2 : k = i - 1
    · rw [if_pos (by omega), if_pos ⟨h2, h1.2⟩]
    · rw [if_neg (by omega), if_neg (by omega)]
      simp only [cget, bitOf, Nat.add_sub_cancel, h1.1]
  · rw [if_neg h1, if_neg (by omega)]

/-! ## The carry loops of `pushfirst!`, `popfirst!`, `insert!` and `deleteat!` -/

theorem bitOf_cset_shl (bc : List U64) (i k : Nat) (hi : 2 ≤ i) :
    bitOf (cset bc i ((cget bc i <<< 1) ||| (cget bc (i - 1) >>> 63))) k =
      if k / 64 = i - 1 ∧ k / 64 < bc.length then bitOf bc (k - 1) else bitOf bc k := by
  rw [bitOf_cset]
  by_cases h : k / 64 = i - 1 ∧ k / 64 < bc.length
  · rw [if_pos h, if_pos h, getLsbD_shlCarry _ _ (Nat.mod_lt _ (by omega))]
    by_cases h0 : k % 64 = 0
    · rw [if_pos h0, getLsbD_cget_lt _ _ (by omega)]; congr 1; omega
    · rw [if_neg h0, getLsbD_cget_lt _ _ (by omega)]; congr 1; omega
  · rw [if_neg h, if_neg h]

theorem bitOf_cset_shr (bc : List U64) (i k : Nat) :
    bitOf (cset bc (i + 1) ((cget bc (i + 1) >>> 1) ||| (cget bc (i + 1 + 1) <<< 63))) k =
      if k / 64 = i ∧ i < bc.length then bitOf bc (k + 1) else bitOf bc k := by
  rw [bitOf_cset, Nat.add_sub_cancel]
  by_cases h : k / 64 = i ∧ i < bc.length
  · rw [if_pos ⟨h.1, by omega⟩, if_pos h, getLsbD_shrCarry _ _ (Nat.mod_lt _ (by omega))]
    by_cases h0 : k % 64 = 63
    · rw [if_pos h0, getLsbD_cget_lt _ _ (by omega)]; congr 1; omega
    · rw [if_neg h0, getLsbD_cget_lt _ _ (by omega)]; congr 1; omega
  · rw [if_neg (by omega), if_neg h]

theorem length_shiftUpLoop : ∀ (f i : Nat) (bc : List U64), (shiftUpLoop i f bc).length = bc.length
  | 0, _, _ => rfl
  | f + 1, i, bc => by simp only [shiftUpLoop]; rw [length_shiftUpLoop, length_cset]

theorem length_shiftDownLoop : ∀ (f i : Nat) (bc : List U64), (shiftDownLoop i f bc).length = bc.length
  | 0, _, _ => rfl
  | f + 1, i, bc => by simp only [shiftDownLoop]; rw [length_shiftDownLoop, length_cset]

/-- `for j = i:-1:i-f+1; Bc[j] = (Bc[j] << 1) | (Bc[j-1] >>> 63); end` moves every
bit of chunks `i-f+1:i` up by one position, reading the old bits. -/
theorem bitOf_shiftUpLoop : ∀ (f i : Nat) (bc : List U64), f + 1 ≤ i → ∀ k,
    bitOf (shiftUpLoop i f bc) k =
      if 64 * (i - f) ≤ k ∧ k < 64 * i ∧ k / 64 < bc.length then bitOf bc (k - 1) else bitOf bc k
  | 0, i, bc, _, k => by
      simp only [shiftUpLoop, Nat.sub_zero]; rw [if_neg (by omega)]
  | f + 1, i, bc, h1, k => by
      simp only [shiftUpLoop]
      rw [bitOf_shiftUpLoop f (i - 1) _ (by omega), length_cset,
        bitOf_cset_shl _ _ _ (by omega), bitOf_cset_shl _ _ _ (by omega)]
      (repeat' split) <;> first | rfl | omega | (congr 1; omega)

/-- `for j = i+1:i+f; Bc[j] = (Bc[j] >>> 1) | (Bc[j+1] << 63); end` moves every bit
of chunks `i+1:i+f` down by one position, reading the old bits. -/
theorem bitOf_shiftDownLoop : ∀ (f i : Nat) (bc : List U64) (k : Nat),
    bitOf (shiftDownLoop (i + 1) f bc) k =
      if 64 * i ≤ k ∧ k < 64 * (i + f) ∧ k / 64 < bc.length then bitOf bc (k + 1) else bitOf bc k
  | 0, i, bc, k => by
      simp only [shiftDownLoop, Nat.add_zero]; rw [if_neg (by omega)]
  | f + 1, i, bc, k => by
      simp only [shiftDownLoop]
      rw [bitOf_shiftDownLoop f (i + 1) _ k, length_cset, bitOf_cset_shr, bitOf_cset_shr]
      (repeat' split) <;> first | rfl | omega | (congr 1; omega)

theorem bitOf_shiftDownLoop_one (f : Nat) (bc : List U64) (k : Nat) :
    bitOf (shiftDownLoop 1 f bc) k =
      if k < 64 * f ∧ k / 64 < bc.length then bitOf bc (k + 1) else bitOf bc k := by
  have h := bitOf_shiftDownLoop f 0 bc k
  simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and] at h
  exact h

/-! ## `any` on chunks and on `Bool` lists -/

theorem any_chunks_iff (cs : List U64) : cs.any (· != 0) = true ↔ ∃ k, bitOf cs k = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hne⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp hx
    have hex : ∃ j, j < 64 ∧ cs[c].getLsbD j = true := by
      apply Classical.byContradiction
      intro hno
      apply (show cs[c] ≠ 0 by simpa using hne)
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [getLsbD_zero64]
      cases h : cs[c].getLsbD j
      · rfl
      · exact absurd ⟨j, hj, h⟩ hno
    obtain ⟨j, hj, hb⟩ := hex
    exact ⟨64 * c + j, by rw [bitOf_eq_getElem cs c j hc hj]; exact hb⟩
  · rintro ⟨k, hk⟩
    have hlt : k / 64 < cs.length := by
      apply Classical.byContradiction
      intro h
      rw [bitOf_ge (by omega)] at hk
      exact Bool.false_ne_true hk
    refine ⟨cs[k / 64], List.getElem_mem hlt, ?_⟩
    have e := bitOf_eq_getElem cs (k / 64) (k % 64) hlt (Nat.mod_lt _ (by omega))
    rw [show 64 * (k / 64) + k % 64 = k by omega] at e
    rw [e] at hk
    simp only [bne_iff_ne, ne_eq]
    intro h0
    rw [h0, getLsbD_zero64] at hk
    exact Bool.false_ne_true hk

theorem any_bools_iff (l : List Bool) : l.any id = true ↔ ∃ k, l.getD k false = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hb⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i, by rw [getD_lt hi]; exact hb⟩
  · rintro ⟨k, hk⟩
    have hlt : k < l.length := by
      apply Classical.byContradiction
      intro h
      rw [getD_ge (by omega)] at hk
      exact Bool.false_ne_true hk
    exact ⟨l[k], List.getElem_mem hlt, by rw [← getD_lt hlt]; exact hk⟩

theorem all_bools_iff (l : List Bool) : l.all id = true ↔ ∀ k, k < l.length → l.getD k false = true := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    rw [getD_lt hk]; exact h _ (List.getElem_mem hk)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have := h i hi
    rw [getD_lt hi] at this
    exact this

/-! ## Tactics -/

/-- Rewrite bits of chunk-vector expressions down to `List.getD` of element lists. -/
macro "bitsimp" : tactic => `(tactic| simp only [bitOf_ite, bitOf_cset, bitOf_csetEnd, bitOf_growend,
  bitOf_deleteend, bitOf_pack, bitOf_unsafeBitset, bitOf_shiftDownLoop, bitOf_shiftDownLoop_one,
  bitOf_map_const, length_cset, length_csetEnd, length_growend, length_deleteend, length_ite,
  length_shiftUpLoop, length_shiftDownLoop, length_unsafeBitset, length_map_const, pack_length,
  getLsbD_cget, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_shl,
  getLsbD_ofBool, getLsbD_msk64, getLsbD_mskEnd_ite, getLsbD_zero64, getLsbD_insChunk,
  getLsbD_not64, cgetEnd_eq, ite_self, numBitChunks_eq, getD_set, getD_append, getD_cons,
  getD_insertIdx, getD_eraseIdx, getD_dropLast, getD_tail, getD_replicate, List.getD_nil,
  List.length_append, List.length_cons, List.length_nil, List.length_set, List.length_dropLast,
  List.length_tail, List.length_replicate])

/-- Close a goal of nested `if`s over `Bool` element reads by case analysis and `omega`. -/
macro "bfin" : tactic => `(tactic| all_goals ((repeat' split) <;>
  (try simp only [Bool.or_false, Bool.false_or, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false]) <;>
  first
  | rfl
  | omega
  | (congr 1; omega)
  | exact getD_ge (by omega)
  | exact (getD_ge (by omega)).symm
  | exact (getD_ge (by omega)).trans (getD_ge (by omega)).symm
  | exact bitOf_ge (by omega)
  | exact (bitOf_ge (by omega)).symm
  | exact (bitOf_ge (by omega)).trans (bitOf_ge (by omega)).symm))

end JuliaLean.BitArrays
