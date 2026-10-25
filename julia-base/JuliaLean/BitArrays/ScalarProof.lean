import JuliaLean.BitArrays.Basic

/-!
# Proofs: scalar indexing, dequeue operations, `insert!`/`deleteat!`, `fill!`,
`count`/`any`/`all`

Each operation on `BV.ofList l` is unfolded to an explicit chunk expression;
`eq_ofList_of_bits` then reduces the equation with the reference result to a
length check and a bitwise comparison, decided by `bitsimp` and `bfin`.
-/

namespace JuliaLean.BitArrays

open BV

/-! ## The chunk vector after `push!`/`pushfirst!`/`insert!` grow it by one element -/

/-- `chunks` after the `_growend!` step of `push!`, `pushfirst!` and `insert!`. -/
def growBC (l : List Bool) (dirty : U64) : List U64 :=
  if l.length % 64 = 0 then csetEnd (growend (pack l) 1 dirty) 0 else pack l

theorem growBC_length (l : List Bool) (dirty : U64) :
    (growBC l dirty).length = (l.length + 1 + 63) / 64 := by
  unfold growBC; bitsimp; split <;> omega

theorem bitOf_growBC (l : List Bool) (dirty : U64) (k : Nat) :
    bitOf (growBC l dirty) k = l.getD k false := by
  unfold growBC; bitsimp; bfin

/-! ## Scalar indexing -/

theorem scalarIndexAgrees : ScalarIndexAgrees := by
  intro l i x _
  unfold idx
  by_cases h : 1 ≤ i.val ∧ i.val ≤ l.length
  · rw [if_pos h]
    have hq : ((i.val.toNat : Nat) : Int) = i.val := Int.toNat_of_nonneg (by omega)
    have hb : inBounds (BV.ofList l) i = true := by simp [inBounds, ofList_len, h]
    refine ⟨?_, ?_⟩
    · show kindOf (if inBounds (BV.ofList l) i = true then _ else _) = _
      rw [if_pos hb]
      show Except.ok (unsafeBitget (pack l) i.val.toNat) = Except.ok (l.getD (i.val.toNat - 1) false)
      rw [unsafeBitget_eq, bitOf_pack]
    · show kindOf (if inBounds (BV.ofList l) i = true then _ else _) = _
      rw [if_pos hb]
      show Except.ok (⟨unsafeBitset (pack l) x i.val.toNat, l.length⟩ : BV) =
        Except.ok (BV.ofList (l.set (i.val.toNat - 1) x))
      generalize i.val.toNat = q at hq ⊢
      congr 1
      apply eq_ofList_of_bits
      · simp
      · bitsimp
      · intro k; bitsimp; bfin
  · rw [if_neg h]
    have hb : inBounds (BV.ofList l) i = false := by
      simp only [inBounds, ofList_len]; exact decide_eq_false h
    refine ⟨?_, ?_⟩
    · show kindOf (if inBounds (BV.ofList l) i = true then _ else _) = _
      rw [hb]; rfl
    · show kindOf (if inBounds (BV.ofList l) i = true then _ else _) = _
      rw [hb]; rfl

/-! ## Dequeue operations -/

theorem push_ofList (l : List Bool) (x : Bool) (dirty : U64) :
    push (BV.ofList l) x dirty = BV.ofList (l ++ [x]) := by
  have hL := growBC_length l dirty
  cases x
  · show (⟨growBC l dirty, l.length + 1⟩ : BV) = _
    apply eq_ofList_of_bits
    · simp
    · simp only [hL, List.length_append, List.length_cons, List.length_nil, numBitChunks_eq]
    · intro k; simp only [bitOf_growBC]; bitsimp; bfin
  · show (⟨unsafeBitset (growBC l dirty) true (l.length + 1), l.length + 1⟩ : BV) = _
    apply eq_ofList_of_bits
    · simp
    · simp only [length_unsafeBitset, hL, List.length_append, List.length_cons, List.length_nil,
        numBitChunks_eq]
    · intro k; simp only [bitOf_unsafeBitset, bitOf_growBC, hL]; bitsimp; bfin

theorem pushfirst_ofList (l : List Bool) (x : Bool) (dirty : U64) :
    pushfirst (BV.ofList l) x dirty = BV.ofList (x :: l) := by
  cases l with
  | nil =>
    show (⟨cset (growBC [] dirty) 1 (ofBool x), 1⟩ : BV) = _
    have hL := growBC_length [] dirty
    apply eq_ofList_of_bits
    · rfl
    · rw [length_cset, hL, numBitChunks_eq]; simp
    · intro k
      rw [getD_cons]
      simp only [bitOf_cset, bitOf_growBC, hL, getLsbD_ofBool, List.getD_nil, List.length_nil]
      bfin
  | cons a t =>
    show (⟨cset (shiftUpLoop (growBC (a :: t) dirty).length ((growBC (a :: t) dirty).length - 1)
          (growBC (a :: t) dirty)) 1
        (ofBool x ||| (cget (shiftUpLoop (growBC (a :: t) dirty).length
          ((growBC (a :: t) dirty).length - 1) (growBC (a :: t) dirty)) 1 <<< 1)),
        (a :: t).length + 1⟩ : BV) = _
    have hpos : 0 < (a :: t).length := by simp
    generalize a :: t = l at hpos ⊢
    have hL := growBC_length l dirty
    have hS := bitOf_shiftUpLoop ((growBC l dirty).length - 1) (growBC l dirty).length
      (growBC l dirty) (by rw [hL]; omega)
    rw [hL] at hS
    apply eq_ofList_of_bits
    · simp
    · simp only [length_cset, length_shiftUpLoop, hL, List.length_cons]
      rw [numBitChunks_eq]
    · intro k
      rw [getD_cons]
      bitsimp
      simp only [hL, hS, bitOf_growBC]
      bfin

theorem pop_ofList (l : List Bool) (h : l ≠ []) :
    pop (BV.ofList l) = .ok (⟨if l.length % 64 = 1 then deleteend (unsafeBitset (pack l) false l.length) 1
        else unsafeBitset (pack l) false l.length, l.length - 1⟩, unsafeBitget (pack l) l.length) := by
  have hn : ¬ (BV.ofList l).len = 0 := by
    rw [ofList_len]; exact fun h0 => h (List.eq_nil_of_length_eq_zero h0)
  unfold pop
  rw [if_neg hn]
  rfl

theorem popfirst_ofList (l : List Bool) (h : l ≠ []) :
    popfirst (BV.ofList l) = .ok (⟨if l.length % 64 = 1
        then deleteend (shiftDownLoop 1 ((pack l).length - 1) (pack l)) 1
        else csetEnd (shiftDownLoop 1 ((pack l).length - 1) (pack l))
          (cgetEnd (shiftDownLoop 1 ((pack l).length - 1) (pack l)) >>> 1), l.length - 1⟩,
      unsafeBitget (pack l) 1) := by
  have hn : ¬ (BV.ofList l).len = 0 := by
    rw [ofList_len]; exact fun h0 => h (List.eq_nil_of_length_eq_zero h0)
  unfold popfirst
  rw [if_neg hn]
  rfl

theorem dequeAgrees : DequeAgrees := by
  intro l x dirty _
  refine ⟨push_ofList l x dirty, pushfirst_ofList l x dirty, ?_, ?_⟩
  · by_cases h : l = []
    · subst h; first | rfl | decide | simp [pop, kindOf, excType, BV.ofList]
    · have hpos : 0 < l.length := List.length_pos_iff.mpr h
      rw [if_neg h, pop_ofList l h]
      simp only [kindOf, Except.ok.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · apply eq_ofList_of_bits
        · simp [List.length_dropLast]
        · bitsimp; split <;> omega
        · intro k; bitsimp; bfin
      · rw [unsafeBitget_eq, bitOf_pack, getLastD_eq]
  · by_cases h : l = []
    · subst h; first | rfl | decide | simp [popfirst, kindOf, excType, BV.ofList]
    · have hpos : 0 < l.length := List.length_pos_iff.mpr h
      rw [if_neg h, popfirst_ofList l h]
      simp only [kindOf, Except.ok.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · apply eq_ofList_of_bits
        · simp
        · bitsimp; split <;> omega
        · intro k; bitsimp; bfin
      · rw [unsafeBitget_eq, bitOf_pack, headD_eq]

/-! ## `insert!` and `deleteat!` -/

/-- `chunks` after the carry loop of `insert!(B, q, x)`. -/
def insS (l : List Bool) (q : Nat) (dirty : U64) : List U64 :=
  shiftUpLoop (growBC l dirty).length ((growBC l dirty).length - ((q - 1) / 64 + 1)) (growBC l dirty)

/-- `chunks` after `insert!` has opened the gap in the chunk of element `q`. -/
def insBC (l : List Bool) (q : Nat) (dirty : U64) : List U64 :=
  cset (insS l q dirty) ((q - 1) / 64 + 1)
    ((~~~(msk64 <<< ((q - 1) % 64)) &&& cget (insS l q dirty) ((q - 1) / 64 + 1)) |||
      ((msk64 <<< ((q - 1) % 64) &&& cget (insS l q dirty) ((q - 1) / 64 + 1)) <<< 1))

theorem length_insS (l : List Bool) (q : Nat) (dirty : U64) :
    (insS l q dirty).length = (l.length + 1 + 63) / 64 := by
  unfold insS; rw [length_shiftUpLoop, growBC_length]

theorem bitOf_insS (l : List Bool) (q : Nat) (dirty : U64) (k : Nat) :
    bitOf (insS l q dirty) k =
      if 64 * ((q - 1) / 64 + 1) ≤ k ∧ k < 64 * ((l.length + 1 + 63) / 64) then l.getD (k - 1) false
      else l.getD k false := by
  have hL := growBC_length l dirty
  unfold insS
  rw [bitOf_shiftUpLoop _ _ _ (by rw [hL]; omega), bitOf_growBC, bitOf_growBC, hL]
  bfin

theorem insert_ofList (l : List Bool) (i : JInt64) (x : Bool) (dirty : U64)
    (h : 1 ≤ i.val ∧ i.val ≤ l.length + 1) :
    insert (BV.ofList l) i x dirty = .ok ⟨unsafeBitset (insBC l i.val.toNat dirty) x i.val.toNat, l.length + 1⟩ := by
  show (if ¬ (1 ≤ i.val ∧ i.val ≤ (l.length : Int) + 1) then Except.error JlError.boundsError else
    Except.ok (⟨unsafeBitset (insBC l i.val.toNat dirty) x i.val.toNat, l.length + 1⟩ : BV)) = _
  rw [if_neg (not_not_intro h)]

/-- The chunk expression of `deleteat!(B, q)` up to its carry loop. -/
def delS12 (cs : List U64) (q : Nat) : List U64 :=
  if (cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))).length > (q - 1) / 64 + 1
  then cset (cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))) ((q - 1) / 64 + 1)
    (cget (cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))) ((q - 1) / 64 + 1) |||
      (cget (cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))) ((q - 1) / 64 + 1 + 1) <<< 63))
  else cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))

theorem bitOf_delS1 (cs : List U64) (q p : Nat) :
    bitOf (cset cs ((q - 1) / 64 + 1) (((msk64 >>> (63 - (q - 1) % 64)) >>> 1 &&& cget cs ((q - 1) / 64 + 1)) |||
        ((~~~(msk64 >>> (63 - (q - 1) % 64)) &&& cget cs ((q - 1) / 64 + 1)) >>> 1))) p =
      if p / 64 = (q - 1) / 64 ∧ p / 64 < cs.length then
        (if p < q - 1 then bitOf cs p else if p % 64 < 63 then bitOf cs (p + 1) else false)
      else bitOf cs p := by
  rw [bitOf_cset, Nat.add_sub_cancel, getLsbD_delChunk _ _ _ (Nat.mod_lt _ (by omega)),
    getLsbD_cget, getLsbD_cget]
  bfin

theorem length_delS12 (cs : List U64) (q : Nat) : (delS12 cs q).length = cs.length := by
  unfold delS12; simp only [length_ite, length_cset, ite_self]

theorem bitOf_delS12 (cs : List U64) (q p : Nat) :
    bitOf (delS12 cs q) p =
      if p / 64 = (q - 1) / 64 ∧ q - 1 ≤ p then bitOf cs (p + 1) else bitOf cs p := by
  unfold delS12
  rw [bitOf_ite, length_cset]
  by_cases hL : cs.length > (q - 1) / 64 + 1
  · rw [if_pos hL, bitOf_cset, length_cset, Nat.add_sub_cancel]
    simp only [BitVec.getLsbD_or, getLsbD_cget, getLsbD_shl, bitOf_delS1]
    bfin
  · rw [if_neg hL, bitOf_delS1]
    bfin

theorem deleteat_ofList (l : List Bool) (i : JInt64) (h : 1 ≤ i.val ∧ i.val ≤ l.length) :
    deleteat (BV.ofList l) i = .ok ⟨
      if l.length % 64 = 1 then
        deleteend (shiftDownLoop ((i.val.toNat - 1) / 64 + 1 + 1)
          ((delS12 (pack l) i.val.toNat).length - 1 - ((i.val.toNat - 1) / 64 + 1)) (delS12 (pack l) i.val.toNat)) 1
      else if (shiftDownLoop ((i.val.toNat - 1) / 64 + 1 + 1)
          ((delS12 (pack l) i.val.toNat).length - 1 - ((i.val.toNat - 1) / 64 + 1))
          (delS12 (pack l) i.val.toNat)).length > (i.val.toNat - 1) / 64 + 1 then
        csetEnd (shiftDownLoop ((i.val.toNat - 1) / 64 + 1 + 1)
          ((delS12 (pack l) i.val.toNat).length - 1 - ((i.val.toNat - 1) / 64 + 1)) (delS12 (pack l) i.val.toNat))
          (cgetEnd (shiftDownLoop ((i.val.toNat - 1) / 64 + 1 + 1)
            ((delS12 (pack l) i.val.toNat).length - 1 - ((i.val.toNat - 1) / 64 + 1))
            (delS12 (pack l) i.val.toNat)) >>> 1)
      else shiftDownLoop ((i.val.toNat - 1) / 64 + 1 + 1)
          ((delS12 (pack l) i.val.toNat).length - 1 - ((i.val.toNat - 1) / 64 + 1)) (delS12 (pack l) i.val.toNat),
      l.length - 1⟩ := by
  show (if 1 ≤ i.val ∧ i.val ≤ (l.length : Int) then Except.ok (deleteatUnsafe (BV.ofList l) i.val.toNat)
    else Except.error JlError.boundsError) = _
  rw [if_pos h]
  rfl

theorem insertDeleteAgrees : InsertDeleteAgrees := by
  intro l i x dirty _
  refine ⟨?_, ?_⟩
  · by_cases h : 1 ≤ i.val ∧ i.val ≤ l.length + 1
    · rw [if_pos h, insert_ofList l i x dirty h]
      have hq : ((i.val.toNat : Nat) : Int) = i.val := Int.toNat_of_nonneg (by omega)
      generalize i.val.toNat = q at hq ⊢
      show Except.ok _ = Except.ok _
      congr 1
      apply eq_ofList_of_bits
      · rw [List.length_insertIdx, if_pos (show q - 1 ≤ l.length by omega)]
      · rw [length_unsafeBitset, insBC, length_cset, length_insS, List.length_insertIdx,
          if_pos (show q - 1 ≤ l.length by omega), numBitChunks_eq]
      · intro k
        rw [bitOf_unsafeBitset, insBC, bitOf_cset, length_cset, getLsbD_insChunk, getD_insertIdx]
        simp only [getLsbD_cget, bitOf_insS, length_insS]
        bfin
    · rw [if_neg h]
      show kindOf (if ¬ (1 ≤ i.val ∧ i.val ≤ (l.length : Int) + 1) then Except.error JlError.boundsError
        else _) = _
      rw [if_pos h]; rfl
  · unfold idx
    by_cases h : 1 ≤ i.val ∧ i.val ≤ l.length
    · rw [if_pos h, deleteat_ofList l i h]
      have hq : ((i.val.toNat : Nat) : Int) = i.val := Int.toNat_of_nonneg (by omega)
      generalize i.val.toNat = q at hq ⊢
      show Except.ok _ = Except.ok _
      congr 1
      apply eq_ofList_of_bits
      · rw [List.length_eraseIdx, if_pos (show q - 1 < l.length by omega)]
      · bitsimp
        simp only [length_delS12, pack_length, numBitChunks_eq, List.length_eraseIdx]
        (repeat' split) <;> omega
      · intro k
        bitsimp
        simp only [length_delS12, bitOf_delS12, pack_length, numBitChunks_eq, bitOf_pack,
          List.length_eraseIdx]
        bfin
    · rw [if_neg h]
      show kindOf (if 1 ≤ i.val ∧ i.val ≤ (l.length : Int) then _ else Except.error JlError.boundsError) = _
      rw [if_neg h]; rfl

/-! ## `fill!` -/

theorem fillAgrees : FillAgrees := by
  intro l y _
  by_cases hn : l.length = 0
  · have : l = [] := List.eq_nil_of_length_eq_zero hn
    subst this; cases y <;> rfl
  · unfold fill
    rw [if_neg (show ¬ (BV.ofList l).len = 0 from hn)]
    cases y
    · show (⟨(pack l).map (fun _ => 0), l.length⟩ : BV) = _
      apply eq_ofList_of_bits
      · simp
      · simp [pack_length]
      · intro k; bitsimp; bfin
    · show (⟨csetEnd ((pack l).map (fun _ => msk64))
          (cgetEnd ((pack l).map (fun _ => msk64)) &&& mskEnd l.length), l.length⟩ : BV) = _
      apply eq_ofList_of_bits
      · simp
      · simp [length_csetEnd, pack_length]
      · intro k; bitsimp; bfin

/-! ## `count`, `any`, `all` -/

theorem foldl_count (cs : List U64) : ∀ (init : JInt .i64), 0 ≤ init.val →
    init.val + ((cs.map countOnes).sum : Int) < 9223372036854775808 →
    (cs.foldl (fun n c => JInt.wrap .i64 (n.val + countOnes c)) init).val =
      init.val + (cs.map countOnes).sum := by
  induction cs with
  | nil => intro init _ _; simp
  | cons c cs ih =>
    intro init h0 h1
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at h1 ⊢
    have hw : (JInt.wrap .i64 (init.val + countOnes c)).val = init.val + countOnes c := by
      show wrapInt .i64 _ = _
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega
    rw [ih _ (by rw [hw]; omega) (by rw [hw]; omega), hw]
    omega

theorem countOnes_chunkAt (l : List Bool) (c : Nat) :
    countOnes (chunkAt l c) = ((List.range 64).filter (fun j => l.getD (64 * c + j) false)).length := by
  unfold countOnes
  congr 1
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [getLsbD_chunkAt, if_pos hj]

theorem filter_range_add (p : Nat → Bool) (a b : Nat) :
    ((List.range (a + b)).filter p).length =
      ((List.range a).filter p).length + ((List.range b).filter (fun j => p (a + j))).length := by
  rw [List.range_add, List.filter_append, List.length_append, List.filter_map, List.length_map]
  rfl

theorem sum_countOnes (l : List Bool) : ∀ m, ((List.range m).map (fun c => countOnes (chunkAt l c))).sum =
    ((List.range (64 * m)).filter (fun k => l.getD k false)).length
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_countOnes l m, Nat.mul_succ,
      filter_range_add]
    simp [countOnes_chunkAt]

theorem filter_range_length : ∀ (l : List Bool) (N : Nat), l.length ≤ N →
    ((List.range N).filter (fun k => l.getD k false)).length = (l.filter id).length
  | [], N, _ => by simp
  | _ :: _, 0, h => by simp at h
  | a :: t, N + 1, h => by
    have ih := filter_range_length t N (by simp at h; omega)
    simp only [List.getD_eq_getElem?_getD] at ih
    cases a <;> simp [List.range_succ_eq_map, List.filter_map, Function.comp_def, ih]

theorem sum_countOnes_pack (l : List Bool) : ((pack l).map countOnes).sum = (l.filter id).length := by
  simp only [pack, List.map_map, Function.comp_def]
  rw [sum_countOnes, filter_range_length l _ (by rw [numBitChunks_eq]; omega)]

theorem lit0_val : (JInt.lit .i64 0).val = 0 := by decide

theorem countAnyAllAgrees : CountAnyAllAgrees := by
  intro l hl
  have hl' : l.length < 4611686018427387904 := by simpa using hl
  refine ⟨?_, ?_, ?_⟩
  · show (bitcount (pack l) (JInt.lit .i64 0)).val = _
    have hle : (l.filter id).length ≤ l.length := List.length_filter_le _ _
    unfold bitcount
    rw [foldl_count _ _ (by rw [lit0_val]; omega) (by rw [lit0_val, sum_countOnes_pack]; omega),
      lit0_val, sum_countOnes_pack]
    simp
  · show (if l.length = 0 then false else (pack l).any (· != 0)) = l.any id
    by_cases hn : l.length = 0
    · rw [if_pos hn, List.eq_nil_of_length_eq_zero hn]; rfl
    · rw [if_neg hn]
      apply Bool.eq_iff_iff.mpr
      rw [any_chunks_iff, any_bools_iff]
      simp only [bitOf_pack]
  · show (if l.length = 0 then true else
      ((List.range ((pack l).length - 1)).all (fun j => cget (pack l) (j + 1) == msk64) &&
        cgetEnd (pack l) == mskEnd l.length)) = l.all id
    by_cases hn : l.length = 0
    · rw [if_pos hn, List.eq_nil_of_length_eq_zero hn]; rfl
    · rw [if_neg hn]
      apply Bool.eq_iff_iff.mpr
      rw [all_bools_iff]
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
        cgetEnd_eq, cget_eq_iff, bitOf_pack, getLsbD_msk64, getLsbD_mskEnd_ite, pack_length,
        numBitChunks_eq]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        by_cases hc : k / 64 < (l.length + 63) / 64 - 1
        · have hm : k % 64 < 64 := Nat.mod_lt _ (by omega)
          have := h1 (k / 64) hc (k % 64) hm
          rw [if_pos hm] at this
          rw [← this]; congr 1; omega
        · have hm : k % 64 < 64 := Nat.mod_lt _ (by omega)
          have := h2 (k % 64) hm
          rw [if_pos (show k % 64 < 64 ∧ (l.length % 64 = 0 ∨ k % 64 < l.length % 64) by omega)] at this
          rw [← this]; congr 1; omega
      · intro h
        refine ⟨fun c hc j hj => ?_, fun j hj => ?_⟩
        · rw [if_pos hj]; exact h _ (by omega)
        · by_cases hlt : 64 * ((l.length + 63) / 64 - 1) + j < l.length
          · rw [h _ hlt, if_pos (show j < 64 ∧ (l.length % 64 = 0 ∨ j < l.length % 64) by omega)]
          · rw [getD_ge (show l.length ≤ 64 * ((l.length + 63) / 64 - 1) + j by omega),
              if_neg (show ¬ (j < 64 ∧ (l.length % 64 = 0 ∨ j < l.length % 64)) by omega)]

end JuliaLean.BitArrays
