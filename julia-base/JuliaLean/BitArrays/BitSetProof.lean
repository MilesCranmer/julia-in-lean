import JuliaLean.BitArrays.Properties

/-!
# Proof of `BitSetPushDeleteAgrees`

`G bits off c j` is bit `j` of the chunk holding the elements `64c:64c+63` when
`bits` starts at chunk offset `off`; `contains` reads exactly that bit. `setint`
keeps the invariant `offset = NO_OFFSET → bits = []` and changes `G` only at the
written element.
-/

namespace JuliaLean.BitArrays

namespace BitSetProof

/-- Bit `j` of chunk `c` (floor index) of a `BitSet` with chunks `bits` at chunk offset `off`. -/
def G (bits : List U64) (off c : Int) (j : Nat) : Bool :=
  if 0 ≤ c - off then (bits.getD (c - off).toNat 0).getLsbD j else false

/-- The invariant kept by `_setint!`. -/
def Inv (s : BitSetS) : Prop := s.offset = noOffset → s.bits = []

theorem noOffset_eq : noOffset = -1152921504606846976 := by decide

theorem jint64_bounds (n : JInt64) : -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 := by
  have h := n.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem getD_ge (l : List U64) (i : Nat) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_replicate_zero : ∀ (k i : Nat), (List.replicate k (0 : U64)).getD i 0 = 0
  | 0, _ => by simp
  | _ + 1, 0 => by simp
  | k + 1, i + 1 => by rw [List.replicate_succ, List.getD_cons_succ, getD_replicate_zero k i]

theorem getD_append_zeros (k : Nat) : ∀ (bits : List U64) (i : Nat),
    (bits ++ List.replicate k 0).getD i 0 = bits.getD i 0
  | [], i => by rw [List.nil_append, getD_replicate_zero]; simp
  | _ :: _, 0 => by simp
  | _ :: xs, i + 1 => by
    rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ, getD_append_zeros k xs i]

theorem getD_zeros_append (bits : List U64) : ∀ (k i : Nat),
    (List.replicate k 0 ++ bits).getD i 0 = if i < k then 0 else bits.getD (i - k) 0
  | 0, i => by simp
  | k + 1, 0 => by rw [List.replicate_succ, List.cons_append, List.getD_cons_zero, if_pos (by omega)]
  | k + 1, i + 1 => by
    rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, getD_zeros_append bits k i]
    by_cases h : i < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega), Nat.add_sub_add_right]

theorem getD_set (v : U64) : ∀ (l : List U64) (d i : Nat), d < l.length →
    (l.set d v).getD i 0 = if i = d then v else l.getD i 0
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, 0, _ => by simp
  | _ :: _, 0, _ + 1, _ => by simp
  | _ :: _, _ + 1, 0, _ => by simp
  | _ :: xs, d + 1, i + 1, h => by
    rw [List.set_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
      getD_set v xs d i (by simp at h; omega)]
    by_cases hid : i = d
    · simp [hid]
    · rw [if_neg hid, if_neg (by omega)]

theorem bit_update (c : U64) (b : Bool) (i2 j : Nat) (hi : i2 < 64) (hj : j < 64) :
    (if b then c ||| (1 : U64) <<< i2 else c &&& ~~~((1 : U64) <<< i2)).getLsbD j =
      if j = i2 then b else c.getLsbD j := by
  have hu : ((1 : U64) <<< i2).getLsbD j = decide (j = i2) := by
    rw [BitVec.getLsbD_shiftLeft]
    by_cases h : j = i2
    · subst h; simp [hj]
    · by_cases h' : j < i2
      · simp [h, h']
      · have : j - i2 ≠ 0 := by omega
        simp [h, h', this]
  cases b
  · show (c &&& ~~~((1 : U64) <<< i2)).getLsbD j = if j = i2 then false else c.getLsbD j
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, hu]
    by_cases h : j = i2 <;> simp [h, hj]
  · show (c ||| (1 : U64) <<< i2).getLsbD j = if j = i2 then true else c.getLsbD j
    rw [BitVec.getLsbD_or, hu]
    by_cases h : j = i2 <;> simp [h]

theorem contains_eq (s : BitSetS) (m : JInt64) :
    s.contains m = G s.bits s.offset (m.val / 64) (m.val % 64).toNat := by
  simp only [BitSetS.contains, cget, G]
  by_cases h : 1 ≤ m.val / 64 - s.offset + 1 ∧ m.val / 64 - s.offset + 1 ≤ s.bits.length
  · rw [if_pos h, if_pos (by omega),
      show (m.val / 64 - s.offset + 1).toNat - 1 = (m.val / 64 - s.offset).toNat by omega]
  · rw [if_neg h]
    by_cases hc : 0 ≤ m.val / 64 - s.offset
    · rw [if_pos hc, getD_ge _ _ (by omega)]
      simp
    · rw [if_neg hc]

theorem G_nil (off c : Int) (j : Nat) : G [] off c j = false := by
  unfold G
  split
  · simp
  · rfl

theorem G_out (bits : List U64) (off c : Int) (j : Nat) (h : c - off < 0 ∨ bits.length ≤ c - off) :
    G bits off c j = false := by
  unfold G
  split
  · rw [getD_ge _ _ (by omega)]
    simp
  · rfl

theorem G_growend0 (bits : List U64) (k : Nat) (off c : Int) (j : Nat) :
    G (BitSetS.growend0 bits k) off c j = G bits off c j := by
  unfold G BitSetS.growend0
  rw [getD_append_zeros]

theorem G_growbeg0 (bits : List U64) (k : Nat) (off' off c : Int) (j : Nat) (h : off' = off - k) :
    G (BitSetS.growbeg0 bits k) off' c j = G bits off c j := by
  unfold G BitSetS.growbeg0
  subst h
  by_cases hc : 0 ≤ c - off
  · rw [if_pos (by omega), if_pos hc, getD_zeros_append, if_neg (by omega),
      show (c - (off - k)).toNat - k = (c - off).toNat by omega]
  · rw [if_neg hc]
    split
    · rw [getD_zeros_append, if_pos (by omega)]
      simp
    · rfl

theorem G_set (bits : List U64) (off c : Int) (j : Nat) (b : Bool) (d i1 i2 : Nat)
    (hd : d < bits.length) (hi1 : i1 = d + 1) (hi2 : i2 < 64) (hj : j < 64) :
    G (unsafeBitsetAt bits b i1 i2) off c j =
      if c = off + d ∧ j = i2 then b else G bits off c j := by
  subst hi1
  simp only [unsafeBitsetAt, cset, cget, G, Nat.add_sub_cancel]
  by_cases hc : 0 ≤ c - off
  · rw [if_pos hc, if_pos hc, getD_set _ _ _ _ hd]
    by_cases hcd : c = off + d
    · rw [if_pos (show (c - off).toNat = d by omega), bit_update _ _ _ _ hi2 hj,
        show (c - off).toNat = d by omega]
      by_cases hji : j = i2
      · simp [hji, hcd]
      · simp [hji]
    · rw [if_neg (show (c - off).toNat ≠ d by omega), if_neg (fun h => hcd h.1)]
  · rw [if_neg hc, if_neg hc, if_neg (fun h => by omega)]

theorem ite_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (x y : Bool) :
    (if p then x else y) = (if q then x else y) := by
  by_cases hq : q
  · rw [if_pos (h.mpr hq), if_pos hq]
  · rw [if_neg (fun hp => hq (h.mp hp)), if_neg hq]

theorem eq_iff (m n : JInt64) :
    m = n ↔ (m.val / 64 = n.val / 64 ∧ (m.val % 64).toNat = (n.val % 64).toNat) := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    omega

/-- `_setint!` keeps the invariant and changes membership only at the written element. -/
theorem setint_spec (bits : List U64) (off : Int) (hs : Inv ⟨bits, off⟩) (n : JInt64) (b : Bool) :
    Inv (BitSetS.setint ⟨bits, off⟩ n b) ∧ ∀ m : JInt64,
      (BitSetS.setint ⟨bits, off⟩ n b).contains m =
        if m = n then b else (BitSetS.mk bits off).contains m := by
  have hn := jint64_bounds n
  have hjn : (n.val % 64).toNat < 64 := by omega
  have hoff := noOffset_eq
  refine ⟨?_, fun m => ?_⟩
  · by_cases h1 : n.val / 64 - off ≥ (bits.length : Int)
    · cases b
      · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by simp [BitSetS.setint, h1]
        rw [hr]
        exact hs
      · by_cases h2 : off = noOffset
        · have hb : bits = [] := hs h2
          subst hb
          have hr : BitSetS.setint ⟨[], off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growend0 [] 1) true 1 (n.val % 64).toNat, n.val / 64⟩ := by
            subst h2
            have hle : noOffset ≤ n.val / 64 := by rw [noOffset_eq]; omega
            simp [BitSetS.setint, hle]
          rw [hr]
          intro h
          simp only at h
          omega
        · have hr : BitSetS.setint ⟨bits, off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growend0 bits (n.val / 64 - off - bits.length + 1).toNat) true
                (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
            simp [BitSetS.setint, h1, h2]
          rw [hr]
          intro h
          exact absurd h h2
    · by_cases h3 : n.val / 64 - off < 0
      · cases b
        · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by
            simp [BitSetS.setint, h1, h3]
          rw [hr]
          exact hs
        · have hr : BitSetS.setint ⟨bits, off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growbeg0 bits (-(n.val / 64 - off)).toNat) true 1
                (n.val % 64).toNat, off + (n.val / 64 - off)⟩ := by
            simp [BitSetS.setint, h1, h3]
          rw [hr]
          intro h
          simp only at h
          omega
      · have hr : BitSetS.setint ⟨bits, off⟩ n b =
            ⟨unsafeBitsetAt bits b (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
          simp [BitSetS.setint, h1, h3]
        rw [hr]
        intro h
        have hb : bits = [] := hs h
        subst hb
        simp at h1
        omega
  · have hm := jint64_bounds m
    have hjm : (m.val % 64).toNat < 64 := by omega
    rw [contains_eq, contains_eq, ite_iff (eq_iff m n)]
    dsimp only
    have hiff : ∀ (c : Int), c = n.val / 64 →
        (m.val / 64 = c ∧ (m.val % 64).toNat = (n.val % 64).toNat ↔
          m.val / 64 = n.val / 64 ∧ (m.val % 64).toNat = (n.val % 64).toNat) := by
      intro c hc
      subst hc
      exact Iff.rfl
    by_cases h1 : n.val / 64 - off ≥ (bits.length : Int)
    · cases b
      · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by simp [BitSetS.setint, h1]
        rw [hr]
        dsimp only
        by_cases hc : m.val / 64 = n.val / 64 ∧ (m.val % 64).toNat = (n.val % 64).toNat
        · rw [if_pos hc, G_out _ _ _ _ (by omega)]
        · rw [if_neg hc]
      · by_cases h2 : off = noOffset
        · have hb : bits = [] := hs h2
          subst hb
          have hr : BitSetS.setint ⟨[], off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growend0 [] 1) true 1 (n.val % 64).toNat, n.val / 64⟩ := by
            subst h2
            have hle : noOffset ≤ n.val / 64 := by rw [noOffset_eq]; omega
            simp [BitSetS.setint, hle]
          rw [hr]
          simp only
          rw [G_set _ _ _ _ _ 0 _ _ (by simp [BitSetS.growend0]) rfl hjn hjm, G_growend0, G_nil,
            G_nil]
          exact ite_iff (hiff _ (by omega)) _ _
        · have hr : BitSetS.setint ⟨bits, off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growend0 bits (n.val / 64 - off - bits.length + 1).toNat) true
                (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
            simp [BitSetS.setint, h1, h2]
          rw [hr]
          simp only
          rw [G_set _ _ _ _ _ (n.val / 64 - off).toNat _ _
              (by simp [BitSetS.growend0]; omega) (by omega) hjn hjm, G_growend0]
          exact ite_iff (hiff _ (by omega)) _ _
    · by_cases h3 : n.val / 64 - off < 0
      · cases b
        · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by
            simp [BitSetS.setint, h1, h3]
          rw [hr]
          dsimp only
          by_cases hc : m.val / 64 = n.val / 64 ∧ (m.val % 64).toNat = (n.val % 64).toNat
          · rw [if_pos hc, G_out _ _ _ _ (by omega)]
          · rw [if_neg hc]
        · have hr : BitSetS.setint ⟨bits, off⟩ n true =
              ⟨unsafeBitsetAt (BitSetS.growbeg0 bits (-(n.val / 64 - off)).toNat) true 1
                (n.val % 64).toNat, off + (n.val / 64 - off)⟩ := by
            simp [BitSetS.setint, h1, h3]
          rw [hr]
          simp only
          rw [G_set _ _ _ _ _ 0 _ _ (by simp [BitSetS.growbeg0]; omega) rfl hjn hjm,
            G_growbeg0 bits (-(n.val / 64 - off)).toNat _ off _ _ (by omega)]
          exact ite_iff (hiff _ (by omega)) _ _
      · have hr : BitSetS.setint ⟨bits, off⟩ n b =
            ⟨unsafeBitsetAt bits b (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
          simp [BitSetS.setint, h1, h3]
        rw [hr]
        simp only
        rw [G_set _ _ _ _ _ (n.val / 64 - off).toNat _ _ (by omega) (by omega) hjn hjm]
        exact ite_iff (hiff _ (by omega)) _ _

theorem step_eq (s : BitSetS) (o : Bool × JInt64) :
    (if o.1 then s.push o.2 else s.delete o.2) = s.setint o.2 o.1 := by
  cases h : o.1 <;> rfl

theorem fold_agrees (ops : List (Bool × JInt64)) : ∀ (s : BitSetS) (S : JInt64 → Bool),
    Inv s → (∀ m, s.contains m = S m) → ∀ n,
    (ops.foldl (fun s (o : Bool × JInt64) => if o.1 then s.push o.2 else s.delete o.2) s).contains n =
      (ops.foldl (fun (S : JInt64 → Bool) (o : Bool × JInt64) =>
        fun y => if y = o.2 then o.1 else S y) S) n := by
  induction ops with
  | nil => intro s S _ h n; exact h n
  | cons o ops ih =>
    intro s S hs h n
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨bits, off⟩ := s
    have hspec := setint_spec bits off hs o.2 o.1
    apply ih
    · rw [step_eq]
      exact hspec.1
    · intro m
      rw [step_eq, hspec.2 m, h m]

end BitSetProof

open BitSetProof in
theorem bitSetPushDeleteAgrees : BitSetPushDeleteAgrees := by
  intro ops n
  apply fold_agrees ops BitSetS.empty (fun _ => false)
  · intro _
    rfl
  · intro m
    rw [contains_eq]
    exact G_nil _ _ _

end JuliaLean.BitArrays
