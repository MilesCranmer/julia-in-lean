import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.count
import JuliaLean.Proofs.base.bitarray.common.shift

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096

/-- Intersecting with two's-complement negation keeps only the first set bit. -/
theorem cmp_lowbit_at {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    (x &&& (-x)).getLsbD i =
      (x.getLsbD i && !(decide (∃ j < i, x.getLsbD j = true))) := by
  rw [BitVec.getLsbD_and, BitVec.getLsbD_neg]
  simp only [hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases decide (∃ j < i, x.getLsbD j = true) <;> rfl

/-- The least-set-bit mask has a single true bit at the first nonzero position. -/
theorem cmp_lowbit_isolated {w : Nat} (x : BitVec w) (k : Nat)
    (hk : x.getLsbD k = true)
    (hlower : ∀ j < k, x.getLsbD j = false)
    (i : Nat) (hi : i < w) :
    (x &&& (-x)).getLsbD i = decide (i = k) := by
  rw [cmp_lowbit_at x i hi]
  by_cases hik : i < k
  · have hne : i ≠ k := by omega
    simp only [hlower i hik, Bool.false_and, hne, decide_false]
  · by_cases heq : i = k
    · subst i
      have hnone : ¬ ∃ j < k, x.getLsbD j = true := by
        rintro ⟨j, hj, hbit⟩
        rw [hlower j hj] at hbit
        cases hbit
      simp only [hk, hnone, decide_false, Bool.not_false, Bool.true_and,
        decide_true]
    · have hex : ∃ j < i, x.getLsbD j = true := ⟨k, by omega, hk⟩
      simp only [hex, decide_true, Bool.not_true, Bool.and_false, heq, decide_false]

/-- The word-level comparison test reads the second word at the first differing bit. -/
theorem cmp_first_difference_test {w : Nat} (a b : BitVec w) (k : Nat)
    (hdiff : a.getLsbD k ≠ b.getLsbD k)
    (hlower : ∀ j < k, a.getLsbD j = b.getLsbD j) :
    ((b &&& (a ^^^ b)) &&& (-(a ^^^ b)) = 0#w) ↔ b.getLsbD k = false := by
  have hk : (a ^^^ b).getLsbD k = true := by
    rw [BitVec.getLsbD_xor]
    cases ha : a.getLsbD k <;> cases hb : b.getLsbD k <;>
      simp only [ha, hb] at hdiff ⊢
    all_goals first | rfl | exact False.elim (hdiff rfl)
  have hl : ∀ j < k, (a ^^^ b).getLsbD j = false := by
    intro j hj
    rw [BitVec.getLsbD_xor, hlower j hj, Bool.xor_self]
  have hkw : k < w := BitVec.lt_of_getLsbD hk
  rw [BitVec.and_assoc]
  constructor
  · intro hzero
    have hb := congrArg (fun value : BitVec w => value.getLsbD k) hzero
    rw [BitVec.getLsbD_and, cmp_lowbit_isolated (a ^^^ b) k hk hl k hkw] at hb
    simpa only [decide_true, Bool.and_true, BitVec.getLsbD_zero] using hb
  · intro hb
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    rw [BitVec.getLsbD_and, cmp_lowbit_isolated (a ^^^ b) k hk hl i hi,
      BitVec.getLsbD_zero]
    by_cases heq : i = k
    · subst i
      simp only [hb, Bool.false_and]
    · simp only [heq, decide_false, Bool.and_false]

/-- Per-chunk decision used by the installed BitVector comparison loop. -/
def cmpWordDecision (left right : U64) : Option I64 :=
  let d := xor_int left right
  if d != u64 0 then
    some (if and_int (and_int right d) (and_int d (-d)) == u64 0
      then int 1 else int (-1))
  else none

/-- Read-only chunk comparison returns the first differing word's decision. -/
theorem cmp_readonly_loop {I : Type} (readLeft readRight : I → BitMutationM U64)
    (left right : I → U64) (s : State) :
    ∀ indices : List I,
    (∀ i ∈ indices, (readLeft i).run s = (.ok (left i), s)) →
    (∀ i ∈ indices, (readRight i).run s = (.ok (right i), s)) →
    (forIn indices (none, ()) (fun i (_ : Option I64 × Unit) => do
      let d := xor_int (← readLeft i) (← readRight i)
      if d != u64 0 then
        let low := and_int d (-d)
        if and_int (and_int (← readRight i) d) low == u64 0 then
          pure (ForInStep.done (some (int 1), ()))
        else pure (ForInStep.done (some (int (-1)), ()))
      else pure (ForInStep.yield (none, ())))).run s =
        (.ok (indices.findSome? (fun i => cmpWordDecision (left i) (right i)), ()), s) := by
  intro indices
  induction indices with
  | nil =>
    intro _ _
    rfl
  | cons i indices ih =>
    intro hl hr
    have htail := ih (fun j hj => hl j (List.mem_cons_of_mem i hj))
      (fun j hj => hr j (List.mem_cons_of_mem i hj))
    simp only [List.forIn_cons, shape_run_bind, hl i List.mem_cons_self,
      hr i List.mem_cons_self, shape_run_pure, List.findSome?_cons, cmpWordDecision]
    by_cases hdiff : (xor_int (left i) (right i) != u64 0) = true
    · simp only [hdiff, ite_true, shape_run_bind, hr i List.mem_cons_self]
      by_cases hbit : (and_int (and_int (right i) (xor_int (left i) (right i)))
          (and_int (xor_int (left i) (right i)) (-(xor_int (left i) (right i)))) == u64 0) = true
      · simp only [hbit, ite_true, shape_run_pure]
      · simp only [hbit, Bool.false_eq_true, ite_false, shape_run_pure]
    · simp only [hdiff, ite_false, shape_run_pure]
      exact htail
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096

open JuliaLean.Proofs.base.int

/-- The imported integer encoding and decoding preserve every finite bit pattern. -/
theorem cmp_roundtrip {t : IntTy} (word : BitVec t.bits) : fromJInt (toJInt t word) = word := by
  apply BitVec.eq_of_toNat_eq
  rw [← pattern_fromJInt, pattern_toJInt]

/-- Comparing encoded unsigned bit patterns is equivalent to comparing model words. -/
theorem cmp_from_eq_iff (a b : U64) : fromJInt a = fromJInt b ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (toJInt .u64) h
    simpa only [toJInt_fromJInt] using hh
  · intro h
    rw [h]

/-- The core wrapping negation has exactly the two's-complement negative bit pattern. -/
theorem cmp_neg_bits (word : U64) : fromJInt (-word) = -(fromJInt word) := by
  change BitVec.ofInt IntTy.u64.bits (wrapInt .u64 (-word.val)) =
    -(BitVec.ofInt IntTy.u64.bits word.val)
  rw [← BitVec.ofInt_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  change (((-word.val) % 18446744073709551616) % 18446744073709551616).toNat =
    ((-word.val) % 18446744073709551616).toNat
  rw [Int.emod_emod]

/-- XOR is zero exactly when both stored words agree. -/
theorem cmp_xor_zero_iff (a b : U64) : xor_int a b = u64 0 ↔ a = b := by
  rw [← cmp_from_eq_iff]
  simp only [xor_int, jlXorInt, cmp_roundtrip]
  change ((fromJInt a) ^^^ (fromJInt b) = 0#IntTy.u64.bits) ↔ a = b
  rw [BitVec.xor_eq_zero_iff, cmp_from_eq_iff]

/-- Repeating the difference mask does not change the least-difference sign test. -/
theorem cmp_and_duplicate {w : Nat} (b d : BitVec w) :
    (b &&& d) &&& (d &&& (-d)) = (b &&& d) &&& (-d) := by
  rw [← BitVec.and_assoc, BitVec.and_assoc b d d, BitVec.and_self]

/-- Identical words produce no comparison decision. -/
theorem cmp_word_same (word : U64) : cmpWordDecision word word = none := by
  have hx := (cmp_xor_zero_iff word word).mpr rfl
  simp only [cmpWordDecision, hx, show (u64 0 != u64 0) = false from rfl,
    Bool.false_eq_true, ite_false]

/-- The first differing bit determines the exact word comparison result. -/
theorem cmp_word_first (a b : U64) (k : Nat)
    (hdiff : (fromJInt a).getLsbD k ≠ (fromJInt b).getLsbD k)
    (hlower : ∀ j < k, (fromJInt a).getLsbD j = (fromJInt b).getLsbD j) :
    cmpWordDecision a b = some (if (fromJInt b).getLsbD k then int (-1) else int 1) := by
  have hne : a ≠ b := by intro h; subst a; exact hdiff rfl
  have hx : xor_int a b ≠ u64 0 := fun h => hne ((cmp_xor_zero_iff a b).mp h)
  have htest : and_int (and_int b (xor_int a b))
      (and_int (xor_int a b) (-(xor_int a b))) = u64 0 ↔
        (fromJInt b).getLsbD k = false := by
    rw [← cmp_from_eq_iff]
    simp only [and_int, xor_int, jlAndInt, jlXorInt, cmp_roundtrip, cmp_neg_bits]
    change ((fromJInt b &&& (fromJInt a ^^^ fromJInt b)) &&&
      ((fromJInt a ^^^ fromJInt b) &&& (-(fromJInt a ^^^ fromJInt b))) = 0#IntTy.u64.bits) ↔ _
    rw [cmp_and_duplicate]
    exact cmp_first_difference_test (fromJInt a) (fromJInt b) k hdiff hlower
  unfold cmpWordDecision
  rw [if_pos (bne_iff_ne.mpr hx)]
  cases hb : (fromJInt b).getLsbD k
  · have hz := htest.mpr hb
    rw [if_pos (beq_iff_eq.mpr hz)]
    rfl
  · have hz : and_int (and_int b (xor_int a b))
        (and_int (xor_int a b) (-(xor_int a b))) ≠ u64 0 := by
      intro h
      have := htest.mp h
      rw [hb] at this
      cases this
    rw [if_neg (fun h => hz (beq_iff_eq.mp h))]
    rfl

/-- A single differing Boolean pair yields its lexicographic sign. -/
def cmpBitDecision (a b : Bool) : Option I64 :=
  if a != b then some (if b then int (-1) else int 1) else none

/-- Returning a mapped first match is the same as scanning optional decisions. -/
theorem cmp_findSome_find {α β : Type} (items : List α) (p : α → Bool) (f : α → β) :
    items.findSome? (fun x => if p x then some (f x) else none) = (items.find? p).map f := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.findSome?_cons, List.find?_cons]
    cases hp : p item <;> simp only [hp, Bool.false_eq_true, ite_false, ite_true, Option.map_none,
      Option.map_some, ih]

/-- Word comparison scans its 64 bits in the same order as logical vector comparison. -/
theorem cmp_word_decision_bits (a b : U64) :
    cmpWordDecision a b = (List.range 64).findSome? (fun bit =>
      cmpBitDecision ((fromJInt a).getLsbD bit) ((fromJInt b).getLsbD bit)) := by
  unfold cmpBitDecision
  rw [cmp_findSome_find]
  cases hf : (List.range 64).find? (fun bit => (fromJInt a).getLsbD bit != (fromJInt b).getLsbD bit) with
  | none =>
    have he : a = b := by
      apply (cmp_from_eq_iff a b).mp
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro bit hbit
      have hh := List.find?_eq_none.mp hf bit (List.mem_range.mpr hbit)
      by_cases he : (fromJInt a).getLsbD bit = (fromJInt b).getLsbD bit
      · exact he
      · exact False.elim (hh (bne_iff_ne.mpr he))
    rw [he, cmp_word_same]
    rfl
  | some bit =>
    have hh := List.find?_range_eq_some.mp hf
    have hd := bne_iff_ne.mp hh.1
    have hl : ∀ j < bit, (fromJInt a).getLsbD j = (fromJInt b).getLsbD j := by
      intro j hj
      have hn := hh.2.2 j hj
      by_cases he : (fromJInt a).getLsbD j = (fromJInt b).getLsbD j
      · exact he
      · rw [bne_iff_ne.mpr he] at hn
        cases hn
    rw [cmp_word_first a b bit hd hl]
    rfl

/-- Pure sign of a comparison between two logical lengths. -/
def cmpLengths (left right : Nat) : I64 :=
  if left < right then int (-1) else if right < left then int 1 else int 0

/-- Pure scan of logical bits, padding beyond each list with false. -/
def cmpBitScan (left right : List Bool) (count : Nat) : Option I64 :=
  (List.range count).findSome? (fun i => cmpBitDecision (left.getD i false) (right.getD i false))

/-- A scan against an empty left side only ever decides that the right side is greater. -/
theorem cmp_scan_empty_left (right : List Bool) (count : Nat) :
    (cmpBitScan [] right count).getD (int (-1)) = int (-1) := by
  cases hs : cmpBitScan [] right count with
  | none => rfl
  | some value =>
    obtain ⟨i, hi, hv⟩ := List.exists_of_findSome?_eq_some hs
    change cmpBitDecision false (right.getD i false) = some value at hv
    cases hb : right.getD i false <;> simp only [cmpBitDecision, hb] at hv
    · cases hv
    · cases hv
      rfl

/-- A scan against an empty right side only ever decides that the left side is greater. -/
theorem cmp_scan_empty_right (left : List Bool) (count : Nat) :
    (cmpBitScan left [] count).getD (int 1) = int 1 := by
  cases hs : cmpBitScan left [] count with
  | none => rfl
  | some value =>
    obtain ⟨i, hi, hv⟩ := List.exists_of_findSome?_eq_some hs
    change cmpBitDecision (left.getD i false) false = some value at hv
    cases hb : left.getD i false <;> simp only [cmpBitDecision, hb] at hv
    · cases hv
    · cases hv
      rfl

/-- A bit scan consumes the first Boolean pair before considering the tails. -/
theorem cmp_scan_cons (a b : Bool) (left right : List Bool) (count : Nat) :
    cmpBitScan (a :: left) (b :: right) (count + 1) =
      match cmpBitDecision a b with
      | some value => some value
      | none => cmpBitScan left right count := by
  simp only [cmpBitScan, List.range_succ_eq_map, List.findSome?_cons, List.findSome?_map,
    Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
  cases a <;> cases b <;> rfl

/-- At any scan length covering the common logical prefix, padding plus length comparison is exact. -/
theorem cmp_scan_correct (left right : List Bool) (count : Nat)
    (hcount : min left.length right.length ≤ count) :
    (cmpBitScan left right count).getD (cmpLengths left.length right.length) =
      Round5.Round2.compareBoolLists left right := by
  induction left generalizing right count with
  | nil =>
    cases right with
    | nil =>
      have hz : (List.range count).findSome? (fun _ : Nat => (none : Option I64)) = none :=
        List.findSome?_eq_none_iff.mpr (fun _ _ => rfl)
      simpa only [cmpBitScan, cmpBitDecision, cmpLengths, Round5.Round2.compareBoolLists,
        List.getD_nil, show (false != false) = false from rfl, Bool.false_eq_true,
        ite_false, hz, Option.getD_none, List.length_nil, Nat.lt_irrefl]
    | cons b right =>
      change (cmpBitScan [] (b :: right) count).getD (int (-1)) = int (-1)
      exact cmp_scan_empty_left _ _
  | cons a left ih =>
    cases right with
    | nil =>
      change (cmpBitScan (a :: left) [] count).getD (int 1) = int 1
      exact cmp_scan_empty_right _ _
    | cons b right =>
      cases count with
      | zero => simp only [List.length_cons] at hcount; omega
      | succ count =>
        have ht : min left.length right.length ≤ count := by
          simp only [List.length_cons] at hcount
          omega
        have hl : cmpLengths (a :: left).length (b :: right).length = cmpLengths left.length right.length := by
          simp only [cmpLengths, List.length_cons, Nat.add_lt_add_iff_right]
        rw [cmp_scan_cons, hl]
        cases a <;> cases b <;>
          simp only [cmpBitDecision, Round5.Round2.compareBoolLists]
        · exact ih right count ht
        · rfl
        · rfl
        · exact ih right count ht

/-- A first-decision scan respects pointwise agreement on its visited indices. -/
theorem cmp_findSome_congr {α β : Type} (items : List α) (f g : α → Option β)
    (h : ∀ x ∈ items, f x = g x) : items.findSome? f = items.findSome? g := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h item List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem item hx))]

/-- Nested first-decision scans agree with a scan of the flattened indices. -/
theorem cmp_findSome_flatMap {α β γ : Type} (items : List α) (f : α → List β) (p : β → Option γ) :
    (items.flatMap f).findSome? p = items.findSome? (fun x => (f x).findSome? p) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.flatMap_cons, List.findSome?_append, List.findSome?_cons, ih]
    cases (f item).findSome? p <;> rfl

/-- Consecutive packed-word decisions scan logical bits in their original order. -/
theorem cmp_chunks_bits (left right : List Bool) (chunks : Nat) :
    (List.range chunks).findSome? (fun c => cmpWordDecision (packedPrefix left c 64) (packedPrefix right c 64)) =
      cmpBitScan left right (chunks * 64) := by
  have hflat := packedGrouping_flatMapRange 64 chunks (fun i : Nat => i)
  simp only [List.map_id'] at hflat
  unfold cmpBitScan
  rw [← hflat, cmp_findSome_flatMap]
  apply cmp_findSome_congr
  intro chunk hchunk
  rw [cmp_word_decision_bits, List.findSome?_map]
  apply cmp_findSome_congr
  intro bit hbit
  have hb := List.mem_range.mp hbit
  simp only [Function.comp_def, packedBit_fromJInt, packedWord_bit left chunk bit hb,
    packedWord_bit right chunk bit hb]

/-- The installed comparison routine is read-only and returns its first word decision or length result. -/
theorem cmp_run_readonly {A : Type} (trailing top : U64 → I64) (cmpLength : I64 → I64 → I64)
    (a b : BitVector) (s : State) (al bl : I64) (left right : I64 → U64)
    (ha : (mutableLength a.chunks).run s = (.ok al, s))
    (hb : (mutableLength b.chunks).run s = (.ok bl, s))
    (hl : ∀ i ∈ intRange (int 1) (if al < bl then al else bl),
      (mutableGet a.chunks i).run s = (.ok (left i), s))
    (hr : ∀ i ∈ intRange (int 1) (if al < bl then al else bl),
      (mutableGet b.chunks i).run s = (.ok (right i), s)) :
    (bitVectorCmp (A := A) trailing top cmpLength a b).run s =
      (.ok (((intRange (int 1) (if al < bl then al else bl)).findSome?
        (fun i => cmpWordDecision (left i) (right i))).getD (cmpLength a.len b.len)), s) := by
  unfold bitVectorCmp
  simp only [shape_run_bind, ha, hb]
  rw [cmp_readonly_loop (mutableGet a.chunks) (mutableGet b.chunks) left right s _ hl hr]
  cases (intRange (int 1) (if al < bl then al else bl)).findSome?
    (fun i => cmpWordDecision (left i) (right i)) <;> rfl

/-- The common chunk count is the natural minimum when both lengths fit in Int64. -/
theorem cmp_min_length (left right : Nat) (hl : left ≤ 9223372036854775807)
    (hr : right ≤ 9223372036854775807) :
    (if int left < int right then int left else int right) = int ((min left right : Nat) : Int) := by
  have hc : (int left < int right) ↔ left < right := by
    change ((int left).val < (int right).val) ↔ _
    rw [packedInt_val left hl, packedInt_val right hr]
    omega
  by_cases h : left < right
  · rw [if_pos (hc.mpr h), Nat.min_eq_left (by omega)]
  · rw [if_neg (fun hh => h (hc.mp hh)), Nat.min_eq_right (by omega)]

/-- The public integer comparison callback computes the natural length sign. -/
theorem cmp_public_lengths (left right : Nat) (hl : left ≤ 9223372036854775807)
    (hr : right ≤ 9223372036854775807) :
    int (JuliaLean.base.operators.cmpInteger
      (fun a b => JuliaLean.base.int.lt a b) (fun a b => JuliaLean.base.int.lt a b)
      (int left) (int right)) = cmpLengths left right := by
  have hleft : JuliaLean.base.int.lt (int left) (int right) = decide (left < right) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, packedInt_val left hl, packedInt_val right hr]
    simp only [Int.ofNat_lt]
  have hright : JuliaLean.base.int.lt (int right) (int left) = decide (right < left) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, packedInt_val left hl, packedInt_val right hr]
    simp only [Int.ofNat_lt]
  dsimp only [JuliaLean.base.operators.cmpInteger]
  rw [hleft, hright]
  by_cases hlt : left < right
  · simp only [hlt, decide_true, cmpLengths, ite_true]
    rfl
  · by_cases hgt : right < left
    · simp only [hlt, hgt, decide_true, decide_false, cmpLengths, ite_false, ite_true]
      rfl
    · simp only [hlt, hgt, decide_false, cmpLengths, ite_false]
      rfl

/-- Packed storage contains exactly the ceiling of the logical length divided by 64. -/
theorem cmp_encode_length (xs : List Bool) : (encodeBits xs).length = (xs.length + 63) / 64 := by
  simp only [encodeBits, List.length_map, List.length_range, wordCount]

/-- Every valid encoded chunk is the corresponding installed prefix packer. -/
theorem cmp_encode_get (xs : List Bool) (j : Nat) (hj : j < (encodeBits xs).length) :
    (encodeBits xs)[j] = packedPrefix xs j 64 := by
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]

/-- Running the installed comparator on encoded inputs is exactly the padded logical-bit scan. -/
theorem cmp_encoded_run (xs ys : List Bool)
    (hxs : xs.length ≤ 9223372036854775807) (hys : ys.length ≤ 9223372036854775807)
    (trailing top : U64 → I64) (cmpLength : I64 → I64 → I64) :
    let a : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitVector := ⟨1, int ys.length, [int ys.length]⟩
    let s := cmpInitialState (encodeBits xs) (encodeBits ys)
    (bitVectorCmp (A := Unit) trailing top cmpLength a b).run s =
      (.ok ((cmpBitScan xs ys ((min (encodeBits xs).length (encodeBits ys).length) * 64)).getD
        (cmpLength (int xs.length) (int ys.length))), s) := by
  dsimp only
  let left := encodeBits xs
  let right := encodeBits ys
  let n : Nat := min left.length right.length
  let s := cmpInitialState left right
  let L : I64 → U64 := fun i => packedPrefix xs (i.val.toNat - 1) 64
  let R : I64 → U64 := fun i => packedPrefix ys (i.val.toNat - 1) 64
  have hlbound : left.length ≤ 9223372036854775807 := by dsimp only [left]; rw [cmp_encode_length]; omega
  have hrbound : right.length ≤ 9223372036854775807 := by dsimp only [right]; rw [cmp_encode_length]; omega
  have hnbound : n ≤ 9223372036854775807 := by dsimp only [n]; omega
  have hindices : intRange (int 1) (if int left.length < int right.length then int left.length else int right.length) =
      (List.range n).map (fun j => int ((j + 1 : Nat) : Int)) := by
    rw [cmp_min_length _ _ hlbound hrbound, packedObserve_intRange _ hnbound]
  have hl : ∀ i ∈ intRange (int 1) (if int left.length < int right.length then int left.length else int right.length),
      (mutableGet 0 i).run s = (.ok (L i), s) := by
    intro i hi
    rw [hindices] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hjn := List.mem_range.mp hj
    have hjleft : j < left.length := by dsimp only [n] at hjn; omega
    have hidx : (int ((j + 1 : Nat) : Int)).val.toNat - 1 = j := by
      rw [packedInt_val (j + 1) (by omega), Int.toNat_natCast]
      omega
    have hread := cmp_initial_read_left left right hlbound j hjleft
    have hword : left[j] = packedPrefix xs j 64 := cmp_encode_get xs j hjleft
    rw [hword] at hread
    dsimp only [L]
    rw [hidx]
    exact hread
  have hr : ∀ i ∈ intRange (int 1) (if int left.length < int right.length then int left.length else int right.length),
      (mutableGet 1 i).run s = (.ok (R i), s) := by
    intro i hi
    rw [hindices] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hjn := List.mem_range.mp hj
    have hjright : j < right.length := by dsimp only [n] at hjn; omega
    have hidx : (int ((j + 1 : Nat) : Int)).val.toNat - 1 = j := by
      rw [packedInt_val (j + 1) (by omega), Int.toNat_natCast]
      omega
    have hread := cmp_initial_read_right left right hrbound j hjright
    have hword : right[j] = packedPrefix ys j 64 := cmp_encode_get ys j hjright
    rw [hword] at hread
    dsimp only [R]
    rw [hidx]
    exact hread
  have hrun := cmp_run_readonly (A := Unit) trailing top cmpLength
    (⟨0, int xs.length, [int xs.length]⟩ : BitVector)
    (⟨1, int ys.length, [int ys.length]⟩ : BitVector) s
    (int left.length) (int right.length) L R
    (cmp_initial_lengths left right).1 (cmp_initial_lengths left right).2 hl hr
  rw [hindices, List.findSome?_map] at hrun
  simp only [Function.comp_def] at hrun
  have hscan : (List.range n).findSome? (fun j => cmpWordDecision (L (int ((j + 1 : Nat) : Int)))
      (R (int ((j + 1 : Nat) : Int)))) =
      (List.range n).findSome? (fun j => cmpWordDecision (packedPrefix xs j 64) (packedPrefix ys j 64)) := by
    apply cmp_findSome_congr
    intro j hj
    have hjn := List.mem_range.mp hj
    have hidx : (int ((j + 1 : Nat) : Int)).val.toNat - 1 = j := by
      rw [packedInt_val (j + 1) (by omega), Int.toNat_natCast]
      omega
    simp only [L, R, hidx]
  rw [hscan, cmp_chunks_bits] at hrun
  exact hrun

/-- Frozen target: packed BitVector comparison is exactly lexicographic Boolean-list comparison. -/
theorem BitarrayBitVectorComparisonAgrees_proven : JuliaLean.Proofs.base.bitarray.Round5.BitVectorComparisonAgrees := by
  intro xs ys hx hy
  have hxs : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hx
    omega
  have hys : ys.length ≤ 9223372036854775807 := by
    change ys.length < 4611686018427387903 at hy
    omega
  change ((bitVectorCmp (A := Unit) JuliaLean.base.int.trailing_zeros JuliaLean.base.int.top_set_bit
    (fun m n => int (JuliaLean.base.operators.cmpInteger
      (fun a b => JuliaLean.base.int.lt a b) (fun a b => JuliaLean.base.int.lt a b) m n))
    (⟨0, int xs.length, [int xs.length]⟩ : BitVector)
    (⟨1, int ys.length, [int ys.length]⟩ : BitVector)).run
    (cmpInitialState (encodeBits xs) (encodeBits ys))).1 = .ok (Round5.Round2.compareBoolLists xs ys)
  rw [cmp_encoded_run xs ys hxs hys]
  change Except.ok ((cmpBitScan xs ys (min (encodeBits xs).length (encodeBits ys).length * 64)).getD
    (int (JuliaLean.base.operators.cmpInteger
      (fun a b => JuliaLean.base.int.lt a b) (fun a b => JuliaLean.base.int.lt a b)
      (int xs.length) (int ys.length)))) = .ok (Round5.Round2.compareBoolLists xs ys)
  rw [cmp_public_lengths xs.length ys.length hxs hys]
  have hcover : min xs.length ys.length ≤ min (encodeBits xs).length (encodeBits ys).length * 64 := by
    rw [cmp_encode_length, cmp_encode_length]
    have hleft := packedGrouping_paddingBound xs.length
    have hright := packedGrouping_paddingBound ys.length
    omega
  rw [cmp_scan_correct xs ys _ hcover]
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Two prefixes of the same Boolean stream compare exactly by their lengths. -/
theorem spc_compare_prefixes (f : Nat → Bool) (n m : Nat) :
    compareBooleanSequences ((List.range n).map f) ((List.range m).map f) =
      if n < m then -1 else if m < n then 1 else 0 := by
  induction n generalizing f m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [List.range_zero, List.map_nil, List.range_succ_eq_map, List.map_cons,
        compareBooleanSequences, Nat.zero_lt_succ, ite_true]
  | succ n ih =>
    cases m with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.range_succ_eq_map, List.map_cons,
        compareBooleanSequences, Nat.not_lt_zero, Nat.zero_lt_succ, ite_false, ite_true]
    | succ m =>
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        Nat.add_lt_add_iff_right]
      cases hf : f 0 <;>
        simp only [compareBooleanSequences, ih]

/-- Native length comparison agrees with the nonnegative natural lengths in the contract. -/
theorem spc_compare_nonnegative_lengths (m n : I64) (hm : 0 ≤ m.val) (hn : 0 ≤ n.val) :
    compareNativeLengths m n =
      int (if m.val.toNat < n.val.toNat then -1 else if n.val.toNat < m.val.toNat then 1 else 0) := by
  have hmn : (m.val < n.val) ↔ m.val.toNat < n.val.toNat := by omega
  have hnm : (n.val < m.val) ↔ n.val.toNat < m.val.toNat := by omega
  simp only [compareNativeLengths, JuliaLean.base.operators.cmpInteger,
    JuliaLean.base.operators.islessReal, JuliaLean.base.int.lt_BitSigned,
    JuliaLean.Proofs.base.int.slt_int_eq (t := .i64) rfl,
    JuliaLean.base.operators.ifelseValue_eq, hmn, hnm, decide_eq_true_eq]

/-- The earlier packed-list specification agrees with the independently
    recursive logical comparator in the frozen alias-aware target. -/
theorem spc_compare_specs (xs ys : List Bool) :
    Round5.Round2.compareBoolLists xs ys = int (compareBooleanSequences xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      cases a <;> cases b <;>
        simp only [Round5.Round2.compareBoolLists, compareBooleanSequences, ih]

/-- Native nonnegative lengths supply the pure scan's default comparison. -/
theorem spc_native_cmpLengths (m n : I64) (hm : 0 ≤ m.val) (hn : 0 ≤ n.val) :
    compareNativeLengths m n = cmpLengths m.val.toNat n.val.toNat := by
  rw [spc_compare_nonnegative_lengths m n hm hn]
  unfold cmpLengths
  by_cases hmn : m.val.toNat < n.val.toNat
  · simp only [hmn, ite_true]
  · by_cases hnm : n.val.toNat < m.val.toNat
    · simp only [hmn, hnm, ite_false, ite_true]
    · simp only [hmn, hnm, ite_false]
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesCmp1 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-vector-comparison-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["cmp@1211"],
    statement := "For vectors below the native-size bound, BitVector comparison follows the first differing bit, then compares vector lengths.", source := "base/bitarray.jl:1211-1218",
    status := .proven, prop := ``Round5.BitVectorComparisonAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group2.BitarrayBitVectorComparisonAgrees_proven }
]
def entriesCmp2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-comparison-alias-full", juliaFile := "base/bitarray.jl",
    juliaFns := ["cmp(::BitVector, ::BitVector)"],
    statement := "BitVector comparison is lexicographic on logical Boolean values and preserves both inputs and all aliases, including readable states reached through alias growth.",
    source := "base/bitarray.jl:1211-1218", status := .todo,
    prop := ``Archive20261102Round6.BitVectorComparisonFull, thm := none, notes := "No complete exact proof returned. proved validity of a one-bit alias-growth state and computed model cmp=1 versus logical cmp=0, but the public Julia 1.13.2 probe printed NOT_REPRODUCED bitarray-comparison-alias-full because the release uses logical AbstractVector comparison, so the witness does not satisfy the required two-version reproduction rule." }
]
end JuliaLean.Proofs.base.bitarray

