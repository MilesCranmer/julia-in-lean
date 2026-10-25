import JuliaLean.BitArrays.Properties

/-!
# Bit-level specification of `copy_chunks!`

`copyChunks dest pd src ps n` (`base/bitarray.jl:135-187`) sets the bits
`pd-1, …, pd+n-2` (0-based) of `dest` to the bits `ps-1, …, ps+n-2` of the source
as it was before the call, and keeps every other bit and the chunk count
(`copyChunks_spec`). This holds on the three code paths of the model:

* a source distinct from the destination (`copyChunksLtoR` with `.other`);
* the destination itself with `pd ≤ ps` (`copyChunksLtoR` with `.self`): iteration
  `i` of `copyLoop` reads source chunks `ks0+i` and `ks0+i+1` and writes chunk
  `kd0+i ≤ ks0+i`, so it only reads chunks it has not written yet;
* the destination itself with `pd > ps` (`copy_chunks_rtol!`, `rtolLoop`): each
  block of at most 64 bits is read in full before it is written, and the blocks go
  from the high end down, so the source bits of a block lie below every bit
  written before it.

The helper definitions `ltorFirst`, `ltorChunkS1`, `ltorLast`, `ltorCore`,
`rtolWrite` and `rtolBlock` name sub-terms of the model definitions; the
equations `copyChunksLtoR_eq` and `rtolLoop_succ` hold by `rfl`.
-/

namespace JuliaLean.BitArrays

namespace CopySpec

/-- Splits the two `if`s of an equation between conditionals with linear-arithmetic
conditions and closes the four cases. -/
macro "bitcopy_ifs" : tactic =>
  `(tactic| (split <;> split <;> first | rfl | (exfalso; omega) | (congr 1; omega)))

/-! ## Bits of chunks -/

theorem getLsbD_msk64 (i : Nat) : msk64.getLsbD i = decide (i < 64) := by
  unfold msk64
  exact BitVec.getLsbD_allOnes

theorem getLsbD_ge64 (x : U64) (i : Nat) (h : 64 ≤ i) : x.getLsbD i = false :=
  BitVec.getLsbD_of_ge x i h

theorem shl_bit_lt (x : U64) (k b : Nat) (h : b < k) : (x <<< k).getLsbD b = false := by
  rw [BitVec.getLsbD_shiftLeft, decide_eq_true h]
  simp

theorem shl_bit_ge (x : U64) (k b : Nat) (hb : b < 64) (h : k ≤ b) :
    (x <<< k).getLsbD b = x.getLsbD (b - k) := by
  rw [BitVec.getLsbD_shiftLeft, decide_eq_true hb, decide_eq_false (Nat.not_lt.mpr h)]
  rfl

theorem shl_bit (x : U64) (k b : Nat) :
    (x <<< k).getLsbD b = if b < 64 ∧ k ≤ b then x.getLsbD (b - k) else false := by
  by_cases h1 : b < 64
  · by_cases h2 : k ≤ b
    · rw [if_pos ⟨h1, h2⟩, shl_bit_ge x k b h1 h2]
    · rw [if_neg (fun h => h2 h.2), shl_bit_lt x k b (by omega)]
  · rw [if_neg (fun h => h1 h.1), getLsbD_ge64 _ _ (by omega)]

theorem not_bit (x : U64) (b : Nat) : (~~~x).getLsbD b = if b < 64 then !x.getLsbD b else false := by
  rw [BitVec.getLsbD_not]
  by_cases h : b < 64
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem msk_bit (b : Nat) : msk64.getLsbD b = if b < 64 then true else false := by
  rw [getLsbD_msk64]
  by_cases h : b < 64
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

theorem length_cset (cs : List U64) (k : Nat) (v : U64) : (cset cs k v).length = cs.length := by
  simp [cset]

theorem getLsbD_cget (cs : List U64) (k i : Nat) :
    (cget cs k).getLsbD i = (decide (i < 64) && bitOf cs (64 * (k - 1) + i)) := by
  by_cases hi : i < 64
  · have h1 : (64 * (k - 1) + i) / 64 = k - 1 := by omega
    have h2 : (64 * (k - 1) + i) % 64 = i := by omega
    unfold bitOf cget
    rw [h1, h2]
    simp [hi]
  · rw [getLsbD_ge64 _ _ (by omega)]
    simp [hi]

theorem bitOf_cset_ne (cs : List U64) (k : Nat) (v : U64) (p : Nat) (h : p / 64 ≠ k - 1) :
    bitOf (cset cs k v) p = bitOf cs p := by
  unfold bitOf cset
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set, if_neg (Ne.symm h)]

theorem bitOf_cset_eq (cs : List U64) (k : Nat) (v : U64) (p : Nat) (h : p / 64 = k - 1)
    (hl : k - 1 < cs.length) : bitOf (cset cs k v) p = v.getLsbD (p % 64) := by
  unfold bitOf cset
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos h.symm, if_pos hl] <;> rfl

/-- A masked chunk write `cs[k] = (cs[k] & m) | (X & ~m)`. -/
theorem bitOf_cset_masked (cs : List U64) (k : Nat) (m X : U64) (p : Nat) (h : p / 64 = k - 1)
    (hl : k - 1 < cs.length) :
    bitOf (cset cs k ((cget cs k &&& m) ||| (X &&& ~~~m))) p =
      if m.getLsbD (p % 64) then bitOf cs p else X.getLsbD (p % 64) := by
  have hp : p % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [bitOf_cset_eq cs k _ p h hl]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  rw [getLsbD_cget, show 64 * (k - 1) + p % 64 = p by omega]
  cases m.getLsbD (p % 64) <;> simp [hp]

/-- Reading a source that is either a distinct vector or the destination, where the
destination still holds its original bits from position `W` on. -/
theorem read_bitOf (src : Src) (dest0 cur : List U64) (W q : Nat)
    (hcur : ∀ p, W ≤ p → bitOf cur p = bitOf dest0 p) (hq : src = .self → W ≤ q) :
    bitOf (src.read cur) q = bitOf (src.read dest0) q := by
  cases src with
  | other cs => rfl
  | self => exact hcur q (hq rfl)

/-! ## Masks -/

theorem mskD0_bit (a e : Nat) (hae : a ≤ e) : ∀ b, b < 64 →
    ((if e / 64 + 1 - (a / 64 + 1) = 0 then ~~~(msk64 <<< (a % 64)) ||| (msk64 <<< (e % 64 + 1))
      else ~~~(msk64 <<< (a % 64))).getLsbD b = true ↔
      ¬ (a % 64 ≤ b ∧ 64 * (a / 64) + b ≤ e)) := by
  intro b hb
  split <;> simp only [BitVec.getLsbD_or, not_bit, shl_bit, msk_bit] <;> (repeat' split) <;>
    simp <;> omega

theorem mskD1_bit (e : Nat) : ∀ b, b < 64 →
    ((msk64 <<< (e % 64 + 1)).getLsbD b = true ↔ e < 64 * (e / 64) + b) := by
  intro b hb
  simp only [shl_bit, msk_bit]
  (repeat' split) <;> simp <;> omega

theorem mskS0_bit (s f : Nat) (hsf : s ≤ f) : ∀ b, b < 64 →
    ((if f / 64 + 1 - (s / 64 + 1) = 0 then (msk64 <<< (s % 64)) &&& ~~~(msk64 <<< (f % 64 + 1))
      else msk64 <<< (s % 64)).getLsbD b = true ↔
      (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f)) := by
  intro b hb
  split <;> simp only [BitVec.getLsbD_and, not_bit, shl_bit, msk_bit] <;> (repeat' split) <;>
    simp <;> omega

/-! ## `glue_src_bitchunks` -/

/-- Bit `j` of the glued source chunk `k` is source bit `64(k-1) + ls0 + j`, for every
position up to the last copied one `f` (`s` is the first one). -/
theorem glue_bit (src : List U64) (s f k j q : Nat) (mskS0 : U64)
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f)))
    (hk : s / 64 + 1 ≤ k) (hj : j < 64) (hq : q = 64 * (k - 1) + s % 64 + j) (hqf : q ≤ f) :
    (glue src k (f / 64 + 1) mskS0 (s % 64)).getLsbD j = bitOf src q := by
  have hC : ((cget src k &&& mskS0) >>> (s % 64)).getLsbD j =
      (decide (s % 64 + j < 64) && bitOf src q) := by
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, getLsbD_cget]
    by_cases h : s % 64 + j < 64
    · have hm : mskS0.getLsbD (s % 64 + j) = true := (hS0 _ h).mpr ⟨by omega, by omega⟩
      have e : 64 * (k - 1) + (s % 64 + j) = q := by omega
      rw [hm, e]
      simp [h]
    · simp [h]
  have hD : ((cget src (k + 1) &&& ~~~mskS0) <<< (64 - s % 64)).getLsbD j =
      (!decide (s % 64 + j < 64) && bitOf src q) := by
    by_cases h : s % 64 + j < 64
    · rw [shl_bit_lt _ (64 - s % 64) j (by omega)]
      simp [h]
    · rw [shl_bit_ge _ (64 - s % 64) j hj (by omega), BitVec.getLsbD_and, BitVec.getLsbD_not,
        getLsbD_cget]
      have hb : j - (64 - s % 64) < 64 := by omega
      have hm : mskS0.getLsbD (j - (64 - s % 64)) = false := by
        cases hx : mskS0.getLsbD (j - (64 - s % 64)) with
        | false => rfl
        | true => exact absurd ((hS0 _ hb).mp hx).1 (by omega)
      have e : 64 * (k + 1 - 1) + (j - (64 - s % 64)) = q := by omega
      rw [hm, e]
      simp [h, hb]
  simp only [glue]
  split
  · rw [BitVec.getLsbD_or, hC, hD]
    by_cases h : s % 64 + j < 64 <;> simp [h]
  · rename_i hc
    rw [hC]
    have h : s % 64 + j < 64 := by
      rcases Nat.lt_or_ge (s % 64 + j) 64 with h | h
      · exact h
      · exact (hc ⟨by omega, by omega⟩).elim
    simp [h]

/-! ## `copy_chunks!` from left to right -/

/-- The write of the first destination chunk. -/
def ltorFirst (dest : List U64) (kd0 ld0 : Nat) (mskD0 c0 : U64) : List U64 :=
  cset dest kd0 ((cget dest kd0 &&& mskD0) ||| ((c0 <<< ld0) &&& ~~~mskD0))

/-- `chunk_s1` before the last destination chunk. -/
def ltorChunkS1 (src : Src) (dest : List U64) (kd0 kd1 ks0 ls0 ks1 : Nat) (mskS0 : U64) : U64 :=
  if ks1 ≥ ks0 + (kd1 - kd0) then glue (src.read dest) (ks0 + (kd1 - kd0)) ks1 mskS0 ls0 else 0

/-- The write of the last destination chunk. -/
def ltorLast (src : Src) (dest : List U64) (c : U64) (kd0 ld0 kd1 ks0 ls0 ks1 : Nat)
    (mskD1 mskS0 : U64) : List U64 :=
  cset dest kd1 ((cget dest kd1 &&& mskD1) |||
    (((c >>> (64 - ld0)) ||| (ltorChunkS1 src dest kd0 kd1 ks0 ls0 ks1 mskS0 <<< ld0)) &&& ~~~mskD1))

/-- `copyChunksLtoR` with the chunk indices, offsets and masks as parameters. -/
def ltorCore (dest : List U64) (src : Src) (kd0 ld0 kd1 ks0 ls0 ks1 : Nat)
    (mskD0 mskD1 mskS0 : U64) : List U64 :=
  if kd1 - kd0 = 0 then ltorFirst dest kd0 ld0 mskD0 (glue (src.read dest) ks0 ks1 mskS0 ls0) else
  ltorLast src
    (copyLoop src kd0 ld0 ks0 ks1 ls0 mskS0 1 (kd1 - kd0 - 1)
      (ltorFirst dest kd0 ld0 mskD0 (glue (src.read dest) ks0 ks1 mskS0 ls0))
      (glue (src.read dest) ks0 ks1 mskS0 ls0)).1
    (copyLoop src kd0 ld0 ks0 ks1 ls0 mskS0 1 (kd1 - kd0 - 1)
      (ltorFirst dest kd0 ld0 mskD0 (glue (src.read dest) ks0 ks1 mskS0 ls0))
      (glue (src.read dest) ks0 ks1 mskS0 ls0)).2
    kd0 ld0 kd1 ks0 ls0 ks1 mskD1 mskS0

theorem copyChunksLtoR_eq (dest : List U64) (pd : Nat) (src : Src) (ps n : Nat) :
    copyChunksLtoR dest pd src ps n =
      ltorCore dest src ((pd - 1) / 64 + 1) ((pd - 1) % 64) ((pd + n - 1 - 1) / 64 + 1)
        ((ps - 1) / 64 + 1) ((ps - 1) % 64) ((ps + n - 1 - 1) / 64 + 1)
        (if (pd + n - 1 - 1) / 64 + 1 - ((pd - 1) / 64 + 1) = 0 then
          ~~~(msk64 <<< ((pd - 1) % 64)) ||| (msk64 <<< ((pd + n - 1 - 1) % 64 + 1))
         else ~~~(msk64 <<< ((pd - 1) % 64)))
        (msk64 <<< ((pd + n - 1 - 1) % 64 + 1))
        (if (ps + n - 1 - 1) / 64 + 1 - ((ps - 1) / 64 + 1) = 0 then
          (msk64 <<< ((ps - 1) % 64)) &&& ~~~(msk64 <<< ((ps + n - 1 - 1) % 64 + 1))
         else msk64 <<< ((ps - 1) % 64)) := rfl

/-- State before iteration `i` of `copyLoop`, copying destination bits `a..e` from
source bits `s..f`: the destination bits below chunk `kd0 + i` hold the copy, the
others are the original ones, and `c` is the glued source chunk `ks0 + i - 1`. -/
abbrev LoopInv (S : Nat → Bool) (dest0 : List U64) (a e s f i : Nat) (cur : List U64) (c : U64) :
    Prop :=
  cur.length = dest0.length ∧
  (∀ p, bitOf cur p =
    if a ≤ p ∧ p < 64 * (a / 64 + i) ∧ p ≤ e then S (p - a + s) else bitOf dest0 p) ∧
  (∀ j q, j < 64 → q = 64 * (s / 64 + i - 1) + s % 64 + j → q ≤ f → c.getLsbD j = S q)

theorem ltorFirst_inv (src : Src) (dest0 : List U64) (a e s f : Nat) (mskD0 mskS0 : U64)
    (hae : a ≤ e) (hd : e + s = f + a) (hlen : e < 64 * dest0.length)
    (hD0 : ∀ b, b < 64 → (mskD0.getLsbD b = true ↔ ¬ (a % 64 ≤ b ∧ 64 * (a / 64) + b ≤ e)))
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f))) :
    LoopInv (bitOf (src.read dest0)) dest0 a e s f 1
      (ltorFirst dest0 (a / 64 + 1) (a % 64) mskD0
        (glue (src.read dest0) (s / 64 + 1) (f / 64 + 1) mskS0 (s % 64)))
      (glue (src.read dest0) (s / 64 + 1) (f / 64 + 1) mskS0 (s % 64)) := by
  have hc0 : ∀ j q, j < 64 → q = 64 * (s / 64 + 1 - 1) + s % 64 + j → q ≤ f →
      (glue (src.read dest0) (s / 64 + 1) (f / 64 + 1) mskS0 (s % 64)).getLsbD j =
        bitOf (src.read dest0) q :=
    fun j q hj hq hqf => glue_bit (src.read dest0) s f (s / 64 + 1) j q mskS0 hS0 (Nat.le_refl _) hj hq hqf
  refine ⟨length_cset _ _ _, ?_, hc0⟩
  intro p
  unfold ltorFirst
  by_cases hp : p / 64 = a / 64
  · have hp64 : p % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [bitOf_cset_masked dest0 (a / 64 + 1) _ _ p (by omega) (by omega)]
    by_cases hm : mskD0.getLsbD (p % 64) = true
    · have hm' := (hD0 _ hp64).mp hm
      rw [if_pos hm]
      split
      · exfalso; omega
      · rfl
    · have hm' : a % 64 ≤ p % 64 ∧ 64 * (a / 64) + p % 64 ≤ e :=
        Decidable.byContradiction fun h => hm ((hD0 _ hp64).mpr h)
      rw [if_neg hm, shl_bit_ge _ (a % 64) (p % 64) hp64 hm'.1,
        hc0 (p % 64 - a % 64) (p - a + s) (by omega) (by omega) (by omega)]
      split
      · rfl
      · exfalso; omega
  · rw [bitOf_cset_ne dest0 (a / 64 + 1) _ p (by omega)]
    split
    · exfalso; omega
    · rfl

theorem copyLoop_inv (src : Src) (dest0 : List U64) (a e s f : Nat) (mskS0 : U64)
    (hd : e + s = f + a) (hlen : e < 64 * dest0.length)
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f)))
    (hself : src = .self → a ≤ s) (fuel : Nat) :
    ∀ i cur c, 1 ≤ i → i + fuel ≤ e / 64 - a / 64 →
      LoopInv (bitOf (src.read dest0)) dest0 a e s f i cur c →
      LoopInv (bitOf (src.read dest0)) dest0 a e s f (i + fuel)
        (copyLoop src (a / 64 + 1) (a % 64) (s / 64 + 1) (f / 64 + 1) (s % 64) mskS0 i fuel cur c).1
        (copyLoop src (a / 64 + 1) (a % 64) (s / 64 + 1) (f / 64 + 1) (s % 64) mskS0 i fuel cur c).2 := by
  induction fuel with
  | zero => intro i cur c _ _ h; simpa [copyLoop] using h
  | succ fuel ih =>
    intro i cur c hi hf hinv
    obtain ⟨hl, hb, hc⟩ := hinv
    have hW : ∀ p, 64 * (a / 64 + i) ≤ p → bitOf cur p = bitOf dest0 p := by
      intro p hp
      rw [hb p]
      split
      · exfalso; omega
      · rfl
    have hc1 : ∀ j q, j < 64 → q = 64 * (s / 64 + (i + 1) - 1) + s % 64 + j → q ≤ f →
        (glue (src.read cur) (s / 64 + 1 + i) (f / 64 + 1) mskS0 (s % 64)).getLsbD j =
          bitOf (src.read dest0) q := by
      intro j q hj hq hqf
      rw [glue_bit (src.read cur) s f (s / 64 + 1 + i) j q mskS0 hS0 (by omega) hj (by omega) hqf]
      exact read_bitOf src dest0 cur _ q hW (fun h => by have := hself h; omega)
    have hV : ∀ p, p / 64 = a / 64 + i → p ≤ e →
        ((c >>> (64 - a % 64)) |||
          (glue (src.read cur) (s / 64 + 1 + i) (f / 64 + 1) mskS0 (s % 64) <<< (a % 64))).getLsbD (p % 64) =
          bitOf (src.read dest0) (p - a + s) := by
      intro p hp hpe
      have hp64 : p % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
      by_cases hlt : p % 64 < a % 64
      · rw [shl_bit_lt _ _ _ hlt, hc (64 - a % 64 + p % 64) (p - a + s) (by omega) (by omega) (by omega),
          Bool.or_false]
      · rw [getLsbD_ge64 c (64 - a % 64 + p % 64) (by omega), Bool.false_or,
          shl_bit_ge _ (a % 64) (p % 64) hp64 (by omega),
          hc1 (p % 64 - a % 64) (p - a + s) (by omega) (by omega) (by omega)]
    have hbits : ∀ p, bitOf (cset cur (a / 64 + 1 + i) ((c >>> (64 - a % 64)) |||
          (glue (src.read cur) (s / 64 + 1 + i) (f / 64 + 1) mskS0 (s % 64) <<< (a % 64)))) p =
        if a ≤ p ∧ p < 64 * (a / 64 + (i + 1)) ∧ p ≤ e then bitOf (src.read dest0) (p - a + s)
        else bitOf dest0 p := by
      intro p
      by_cases hp : p / 64 = a / 64 + i
      · rw [bitOf_cset_eq cur (a / 64 + 1 + i) _ p (by omega) (by omega), hV p hp (by omega)]
        split
        · rfl
        · exfalso; omega
      · rw [bitOf_cset_ne cur (a / 64 + 1 + i) _ p (by omega), hb p]
        bitcopy_ifs
    have step := ih (i + 1) _ _ (by omega) (by omega) ⟨by rw [length_cset]; exact hl, hbits, hc1⟩
    rw [show i + (fuel + 1) = i + 1 + fuel by omega]
    simp only [copyLoop]
    exact step

theorem ltorLast_spec (src : Src) (dest0 : List U64) (a e s f : Nat) (mskD1 mskS0 : U64)
    (cur : List U64) (c : U64) (i : Nat)
    (hae : a ≤ e) (hd : e + s = f + a) (hlen : e < 64 * dest0.length)
    (hself : src = .self → a ≤ s)
    (hD1 : ∀ b, b < 64 → (mskD1.getLsbD b = true ↔ e < 64 * (e / 64) + b))
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f)))
    (hi : i = e / 64 - a / 64) (hi1 : 1 ≤ i)
    (hinv : LoopInv (bitOf (src.read dest0)) dest0 a e s f i cur c) :
    (ltorLast src cur c (a / 64 + 1) (a % 64) (e / 64 + 1) (s / 64 + 1) (s % 64) (f / 64 + 1)
        mskD1 mskS0).length = dest0.length ∧
    ∀ p, bitOf (ltorLast src cur c (a / 64 + 1) (a % 64) (e / 64 + 1) (s / 64 + 1) (s % 64)
        (f / 64 + 1) mskD1 mskS0) p =
      if a ≤ p ∧ p ≤ e then bitOf (src.read dest0) (p - a + s) else bitOf dest0 p := by
  obtain ⟨hl, hb, hc⟩ := hinv
  have hW : ∀ p, 64 * (a / 64 + i) ≤ p → bitOf cur p = bitOf dest0 p := by
    intro p hp
    rw [hb p]
    split
    · exfalso; omega
    · rfl
  have hS1 : ∀ j q, j < 64 → q = 64 * (s / 64 + i) + s % 64 + j → q ≤ f →
      (ltorChunkS1 src cur (a / 64 + 1) (e / 64 + 1) (s / 64 + 1) (s % 64) (f / 64 + 1) mskS0).getLsbD j =
        bitOf (src.read dest0) q := by
    intro j q hj hq hqf
    unfold ltorChunkS1
    split
    · rw [glue_bit (src.read cur) s f (s / 64 + 1 + (e / 64 + 1 - (a / 64 + 1))) j q mskS0 hS0
        (by omega) hj (by omega) hqf]
      exact read_bitOf src dest0 cur _ q hW (fun h => by have := hself h; omega)
    · exfalso; omega
  unfold ltorLast
  refine ⟨by rw [length_cset]; exact hl, fun p => ?_⟩
  by_cases hp : p / 64 = e / 64
  · have hp64 : p % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [bitOf_cset_masked cur (e / 64 + 1) _ _ p (by omega) (by omega)]
    by_cases hm : mskD1.getLsbD (p % 64) = true
    · have hm' := (hD1 _ hp64).mp hm
      rw [if_pos hm, hb p]
      bitcopy_ifs
    · have hm' : ¬ e < 64 * (e / 64) + p % 64 := fun h => hm ((hD1 _ hp64).mpr h)
      rw [if_neg hm, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
      by_cases hlt : p % 64 < a % 64
      · rw [shl_bit_lt _ _ _ hlt, hc (64 - a % 64 + p % 64) (p - a + s) (by omega) (by omega) (by omega),
          Bool.or_false]
        split
        · rfl
        · exfalso; omega
      · rw [getLsbD_ge64 c (64 - a % 64 + p % 64) (by omega), Bool.false_or,
          shl_bit_ge _ (a % 64) (p % 64) hp64 (by omega),
          hS1 (p % 64 - a % 64) (p - a + s) (by omega) (by omega) (by omega)]
        split
        · rfl
        · exfalso; omega
  · rw [bitOf_cset_ne cur (e / 64 + 1) _ p (by omega), hb p]
    bitcopy_ifs

theorem ltorCore_spec (dest0 : List U64) (src : Src) (a e s f : Nat) (mskD0 mskD1 mskS0 : U64)
    (hae : a ≤ e) (hd : e + s = f + a) (hlen : e < 64 * dest0.length)
    (hself : src = .self → a ≤ s)
    (hD0 : ∀ b, b < 64 → (mskD0.getLsbD b = true ↔ ¬ (a % 64 ≤ b ∧ 64 * (a / 64) + b ≤ e)))
    (hD1 : ∀ b, b < 64 → (mskD1.getLsbD b = true ↔ e < 64 * (e / 64) + b))
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f))) :
    (ltorCore dest0 src (a / 64 + 1) (a % 64) (e / 64 + 1) (s / 64 + 1) (s % 64) (f / 64 + 1)
        mskD0 mskD1 mskS0).length = dest0.length ∧
    ∀ p, bitOf (ltorCore dest0 src (a / 64 + 1) (a % 64) (e / 64 + 1) (s / 64 + 1) (s % 64)
        (f / 64 + 1) mskD0 mskD1 mskS0) p =
      if a ≤ p ∧ p ≤ e then bitOf (src.read dest0) (p - a + s) else bitOf dest0 p := by
  have h1 := ltorFirst_inv src dest0 a e s f mskD0 mskS0 hae hd hlen hD0 hS0
  unfold ltorCore
  by_cases hk : e / 64 + 1 - (a / 64 + 1) = 0
  · rw [if_pos hk]
    obtain ⟨hl, hb, -⟩ := h1
    refine ⟨hl, fun p => ?_⟩
    rw [hb p]
    bitcopy_ifs
  · rw [if_neg hk]
    exact ltorLast_spec src dest0 a e s f mskD1 mskS0 _ _ _ hae hd hlen hself hD1 hS0
      (by omega) (by omega)
      (copyLoop_inv src dest0 a e s f mskS0 hd hlen hS0 hself _ 1 _ _ (Nat.le_refl 1) (by omega) h1)

theorem copyChunksLtoR_spec (dest : List U64) (pd : Nat) (src : Src) (ps n : Nat)
    (hpd : 1 ≤ pd) (hps : 1 ≤ ps) (hn : 1 ≤ n) (hlen : pd + n - 1 ≤ 64 * dest.length)
    (hself : src = .self → pd ≤ ps) :
    (copyChunksLtoR dest pd src ps n).length = dest.length ∧
    ∀ k, bitOf (copyChunksLtoR dest pd src ps n) k =
      if pd - 1 ≤ k ∧ k < pd - 1 + n then bitOf (src.read dest) (k - (pd - 1) + (ps - 1))
      else bitOf dest k := by
  have h := ltorCore_spec dest src (pd - 1) (pd + n - 1 - 1) (ps - 1) (ps + n - 1 - 1) _ _ _
    (by omega) (by omega) (by omega) (fun h => by have := hself h; omega)
    (mskD0_bit (pd - 1) (pd + n - 1 - 1) (by omega)) (mskD1_bit (pd + n - 1 - 1))
    (mskS0_bit (ps - 1) (ps + n - 1 - 1) (by omega))
  rw [copyChunksLtoR_eq]
  refine ⟨h.1, fun k => ?_⟩
  rw [h.2 k]
  bitcopy_ifs

/-! ## `copy_chunks_rtol!` -/

/-- The writes of one block of `copy_chunks_rtol!`, given the source chunk `c`. -/
def rtolWrite (chunks : List U64) (c : U64) (kd0 ld0 kd1 : Nat) (mskD0 mskD1 : U64) : List U64 :=
  if kd1 - kd0 ≠ 0 then
    cset (ltorFirst chunks kd0 ld0 mskD0 c) kd1
      ((cget (ltorFirst chunks kd0 ld0 mskD0 c) kd1 &&& mskD1) ||| ((c >>> (64 - ld0)) &&& ~~~mskD1))
  else ltorFirst chunks kd0 ld0 mskD0 c

/-- One block of `copy_chunks_rtol!`: `s` bits from position `ps` to position `pd`. -/
def rtolBlock (chunks : List U64) (pd ps s : Nat) : List U64 :=
  rtolWrite chunks
    (glue chunks ((ps - 1) / 64 + 1) ((ps + s - 1 - 1) / 64 + 1)
      (if (ps + s - 1 - 1) / 64 + 1 - ((ps - 1) / 64 + 1) = 0 then
        (msk64 <<< ((ps - 1) % 64)) &&& ~~~(msk64 <<< ((ps + s - 1 - 1) % 64 + 1))
       else msk64 <<< ((ps - 1) % 64)) ((ps - 1) % 64) &&& ~~~(msk64 <<< s))
    ((pd - 1) / 64 + 1) ((pd - 1) % 64) ((pd + s - 1 - 1) / 64 + 1)
    (if (pd + s - 1 - 1) / 64 + 1 - ((pd - 1) / 64 + 1) = 0 then
      ~~~(msk64 <<< ((pd - 1) % 64)) ||| (msk64 <<< ((pd + s - 1 - 1) % 64 + 1))
     else ~~~(msk64 <<< ((pd - 1) % 64)))
    (msk64 <<< ((pd + s - 1 - 1) % 64 + 1))

theorem rtolLoop_succ (posD posS fuel left : Nat) (chunks : List U64) :
    rtolLoop posD posS (fuel + 1) left chunks =
      if left = 0 then chunks else
      rtolLoop posD posS fuel (left - min left 64)
        (rtolBlock chunks (posD + (left - min left 64)) (posS + (left - min left 64)) (min left 64)) :=
  rfl

theorem rtolChunk_bit (cur : List U64) (s f m : Nat) (mskS0 : U64) (hf : f + 1 = s + m)
    (hS0 : ∀ b, b < 64 → (mskS0.getLsbD b = true ↔ (s % 64 ≤ b ∧ 64 * (s / 64) + b ≤ f)))
    (hm64 : m ≤ 64) :
    ∀ j, j < m → (glue cur (s / 64 + 1) (f / 64 + 1) mskS0 (s % 64) &&& ~~~(msk64 <<< m)).getLsbD j =
      bitOf cur (s + j) := by
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, shl_bit_lt _ _ _ hj,
    glue_bit cur s f (s / 64 + 1) j (s + j) mskS0 hS0 (Nat.le_refl _) (by omega) (by omega) (by omega)]
  simp [show j < 64 by omega]

theorem rtolWrite_spec (cur : List U64) (c : U64) (a e s m : Nat) (mskD0 mskD1 : U64)
    (hem : e + 1 = a + m) (hm : 1 ≤ m) (hm64 : m ≤ 64) (hlen : e < 64 * cur.length)
    (hD0 : ∀ b, b < 64 → (mskD0.getLsbD b = true ↔ ¬ (a % 64 ≤ b ∧ 64 * (a / 64) + b ≤ e)))
    (hD1 : ∀ b, b < 64 → (mskD1.getLsbD b = true ↔ e < 64 * (e / 64) + b))
    (hc : ∀ j, j < m → c.getLsbD j = bitOf cur (s + j)) :
    (rtolWrite cur c (a / 64 + 1) (a % 64) (e / 64 + 1) mskD0 mskD1).length = cur.length ∧
    ∀ p, bitOf (rtolWrite cur c (a / 64 + 1) (a % 64) (e / 64 + 1) mskD0 mskD1) p =
      if a ≤ p ∧ p ≤ e then bitOf cur (p - a + s) else bitOf cur p := by
  have hd1 : ∀ p, bitOf (ltorFirst cur (a / 64 + 1) (a % 64) mskD0 c) p =
      if a ≤ p ∧ p ≤ e ∧ p / 64 = a / 64 then bitOf cur (p - a + s) else bitOf cur p := by
    intro p
    unfold ltorFirst
    by_cases hp : p / 64 = a / 64
    · have hp64 : p % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [bitOf_cset_masked cur (a / 64 + 1) _ _ p (by omega) (by omega)]
      by_cases hmk : mskD0.getLsbD (p % 64) = true
      · have hm' := (hD0 _ hp64).mp hmk
        rw [if_pos hmk]
        split
        · exfalso; omega
        · rfl
      · have hm' : a % 64 ≤ p % 64 ∧ 64 * (a / 64) + p % 64 ≤ e :=
          Decidable.byContradiction fun h => hmk ((hD0 _ hp64).mpr h)
        rw [if_neg hmk, shl_bit_ge _ (a % 64) (p % 64) hp64 hm'.1, hc (p % 64 - a % 64) (by omega)]
        split
        · congr 1; omega
        · exfalso; omega
    · rw [bitOf_cset_ne cur (a / 64 + 1) _ p (by omega)]
      split
      · exfalso; omega
      · rfl
  have hl1 : (ltorFirst cur (a / 64 + 1) (a % 64) mskD0 c).length = cur.length := length_cset _ _ _
  unfold rtolWrite
  by_cases hk : e / 64 + 1 - (a / 64 + 1) ≠ 0
  · rw [if_pos hk]
    refine ⟨by rw [length_cset, hl1], fun p => ?_⟩
    by_cases hp : p / 64 = e / 64
    · have hp64 : p % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [bitOf_cset_masked (ltorFirst cur (a / 64 + 1) (a % 64) mskD0 c) (e / 64 + 1) _ _ p
        (by omega) (by omega)]
      by_cases hmk : mskD1.getLsbD (p % 64) = true
      · have hm' := (hD1 _ hp64).mp hmk
        rw [if_pos hmk, hd1 p]
        bitcopy_ifs
      · have hm' : ¬ e < 64 * (e / 64) + p % 64 := fun h => hmk ((hD1 _ hp64).mpr h)
        rw [if_neg hmk, BitVec.getLsbD_ushiftRight, hc (64 - a % 64 + p % 64) (by omega)]
        split
        · congr 1; omega
        · exfalso; omega
    · rw [bitOf_cset_ne (ltorFirst cur (a / 64 + 1) (a % 64) mskD0 c) (e / 64 + 1) _ p (by omega), hd1 p]
      bitcopy_ifs
  · rw [if_neg hk]
    refine ⟨hl1, fun p => ?_⟩
    rw [hd1 p]
    bitcopy_ifs

theorem rtolBlock_spec (cur : List U64) (pd ps m : Nat) (hpd : 1 ≤ pd) (hps : 1 ≤ ps) (hm : 1 ≤ m)
    (hm64 : m ≤ 64) (hlen : pd + m - 1 ≤ 64 * cur.length) :
    (rtolBlock cur pd ps m).length = cur.length ∧
    ∀ p, bitOf (rtolBlock cur pd ps m) p =
      if pd - 1 ≤ p ∧ p < pd - 1 + m then bitOf cur (p - (pd - 1) + (ps - 1)) else bitOf cur p := by
  have h := rtolWrite_spec cur _ (pd - 1) (pd + m - 1 - 1) (ps - 1) m _ _ (by omega) hm hm64 (by omega)
    (mskD0_bit (pd - 1) (pd + m - 1 - 1) (by omega)) (mskD1_bit (pd + m - 1 - 1))
    (rtolChunk_bit cur (ps - 1) (ps + m - 1 - 1) m _ (by omega)
      (mskS0_bit (ps - 1) (ps + m - 1 - 1) (by omega)) hm64)
  unfold rtolBlock
  refine ⟨h.1, fun p => ?_⟩
  rw [h.2 p]
  bitcopy_ifs

theorem rtolLoop_spec (posD posS n : Nat) (D0 : List U64) (hps : 1 ≤ posS) (hlt : posS < posD)
    (hlen : posD - 1 + n ≤ 64 * D0.length) (fuel : Nat) :
    ∀ left cur, left ≤ n → left ≤ fuel → cur.length = D0.length →
      (∀ p, bitOf cur p = if posD - 1 + left ≤ p ∧ p < posD - 1 + n then
        bitOf D0 (p - (posD - 1) + (posS - 1)) else bitOf D0 p) →
      (rtolLoop posD posS fuel left cur).length = D0.length ∧
      ∀ p, bitOf (rtolLoop posD posS fuel left cur) p =
        if posD - 1 ≤ p ∧ p < posD - 1 + n then bitOf D0 (p - (posD - 1) + (posS - 1))
        else bitOf D0 p := by
  induction fuel with
  | zero =>
    intro left cur _ hf hl hb
    simp only [rtolLoop]
    refine ⟨hl, fun p => ?_⟩
    rw [hb p]
    bitcopy_ifs
  | succ fuel ih =>
    intro left cur hn hf hl hb
    rw [rtolLoop_succ]
    by_cases h0 : left = 0
    · rw [if_pos h0]
      refine ⟨hl, fun p => ?_⟩
      rw [hb p]
      bitcopy_ifs
    · rw [if_neg h0]
      have hB := rtolBlock_spec cur (posD + (left - min left 64)) (posS + (left - min left 64))
        (min left 64) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hbits : ∀ p, bitOf (rtolBlock cur (posD + (left - min left 64)) (posS + (left - min left 64))
          (min left 64)) p =
          if posD - 1 + (left - min left 64) ≤ p ∧ p < posD - 1 + n then
            bitOf D0 (p - (posD - 1) + (posS - 1)) else bitOf D0 p := by
        intro p
        rw [hB.2 p]
        by_cases hr : posD + (left - min left 64) - 1 ≤ p ∧
            p < posD + (left - min left 64) - 1 + min left 64
        · rw [if_pos hr, hb]
          bitcopy_ifs
        · rw [if_neg hr, hb]
          bitcopy_ifs
      exact ih (left - min left 64) _ (by omega) (by omega) (by rw [hB.1, hl]) hbits

end CopySpec

open CopySpec in
/-- `copy_chunks!(dest, pd, src, ps, n)` writes the destination bits `pd-1, …, pd+n-2`
(0-based) with the source bits `ps-1, …, ps+n-2` as they were before the call
(`src.read dest` is the source vector, `dest` itself for `.self`), and keeps every
other bit and the chunk count. -/
theorem copyChunks_spec (dest : List U64) (pd : Nat) (src : Src) (ps n : Nat)
    (hpd : 1 ≤ pd) (hps : 1 ≤ ps) (hlen : pd + n - 1 ≤ 64 * dest.length) :
    (copyChunks dest pd src ps n).length = dest.length ∧
    ∀ k, bitOf (copyChunks dest pd src ps n) k =
      if pd - 1 ≤ k ∧ k < pd - 1 + n then bitOf (src.read dest) (k - (pd - 1) + (ps - 1))
      else bitOf dest k := by
  unfold copyChunks
  by_cases hn : n = 0
  · rw [if_pos hn]
    refine ⟨rfl, fun k => ?_⟩
    split
    · exfalso; omega
    · rfl
  · rw [if_neg hn]
    cases src with
    | other cs =>
      exact copyChunksLtoR_spec dest pd (.other cs) ps n hpd hps (by omega) hlen (fun h => by cases h)
    | self =>
      by_cases hgt : pd > ps
      · have h1 : ¬ pd = ps := by omega
        have h2 : ¬ pd < ps := by omega
        rw [if_pos hgt]
        unfold copyChunksRtol
        rw [if_neg h1, if_neg h2]
        exact rtolLoop_spec pd ps n dest hps hgt (by omega) n n dest (Nat.le_refl n) (Nat.le_refl n) rfl
          (fun p => by split <;> first | rfl | (exfalso; omega))
      · rw [if_neg hgt]
        exact copyChunksLtoR_spec dest pd .self ps n hpd hps (by omega) hlen (fun _ => by omega)

end JuliaLean.BitArrays
