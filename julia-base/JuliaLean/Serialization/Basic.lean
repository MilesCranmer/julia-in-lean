import JuliaLean.Serialization.Props

/-!
Lemmas about the decoder monad, byte reads, integers, `Char`s, the `Bool`
run-length code and bits-array chunks.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-! ### The decoder monad -/

theorem bind_run {α β : Type} {m : Dm α} {k : α → Dm β} {s s' : DS} {a : α}
    (h : m s = .ok (a, s')) : (m >>= k) s = k a s' := by
  show Dm.bind m k s = k a s'
  simp only [Dm.bind, h]

theorem bind_err {α β : Type} {m : Dm α} {k : α → Dm β} {s : DS} {e : SErr}
    (h : m s = .error e) : (m >>= k) s = .error e := by
  show Dm.bind m k s = .error e
  simp only [Dm.bind, h]

theorem pure_run {α : Type} (a : α) (s : DS) : (pure a : Dm α) s = .ok (a, s) := rfl

theorem readU8_run {s : DS} {b : UInt8} {bs : Bytes} (h : s.io = b :: bs) :
    readU8 s = .ok (b, { s with io := bs }) := by
  simp [readU8, h]

theorem readN_run {s : DS} {bs rest : Bytes} (h : s.io = bs ++ rest) :
    readN bs.length s = .ok (bs, { s with io := rest }) := by
  simp [readN, h]

/-! ### Little-endian integers -/

theorem le_length : ∀ n m, (le n m).length = n
  | 0, _ => rfl
  | n + 1, m => by simp [le, le_length n]

theorem unle_le : ∀ n m, unle (le n m) = m % 256 ^ n
  | 0, m => by simp [le, unle, Nat.mod_one]
  | n + 1, m => by
    simp only [le, unle, unle_le n, UInt8.toNat_ofNat']
    have h1 : m % 256 % 2 ^ 8 = m % 256 := by simp
    rw [h1, Nat.pow_succ', Nat.mod_mul]

theorem readLE_run {s : DS} {n m : Nat} {rest : Bytes} (h : s.io = le n m ++ rest) :
    readLE n s = .ok (m % 256 ^ n, { s with io := rest }) := by
  have h1 := readN_run (bs := le n m) h
  rw [le_length] at h1
  unfold readLE
  rw [bind_run h1, unle_le]
  rfl

theorem intBits_lt (t : IntTy) (x : Int) : intBits t x < 256 ^ nbytes t := by
  cases t <;> simp [intBits, nbytes, IntTy.bits] <;> omega

theorem ofBits_intBits (t : IntTy) (x : Int) (h : InRange t x) : ofBits t (intBits t x) = x := by
  cases t <;>
    simp only [ofBits, intBits, InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at * <;>
    simp at * <;> (try split) <;> omega

theorem readInt_run {s : DS} {t : IntTy} {x : Int} {rest : Bytes} (hx : InRange t x)
    (h : s.io = le (nbytes t) (intBits t x) ++ rest) :
    readInt t s = .ok (x, { s with io := rest }) := by
  unfold readInt
  rw [bind_run (readLE_run h), Nat.mod_eq_of_lt (intBits_lt t x), ofBits_intBits t x hx]
  rfl

/-! ### `Char` -/

theorem cont_iff (n : Nat) (h : n < 256) :
    (UInt8.ofNat n &&& 0xc0 = 0x80) ↔ (128 ≤ n ∧ n < 192) := by
  have key : ∀ m, m < 256 → ((UInt8.ofNat m &&& 0xc0 = 0x80) ↔ (128 ≤ m ∧ m < 192)) := by
    decide +kernel
  exact key n h

theorem toNat_ofNat_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat']; omega

theorem ok_pair_eq {a b : Nat} {s t : DS} (h1 : a = b) (h2 : s = t) :
    (Except.ok (a, s) : Except SErr (Nat × DS)) = .ok (b, t) := by
  subst h1; subst h2; rfl

/-- `read(io, Char)` after the bytes `write(io, c)` emits, for a `Char` given by its
four bytes `b0 b1 b2 b3` (most significant first) forming a complete sequence. -/
theorem readChar_bytes {s : DS} {rest : Bytes} (b0 b1 b2 b3 : Nat)
    (l0 : b0 < 256) (l1 : b1 < 256) (l2 : b2 < 256) (l3 : b3 < 256)
    (hk : if leadingOnes8 b0 = 2 then isContN b1 ∧ b2 = 0 ∧ b3 = 0
      else if leadingOnes8 b0 = 3 then isContN b1 ∧ isContN b2 ∧ b3 = 0
      else if leadingOnes8 b0 = 4 then isContN b1 ∧ isContN b2 ∧ isContN b3
      else b1 = 0 ∧ b2 = 0 ∧ b3 = 0)
    (h : s.io = charLoop 4 (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) ++ rest) :
    readChar s = .ok (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3, { s with io := rest }) := by
  simp only [charLoop] at h
  have u0 : (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) % 256 = b0 := by omega
  have u1 : (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 % 256 = b1 := by omega
  have u2 : (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 % 256 = b2 := by omega
  have u3 : (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 / 256 % 256 = b3 := by
    omega
  have u4 : (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 / 256 / 256 = 0 := by
    omega
  simp only [u0, u1, u2, u3, u4, ite_true] at h
  unfold readChar
  unfold isContN at hk
  by_cases hlo2 : leadingOnes8 b0 = 2
  · simp only [hlo2, ite_true] at hk
    obtain ⟨hc1, hz2, hz3⟩ := hk
    have v1 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have v2 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 = 0) = True := by
      simp only [eq_iff_iff, iff_true]; omega
    simp only [v1, v2, ite_false, ite_true, List.cons_append, List.nil_append] at h
    rw [bind_run (readU8_run h)]
    simp only [toNat_ofNat_lt l0, hlo2, show (2 ≤ 2 ∧ 2 ≤ 4) from by decide, and_self, ↓reduceIte]
    simp only [readCharLoop, Nat.reduceMul, Nat.reduceSub, Nat.le_refl, ↓reduceIte,
      (cont_iff b1 l1).2 hc1, toNat_ofNat_lt l1, show ¬ (16 ≤ 8) from by decide]
    exact ok_pair_eq (by simp only [Nat.reducePow]; omega) rfl
  by_cases hlo3 : leadingOnes8 b0 = 3
  · simp only [hlo3, ite_true, show ¬ ((3 : Nat) = 2) from by decide, ite_false] at hk
    obtain ⟨hc1, hc2, hz3⟩ := hk
    have v1 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have v2 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have v3 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 / 256 = 0) = True := by
      simp only [eq_iff_iff, iff_true]; omega
    simp only [v1, v2, v3, ite_false, ite_true, List.cons_append, List.nil_append] at h
    rw [bind_run (readU8_run h)]
    simp only [toNat_ofNat_lt l0, hlo3, show (2 ≤ 3 ∧ 3 ≤ 4) from by decide, and_self, ↓reduceIte]
    simp only [readCharLoop, Nat.reduceMul, Nat.reduceSub, Nat.le_refl, ↓reduceIte,
      (cont_iff b1 l1).2 hc1, (cont_iff b2 l2).2 hc2, toNat_ofNat_lt l1, toNat_ofNat_lt l2,
      show (8 ≤ 16) from by decide, show ¬ (8 ≤ 0) from by decide]
    exact ok_pair_eq (by simp only [Nat.reducePow]; omega) rfl
  by_cases hlo4 : leadingOnes8 b0 = 4
  · simp only [hlo4, ite_true, show ¬ ((4 : Nat) = 2) from by decide,
      show ¬ ((4 : Nat) = 3) from by decide, ite_false] at hk
    obtain ⟨hc1, hc2, hc3⟩ := hk
    have v1 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have v2 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    have v3 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 / 256 / 256 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    simp only [v1, v2, v3, ite_false, ite_true, List.cons_append, List.nil_append] at h
    rw [bind_run (readU8_run h)]
    simp only [toNat_ofNat_lt l0, hlo4, show (2 ≤ 4 ∧ 4 ≤ 4) from by decide, and_self, ↓reduceIte]
    simp only [readCharLoop, Nat.reduceMul, Nat.reduceSub, Nat.le_refl, ↓reduceIte,
      (cont_iff b1 l1).2 hc1, (cont_iff b2 l2).2 hc2, (cont_iff b3 l3).2 hc3,
      toNat_ofNat_lt l1, toNat_ofNat_lt l2, toNat_ofNat_lt l3,
      show (0 ≤ 16) from by decide, show (0 ≤ 8) from by decide, Nat.zero_le]
    rw [pure_run]
    exact ok_pair_eq (by simp only [Nat.reducePow]; omega) rfl
  simp only [hlo2, hlo3, hlo4, ite_false] at hk
  obtain ⟨hz1, hz2, hz3⟩ := hk
  have v1 : ((b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 = 0) = True := by
    simp only [eq_iff_iff, iff_true]; omega
  simp only [v1, ite_true, List.cons_append, List.nil_append] at h
  rw [bind_run (readU8_run h)]
  simp only [toNat_ofNat_lt l0]
  rw [if_neg (by omega), pure_run]
  exact ok_pair_eq (by simp only [Nat.reducePow]; omega) rfl

theorem bytes_recompose (c : Nat) (h : c < 2 ^ 32) :
    c / 16777216 % 256 * 16777216 + c / 65536 % 256 * 65536 + c / 256 % 256 * 256 + c % 256 = c := by
  omega

/-- `write(io, c)` followed by `read(io, Char)` returns `c` and leaves the rest of the
stream for every complete `Char`. -/
theorem readChar_run {s : DS} {c : Nat} {rest : Bytes} (hc : CharWF c)
    (h : s.io = writeChar c ++ rest) : readChar s = .ok (c, { s with io := rest }) := by
  obtain ⟨hlt, hk⟩ := hc
  simp only [cbyte, Nat.reduceMul, Nat.reduceSub, Nat.reducePow, Nat.div_one] at hk
  have hw : bswap32 c = c / 16777216 % 256 + c / 65536 % 256 * 256 + c / 256 % 256 * 65536 +
      c % 256 * 16777216 := by
    rfl
  simp only [writeChar, hw] at h
  have := readChar_bytes (s := s) (rest := rest) (c / 16777216 % 256) (c / 65536 % 256)
    (c / 256 % 256) (c % 256) (by omega) (by omega) (by omega) (by omega) hk h
  rw [this]
  exact ok_pair_eq (bytes_recompose c hlt) rfl

/-! ### `Bool` run-length code -/

theorem rle_byte_toNat (last : Bool) (count : Nat) (h : count ≤ 127) :
    (UInt8.ofNat ((if last then 128 else 0) + count)).toNat = (if last then 128 else 0) + count := by
  apply toNat_ofNat_lt; cases last <;> simp <;> omega

theorem rle_byte_v (last : Bool) (count : Nat) (h : count ≤ 127) :
    decide ((if last then 128 else 0) + count ≥ 128) = last := by
  cases last <;> simp <;> omega

theorem rle_byte_c (last : Bool) (count : Nat) (h : count ≤ 127) :
    ((if last then 128 else 0) + count) % 128 = count := by
  cases last <;> simp <;> omega

theorem rleRead_go (n : Nat) : ∀ (ys : List Bool) (last : Bool) (count : Nat) (acc : List Bool)
    (fuel : Nat) (s : DS) (rest : Bytes),
    1 ≤ count → count ≤ 127 → acc.length + count + ys.length = n →
    s.io = rleGo last count ys ++ rest → (rleGo last count ys).length < fuel →
    rleRead n fuel acc s = .ok (acc ++ List.replicate count last ++ ys, { s with io := rest })
  | [], last, count, acc, fuel, s, rest, h1, h2, hn, hio, hf => by
    simp only [rleGo, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [rleGo, List.cons_append, List.nil_append] at hio
    unfold rleRead
    simp only [List.length_nil, Nat.add_zero] at hn
    rw [if_neg (by omega)]
    rw [bind_run (readU8_run hio)]
    simp only [rle_byte_toNat last count h2, rle_byte_v last count h2, rle_byte_c last count h2]
    rw [if_neg (by omega)]
    unfold rleRead
    rw [if_pos (by simp; omega), pure_run, List.append_nil]
  | x :: xs, last, count, acc, fuel, s, rest, h1, h2, hn, hio, hf => by
    simp only [List.length_cons] at hn
    by_cases hx : (x != last || count == 127) = true
    · simp only [rleGo, hx, ↓reduceIte, List.cons_append, List.length_cons] at hio hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      unfold rleRead
      rw [if_neg (by omega)]
      rw [bind_run (readU8_run hio)]
      simp only [rle_byte_toNat last count h2, rle_byte_v last count h2, rle_byte_c last count h2]
      rw [if_neg (by omega)]
      have ih := rleRead_go n xs x 1 (acc ++ List.replicate count last) f { s with io := rleGo x 1 xs ++ rest }
        rest (by omega) (by omega) (by simp; omega) rfl (by omega)
      rw [ih]
      simp
    · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at hx
      obtain ⟨rfl, hc⟩ := hx
      simp only [rleGo, bne_self_eq_false, Bool.false_or, hc, beq_iff_eq, ↓reduceIte,
        decide_false, Bool.false_eq_true] at hio hf
      have ih := rleRead_go n xs x (count + 1) acc fuel s rest (by omega) (by omega) (by omega) hio hf
      rw [ih, List.replicate_succ']
      simp

theorem rleRead_rle (xs : List Bool) (hne : xs ≠ []) (s : DS) (rest : Bytes) (fuel : Nat)
    (hio : s.io = rle xs ++ rest) (hf : (rle xs).length < fuel) :
    rleRead xs.length fuel [] s = .ok (xs, { s with io := rest }) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x ys =>
    simp only [rle] at hio hf
    have := rleRead_go (x :: ys).length ys x 1 [] fuel s rest (by omega) (by omega)
      (by simp; omega) hio hf
    rw [this]
    simp

/-! ### Bits arrays -/

theorem chunks_flatten (nb : Nat) (enc : Int → Bytes) (henc : ∀ x, (enc x).length = nb) :
    ∀ xs : List Int, chunks nb xs.length (xs.map enc).flatten = xs.map enc
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.flatten_cons, List.length_cons, chunks,
      List.take_left' (henc x), List.drop_left' (henc x), chunks_flatten nb enc henc xs]

theorem flatten_length (nb : Nat) (enc : Int → Bytes) (henc : ∀ x, (enc x).length = nb) :
    ∀ xs : List Int, ((xs.map enc).flatten).length = xs.length * nb
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, henc x,
      flatten_length nb enc henc xs, List.length_cons, Nat.succ_mul]
    omega

end JuliaLean.Serialization
