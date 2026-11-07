import JuliaLean.base.secretbuffer
import JuliaLean.Proofs.base.io.IOCovCommon


section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Secret

open JuliaLean JuliaLean.IOCov

/-! ## Properties -/

theorem writeByte_end (s : SB) (b : UInt8) (h : s.ptr = s.size + 1) :
    (writeByte s b).content = s.content ++ [b] ∧ (writeByte s b).ptr = s.ptr + 1 := by
  unfold writeByte; simp [h]

theorem writeBytes_end (bs : List UInt8) : ∀ s : SB, s.ptr = s.size + 1 →
    (writeBytes s bs).content = s.content ++ bs ∧ (writeBytes s bs).ptr = (writeBytes s bs).size + 1 := by
  induction bs with
  | nil => intro s h; simp [writeBytes, h]
  | cons b bs ih =>
    intro s h
    have ⟨h1, h2⟩ := writeByte_end s b h
    have := ih (writeByte s b) (by simp [SB.size, h1, h2, h])
    simp only [writeBytes, List.foldl_cons] at this ⊢
    rw [h1] at this; simpa using this

theorem ofString_spec (str : List UInt8) :
    (ofString str).content = str ∧ (ofString str).ptr = 1 := by
  have := writeBytes_end str (create str.length) (by simp [create, SB.size])
  simp only [ofString, seek]
  refine ⟨by simpa [create] using this.1, ?_⟩
  simp only [show ¬ ((0 : Int) < 0) by decide, if_false, Int.toNat_zero]
  omega

theorem takeWhile_ne0 (b : List UInt8) (hb : 0 ∉ b) : b.takeWhile (· != 0) = b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := fun e => hb (e ▸ List.mem_cons_self ..)
    simp [List.takeWhile_cons, hx, ih (fun m => hb (List.mem_cons_of_mem _ m))]

theorem readAll_from (c sl : List UInt8) : ∀ n k, k + n = c.length →
    readAll (n + 1) ⟨c, sl, k + 1⟩ = c.drop k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : ¬ (k + 1 ≤ c.length) := by omega
    simp [readAll, read, eof, SB.size, show c.length < k + 1 by omega,
      List.drop_eq_nil_of_le (show c.length ≤ k by omega)]
  | succ n ih =>
    intro k hk
    have hlt : k < c.length := by omega
    have hr : read ⟨c, sl, k + 1⟩ = .ok (c[k], ⟨c, sl, k + 1 + 1⟩) := by
      simp [read, eof, SB.size, show ¬ (c.length < k + 1) by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt]
    show (match read (⟨c, sl, k + 1⟩ : SB) with
      | .ok (b, s') => b :: readAll (n + 1) s' | .error _ => []) = c.drop k
    rw [hr]
    dsimp only
    rw [ih (k + 1) (by omega)]
    exact (List.drop_eq_getElem_cons hlt).symm

/-- A `SecretBuffer` built from a string reads back exactly the string's bytes. -/
def RoundTrip : Prop :=
  (∀ str, (ofString str).content = str ∧ position (ofString str) = 0) ∧
  (∀ str, readAll (str.length + 1) (ofString str) = str) ∧
  (∀ str, ofAbstractString str = ofString str ∧ convertSB str = ofString str) ∧
  (∀ d, (ofBytesBang d).1 = ofString d ∧ ∀ x ∈ (ofBytesBang d).2, x = 0) ∧
  unsafeOfPtr none = argErr "cannot convert NULL to SecretBuffer" ∧
  (∀ b, unsafeOfPtr (some b) = .ok (ofBytesBang b)) ∧
  (∀ b, 0 ∉ b → unsafeOfCstring (some b) = .ok (ofBytesBang b))

theorem roundTrip : RoundTrip := by
  refine ⟨fun str => ⟨(ofString_spec str).1, by simp [position, (ofString_spec str).2]⟩, ?_,
    fun _ => ⟨rfl, rfl⟩, fun d => ⟨rfl, fun x hx => by simp [ofBytesBang, zeros] at hx; exact hx.2.symm⟩,
    rfl, fun _ => rfl, ?_⟩
  · intro str
    obtain ⟨h1, h2⟩ := ofString_spec str
    have := readAll_from str (ofString str).slack str.length 0 (by simp)
    rw [show (ofString str) = ⟨str, (ofString str).slack, 0 + 1⟩ by
      cases h : ofString str; simp_all]
    simpa using this
  · intro b hb
    have : b.takeWhile (· != 0) = b := takeWhile_ne0 b hb
    simp [unsafeOfCstring, unsafeOfPtr, this]

/-- Positioning: `seek` clamps to `0:size`, `position`, `eof` and `bytesavailable` agree. -/
def Positioning : Prop :=
  (∀ s n, 0 ≤ n → n ≤ s.size → position (seek s n) = n) ∧
  (∀ s n, n < 0 → position (seek s n) = 0) ∧
  (∀ s n, (s.size : Int) < n → position (seek s n) = s.size) ∧
  (∀ s, position (seekend s) = s.size ∧ eof (seekend s) = true) ∧
  (∀ s n, skip s n = seek s (position s + n)) ∧
  (∀ s, 1 ≤ s.ptr → (eof s = true ↔ bytesavailable s ≤ 0)) ∧
  (∀ s, isempty s = true ↔ s.content = []) ∧
  (∀ s, eof s = true → peek s = .error .eofError ∧ read s = .error .eofError) ∧
  (∀ s, eof s = false → ∃ b, peek s = .ok b ∧ read s = .ok (b, { s with ptr := s.ptr + 1 }))

theorem positioning : Positioning := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro s n h1 h2; simp only [position, seek, show ¬ n < 0 by omega, if_false]; omega
  · intro s n h; simp only [position, seek, h, if_true]; omega
  · intro s n h; simp only [position, seek, show ¬ n < 0 by omega, if_false, SB.size] at h ⊢; omega
  · intro s
    simp only [position, seekend, seek, eof, SB.size, show ¬ ((s.content.length : Int) + 1 < 0) by omega,
      if_false]
    constructor
    · omega
    · simp
  · intro s hp; simp only [eof, bytesavailable, decide_eq_true_eq]; omega
  · intro s; simp [isempty, SB.size]
  · intro s h; simp [peek, read, h]
  · intro s h; exact ⟨s.content.getD (s.ptr - 1) 0, by simp [peek, h], by simp [read, h]⟩

/-- Comparison, copies and conversions. -/
def Comparisons : Prop :=
  (∀ s, eq s s = true) ∧
  (∀ s, eq s (copy s) = true ∧ copy s = s) ∧
  (∀ d s, copyBang d s = s) ∧
  (∀ mix s t h, eq s t = true → hash mix s h = hash mix t h) ∧
  (∀ s, showSB s = "SecretBuffer(\"*******\")") ∧
  (∀ s, writeTo s = (s.content, s.size)) ∧
  (∀ s, 0 ∉ s.content → ∃ r, cconvert s = .ok (r.data, r) ∧ r.content = s.content ∧ r.ptr = s.ptr ∧
      r.data.take (s.size + 1) = s.content ++ [0]) ∧
  (∀ s, 0 ∈ s.content → cconvert s = argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings")

theorem bufcmp_self (d : List UInt8) (n : Nat) : bufcmp d d n = 0 := by
  simp only [bufcmp, UInt8.xor_self]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp [ih]

theorem comparisons : Comparisons := by
  refine ⟨?_, ?_, fun _ s => rfl, fun _ _ _ _ _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro s; simp [eq, bufcmp_self]
  · intro s; refine ⟨by simp [eq, copy, copyBang, bufcmp_self, SB.data, SB.size], rfl⟩
  · intro s h
    have hc : s.content.contains 0 = false := by simpa using h
    refine ⟨⟨s.content, 0 :: (writeByte { s with ptr := s.size + 1 } 0).slack, s.ptr⟩, ?_, rfl, rfl, ?_⟩
    · rw [cconvert, if_neg (by simp [hc, h])]
      simp [writeByte, SB.size, SB.data]
    · simp only [SB.data, SB.size]; exact take_length_succ_append _ _ _
  · intro s h
    have hc : s.content.contains 0 = true := by simpa using h
    rw [cconvert, if_pos hc]

/-- `shred!` zeroes everything; `shred!(f, x)` shreds even when `f` throws. -/
def Shredding : Prop :=
  (∀ s, isshredded (shred s) = true ∧ (shred s).size = 0 ∧ (shred s).ptr = 1) ∧
  (∀ s, (shred s).data.length = s.data.length) ∧
  (∀ s, (finalShred s).1 = !isshredded s ∧ (finalShred s).2 = shred s) ∧
  (∀ {α : Type} (f : SB → R α) x, (shredDo f x).1 = f x ∧ isshredded (shredDo f x).2 = true) ∧
  (∀ h, (create h).size = 0 ∧ (create h).data.length = h ∧ isshredded (create h) = true)

theorem shredding : Shredding := by
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro s; simp [isshredded, shred, zeros, SB.data, SB.size]
  · intro s; simp [shred, zeros, SB.data]
  · intro α f x; exact ⟨rfl, by simp [shredDo, isshredded, shred, zeros, SB.data]⟩
  · intro h; simp [create, SB.size, SB.data, isshredded]

/-- `peek(s, T)` returns the next value without consuming it (`base/io.jl:382-388`);
for a `SecretBuffer` and `T = Char`, the value `read(s, Char)` would give. -/
def PeekChar : Prop := ∀ s : SB, eof s = false → ∃ c, peekGeneric s = .ok c

theorem peekChar_refuted : ¬ PeekChar := by
  intro h
  obtain ⟨c, hc⟩ := h (ofString [104]) (by decide)
  simp [peekGeneric] at hc


/-! ## Per-method properties -/

def RoundTrip_1 : Prop :=
  (∀ str, (ofString str).content = str ∧ position (ofString str) = 0)
theorem roundTrip_1 : RoundTrip_1 := by
  have h := roundTrip
  exact h.1

def RoundTrip_2 : Prop :=
  (∀ str, readAll (str.length + 1) (ofString str) = str)
theorem roundTrip_2 : RoundTrip_2 := by
  have h := roundTrip
  exact h.2.1

def RoundTrip_3 : Prop :=
  (∀ str, ofAbstractString str = ofString str ∧ convertSB str = ofString str)
theorem roundTrip_3 : RoundTrip_3 := by
  have h := roundTrip
  exact h.2.2.1

def RoundTrip_4 : Prop :=
  (∀ d, (ofBytesBang d).1 = ofString d ∧ ∀ x ∈ (ofBytesBang d).2, x = 0) ∧
  unsafeOfPtr none = argErr "cannot convert NULL to SecretBuffer"
theorem roundTrip_4 : RoundTrip_4 := by
  have h := roundTrip
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

def RoundTrip_5 : Prop :=
  (∀ b, unsafeOfPtr (some b) = .ok (ofBytesBang b))
theorem roundTrip_5 : RoundTrip_5 := by
  have h := roundTrip
  exact h.2.2.2.2.2.1

def RoundTrip_6 : Prop :=
  (∀ b, 0 ∉ b → unsafeOfCstring (some b) = .ok (ofBytesBang b))
theorem roundTrip_6 : RoundTrip_6 := by
  have h := roundTrip
  exact h.2.2.2.2.2.2

def Positioning_1 : Prop :=
  (∀ s n, 0 ≤ n → n ≤ s.size → position (seek s n) = n)
theorem positioning_1 : Positioning_1 := by
  have h := positioning
  exact h.1

def Positioning_2 : Prop :=
  (∀ s n, n < 0 → position (seek s n) = 0)
theorem positioning_2 : Positioning_2 := by
  have h := positioning
  exact h.2.1

def Positioning_3 : Prop :=
  (∀ s n, (s.size : Int) < n → position (seek s n) = s.size)
theorem positioning_3 : Positioning_3 := by
  have h := positioning
  exact h.2.2.1

def Positioning_4 : Prop :=
  (∀ s, position (seekend s) = s.size ∧ eof (seekend s) = true)
theorem positioning_4 : Positioning_4 := by
  have h := positioning
  exact h.2.2.2.1

def Positioning_5 : Prop :=
  (∀ s n, skip s n = seek s (position s + n))
theorem positioning_5 : Positioning_5 := by
  have h := positioning
  exact h.2.2.2.2.1

def Positioning_6 : Prop :=
  (∀ s, 1 ≤ s.ptr → (eof s = true ↔ bytesavailable s ≤ 0))
theorem positioning_6 : Positioning_6 := by
  have h := positioning
  exact h.2.2.2.2.2.1

def Positioning_7 : Prop :=
  (∀ s, isempty s = true ↔ s.content = [])
theorem positioning_7 : Positioning_7 := by
  have h := positioning
  exact h.2.2.2.2.2.2.1

def Positioning_8 : Prop :=
  (∀ s, eof s = true → peek s = .error .eofError ∧ read s = .error .eofError)
theorem positioning_8 : Positioning_8 := by
  have h := positioning
  exact h.2.2.2.2.2.2.2.1

def Positioning_9 : Prop :=
  (∀ s, eof s = false → ∃ b, peek s = .ok b ∧ read s = .ok (b, { s with ptr := s.ptr + 1 }))
theorem positioning_9 : Positioning_9 := by
  have h := positioning
  exact h.2.2.2.2.2.2.2.2

def Comparisons_1 : Prop :=
  (∀ s, eq s s = true)
theorem comparisons_1 : Comparisons_1 := by
  have h := comparisons
  exact h.1

def Comparisons_2 : Prop :=
  (∀ s, eq s (copy s) = true ∧ copy s = s)
theorem comparisons_2 : Comparisons_2 := by
  have h := comparisons
  exact h.2.1

def Comparisons_3 : Prop :=
  (∀ d s, copyBang d s = s)
theorem comparisons_3 : Comparisons_3 := by
  have h := comparisons
  exact h.2.2.1

def Comparisons_4 : Prop :=
  (∀ mix s t h, eq s t = true → hash mix s h = hash mix t h)
theorem comparisons_4 : Comparisons_4 := by
  have h := comparisons
  exact h.2.2.2.1

def Comparisons_5 : Prop :=
  (∀ s, showSB s = "SecretBuffer(\"*******\")")
theorem comparisons_5 : Comparisons_5 := by
  have h := comparisons
  exact h.2.2.2.2.1

def Comparisons_6 : Prop :=
  (∀ s, writeTo s = (s.content, s.size))
theorem comparisons_6 : Comparisons_6 := by
  have h := comparisons
  exact h.2.2.2.2.2.1

def Comparisons_7 : Prop :=
  (∀ s, 0 ∉ s.content → ∃ r, cconvert s = .ok (r.data, r) ∧ r.content = s.content ∧ r.ptr = s.ptr ∧
      r.data.take (s.size + 1) = s.content ++ [0])
theorem comparisons_7 : Comparisons_7 := by
  have h := comparisons
  exact h.2.2.2.2.2.2.1

def Comparisons_8 : Prop :=
  (∀ s, 0 ∈ s.content → cconvert s = argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings")
theorem comparisons_8 : Comparisons_8 := by
  have h := comparisons
  exact h.2.2.2.2.2.2.2

def Shredding_1 : Prop :=
  (∀ s, isshredded (shred s) = true ∧ (shred s).size = 0 ∧ (shred s).ptr = 1)
theorem shredding_1 : Shredding_1 := by
  have h := shredding
  exact h.1

def Shredding_2 : Prop :=
  (∀ s, (shred s).data.length = s.data.length)
theorem shredding_2 : Shredding_2 := by
  have h := shredding
  exact h.2.1

def Shredding_3 : Prop :=
  (∀ s, (finalShred s).1 = !isshredded s ∧ (finalShred s).2 = shred s)
theorem shredding_3 : Shredding_3 := by
  have h := shredding
  exact h.2.2.1

def Shredding_4 : Prop :=
  (∀ (α : Type) (f : SB → R α) x, (shredDo f x).1 = f x ∧ isshredded (shredDo f x).2 = true)
theorem shredding_4 : Shredding_4 := by
  have h := shredding
  exact fun _ f x => h.2.2.2.1 f x

def Shredding_5 : Prop :=
  (∀ h, (create h).size = 0 ∧ (create h).data.length = h ∧ isshredded (create h) = true)
theorem shredding_5 : Shredding_5 := by
  have h := shredding
  exact h.2.2.2.2
end JuliaLean.IOCov.Secret
end
