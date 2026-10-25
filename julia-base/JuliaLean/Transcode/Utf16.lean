import JuliaLean.Transcode.Valid
import JuliaLean.Strings.Theory

/-!
# `transcode` between UTF-8 and UTF-16 never fails and never reads or writes out of bounds

* `transcode(UInt16, ::AbstractVector{UInt8})` returns for every byte vector:
  every `src[i += 1]` is guarded by `i < n` (`u16Loop_ok`).
* `transcode(UInt8, ::AbstractVector{UInt16})` returns for every code-unit
  vector, its first loop counts exactly the bytes its second loop writes, and
  every write `dst[j += 1]` is within `StringVector(m)` (`transcode8_spec`).
-/

namespace JuliaLean.Transcode

open JuliaLean.Strings

@[simp] theorem ix0 : (ix 0).val = 0 := rfl
@[simp] theorem ix4 : (ix 4).val = 4 := rfl

/-- `true` for a returned value, `false` for a thrown exception. -/
def okB {α : Type} : SJl α → Bool
  | .ok _ => true
  | .error _ => false

theorem okB_exists {α : Type} {x : SJl α} (h : okB x = true) : ∃ y, x = .ok y := by
  cases x with
  | ok y => exact ⟨y, rfl⟩
  | error e => simp [okB] at h

theorem stepNext_cons {α β : Type} (loop : α → List α → β → SJl β) (d : β) (x : α) (r : List α) :
    stepNext loop d (x :: r) = loop x r d := rfl

theorem stepNext_nil {α β : Type} (loop : α → List α → β → SJl β) (d : β) :
    stepNext loop d [] = .ok d := rfl

/-! ## UTF-8 to UTF-16 -/

theorem stepNext16_ok {k : Nat}
    (ih : ∀ (a : UInt8) (r : List UInt8) (d : List UInt16), r.length < k → okB (u16Loop k a r d) = true)
    (dst : List UInt16) (rest : List UInt8) (h : rest.length ≤ k) :
    okB (stepNext (u16Loop k) dst rest) = true := by
  cases rest with
  | nil => rfl
  | cons x r => rw [stepNext_cons]; exact ih x r dst (by simp at h; omega)

/-- The UTF-8 to UTF-16 loop returns for every input; its bound `rest.length + 1`
on the number of iterations is never exhausted. -/
theorem u16Loop_ok : ∀ (k : Nat) (a : UInt8) (rest : List UInt8) (dst : List UInt16),
    rest.length < k → okB (u16Loop k a rest dst) = true := by
  intro k
  induction k with
  | zero => intro a rest dst h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro a rest dst h
    have T := @stepNext16_ok k ih
    rcases rest with _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩ <;>
      simp only [u16Loop, nextB, List.isEmpty_nil, List.isEmpty_cons, Bool.not_true, Bool.not_false,
        Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] <;>
      (repeat' split) <;>
      first
        | rfl
        | exact ih _ _ _ (by simp at h ⊢; omega)
        | exact T _ _ (by simp at h ⊢; omega)
        | (simp_all; done)

theorem transcode16_ok (src : List UInt8) : ∃ us, transcode16 src = .ok us := by
  cases src with
  | nil => exact ⟨[], rfl⟩
  | cons a rest => exact okB_exists (u16Loop_ok _ a rest [] (by simp))

/-! ## UTF-16 to UTF-8 -/

/-- `stepNext` without the reads: the next iteration's value, or `[]` at the end. -/
def nx (f : UInt16 → List UInt16 → List UInt8) : List UInt16 → List UInt8
  | [] => []
  | x :: r => f x r

/-- The bytes the second loop of `transcode(UInt8, ::AbstractVector{UInt16})`
writes, with the same branches and without the capacity checks. -/
def wrSpec : Nat → UInt16 → List UInt16 → List UInt8
  | 0, _, _ => []
  | k + 1, a, rest =>
    if a < 0x80 then [a.toUInt8] ++ nx (wrSpec k) rest
    else if a < 0x800 then enc2 a ++ nx (wrSpec k) rest
    else if (a &&& 0xfc00) == 0xd800 && !rest.isEmpty then
      match rest with
      | b :: r => if (b &&& 0xfc00) == 0xdc00 then enc4 a b ++ nx (wrSpec k) r else enc3 a ++ wrSpec k b r
      | [] => []
    else enc3 a ++ nx (wrSpec k) rest

theorem putAll_ok (m : JInt64) : ∀ (dst xs : List UInt8), (dst.length : Int) + xs.length ≤ m.val →
    putAll m dst xs = .ok (dst ++ xs) := by
  intro dst xs
  induction xs generalizing dst with
  | nil => intro _; simp [putAll]
  | cons x xs ih =>
    intro h
    have h1 : (dst.length : Int) + 1 ≤ m.val := by simp at h; omega
    simp only [putAll, put, h1, ↓reduceIte, bind, Except.bind]
    rw [ih (dst ++ [x]) (by simp at h ⊢; omega)]
    simp

@[simp] theorem enc2_length (a : UInt16) : (enc2 a).length = 2 := rfl
@[simp] theorem enc3_length (a : UInt16) : (enc3 a).length = 3 := rfl
@[simp] theorem enc4_length (a b : UInt16) : (enc4 a b).length = 4 := rfl

theorem wrSpec_length : ∀ (k : Nat) (a : UInt16) (rest : List UInt16),
    (wrSpec k a rest).length ≤ 3 * (rest.length + 1) := by
  intro k
  induction k with
  | zero => intro a rest; simp [wrSpec]
  | succ k ih =>
    intro a rest
    have N : ∀ r : List UInt16, (nx (wrSpec k) r).length ≤ 3 * r.length := by
      intro r; cases r with
      | nil => simp [nx]
      | cons x r => have := ih x r; simp [nx] at this ⊢; omega
    rcases rest with _ | ⟨b, r⟩
    · simp only [wrSpec]
      repeat' split
      all_goals simp [nx]
    · have N1 := N r
      have I1 := ih b r
      simp only [wrSpec]
      repeat' split
      all_goals (try simp only [nx, List.length_append, List.length_cons, List.length_nil,
        enc2_length, enc3_length, enc4_length] at N1 I1 ⊢)
      all_goals omega

theorem wrLoop_spec (m : JInt64) : ∀ (k : Nat) (a : UInt16) (rest : List UInt16) (dst : List UInt8),
    rest.length < k → (dst.length : Int) + (wrSpec k a rest).length ≤ m.val →
    wrLoop m k a rest dst = .ok (dst ++ wrSpec k a rest) := by
  intro k
  induction k with
  | zero => intro a rest dst h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro a rest dst hk hc
    have N : ∀ (d : List UInt8) (r : List UInt16), r.length ≤ k →
        (d.length : Int) + (nx (wrSpec k) r).length ≤ m.val →
        stepNext (wrLoop m k) d r = .ok (d ++ nx (wrSpec k) r) := by
      intro d r hr hc'
      cases r with
      | nil => simp [stepNext_nil, nx]
      | cons x r => rw [stepNext_cons]; exact ih x r d (by simp at hr; omega) hc'
    rcases rest with _ | ⟨b, r⟩
    · simp only [wrSpec, wrLoop, List.isEmpty_nil, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at hc ⊢
      by_cases h1 : a < 0x80
      · simp only [h1, ↓reduceIte, List.length_append] at hc ⊢
        rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
        simp [stepNext_nil, nx]
      · by_cases h2 : a < 0x800
        · simp only [h1, h2, ↓reduceIte, List.length_append] at hc ⊢
          rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
          simp [stepNext_nil, nx]
        · simp only [h1, h2, ↓reduceIte, List.length_append] at hc ⊢
          rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
          simp [stepNext_nil, nx]
    · have hk' : r.length < k := by simp at hk; omega
      simp only [wrSpec, wrLoop, List.isEmpty_cons, Bool.not_false, Bool.and_true, nextB,
        bind, Except.bind] at hc ⊢
      by_cases h1 : a < 0x80
      · simp only [h1, ↓reduceIte, List.length_append] at hc ⊢
        rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
        simp only []
        rw [N _ _ (by simp; omega) (by simp at hc ⊢; omega)]
        simp
      · by_cases h2 : a < 0x800
        · simp only [h1, h2, ↓reduceIte, List.length_append] at hc ⊢
          rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
          simp only []
          rw [N _ _ (by simp; omega) (by simp at hc ⊢; omega)]
          simp
        · by_cases h3 : ((a &&& 0xfc00) == 0xd800) = true
          · by_cases h4 : ((b &&& 0xfc00) == 0xdc00) = true
            · simp only [h1, h2, h3, h4, ↓reduceIte, List.length_append] at hc ⊢
              rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
              simp only []
              rw [N _ _ (by omega) (by simp at hc ⊢; omega)]
              simp
            · simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true, List.length_append] at hc ⊢
              rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
              simp only []
              rw [ih b r _ hk' (by simp at hc ⊢; omega)]
              simp
          · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, List.length_append] at hc ⊢
            rw [putAll_ok m _ _ (by simp at hc ⊢; omega)]
            simp only []
            rw [N _ _ (by simp; omega) (by simp at hc ⊢; omega)]
            simp

theorem cntLoop_spec : ∀ (k : Nat) (a : UInt16) (rest : List UInt16) (m0 : JInt64),
    rest.length < k → 0 ≤ m0.val → m0.val + 3 * (rest.length + 1) ≤ 2 ^ 62 →
    ∃ M : JInt64, cntLoop k a rest m0 = .ok M ∧ M.val = m0.val + (wrSpec k a rest).length := by
  intro k
  induction k with
  | zero => intro a rest m0 h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro a rest m0 hk h0 hb
    have N : ∀ (M0 : JInt64) (r : List UInt16), r.length ≤ k → 0 ≤ M0.val →
        M0.val + 3 * r.length ≤ 2 ^ 62 →
        ∃ M : JInt64, stepNext (cntLoop k) M0 r = .ok M ∧ M.val = M0.val + (nx (wrSpec k) r).length := by
      intro M0 r hr h0' hb'
      cases r with
      | nil => exact ⟨M0, rfl, by simp [nx]⟩
      | cons x r =>
        rw [stepNext_cons]
        obtain ⟨M, h1, h2⟩ := ih x r M0 (by simp at hr; omega) h0' (by simp at hb'; omega)
        exact ⟨M, h1, by simp [nx, h2]⟩
    have A : ∀ c : Int, 0 ≤ c → c ≤ 4 → (m0 + ix c).val = m0.val + c := by
      intro c hc0 hc4
      have : (ix c).val = c := ix_val c (by omega) (by omega)
      rw [add_val _ _ (by omega) (by omega), this]
    have L := wrSpec_length k
    rcases rest with _ | ⟨b, r⟩
    · simp only [wrSpec, cntLoop, List.isEmpty_nil, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte] at hb ⊢
      by_cases h1 : a < 0x80
      · simp only [h1, ↓reduceIte]
        exact ⟨_, rfl, by rw [A 1 (by omega) (by omega)]; simp [nx]⟩
      · by_cases h2 : a < 0x800
        · simp only [h1, h2, ↓reduceIte]
          exact ⟨_, rfl, by rw [A 2 (by omega) (by omega)]; simp [nx]⟩
        · simp only [h1, h2, ↓reduceIte]
          exact ⟨_, rfl, by rw [A 3 (by omega) (by omega)]; simp [nx]⟩
    · have hk' : r.length < k := by simp at hk; omega
      have Lb := L b r
      simp only [List.length_cons] at hb hk
      simp only [wrSpec, cntLoop, List.isEmpty_cons, Bool.not_false, Bool.and_true, nextB,
        bind, Except.bind]
      by_cases h1 : a < 0x80
      · simp only [h1, ↓reduceIte]
        obtain ⟨M, e1, e2⟩ := N _ (b :: r) (by simp; omega) (by rw [A 1 (by omega) (by omega)]; omega)
          (by rw [A 1 (by omega) (by omega)]; simp; omega)
        exact ⟨M, e1, by rw [e2, A 1 (by omega) (by omega)]; simp; omega⟩
      · by_cases h2 : a < 0x800
        · simp only [h1, h2, ↓reduceIte]
          obtain ⟨M, e1, e2⟩ := N _ (b :: r) (by simp; omega) (by rw [A 2 (by omega) (by omega)]; omega)
            (by rw [A 2 (by omega) (by omega)]; simp; omega)
          exact ⟨M, e1, by rw [e2, A 2 (by omega) (by omega)]; simp; omega⟩
        · by_cases h3 : ((a &&& 0xfc00) == 0xd800) = true
          · by_cases h4 : ((b &&& 0xfc00) == 0xdc00) = true
            · simp only [h1, h2, h3, h4, ↓reduceIte]
              obtain ⟨M, e1, e2⟩ := N _ r (by omega) (by rw [A 4 (by omega) (by omega)]; omega)
                (by rw [A 4 (by omega) (by omega)]; omega)
              exact ⟨M, e1, by rw [e2, A 4 (by omega) (by omega)]; simp; omega⟩
            · simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]
              obtain ⟨M, e1, e2⟩ := ih b r _ hk' (by rw [A 3 (by omega) (by omega)]; omega)
                (by rw [A 3 (by omega) (by omega)]; omega)
              exact ⟨M, e1, by rw [e2, A 3 (by omega) (by omega)]; simp; omega⟩
          · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true]
            obtain ⟨M, e1, e2⟩ := N _ (b :: r) (by simp; omega) (by rw [A 3 (by omega) (by omega)]; omega)
              (by rw [A 3 (by omega) (by omega)]; simp; omega)
            exact ⟨M, e1, by rw [e2, A 3 (by omega) (by omega)]; simp; omega⟩

/-- `transcode(UInt8, src::AbstractVector{UInt16})` on a nonempty vector: the first
loop allocates exactly the bytes `wrSpec` that the second loop writes, and every
write is within the allocation. Vectors are shorter than `2^60` elements
(`2^61` bytes), far beyond any addressable memory. -/
theorem transcode8_cons (a : UInt16) (rest : List UInt16) (h : rest.length + 1 < 2 ^ 60) :
    ∃ M : JInt64, M.val = (wrSpec (rest.length + 1) a rest).length ∧
      transcode8 (a :: rest) = .ok ⟨M, wrSpec (rest.length + 1) a rest⟩ := by
  obtain ⟨M, e1, e2⟩ := cntLoop_spec (rest.length + 1) a rest (ix 0) (by omega) (by simp)
    (by simp; omega)
  refine ⟨M, by simpa using e2, ?_⟩
  have W := wrLoop_spec M (rest.length + 1) a rest [] (by omega) (by simp [e2])
  simp only [transcode8, List.length_cons, e1, W, bind, Except.bind, List.nil_append]

/-- `transcode(UInt8, ::AbstractVector{UInt16})` returns for every input, writes
within `StringVector(m)`, and initializes all `m` bytes. -/
theorem transcode8_complete (src : List UInt16) (h : src.length < 2 ^ 60) :
    ∃ o : Out, transcode8 src = .ok o ∧ (o.written.length : Int) = o.m.val := by
  cases src with
  | nil => exact ⟨⟨ix 0, []⟩, rfl, by simp⟩
  | cons a rest =>
    obtain ⟨M, e1, e2⟩ := transcode8_cons a rest (by simpa using h)
    exact ⟨_, e2, by simp [e1]⟩

end JuliaLean.Transcode
