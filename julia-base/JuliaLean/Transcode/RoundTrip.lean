import JuliaLean.Transcode.Tables
import JuliaLean.Transcode.Utf16

/-!
# UTF-8 → UTF-16 → UTF-8 round trip for well-formed strings

`transcode(UInt16, ...)` handles a well-formed character in one loop iteration,
producing `units ch`; `transcode(UInt8, ...)` turns those units back into the
character's bytes in one iteration. Induction over the characters gives the
round trip, the well-formedness of the UTF-16 data and its length.
-/

namespace JuliaLean.Transcode

open JuliaLean.Strings

@[simp] theorem List.head!_cons {α : Type} [Inhabited α] (a : α) (l : List α) :
    (a :: l).head! = a := rfl

/-- The UTF-16 code units `transcode(UInt16, ...)` produces for one well-formed character. -/
def units : List UInt8 → List UInt16
  | [a] => [a.toUInt16]
  | [a, b] => [dec2 a b]
  | [a, b, c] => [dec3 a b c]
  | [a, b, c, d] => [dec4hi a b c, dec4lo c d]
  | _ => []

theorem wf_cases (ch : List UInt8) (hw : wfChar ch = true) :
    (∃ a, ch = [a]) ∨ (∃ a b, ch = [a, b]) ∨ (∃ a b c, ch = [a, b, c]) ∨
      (∃ a b c d, ch = [a, b, c, d]) := by
  match ch, hw with
  | [a], _ => exact .inl ⟨a, rfl⟩
  | [a, b], _ => exact .inr (.inl ⟨a, b, rfl⟩)
  | [a, b, c], _ => exact .inr (.inr (.inl ⟨a, b, c, rfl⟩))
  | [a, b, c, d], _ => exact .inr (.inr (.inr ⟨a, b, c, d, rfl⟩))
  | [], hw => simp [wfChar] at hw
  | _ :: _ :: _ :: _ :: _ :: _, hw => simp [wfChar] at hw

theorem wf_ne_nil {ch : List UInt8} (hw : wfChar ch = true) : ch ≠ [] := by
  rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;> simp

theorem units_length {ch : List UInt8} (hw : wfChar ch = true) :
    1 ≤ (units ch).length ∧ (units ch).length ≤ ch.length := by
  rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;>
    simp [units]

/-- One iteration of `transcode(UInt16, ...)` consumes exactly one well-formed character. -/
theorem u16_chunk (ch : List UInt8) (hw : wfChar ch = true) (k : Nat) (r : List UInt8)
    (dst : List UInt16) :
    u16Loop (k + 1) ch.head! (ch.tail ++ r) dst = stepNext (u16Loop k) (dst ++ units ch) r := by
  rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · obtain ⟨c1, -⟩ := facts1 a hw
    simp only [u16Loop, List.head!_cons, List.tail_cons, List.nil_append, c1, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, units]
  · obtain ⟨c1, c2, c3, -⟩ := facts2 a b hw
    simp only [u16Loop, List.head!_cons, List.tail_cons, List.cons_append, List.nil_append,
      List.isEmpty_cons, Bool.not_false, Bool.true_and, c1, nextB, bind, Except.bind, c2,
      Bool.false_eq_true, ↓reduceIte, c3, units]
  · obtain ⟨c1, c2, c3, c4, c5, -⟩ := facts3 a b c hw
    simp only [u16Loop, List.head!_cons, List.tail_cons, List.cons_append, List.nil_append,
      List.isEmpty_cons, Bool.not_false, Bool.true_and, c1, nextB, bind, Except.bind, c2,
      Bool.false_eq_true, ↓reduceIte, c3, c4, c5, units]
  · rw [wfChar4] at hw
    have hab : (isC c && pre4 a b) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact ⟨hw.1.1, hw.2⟩
    have hcd : (isC c && isC d) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact hw.1
    obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := facts4a a b c hab
    obtain ⟨d1, -⟩ := facts4b c d hcd
    simp only [u16Loop, List.head!_cons, List.tail_cons, List.cons_append, List.nil_append,
      List.isEmpty_cons, Bool.not_false, Bool.true_and, c1, nextB, bind, Except.bind, c2,
      Bool.false_eq_true, ↓reduceIte, c3, c4, c5, d1, c6, units]

theorem flatten_nil_of_wf : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    cs.flatten = [] → cs = [] := by
  intro cs h e
  cases cs with
  | nil => rfl
  | cons ch cs =>
    have := wf_ne_nil (h ch (by simp))
    simp at e; exact absurd e.1 this

theorem length_le_flatten : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    cs.length ≤ (cs.flatMap units).length ∧ (cs.flatMap units).length ≤ cs.flatten.length := by
  intro cs h
  induction cs with
  | nil => simp
  | cons ch cs ih =>
    have := units_length (h ch (by simp))
    have ih := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatten_cons, List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem flatMap_nil_of_wf (cs : List (List UInt8)) (h : ∀ c ∈ cs, wfChar c = true)
    (e : cs.flatMap units = []) : cs = [] := by
  have := (length_le_flatten cs h).1
  rw [e] at this
  cases cs with
  | nil => rfl
  | cons _ _ => simp at this

theorem u16Loop_chars : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    ∀ (k : Nat) (dst : List UInt16) (a : UInt8) (rest : List UInt8), cs.length ≤ k →
      cs.flatten = a :: rest → u16Loop k a rest dst = .ok (dst ++ cs.flatMap units) := by
  intro cs h
  induction cs with
  | nil => intro k dst a rest _ e; simp at e
  | cons ch cs ih =>
    intro k dst a rest hk e
    have hw := h ch (by simp)
    have hcs : ∀ c ∈ cs, wfChar c = true := fun c hc => h c (by simp [hc])
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨x, bs, rfl⟩ : ∃ x bs, ch = x :: bs := by
      cases ch with
      | nil => exact absurd rfl (wf_ne_nil hw)
      | cons x bs => exact ⟨x, bs, rfl⟩
    simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have := u16_chunk _ hw k cs.flatten dst
    simp only [List.head!_cons, List.tail_cons] at this
    rw [this]
    cases hf : cs.flatten with
    | nil =>
      rw [flatten_nil_of_wf cs hcs hf, stepNext_nil]
      simp
    | cons y r =>
      rw [stepNext_cons, ih hcs k _ y r (by simp at hk; omega) hf]
      simp

/-- `transcode(UInt16, ...)` on well-formed UTF-8 produces the units of each character. -/
theorem transcode16_valid (cs : List (List UInt8)) (h : ∀ c ∈ cs, wfChar c = true) :
    transcode16 cs.flatten = .ok (cs.flatMap units) := by
  cases hf : cs.flatten with
  | nil => rw [flatten_nil_of_wf cs h hf]; rfl
  | cons a rest =>
    have L := length_le_flatten cs h
    rw [hf] at L
    simp only [transcode16]
    rw [u16Loop_chars cs h _ [] a rest (by omega) hf, List.nil_append]

/-- One iteration of `transcode(UInt8, ...)` turns the units of a well-formed
character back into its bytes. -/
theorem wr_chunk (ch : List UInt8) (hw : wfChar ch = true) (k : Nat) (r : List UInt16) :
    wrSpec (k + 1) (units ch).head! ((units ch).tail ++ r) = ch ++ nx (wrSpec k) r := by
  rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · obtain ⟨-, e1, e2, -⟩ := facts1 a hw
    simp only [units, wrSpec, List.head!_cons, List.tail_cons, List.nil_append, e1, ↓reduceIte, e2]
  · obtain ⟨-, -, -, e1, e2, e3, -⟩ := facts2 a b hw
    simp only [units, wrSpec, List.head!_cons, List.tail_cons, List.nil_append, e1, e2,
      ↓reduceIte, e3]
  · obtain ⟨-, -, -, -, -, e1, e2, e3, -, e4, -⟩ := facts3 a b c hw
    simp only [units, wrSpec, List.head!_cons, List.tail_cons, List.nil_append, e1, e2, e3,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, e4]
  · rw [wfChar4] at hw
    have hab : (isC c && pre4 a b) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact ⟨hw.1.1, hw.2⟩
    have hcd : (isC c && isC d) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact hw.1
    obtain ⟨-, -, -, -, -, -, e1, e2, e3, f1, f2, f3, -⟩ := facts4a a b c hab
    obtain ⟨-, g1, g2, g3, g4, -⟩ := facts4b c d hcd
    simp only [units, wrSpec, List.head!_cons, List.tail_cons, List.cons_append, List.nil_append,
      e1, e2, e3, List.isEmpty_cons, Bool.not_false, Bool.and_true, ↓reduceIte, g1]
    simp only [enc4, f1, f2, f3, g2, g3, g4]
    rfl

theorem wrSpec_chars : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    ∀ (k : Nat) (u : UInt16) (us : List UInt16), cs.length ≤ k →
      cs.flatMap units = u :: us → wrSpec k u us = cs.flatten := by
  intro cs h
  induction cs with
  | nil => intro k u us _ e; simp at e
  | cons ch cs ih =>
    intro k u us hk e
    have hw := h ch (by simp)
    have hcs : ∀ c ∈ cs, wfChar c = true := fun c hc => h c (by simp [hc])
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨x, vs, hx⟩ : ∃ x vs, units ch = x :: vs := by
      have := (units_length hw).1
      cases hu : units ch with
      | nil => rw [hu] at this; simp at this
      | cons x vs => exact ⟨x, vs, rfl⟩
    simp only [List.flatMap_cons, hx, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have := wr_chunk ch hw k (cs.flatMap units)
    rw [hx] at this
    simp only [List.head!_cons, List.tail_cons] at this
    rw [this, List.flatten_cons]
    congr 1
    cases hf : cs.flatMap units with
    | nil =>
      rw [flatMap_nil_of_wf cs hcs hf]; rfl
    | cons y r =>
      simp only [nx]
      exact ih hcs k y r (by simp at hk; omega) hf

/-- The round trip through `transcode(UInt16, ...)` and `transcode(UInt8, ...)`
returns the original bytes, and `transcode(UInt8, ...)` allocates exactly them. -/
theorem roundtrip16 (cs : List (List UInt8)) (h : ∀ c ∈ cs, wfChar c = true)
    (hn : cs.flatten.length < 2 ^ 60) :
    transcode16 cs.flatten = .ok (cs.flatMap units) ∧
      ∃ o : Out, transcode8 (cs.flatMap units) = .ok o ∧ o.written = cs.flatten ∧
        o.m.val = cs.flatten.length := by
  refine ⟨transcode16_valid cs h, ?_⟩
  have L := length_le_flatten cs h
  cases hu : cs.flatMap units with
  | nil =>
    rw [flatMap_nil_of_wf cs h hu]
    exact ⟨⟨ix 0, []⟩, rfl, rfl, rfl⟩
  | cons u us =>
    rw [hu, List.length_cons] at L
    obtain ⟨M, e1, e2⟩ := transcode8_cons u us (by omega)
    have W := wrSpec_chars cs h (us.length + 1) u us L.1 hu
    rw [W] at e1 e2
    exact ⟨_, e2, rfl, e1⟩

/-- The UTF-16 data produced for well-formed characters is well-formed. -/
theorem wf16_units : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    wf16 (cs.flatMap units) = true := by
  intro cs h
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    have hw := h ch (by simp)
    have ih := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatMap_cons]
    rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · obtain ⟨-, -, -, e1, e2, -⟩ := facts1 a hw
      simp only [units, List.cons_append, List.nil_append]
      cases hr : List.flatMap units cs <;> simp [wf16, e1, e2] <;> simp_all
    · obtain ⟨-, -, -, -, -, -, e1, e2, -⟩ := facts2 a b hw
      simp only [units, List.cons_append, List.nil_append]
      cases hr : List.flatMap units cs <;> simp [wf16, e1, e2] <;> simp_all
    · obtain ⟨-, -, -, -, -, -, -, e1, e2, -⟩ := facts3 a b c hw
      have e1' : isHigh (dec3 a b c) = false := e1
      simp only [units, List.cons_append, List.nil_append]
      cases hr : List.flatMap units cs <;> simp [wf16, e1', e2] <;> simp_all
    · rw [wfChar4] at hw
      have hab : (isC c && pre4 a b) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact ⟨hw.1.1, hw.2⟩
      have hcd : (isC c && isC d) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact hw.1
      obtain ⟨-, -, -, -, -, -, -, -, e3, -⟩ := facts4a a b c hab
      obtain ⟨-, g1, -⟩ := facts4b c d hcd
      have h1 : isHigh (dec4hi a b c) = true := e3
      have h2 : isLow (dec4lo c d) = true := g1
      simp only [units, List.cons_append, List.nil_append, wf16, h1, h2, ↓reduceIte, Bool.true_and]
      exact ih

end JuliaLean.Transcode
