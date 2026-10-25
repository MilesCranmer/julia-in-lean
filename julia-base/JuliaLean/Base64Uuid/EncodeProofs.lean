import JuliaLean.Base64Uuid.Props

/-!
`Base64EncodePipe`: every sequence of writes encodes like `base64encode` of the
concatenated bytes. The pipe's state after any writes is the encoding of the complete
triplets written so far plus the at most two bytes of the incomplete one.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The characters of the complete triplets of `xs`. -/
def encFull : List Byte → List Byte
  | x1 :: x2 :: x3 :: rest => enc4 x1 x2 x3 ++ encFull rest
  | _ => []

theorem encFull_append : ∀ (a b : List Byte), a.length % 3 = 0 → encFull (a ++ b) = encFull a ++ encFull b
  | [], b, _ => by simp [encFull]
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | x1 :: x2 :: x3 :: a, b, h => by
    simp only [List.cons_append, encFull, List.append_assoc]
    rw [encFull_append a b (by simp at h; omega)]

theorem encLoop_spec : ∀ (rem : List Byte) (b1 b2 b3 : Byte) (out chunk : List Byte),
    ∃ q r, rem = q ++ r ∧ q.length % 3 = 0 ∧ r.length < 3 ∧
      (encLoop b1 b2 b3 out chunk rem).2.2 = r ∧
      (encLoop b1 b2 b3 out chunk rem).1 ++ (encLoop b1 b2 b3 out chunk rem).2.1 =
        out ++ chunk ++ enc4 b1 b2 b3 ++ encFull q ∧
      (encLoop b1 b2 b3 out chunk rem).2.1 ≠ []
  | [], b1, b2, b3, out, chunk =>
    ⟨[], [], rfl, rfl, by simp, rfl, by simp [encLoop, encFull], by simp [encLoop, enc4]⟩
  | [x], b1, b2, b3, out, chunk =>
    ⟨[], [x], rfl, rfl, by simp, rfl, by simp [encLoop, encFull], by simp [encLoop, enc4]⟩
  | [x, y], b1, b2, b3, out, chunk =>
    ⟨[], [x, y], rfl, rfl, by simp, rfl, by simp [encLoop, encFull], by simp [encLoop, enc4]⟩
  | x1 :: x2 :: x3 :: rem, b1, b2, b3, out, chunk => by
    simp only [encLoop]
    split
    · obtain ⟨q, r, hq, hq3, hr, h1, h2, h3⟩ := encLoop_spec rem x1 x2 x3 (out ++ (chunk ++ enc4 b1 b2 b3)) []
      refine ⟨x1 :: x2 :: x3 :: q, r, by simp [hq], by simp; omega, hr, h1, ?_, h3⟩
      rw [h2]; simp [encFull, List.append_assoc]
    · obtain ⟨q, r, hq, hq3, hr, h1, h2, h3⟩ := encLoop_spec rem x1 x2 x3 out (chunk ++ enc4 b1 b2 b3)
      refine ⟨x1 :: x2 :: x3 :: q, r, by simp [hq], by simp; omega, hr, h1, ?_, h3⟩
      rw [h2]; simp [encFull, List.append_assoc]

theorem encMain_spec (full : List Byte) (hf : full.length % 3 = 0) (b1 b2 b3 : Byte) (rem : List Byte) :
    ∃ full' tail', full ++ [b1, b2, b3] ++ rem = full' ++ tail' ∧ full'.length % 3 = 0 ∧
      tail'.length ≤ 2 ∧ encMain (encFull full) b1 b2 b3 rem = ⟨encFull full', tail'⟩ := by
  obtain ⟨q, r, hq, hq3, hr, h1, h2, h3⟩ := encLoop_spec rem b1 b2 b3 (encFull full) []
  refine ⟨full ++ [b1, b2, b3] ++ q, r, by simp [hq], by simp; omega, by omega, ?_⟩
  simp only [encMain]
  generalize hl : encLoop b1 b2 b3 (encFull full) [] rem = l at h1 h2 h3
  obtain ⟨o, c, r'⟩ := l
  simp only at h1 h2 h3 ⊢
  have hc : c.length > 0 := List.length_pos_iff.mpr h3
  simp only [hc, ↓reduceIte, h1, h2, List.append_nil]
  rw [encFull_append _ _ (by simp; omega), encFull_append _ _ hf]
  simp [encFull]

/-- `unsafe_write` keeps the pipe in the shape "encoded complete triplets, leftover
bytes", for any buffer of at most three bytes. -/
theorem unsafeWrite_spec (full buf xs : List Byte) (hf : full.length % 3 = 0) (hb : buf.length ≤ 3) :
    ∃ full' tail', full ++ buf ++ xs = full' ++ tail' ∧ full'.length % 3 = 0 ∧ tail'.length ≤ 2 ∧
      (unsafeWrite ⟨encFull full, buf⟩ xs).1 = ⟨encFull full', tail'⟩ := by
  match buf, xs with
  | [], [] => exact ⟨full, [], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [], [a] => exact ⟨full, [a], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [], [a, b] => exact ⟨full, [a, b], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [], a :: b :: c :: r =>
    obtain ⟨f', t', h1, h2, h3, h4⟩ := encMain_spec full hf a b c r
    exact ⟨f', t', by simpa using h1, h2, h3, by simp [unsafeWrite, loadtriplet, h4]⟩
  | [c1], [] => exact ⟨full, [c1], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [c1], [a] => exact ⟨full, [c1, a], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [c1], a :: b :: r =>
    obtain ⟨f', t', h1, h2, h3, h4⟩ := encMain_spec full hf c1 a b r
    exact ⟨f', t', by simpa using h1, h2, h3, by simp [unsafeWrite, loadtriplet, h4]⟩
  | [c1, c2], [] => exact ⟨full, [c1, c2], by simp, hf, by simp, by simp [unsafeWrite, loadtriplet]⟩
  | [c1, c2], a :: r =>
    obtain ⟨f', t', h1, h2, h3, h4⟩ := encMain_spec full hf c1 c2 a r
    exact ⟨f', t', by simpa using h1, h2, h3, by simp [unsafeWrite, loadtriplet, h4]⟩
  | [c1, c2, c3], xs =>
    obtain ⟨f', t', h1, h2, h3, h4⟩ := encMain_spec full hf c1 c2 c3 xs
    exact ⟨f', t', by simpa using h1, h2, h3, by simp [unsafeWrite, loadtriplet, h4]⟩
  | _ :: _ :: _ :: _ :: _, _ => exact absurd hb (by simp)

/-- The pipe invariant. -/
def EInv (pipe : EPipe) (d : List Byte) : Prop :=
  ∃ full tail, d = full ++ tail ∧ full.length % 3 = 0 ∧ tail.length ≤ 2 ∧ pipe = ⟨encFull full, tail⟩

theorem applyWrite_inv (pipe : EPipe) (d : List Byte) (op : WriteOp) (h : EInv pipe d) :
    EInv (applyWrite pipe op) (d ++ op.data) := by
  obtain ⟨full, tail, hd, hf, ht, hp⟩ := h
  subst hp
  cases op with
  | bytes xs =>
    obtain ⟨f', t', h1, h2, h3, h4⟩ := unsafeWrite_spec full tail xs hf (by omega)
    exact ⟨f', t', by simp [WriteOp.data, hd, ← h1], h2, h3, h4⟩
  | byte x =>
    simp only [applyWrite, writeByte]
    split
    · rename_i h3
      obtain ⟨f', t', h1, h2, h3', h4⟩ := unsafeWrite_spec full (tail ++ [x]) [] hf (by simp; omega)
      exact ⟨f', t', by simp [WriteOp.data, hd, ← h1], h2, h3', h4⟩
    · rename_i h3
      simp only [List.length_append, List.length_singleton, beq_iff_eq] at h3
      exact ⟨full, tail ++ [x], by simp [WriteOp.data, hd], hf, by simp; omega, rfl⟩

theorem foldl_inv : ∀ (ops : List WriteOp) (pipe : EPipe) (d : List Byte), EInv pipe d →
    EInv (ops.foldl applyWrite pipe) (d ++ ops.flatMap WriteOp.data)
  | [], pipe, d, h => by simpa using h
  | op :: ops, pipe, d, h => by
    simp only [List.foldl, List.flatMap_cons]
    rw [← List.append_assoc]
    exact foldl_inv ops _ _ (applyWrite_inv pipe d op h)

theorem close_split (out t : List Byte) (ht : t.length ≤ 2) : close ⟨out, t⟩ = out ++ close ⟨[], t⟩ := by
  match t, ht with
  | [], _ => simp [close, loadtriplet]
  | [a], _ => simp [close, loadtriplet]
  | [a, b], _ => simp [close, loadtriplet]

theorem split3_unique (a b c d : List Byte) (h : a ++ b = c ++ d) (ha : a.length % 3 = 0)
    (hc : c.length % 3 = 0) (hb : b.length ≤ 2) (hd : d.length ≤ 2) : a = c ∧ b = d := by
  have hl : a.length = c.length := by
    have := congrArg List.length h
    simp at this; omega
  exact List.append_inj h hl

/-- `base64encode(x)` is the encoding of the complete triplets of `x` followed by what
`close` writes for the leftover bytes. -/
theorem base64encode_split (x : List Byte) :
    ∃ full tail, x = full ++ tail ∧ full.length % 3 = 0 ∧ tail.length ≤ 2 ∧
      base64encode x = encFull full ++ close ⟨[], tail⟩ := by
  obtain ⟨f', t', h1, h2, h3, h4⟩ := unsafeWrite_spec [] [] x rfl (by simp)
  refine ⟨f', t', by simpa using h1, h2, h3, ?_⟩
  simp only [base64encode, EPipe.new]
  have : (⟨[], []⟩ : EPipe) = ⟨encFull [], []⟩ := rfl
  rw [this, h4, close_split _ _ h3]

theorem encodeStreamSplit_proven : EncodeStreamSplit := by
  intro ops
  obtain ⟨full, tail, hd, hf, ht, hp⟩ := foldl_inv ops EPipe.new [] ⟨[], [], rfl, rfl, by simp, rfl⟩
  obtain ⟨full2, tail2, hd2, hf2, ht2, he⟩ := base64encode_split (ops.flatMap WriteOp.data)
  simp only [List.nil_append] at hd
  obtain ⟨rfl, rfl⟩ := split3_unique full tail full2 tail2 (by rw [← hd, ← hd2]) hf hf2 ht ht2
  simp only [encodeStream]
  rw [hp, close_split _ _ ht, he]

end JuliaLean.Base64Uuid
