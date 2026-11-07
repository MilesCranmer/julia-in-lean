import JuliaLean.Proofs.base.io.IOCovCommon
import JuliaLean.base.iobuffer

set_option linter.unusedSimpArgs false

/-!
Models of the generic `IO` methods of `base/io.jl` at master `bbfa0ce4150`.

A generic stream is a `St`: the bytes already consumed (`pre`), the unread bytes
(`inp`), the `mark` field (`-1` when unmarked), the bytes written (`out`), whether
the concrete type supports `seek`, and whether it is open. The methods that each
`IO` subtype must define (`read(s, UInt8)`, `write(s, ::UInt8)`, `eof`, `seek`,
`close`, ...) are the primitive operations on `St`; the generic methods of
`io.jl` are modelled on top of them, mirroring their loops.
-/

namespace JuliaLean.IOCov.Io

open JuliaLean JuliaLean.IOCov

/-- The UTF-8 structure of one character: a lead byte announcing `bs.length` bytes and
continuation bytes `0b10xxxxxx`. -/
def IsUtf8Char (bs : Bytes) : Prop :=
  match bs with
  | [b] => b.toNat < 0x80
  | [b0, b1] => 0xc0 ≤ b0.toNat ∧ b0.toNat < 0xe0 ∧ b1.toNat / 64 = 2
  | [b0, b1, b2] => 0xe0 ≤ b0.toNat ∧ b0.toNat < 0xf0 ∧ b1.toNat / 64 = 2 ∧ b2.toNat / 64 = 2
  | [b0, b1, b2, b3] => 0xf0 ≤ b0.toNat ∧ b0.toNat < 0xf8 ∧ b1.toNat / 64 = 2 ∧ b2.toNat / 64 = 2 ∧
      b3.toNat / 64 = 2
  | _ => False

/-! ## Properties -/

theorem readByte_cons (s : St) (b : UInt8) (r : Bytes) (h : s.inp = b :: r) :
    readByte s = .ok (b, { s with pre := s.pre ++ [b], inp := r }) := by
  simp [readByte, h]

theorem unsafeWrite_spec (bs : Bytes) : ∀ s : St,
    unsafeWrite s bs = (bs.length, { s with out := s.out ++ bs }) := by
  induction bs with
  | nil => intro s; simp [unsafeWrite]
  | cons b bs ih =>
    intro s
    simp only [unsafeWrite, writeByte, ih]
    simp [Nat.add_comm]

theorem unsafeRead_spec (n : Nat) : ∀ s : St,
    unsafeRead n s = if n ≤ s.inp.length then
      .ok (s.inp.take n, { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n })
    else .error .eofError := by
  induction n with
  | zero => intro s; simp [unsafeRead]
  | succ n ih =>
    intro s
    cases h : s.inp with
    | nil => simp [unsafeRead, readByte, h, bind, Except.bind]
    | cons b r =>
      simp only [unsafeRead, readByte, h, bind, Except.bind, ih]
      by_cases hn : n ≤ r.length
      · simp [hn, pure, Except.pure]
      · simp [hn, pure, Except.pure]

theorem leVal_leBytes (n : Nat) : ∀ x, x < 2 ^ (8 * n) → leVal (leBytes n x) = x := by
  induction n with
  | zero => intro x hx; simp at hx; simp [leBytes, leVal, hx]
  | succ n ih =>
    intro x hx
    have h1 : x / 256 < 2 ^ (8 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by
        rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      omega
    simp only [leBytes, leVal, ih _ h1]
    have : (x % 256).toUInt8.toNat = x % 256 := by
      simp [Nat.toUInt8, UInt8.toNat_ofNat]
    rw [this]; omega

theorem leBytes_length (n : Nat) : ∀ x, (leBytes n x).length = n := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; simp [leBytes, ih]

theorem toUInt8_mod (u : Nat) (b : UInt8) (h : u % 256 = b.toNat) : (u % 256).toUInt8 = b := by
  apply UInt8.toNat.inj
  simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega

theorem readGo_spec (nb : Nat) : ∀ len (s : St), nb * len ≤ s.inp.length →
    readArrayBang.go nb len s = .ok ((List.range len).map (fun i => (s.inp.drop (i * nb)).take nb),
      { s with pre := s.pre ++ s.inp.take (nb * len), inp := s.inp.drop (nb * len) }) := by
  intro len
  induction len with
  | zero => intro s _; simp [readArrayBang.go]
  | succ k ih =>
    intro s h
    have h1 : nb ≤ s.inp.length := by
      have : nb ≤ nb * (k + 1) := Nat.le_mul_of_pos_right nb (by omega)
      omega
    simp only [readArrayBang.go, bind, Except.bind, unsafeRead_spec, if_pos h1]
    have h2 : nb * k ≤ (s.inp.drop nb).length := by
      simp; rw [Nat.mul_succ] at h; omega
    rw [ih _ h2]
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map]
      simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]
    · simp [List.drop_drop, List.take_add, Nat.mul_succ, Nat.add_comm]

theorem writeCharLoop_step (s : St) (u n : Nat) (b : UInt8) (hb : u % 256 = b.toNat) :
    writeCharLoop s u n = if u / 256 = 0 then (n + 1, { s with out := s.out ++ [b] })
      else writeCharLoop { s with out := s.out ++ [b] } (u / 256) (n + 1) := by
  rw [writeCharLoop]; simp [writeByte, toUInt8_mod u b hb]

theorem lo_ascii (b : UInt8) (h : b.toNat < 0x80) : leadingOnes b = 0 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
theorem lo_two (b : UInt8) (h1 : 0xc0 ≤ b.toNat) (h2 : b.toNat < 0xe0) : leadingOnes b = 2 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]
theorem lo_three (b : UInt8) (h1 : 0xe0 ≤ b.toNat) (h2 : b.toNat < 0xf0) : leadingOnes b = 3 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]
theorem lo_four (b : UInt8) (h1 : 0xf0 ≤ b.toNat) (h2 : b.toNat < 0xf8) : leadingOnes b = 4 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]


theorem peekByte_cons (s : St) (b : UInt8) (r : Bytes) (hs : s.seekable = true) (h : s.inp = b :: r) :
    peekByte s = .ok (b, { s with mark := -1 }) := by
  cases s
  simp_all [peekByte, peek, mark, readByte, reset, ismarked, seek, position, bind, Except.bind,
    pure, Except.pure]

theorem readCharLoop_cont (sh : Nat) (shs : List Nat) (c : Nat) (st : St) (b : UInt8) (r : Bytes)
    (hs : st.seekable = true) (h : st.inp = b :: r) (hb : b.toNat / 64 = 2) :
    readCharLoop (sh :: shs) c st = readCharLoop shs (c + b.toNat * 2 ^ sh)
      { st with mark := -1, pre := st.pre ++ [b], inp := r } := by
  simp [readCharLoop, eof, h, peekByte_cons st b r hs h, hb, readByte]

theorem takeWhile_ne0 (b : Bytes) (hb : 0 ∉ b) : b.takeWhile (· != 0) = b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := fun e => hb (e ▸ List.mem_cons_self ..)
    simp [List.takeWhile_cons, hx, ih (fun m => hb (List.mem_cons_of_mem _ m))]

theorem writeFromIO_go (k : Nat) : ∀ fuel n (to frm : St), frm.inp.length < fuel →
    writeFromIO.go k fuel n to frm =
      (n + frm.inp.length, { to with out := to.out ++ frm.inp }, { frm with pre := frm.pre ++ frm.inp, inp := [] }) := by
  intro fuel
  induction fuel with
  | zero => intro n to frm h; omega
  | succ f ih =>
    intro n to frm h
    cases hi : frm.inp with
    | nil => cases frm; simp_all [writeFromIO.go, eof]
    | cons b r =>
      simp only [writeFromIO.go, eof, hi, List.isEmpty_cons, Bool.false_eq_true, if_false, unsafeWrite_spec]
      rw [ih]
      · simp only [Prod.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_drop, List.length_take, List.length_cons]
          have : 1 ≤ max k 1 := Nat.le_max_right _ _
          rw [Nat.min_def]; split <;> omega
        · simp [List.take_append_drop]
        · simp [List.take_append_drop]
      · simp only [List.length_drop, List.length_cons]; rw [hi] at h; simp at h
        have : 1 ≤ max k 1 := Nat.le_max_right _ _
        omega

theorem packChar_one (b : UInt8) : packChar [b] = b.toNat * 2 ^ 24 := by simp [packChar]

theorem foldl_bytes (g : Nat × St → UInt8 → Nat × St)
    (hg : ∀ acc x, g acc x = (acc.1 + 1, { acc.2 with out := acc.2.out ++ [x] })) (xs : Bytes) :
    ∀ n st, xs.foldl g (n, st) = (n + xs.length, { st with out := st.out ++ xs }) := by
  induction xs with
  | nil => intro n st; simp
  | cons x xs ih =>
    intro n st
    simp only [List.foldl_cons, hg]
    rw [ih]
    refine Prod.ext ?_ ?_ <;> simp <;> omega

theorem foldl_chunks (g : Nat × St → Bytes → Nat × St)
    (hg : ∀ acc e, g acc e = (acc.1 + e.length, { acc.2 with out := acc.2.out ++ e })) (es : List Bytes) :
    ∀ n st, es.foldl g (n, st) = (n + es.flatten.length, { st with out := st.out ++ es.flatten }) := by
  induction es with
  | nil => intro n st; simp
  | cons e es ih =>
    intro n st
    simp only [List.foldl_cons, hg]
    rw [ih]
    refine Prod.ext ?_ ?_ <;> simp <;> omega

/-! ### `SystemError` and trivial methods -/

/-- `SystemError(p, e, extrainfo)` stores its fields, converting `e` to `Int32`. -/
def SystemError3Correct : Prop :=
  (∀ p e x, -2147483648 ≤ e → e ≤ 2147483647 → systemError3 p e x = .ok ⟨p, e, x⟩) ∧
  (∀ p e x, (e < -2147483648 ∨ 2147483647 < e) → systemError3 p e x = .error (.jl (.inexactError "Int32")))
theorem systemError3Correct : SystemError3Correct := by
  refine ⟨?_, ?_⟩
  · intro p e x h1 h2
    simp [systemError3, toInt_i32 e h1 h2, bind, Except.bind, pure, Except.pure]
  · intro p e x h
    rw [systemError3, toInt_err .i32 e (by simp; omega)]; rfl

/-- `SystemError(p, e)` has `extrainfo === nothing`. -/
def SystemError2Correct : Prop :=
  ∀ p e, -2147483648 ≤ e → e ≤ 2147483647 → systemError2 p e = .ok ⟨p, e, none⟩
theorem systemError2Correct : SystemError2Correct := fun p e h1 h2 => systemError3Correct.1 p e none h1 h2

/-- `SystemError(p)` records the current `errno` and no extra information. -/
def SystemError1Correct : Prop :=
  ∀ errno p, -2147483648 ≤ errno → errno ≤ 2147483647 → systemError1 errno p = .ok ⟨p, errno, none⟩
theorem systemError1Correct : SystemError1Correct := fun errno p h1 h2 => systemError3Correct.1 p errno none h1 h2

/-- `buffer_writes(x::IO, bufsize)` returns the stream unchanged. -/
def BufferWritesIdentity : Prop := ∀ s n, bufferWrites s n = s
theorem bufferWritesIdentity : BufferWritesIdentity := fun _ _ => rfl

/-- `isreadable(io::IO)` and `iswritable(io::IO)` are `isopen(io)`. -/
def IsreadableOpen : Prop := ∀ s, isreadable s = s.isopen
theorem isreadableOpen : IsreadableOpen := fun _ => rfl
def IswritableOpen : Prop := ∀ s, iswritable s = s.isopen
theorem iswritableOpen : IswritableOpen := fun _ => rfl

/-- `isreadonly(s)` holds exactly for readable, non-writable streams. -/
def IsreadonlyCorrect : Prop := ∀ r w, isreadonly r w = true ↔ r = true ∧ w = false
theorem isreadonlyCorrect : IsreadonlyCorrect := by intro r w; cases r <;> cases w <;> decide

/-- The fallbacks throw: `read(s, Union{})`, `peek(s, Union{})`, byte I/O on a type without
it, `write(io, x)` for an unsupported `x`, and `read(s, T)` for an unsupported `T`. -/
def ReadUnionThrows : Prop := ∀ (α : Type) (s : St), (readUnion s : R α) = .error (.errorException "cannot read a value of type Union{}")
theorem readUnionThrows : ReadUnionThrows := fun _ _ => rfl
def PeekUnionThrows : Prop := ∀ (α : Type) (s : St), (peekUnion s : R α) = .error (.methodError "peek")
theorem peekUnionThrows : PeekUnionThrows := fun _ _ => rfl
def ByteIOFallbackThrows : Prop :=
  ∀ (α : Type) t, (readByteFallback t : R α) = .error (.errorException (t ++ " does not support byte I/O"))
theorem byteIOFallbackThrows : ByteIOFallbackThrows := fun _ _ => rfl
def WriteFallbackThrows : Prop := ∀ (α : Type), (writeFallback : R α) = .error (.methodError "write")
theorem writeFallbackThrows : WriteFallbackThrows := fun _ => rfl
def ReadTypeFallbackThrows : Prop := ∀ (α : Type) t, (readTypeFallback t : R α) =
  .error (.errorException ("The IO stream does not support reading objects of type " ++ t ++ "."))
theorem readTypeFallbackThrows : ReadTypeFallbackThrows := fun _ _ => rfl

/-- `writepartial(io, x)` is `write(io, x)` for a generic stream. -/
def WritepartialIsWrite : Prop := ∀ (α : Type) (w : St → α) s, writepartial w s = w s
theorem writepartialIsWrite : WritepartialIsWrite := fun _ _ _ => rfl

/-! ### Byte loops -/

/-- `unsafe_write(s, p, n)` appends the `n` bytes and returns `n`. -/
def UnsafeWriteAppends : Prop := ∀ s bs, unsafeWrite s bs = (bs.length, { s with out := s.out ++ bs })
theorem unsafeWriteAppends : UnsafeWriteAppends := fun s bs => unsafeWrite_spec bs s

/-- `unsafe_read(s, p, n)` stores the next `n` bytes, or throws `EOFError` if fewer remain. -/
def UnsafeReadNext : Prop :=
  (∀ n s, n ≤ s.inp.length → unsafeRead n s =
      .ok (s.inp.take n, { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n })) ∧
  (∀ n s, s.inp.length < n → unsafeRead n s = .error .eofError)
theorem unsafeReadNext : UnsafeReadNext := by
  refine ⟨?_, ?_⟩
  · intro n s h; rw [unsafeRead_spec, if_pos h]
  · intro n s h; rw [unsafeRead_spec, if_neg (by omega)]

/-- `unsafe_write(s, p::Ptr, n)` converts `n` to `UInt` and writes that many bytes;
`unsafe_write(s, p::Ref, n)` converts the reference and does the same. -/
def UnsafeWritePtrCorrect : Prop :=
  (∀ s mem n, 0 ≤ n → n ≤ 18446744073709551615 → unsafeWriteRef s mem n = .ok (unsafeWrite s (mem.take n.toNat))) ∧
  (∀ s mem n, n < 0 → unsafeWriteRef s mem n = .error (.jl (.inexactError "UInt64")))
theorem unsafeWritePtrCorrect : UnsafeWritePtrCorrect := by
  refine ⟨?_, ?_⟩
  · intro s mem n h1 h2; simp [unsafeWriteRef, toInt_u64 n h1 h2, bind, Except.bind, pure, Except.pure]
  · intro s mem n h; simp [unsafeWriteRef, toInt_u64_neg n h, bind, Except.bind]

/-- `unsafe_read(s, p::Ptr, n)` and `unsafe_read(s, p::Ref, n)` convert `n` to `UInt` and
read that many bytes. -/
def UnsafeReadPtrCorrect : Prop :=
  (∀ s n, 0 ≤ n → n ≤ 18446744073709551615 → unsafeReadRef s n = unsafeRead n.toNat s) ∧
  (∀ s n, n < 0 → unsafeReadRef s n = .error (.jl (.inexactError "UInt64")))
theorem unsafeReadPtrCorrect : UnsafeReadPtrCorrect := by
  refine ⟨?_, ?_⟩
  · intro s n h1 h2; simp [unsafeReadRef, toInt_u64 n h1 h2, bind, Except.bind]
  · intro s n h; simp [unsafeReadRef, toInt_u64_neg n h, bind, Except.bind]

/-! ### `mark`, `unmark`, `reset`, `ismarked`, `peek` -/

/-- `mark(s)` returns the position and marks the stream. -/
def MarkCorrect : Prop := ∀ s, (mark s).1 = position s ∧ ismarked (mark s).2 = true ∧ (mark s).2.inp = s.inp
theorem markCorrect : MarkCorrect := fun s => ⟨rfl, by simp [mark, ismarked], rfl⟩

/-- `ismarked(s)` holds exactly when `s.mark ≥ 0`. -/
def IsmarkedCorrect : Prop := ∀ s, ismarked s = true ↔ 0 ≤ s.mark
theorem ismarkedCorrect : IsmarkedCorrect := fun s => by simp [ismarked]

/-- `unmark(s)` returns whether `s` was marked and leaves it unmarked. -/
def UnmarkCorrect : Prop := ∀ s, (unmark s).1 = ismarked s ∧ ismarked (unmark s).2 = false ∧ (unmark s).2.inp = s.inp
theorem unmarkCorrect : UnmarkCorrect := by
  intro s; by_cases h : ismarked s = true
  · have h' : ¬ s.mark < 0 := by simp [ismarked] at h; omega
    simp [unmark, ismarked, h']; omega
  · simp at h; simp [unmark, h]

/-- `reset(s)` throws on an unmarked stream; after `mark` and reading `k` bytes it returns
the marked position, goes back to it, and removes the mark. -/
def ResetCorrect : Prop :=
  (∀ s, ismarked s = false → reset s = argErr "not marked") ∧
  (∀ s k, s.seekable = true → k ≤ s.inp.length →
      ∃ s', (do let (_, s1) ← unsafeRead k (mark s).2; reset s1) = .ok ((position s : Int), s') ∧
        s'.pre = s.pre ∧ s'.inp = s.inp ∧ ismarked s' = false)
theorem resetCorrect : ResetCorrect := by
  refine ⟨fun s h => by simp [reset, h], ?_⟩
  intro s k hs hk
  refine ⟨{ s with mark := -1 }, ?_, rfl, rfl, by simp [ismarked]⟩
  simp [mark, unsafeRead_spec, hk, reset, ismarked, seek, hs, position, bind, Except.bind, pure, Except.pure]

/-- `peek(s)` returns the next byte without consuming it. -/
def PeekByteCorrect : Prop :=
  ∀ s b r, s.seekable = true → s.inp = b :: r → ∃ s', peekByte s = .ok (b, s') ∧ s'.pre = s.pre ∧ s'.inp = s.inp
theorem peekByteCorrect : PeekByteCorrect := fun s b r hs h => ⟨_, peekByte_cons s b r hs h, rfl, rfl⟩

/-! ### `open_flags` and `open(f, ...)` -/

/-- The documented defaults of `open`'s keyword table (`base/iostream.jl:292-300`):
`read = !write`, `write = truncate | append`, `truncate = !read & write`, `append = false`. -/
def OpenFlagsDoc : Prop :=
  ∀ r w c t a : Option Bool,
    let f := openFlags r w c t a
    f.write = w.getD (t.getD false || a.getD false) ∧ f.read = r.getD (!f.write) ∧
    f.truncate = t.getD (!f.read && f.write) ∧ f.append = a.getD false

theorem openFlagsDoc_refuted : ¬ OpenFlagsDoc := by
  intro h
  have := (h none none none none (some true)).2.2.1
  revert this; decide

/-- Without `append`, `open_flags` follows the documented table, and `create` defaults to
`!read & write | truncate`. -/
def OpenFlagsTable : Prop :=
  ∀ r w c t : Option Bool,
    let f := openFlags r w c t none
    f.write = w.getD (t.getD false) ∧ f.read = r.getD (!f.write) ∧
    f.truncate = t.getD (!f.read && f.write) ∧ f.append = false ∧
    f.create = c.getD ((!f.read && f.write) || t.getD false)

theorem openFlagsTable : OpenFlagsTable := by
  intro r w c t
  rcases r with _ | ⟨_ | _⟩ <;> rcases w with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;>
    rcases t with _ | ⟨_ | _⟩ <;> decide

/-- `open(f, args...)` returns `f`'s result and closes the stream `f` leaves, also when
`f` throws; a failing `open` is propagated. -/
def OpenDoCloses : Prop :=
  (∀ (α : Type) (e : Err) (f : St → R α × St), openDo (.error e) f = (.error e, none)) ∧
  (∀ (α : Type) (io : St) (f : St → R α × St),
      (openDo (.ok io) f).1 = (f io).1 ∧ (openDo (.ok io) f).2 = some { (f io).2 with isopen := false })
theorem openDoCloses : OpenDoCloses := ⟨fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-! ### `AbstractPipe` -/

/-- `getproperty(pipe, name)` returns the field, asserting that the stream fields are `IO`. -/
def PipeGetpropertyCorrect : Prop :=
  (∀ (α : Type) (g : String → α) isIO name, name ∉ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] →
      pipeGetproperty g isIO name = .ok (g name)) ∧
  (∀ (α : Type) (g : String → α) isIO name, name ∈ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] →
      pipeGetproperty g isIO name = if isIO (g name) then .ok (g name) else .error (.typeError "typeassert"))
theorem pipeGetpropertyCorrect : PipeGetpropertyCorrect := by
  refine ⟨?_, ?_⟩
  · intro α g isIO name h; simp only [pipeGetproperty, if_neg h]
  · intro α g isIO name h; simp only [pipeGetproperty, if_pos h]

/-- `iswritable(pipe)` is `iswritable(pipe_writer(pipe))`. -/
def PipeIswritable : Prop := ∀ p, pipeIswritable p = iswritable p.wr
theorem pipeIswritable_eq : PipeIswritable := fun _ => rfl

/-- `flush`/`closewrite(pipe)` act on the writer only. -/
def PipeFlushWriter : Prop :=
  ∀ f p u s, f p.wr = .ok (u, s) → pipeFlushLike f p = .ok (u, { p with wr := s })
theorem pipeFlushWriter : PipeFlushWriter := by
  intro f p u s h; simp [pipeFlushLike, onWriter, pipeWriter, h, bind, Except.bind, pure, Except.pure]

/-- `write(pipe, b::UInt8)` appends `b` to the writer and leaves the reader. -/
def PipeWriteByte : Prop := ∀ p b, pipeWriteByte p b = .ok (1, { p with wr := { p.wr with out := p.wr.out ++ [b] } })
theorem pipeWriteByte_eq : PipeWriteByte := by
  intro p b; simp [pipeWriteByte, onWriter, writeByte, pipeWriter, bind, Except.bind, pure, Except.pure]

/-- `writepartial(pipe, x)` is `writepartial` on the writer. -/
def PipeWritepartial : Prop :=
  ∀ (α : Type) (w : St → R (α × St)) p a s, w p.wr = .ok (a, s) → pipeWritepartial w p = .ok (a, { p with wr := s })
theorem pipeWritepartial_eq : PipeWritepartial := by
  intro α w p a s h; simp [pipeWritepartial, onWriter, writepartial, pipeWriter, h, bind, Except.bind, pure, Except.pure]

/-- `write(to, from::AbstractPipe)` writes from the pipe's reader. -/
def WriteFromPipeReader : Prop := ∀ (α : Type) (w : St → St → α) to p, writeFromPipe w to p = w to p.rd
theorem writeFromPipeReader : WriteFromPipeReader := fun _ _ _ _ => rfl

/-- `unsafe_write(pipe, p, n)` appends to the writer and returns `n`. -/
def PipeUnsafeWrite : Prop := ∀ p bs, pipeUnsafeWrite p bs = .ok (bs.length, { p with wr := { p.wr with out := p.wr.out ++ bs } })
theorem pipeUnsafeWrite_eq : PipeUnsafeWrite := by
  intro p bs; simp [pipeUnsafeWrite, onWriter, unsafeWrite_spec, pipeWriter, bind, Except.bind, pure, Except.pure]

/-- `buffer_writes(pipe, args...)` is `buffer_writes` of the writer. -/
def PipeBufferWrites : Prop := ∀ p, pipeBufferWrites p = p.wr
theorem pipeBufferWrites_eq : PipeBufferWrites := fun _ => rfl

/-- The `@eval`-generated `mark`, `unmark`, `reset`, `ismarked`, `read`, `bytesavailable`,
`reseteof`, `isreadable` on a pipe act on the reader only. -/
def PipeReaderOps : Prop :=
  ∀ (α : Type) (f : St → R (α × St)) p a s, f p.rd = .ok (a, s) → pipeReaderOp f p = .ok (a, { p with rd := s })
theorem pipeReaderOps : PipeReaderOps := by
  intro α f p a s h; simp [pipeReaderOp, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `readavailable(pipe)` reads from the reader. -/
def PipeReadavailable : Prop :=
  ∀ ra p a s, ra p.rd = .ok (a, s) → pipeReadavailable ra p = .ok (a, { p with rd := s })
theorem pipeReadavailable_eq : PipeReadavailable := by
  intro ra p a s h; simp [pipeReadavailable, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `read(pipe, UInt8)` reads the reader's next byte. -/
def PipeReadByte : Prop :=
  ∀ p b r, p.rd.inp = b :: r → pipeReadByte p = .ok (b, { p with rd := { p.rd with pre := p.rd.pre ++ [b], inp := r } })
theorem pipeReadByte_eq : PipeReadByte := by
  intro p b r h; simp [pipeReadByte, onReader, readByte, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `unsafe_read(pipe, p, n)` reads `n` bytes of the reader. -/
def PipeUnsafeRead : Prop :=
  ∀ p n, n ≤ p.rd.inp.length → pipeUnsafeRead p n =
    .ok (p.rd.inp.take n, { p with rd := { p.rd with pre := p.rd.pre ++ p.rd.inp.take n, inp := p.rd.inp.drop n } })
theorem pipeUnsafeRead_eq : PipeUnsafeRead := by
  intro p n h; simp [pipeUnsafeRead, onReader, unsafeRead_spec, h, pipeReader, bind, Except.bind, pure, Except.pure]

/-- `copyuntil(out, pipe, delim)` (each delimiter type), `readuntil_vector!(pipe, ...)`,
`readbytes!(pipe, ...)`, `peek(pipe, T)` and `wait_readnb(pipe, nb)` forward the same
arguments to `pipe_reader(pipe)`. -/
def PipeForwardReader : Prop :=
  ∀ (α : Type) (op : St → R (α × St)) p a s, op p.rd = .ok (a, s) → pipeForward op p = .ok (a, { p with rd := s })
theorem pipeForwardReader : PipeForwardReader := by
  intro α op p a s h; simp [pipeForward, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `eof(pipe)` is `eof(pipe_reader(pipe))`. -/
def PipeEof : Prop := ∀ p, pipeEof p = eof p.rd
theorem pipeEof_eq : PipeEof := fun _ => rfl

/-- `isopen(pipe)` holds while either side is open. -/
def PipeIsopen : Prop := ∀ p, pipeIsopen p = true ↔ p.wr.isopen = true ∨ p.rd.isopen = true
theorem pipeIsopen_iff : PipeIsopen := fun p => by simp [pipeIsopen, pipeWriter, pipeReader]

/-- `close(pipe)` closes both sides, so the pipe is no longer open. -/
def PipeCloseBoth : Prop := ∀ p, (pipeClose p).wr.isopen = false ∧ (pipeClose p).rd.isopen = false ∧ pipeIsopen (pipeClose p) = false
theorem pipeCloseBoth : PipeCloseBoth := fun p => by simp [pipeClose, close, pipeIsopen, pipeWriter, pipeReader]

/-- `wait_close(pipe)` waits for the writer, then the reader. -/
def PipeWaitClose : Prop := ∀ wc p, pipeWaitClose wc p = wc p.wr ++ wc p.rd
theorem pipeWaitClose_eq : PipeWaitClose := fun _ _ => rfl

/-! ### Binary I/O -/

/-- `write(io, x1, xs...)` writes each argument in order and returns the total count. -/
def WriteManyCorrect : Prop :=
  ∀ s (b : UInt8) bs, writeMany writeByte s b bs = (bs.length + 1, { s with out := s.out ++ b :: bs })
theorem writeManyCorrect : WriteManyCorrect := by
  intro s b bs
  simp only [writeMany, writeByte]
  rw [foldl_bytes _ (fun acc x => rfl)]
  refine Prod.ext ?_ ?_ <;> simp <;> omega

/-- `write(s, x::Ref{T})` throws for a `Ptr`, writes the `sizeof(T)` bytes of `isbits`
contents, and otherwise writes `x[]`. -/
def WriteRefCorrect : Prop :=
  (∀ ib bytes (wv : St → R (Nat × St)) s, writeRef true ib bytes wv s = .error (.errorException "write cannot copy from a Ptr")) ∧
  (∀ bytes (wv : St → R (Nat × St)) s, writeRef false true bytes wv s = .ok (bytes.length, { s with out := s.out ++ bytes })) ∧
  (∀ bytes (wv : St → R (Nat × St)) s, writeRef false false bytes wv s = wv s)
theorem writeRefCorrect : WriteRefCorrect :=
  ⟨fun _ _ _ _ => rfl, fun bytes wv s => by simp [writeRef, unsafeWrite_spec], fun _ _ _ => rfl⟩

/-- `write(s, x::Int16..Float64)` emits the `sizeof(x)` little-endian bytes and `read(s, T)`
returns the value. -/
def WriteReadInt : Prop :=
  ∀ t : IntTy, ∀ s x rest, t.min ≤ x → x ≤ t.max →
    let bs := leBytes (t.bits / 8) (bitsOf t x)
    writeInt t s x = (t.bits / 8, { s with out := s.out ++ bs }) ∧
    (readInt t (St.of (bs ++ rest))).map Prod.fst = .ok x
theorem writeReadInt : WriteReadInt := by
  intro t s x rest h1 h2
  have hb : bitsOf t x < 2 ^ (8 * (t.bits / 8)) := by
    cases t <;> simp [bitsOf, IntTy.bits, IntTy.min, IntTy.max] at h1 h2 ⊢ <;> omega
  refine ⟨by simp [writeInt, unsafeWrite_spec, leBytes_length], ?_⟩
  simp only [readInt, St.of, bind, Except.bind, unsafeRead_spec, List.length_append, leBytes_length,
    Nat.le_add_right, if_true, List.take_left' (leBytes_length _ _), pure, Except.pure, Except.map,
    leVal_leBytes _ _ hb]
  cases t <;> simp [bitsOf, wrapInt, IntTy.bits, IntTy.min, IntTy.max, IntTy.signed] at h1 h2 ⊢ <;> omega

/-- Floats: the bit pattern is written little-endian and read back unchanged. -/
def WriteReadFloat : Prop :=
  ∀ n s bits rest, bits < 2 ^ (8 * n) →
    writeFloat n s bits = (n, { s with out := s.out ++ leBytes n bits }) ∧
    (readFloat n (St.of (leBytes n bits ++ rest))).map Prod.fst = .ok bits
theorem writeReadFloat : WriteReadFloat := by
  intro n s bits rest h
  refine ⟨by simp [writeFloat, unsafeWrite_spec, leBytes_length], ?_⟩
  simp only [readFloat, St.of, bind, Except.bind, unsafeRead_spec, List.length_append, leBytes_length,
    Nat.le_add_right, if_true, List.take_left' (leBytes_length _ _), pure, Except.pure, Except.map,
    leVal_leBytes _ _ h]

/-- `write(s, x::Int8)` writes one byte and `read(s, Int8)` returns `x`. -/
def WriteReadInt8 : Prop :=
  ∀ s x rest, -128 ≤ x → x ≤ 127 →
    writeInt8 s x = (1, { s with out := s.out ++ [(bitsOf .i8 x).toUInt8] }) ∧
    (readInt8 (St.of ((bitsOf .i8 x).toUInt8 :: rest))).map Prod.fst = .ok x
theorem writeReadInt8 : WriteReadInt8 := by
  intro s x rest h1 h2
  refine ⟨rfl, ?_⟩
  have : ((bitsOf .i8 x).toUInt8).toNat = bitsOf .i8 x := by
    simp [bitsOf, IntTy.bits, Nat.toUInt8, UInt8.toNat_ofNat]; omega
  simp [readInt8, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map, this]
  simp [bitsOf, wrapInt, IntTy.bits, IntTy.signed]; omega

/-- `write(s, b::Bool)` writes 0 or 1 and `read(s, Bool)` returns `b`. -/
def WriteReadBool : Prop :=
  ∀ s b rest, writeBool s b = (1, { s with out := s.out ++ [if b then 1 else 0] }) ∧
    (readBool (St.of ((if b then 1 else 0) :: rest))).map Prod.fst = .ok b
theorem writeReadBool : WriteReadBool := by
  intro s b rest
  refine ⟨rfl, ?_⟩
  cases b <;> simp [readBool, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map]

/-- `read(s, Bool)` is `true` exactly for a nonzero byte. -/
def ReadBoolNonzero : Prop :=
  ∀ (b : UInt8) rest, (readBool (St.of (b :: rest))).map Prod.fst = .ok (b != 0)
theorem readBoolNonzero : ReadBoolNonzero := by
  intro b rest; simp [readBool, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map]

/-- `write(to, p::Ptr)` writes the address as a `UInt`; `read(s, Ptr{T})` reads it back. -/
def WriteReadPtr : Prop :=
  ∀ s p rest, p < 2 ^ 64 →
    writePtr s p = (8, { s with out := s.out ++ leBytes 8 p }) ∧
    (readPtr (St.of (leBytes 8 p ++ rest))).map Prod.fst = .ok (p : Int)
theorem writeReadPtr : WriteReadPtr := by
  intro s p rest h
  have := writeReadInt .u64 s p rest (by simp) (by simp; omega)
  have hb : bitsOf .u64 (p : Int) = p := by simp [bitsOf, IntTy.bits]; omega
  simp only [hb] at this
  exact ⟨this.1, this.2⟩

/-- `write(s, A::AbstractArray)` writes every element's bytes in order and returns the
total, and throws for non-`isbits` element types. -/
def WriteArrayCorrect : Prop :=
  (∀ s elems, writeArray true s elems = .ok (elems.flatten.length, { s with out := s.out ++ elems.flatten })) ∧
  (∀ s elems, writeArray false s elems = .error (.errorException "`write` is not supported on non-isbits arrays"))
theorem writeArrayCorrect : WriteArrayCorrect := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro s elems
  simp only [writeArray, Bool.not_true, Bool.false_eq_true, if_false]
  rw [foldl_chunks _ (fun acc e => by simp [unsafeWrite_spec])]
  simp

/-- `write(s, B::BitArray)` writes the 64-bit chunks, little-endian. -/
def WriteBitArrayChunks : Prop :=
  ∀ s chunks, writeBitArray s chunks = .ok ((chunks.map (leBytes 8)).flatten.length,
    { s with out := s.out ++ (chunks.map (leBytes 8)).flatten })
theorem writeBitArrayChunks : WriteBitArrayChunks := fun s chunks => writeArrayCorrect.1 s _

/-- `read!(s, x::Ref{T})` throws for a `Ptr`, reads `sizeof(T)` bytes of `isbits`
contents, and otherwise stores `read(s, T)`. -/
def ReadRefCorrect : Prop :=
  (∀ (α : Type) ib size (rv : St → R (α × St)) s, readRefBang true ib size rv s = .error (.errorException "read! cannot copy into a Ptr")) ∧
  (∀ (α : Type) size (rv : St → R (α × St)) s, size ≤ s.inp.length →
      (readRefBang false true size rv s).map Prod.fst = .ok (.inl (s.inp.take size))) ∧
  (∀ (α : Type) size (rv : St → R (α × St)) s v s', rv s = .ok (v, s') →
      readRefBang false false size rv s = .ok (.inr v, s'))
theorem readRefCorrect : ReadRefCorrect := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro α size rv s h
    simp [readRefBang, unsafeRead_spec, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro α size rv s v s' h
    simp [readRefBang, h, bind, Except.bind, pure, Except.pure]

/-- `read!(s, A::AbstractArray)`: the contiguous fast path reads the same elements as the
element loop, namely consecutive `nb`-byte pieces of the input. -/
def ReadArrayCorrect : Prop :=
  (∀ nb len (s : St), nb * len ≤ s.inp.length → readArrayBang true true nb len s = readArrayBang true false nb len s) ∧
  (∀ nb len (s : St), nb * len ≤ s.inp.length →
      (readArrayBang true false nb len s).map Prod.fst = .ok ((List.range len).map (fun i => (s.inp.drop (i * nb)).take nb)))
theorem readArrayCorrect : ReadArrayCorrect := by
  refine ⟨?_, ?_⟩
  · intro nb len s h
    simp only [readArrayBang, Bool.and_self, Bool.and_false, Bool.false_eq_true, if_true, if_false,
      bind, Except.bind, unsafeRead_spec, if_pos h, pure, Except.pure]
    rw [readGo_spec nb len s h]
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [List.drop_take, List.take_take]
    congr 1
    have : (i + 1) * nb ≤ nb * len := by rw [Nat.mul_comm nb]; exact Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  · intro nb len s h
    simp only [readArrayBang, Bool.and_false, Bool.false_eq_true, if_false]
    rw [readGo_spec nb len s h]; rfl

/-- `read!(s, B::BitArray)` with a last chunk that has bits set beyond `length(B)` throws
`DimensionMismatch`; chunks with no such bits are returned unchanged. -/
def ReadBitArrayCorrect : Prop :=
  (∀ n (s : St) cs s', readArrayBang true true 8 ((n + 63) / 64) s = .ok (cs, s') →
      ∀ last, (cs.map leVal).getLast? = some last → last &&& mskEnd n ≠ last →
      readBitArrayBang n s = .error (.jl (.argumentError "DimensionMismatch: read mismatch, found non-zero bits after BitArray length"))) ∧
  (∀ n (s : St) cs s', readArrayBang true true 8 ((n + 63) / 64) s = .ok (cs, s') →
      (∀ last, (cs.map leVal).getLast? = some last → last &&& mskEnd n = last) →
      readBitArrayBang n s = .ok (cs.map leVal, s'))
theorem readBitArrayCorrect : ReadBitArrayCorrect := by
  refine ⟨?_, ?_⟩
  · intro n s cs s' h last hl hm
    simp [readBitArrayBang, h, bind, Except.bind, hl, hm]
  · intro n s cs s' h hm
    simp only [readBitArrayBang, h, bind, Except.bind]
    cases hl : (cs.map leVal).getLast? with
    | none => simp [pure, Except.pure]
    | some last => simp [hm last hl, pure, Except.pure]

/-- `write(s, A::StridedArray)`: non-`isbits` element types throw, contiguous arrays are one
`unsafe_write`, a vector with stride 1 is written whole, other strides use the element
loop, and a matrix with contiguous columns `c` elements apart is written column by
column. -/
def WriteStridedCorrect : Prop :=
  (∀ c sz st mem g s, writeStrided false c sz st mem g s = .error (.errorException "`write` is not supported on non-isbits arrays")) ∧
  (∀ sz st mem g s, writeStrided true true sz st mem g s = .ok (unsafeWrite s (mem.take (sz.foldl (· * ·) 1)).flatten)) ∧
  (∀ m mem g s, writeStrided true false [m] [1] mem g s = .ok (unsafeWrite s (mem.take (1 * m)).flatten)) ∧
  (∀ m k mem g s, k ≠ 1 → writeStrided true false [m] [k] mem g s = writeArray true s g) ∧
  (∀ m k c, m ≠ 1 → k ≠ 1 → c ≠ m →
      stridedPlan true false [m, k] [1, c] = .runs ((List.range k).map (fun j => c * j)) m)
theorem writeStridedCorrect : WriteStridedCorrect := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro m mem g s; simp [writeStrided, stridedPlan, mergeAdjacentDim]
  · intro m k mem g s hk; simp [writeStrided, stridedPlan, mergeAdjacentDim, hk]
  · intro m k c hm hk hc
    simp [stridedPlan, mergeAdjacentDim, mergeLoop, hm, hk, Ne.symm hc, hc, cartesian, List.flatMap,
      Function.comp_def]

/-- `read!(s, A::StridedArray)`: non-`isbits` or contiguous arrays use the `AbstractArray`
method, a stride-1 vector is one `unsafe_read` of all its bytes, and other strides use
the `AbstractArray` method. -/
def ReadStridedCorrect : Prop :=
  (∀ c sz st nb s, readStrided false c sz st nb s = .ok (none, s)) ∧
  (∀ sz st nb s, readStrided true true sz st nb s = .ok (none, s)) ∧
  (∀ m nb s, nb * (1 * m) ≤ s.inp.length →
      (readStrided true false [m] [1] nb s).map Prod.fst = .ok (some [(0, s.inp.take (nb * (1 * m)))])) ∧
  (∀ m k nb s, k ≠ 1 → readStrided true false [m] [k] nb s = .ok (none, s))
theorem readStridedCorrect : ReadStridedCorrect := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro m nb s h
    rw [Nat.one_mul] at h ⊢
    simp [readStrided, stridedPlan, mergeAdjacentDim, unsafeRead_spec, h, bind, Except.bind, pure,
      Except.pure, Except.map]
  · intro m k nb s hk; simp [readStrided, stridedPlan, mergeAdjacentDim, hk]

/-- `write(io, c::Char)` emits the UTF-8 bytes of `c` and `read(io, Char)` decodes them:
writing a character and reading it back gives the same `Char`, whatever follows. -/
def CharRoundTrip : Prop :=
  ∀ bs : Bytes, IsUtf8Char bs → ∀ s rest,
    writeChar s (packChar bs) = (bs.length, { s with out := s.out ++ bs }) ∧
    (readChar (St.of (bs ++ rest))).map Prod.fst = .ok (packChar bs)

theorem charRoundTrip : CharRoundTrip := by
  intro bs hbs s rest
  have hl : ∀ b : UInt8, b.toNat < 256 := fun b => b.toNat_lt
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, t⟩⟩⟩⟩⟩ <;> simp only [IsUtf8Char] at hbs
  · have := hl b0
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0]) = b0.toNat by simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_pos (by omega)]; simp
    · simp [readChar, St.of, readByte, lo_ascii b0 hbs, bind, Except.bind, pure, Except.pure, Except.map,
        packChar]
  · have := hl b0; have := hl b1
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1]) = b1.toNat * 256 + b0.toNat by simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_two b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 2 ∧ 2 ≤ 4) by omega, if_true, show [16, 8, 0].take (2 - 1) = [16] from rfl]
      rw [readCharLoop_cont 16 [] _ _ b1 rest rfl rfl hbs.2.2]
      simp [readCharLoop, Except.map, packChar]
  · have := hl b0; have := hl b1; have := hl b2
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1, b2]) = b2.toNat * 65536 + b1.toNat * 256 + b0.toNat by
        simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b2 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_three b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 3 ∧ 3 ≤ 4) by omega, if_true, show [16, 8, 0].take (3 - 1) = [16, 8] from rfl]
      rw [readCharLoop_cont 16 [8] _ _ b1 (b2 :: rest) rfl rfl hbs.2.2.1,
        readCharLoop_cont 8 [] _ _ b2 rest rfl rfl hbs.2.2.2]
      simp [readCharLoop, Except.map, packChar]
  · have := hl b0; have := hl b1; have := hl b2; have := hl b3
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1, b2, b3]) =
          b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat by
        simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b2 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b3 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_four b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 4 ∧ 4 ≤ 4) by omega, if_true, show [16, 8, 0].take (4 - 1) = [16, 8, 0] from rfl]
      rw [readCharLoop_cont 16 [8, 0] _ _ b1 (b2 :: b3 :: rest) rfl rfl hbs.2.2.1,
        readCharLoop_cont 8 [0] _ _ b2 (b3 :: rest) rfl rfl hbs.2.2.2.1,
        readCharLoop_cont 0 [] _ _ b3 rest rfl rfl hbs.2.2.2.2]
      simp [readCharLoop, Except.map, packChar]

/-- `write(io, s::Symbol)` writes the bytes of the name and returns their number. -/
def WriteSymbolCorrect : Prop := ∀ s name, 0 ∉ name → writeSymbol s name = (name.length, { s with out := s.out ++ name })
theorem writeSymbolCorrect : WriteSymbolCorrect := by
  intro s name h; simp [writeSymbol, takeWhile_ne0 name h, unsafeWrite_spec]

/-- `write(to, from)` copies all of `from` and returns the number of bytes. -/
def WriteFromIOCorrect : Prop :=
  ∀ k to frm, (writeFromIO k to frm).1 = frm.inp.length ∧ (writeFromIO k to frm).2.1.out = to.out ++ frm.inp ∧
    (writeFromIO k to frm).2.2.inp = []
theorem writeFromIOCorrect : WriteFromIOCorrect := by
  intro k to frm
  simp only [writeFromIO]
  rw [writeFromIO_go k _ 0 to frm (by omega)]
  simp

/-! ### `skipchars` -/

/-- `skipchars(predicate, io)` leaves the stream before the first character for which
`predicate` is false, for any `IO` stream. -/
def SkipcharsStreams : Prop :=
  ∀ (pred : Nat → Bool) (rl : St → R St) (s : St) (c : UInt8) (rest : Bytes),
    s.inp = c :: rest → c.toNat < 0x80 → pred (packChar [c]) = false →
    ∃ s', skipchars pred none rl (s.inp.length + 1) s = .ok s' ∧ s'.inp = s.inp

theorem skipcharsStreams_refuted : ¬ SkipcharsStreams := by
  intro h
  obtain ⟨s', hs, _⟩ := h (fun _ => false) (fun s => .ok s) { pre := [], inp := [120], seekable := false }
    120 [] rfl (by decide) rfl
  have e : skipchars (fun _ => false) none (fun s => .ok s) (([120] : Bytes).length + 1)
      ({ pre := [], inp := [120], seekable := false } : St) =
      argErr "seek failed, IOBuffer is not seekable and is not marked" := by decide
  change skipchars (fun _ => false) none (fun s => .ok s) (([120] : Bytes).length + 1)
      ({ pre := [], inp := [120], seekable := false } : St) = _ at hs
  rw [e] at hs; cases hs

/-- On a seekable stream, `skipchars` skips the leading ASCII characters satisfying the
predicate and stops before the first one that does not. -/
def SkipcharsSeekable : Prop :=
  ∀ (pred : Nat → Bool) (rl : St → R St) (ws : Bytes) (c : UInt8) (rest : Bytes) (s : St),
    s.seekable = true → s.inp = ws ++ c :: rest →
    (∀ w ∈ ws, w.toNat < 0x80 ∧ pred (packChar [w]) = true) → c.toNat < 0x80 → pred (packChar [c]) = false →
    ∃ s', skipchars pred none rl (s.inp.length + 1) s = .ok s' ∧ s'.inp = c :: rest

theorem skipcharsSeekable : SkipcharsSeekable := by
  intro pred rl ws c rest s hs hin hws hc hpc
  suffices H : ∀ fuel, ws.length < fuel → ∃ s', skipchars pred none rl fuel s = .ok s' ∧ s'.inp = c :: rest by
    exact H _ (by rw [hin]; simp; omega)
  rw [packChar_one] at hpc
  induction ws generalizing s with
  | nil =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp at hin
    have e : ((s.pre.length : Int) + 1 + -1).toNat = s.pre.length := by omega
    simp [skipchars, eof, hin, readChar, readByte, lo_ascii c hc, hpc, skip, seek, hs, position, bind,
      Except.bind, pure, Except.pure, e]
  | cons w ws ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hw := hws w (by simp)
    rw [packChar_one] at hw
    simp only [List.cons_append] at hin
    have := ih { s with pre := s.pre ++ [w], inp := ws ++ c :: rest } hs rfl
      (fun x hx => hws x (by simp [hx])) f (by simp at hf; omega)
    simp [skipchars, eof, hin, readChar, readByte, lo_ascii w hw.1, hw.2, bind, Except.bind, pure,
      Except.pure]
    exact this


/-! ### `copyline` -/



/-- `copyline(out, s)` copies the same line as `readline(s)` returns, whatever the type of
`out` (its docstring: like `readline`, writing to `out`). -/
def CopylineConsistent : Prop := ∀ inp : Bytes, (copylineLoop [] inp).1 = readlineRef inp

/-- The line `"x\r\r\n"`: `copyline` writes `"x\r\r"`, `readline` gives `"x\r"`. -/
theorem copylineConsistent_refuted : ¬ CopylineConsistent := by
  intro h
  have := h [120, 13, 13, 10]
  have e : copylineLoop [] [120, 13, 13, 10] = ([120, 13, 13], []) := by
    rw [copylineLoop.eq_def]; simp
    rw [copylineLoop.eq_def]; simp
    rw [copylineLoop.eq_def]; simp
  have r : readlineRef [120, 13, 13, 10] = [120, 13] := by decide
  rw [e, r] at this
  simp at this

/-- On lines without `'\r'`, `copyline` copies the bytes before the first newline and
consumes the newline. -/
def CopylinePlain : Prop :=
  ∀ line rest : Bytes, 0x0a ∉ line → 0x0d ∉ line → ∀ out, copylineLoop out (line ++ 0x0a :: rest) = (out ++ line, rest)
theorem copylinePlain : CopylinePlain := by
  intro line rest h1 h2
  induction line with
  | nil => intro out; rw [List.nil_append, copylineLoop.eq_def]; simp
  | cons b bs ih =>
    intro out
    have hb1 : b ≠ 0x0a := fun e => h1 (e ▸ List.mem_cons_self ..)
    have hb2 : b ≠ 0x0d := fun e => h2 (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, copylineLoop.eq_def]
    simp only [hb1, hb2, ite_false]
    rw [ih (fun m => h1 (List.mem_cons_of_mem _ m)) (fun m => h2 (List.mem_cons_of_mem _ m))]
    simp

end JuliaLean.IOCov.Io
