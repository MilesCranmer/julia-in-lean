import JuliaLean.Transcode.RoundTrip
import JuliaLean.Transcode.Bridge
import JuliaLean.Transcode.Alias

/-!
# Properties of `transcode`, `unsafe_string`, `containsnul` and the C string conversions
-/

namespace JuliaLean.Transcode

open JuliaLean.Strings

/-! ## Totality: "it always succeeds for conversions between UTF-XX encodings" -/

/-- `transcode(UInt16, src)` returns for every byte vector, valid UTF-8 or not;
in particular it never reads past the end of `src`. -/
def Utf8ToUtf16Total : Prop := ∀ src : List UInt8, ∃ us, transcode16 src = .ok us

theorem utf8ToUtf16Total_proven : Utf8ToUtf16Total := transcode16_ok

/-- `transcode(UInt8, src::Vector{UInt16})` returns for every code-unit vector,
unpaired surrogates included; its writes stay inside the `StringVector(m)` it
allocates and initialize all `m` bytes. -/
def Utf16ToUtf8Complete : Prop :=
  ∀ src : List UInt16, src.length < 2 ^ 60 →
    ∃ o : Out, transcode8 src = .ok o ∧ (o.written.length : Int) = o.m.val

theorem utf16ToUtf8Complete_proven : Utf16ToUtf8Complete := transcode8_complete

/-- `transcode(UInt32, s)` returns for every String. -/
def Utf8ToUtf32Total : Prop := ∀ s : JStr, ∃ v, transcode32 s = .ok v

/-- `"a\xffb"`. -/
def strAFFB : JStr := ⟨[0x61, 0xff, 0x62], by decide⟩

theorem utf8ToUtf32Total_refuted : ¬ Utf8ToUtf32Total := by
  intro h
  obtain ⟨v, hv⟩ := h strAFFB
  have e : okB (transcode32 strAFFB) = false := by decide
  rw [hv] at e; simp [okB] at e

/-- `transcode(UInt8, v::Vector{UInt32})` (and `transcode(String, v)`) returns for
every `Vector{UInt32}`. -/
def Utf32ToUtf8Total : Prop := ∀ v : List UInt32, ∃ bs, transcode8of32 v = .ok bs

theorem utf32ToUtf8Total_refuted : ¬ Utf32ToUtf8Total := by
  intro h
  obtain ⟨bs, hb⟩ := h [0x61, 0x200000]
  have e : okB (transcode8of32 [0x61, 0x200000]) = false := by decide
  rw [hb] at e; simp [okB] at e

/-! ## Valid strings -/

/-- `transcode(String, transcode(UInt16, s)) == s` for every valid string (the
docstring's example), with `transcode(UInt8, ...)` allocating exactly
`ncodeunits(s)` bytes. Strings are shorter than `2^60` bytes. -/
def RoundTrip16 : Prop :=
  ∀ s : JStr, ValidUtf8 s.bytes → s.bytes.length < 2 ^ 60 →
    ∃ us o, transcode16 s.bytes = .ok us ∧ transcode8 us = .ok o ∧ o.written = s.bytes ∧
      o.m.val = (ncodeunits s).val

theorem roundTrip16_proven : RoundTrip16 := by
  intro s ⟨cs, hc, hs⟩ hn
  rw [hs] at hn
  obtain ⟨e1, o, e2, e3, e4⟩ := roundtrip16 cs hc hn
  refine ⟨_, o, hs ▸ e1, e2, hs ▸ e3, ?_⟩
  rw [ncu_val, e4, hs]

/-- For a valid string, `transcode(UInt16, s)` is well-formed UTF-16: every high
surrogate is followed by a low surrogate and every low surrogate follows a high one. -/
def Utf16WellFormed : Prop :=
  ∀ s : JStr, ValidUtf8 s.bytes → ∃ us, transcode16 s.bytes = .ok us ∧ wf16 us = true

theorem utf16WellFormed_proven : Utf16WellFormed := by
  intro s ⟨cs, hc, hs⟩
  exact ⟨_, hs ▸ transcode16_valid cs hc, wf16_units cs hc⟩

theorem count_units : ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
    (cs.flatMap units).length = cs.length + cs.flatten.countP (fun b => decide (0xf0 ≤ b)) := by
  intro cs h
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    have hw := h ch (by simp)
    have ih := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatMap_cons, List.flatten_cons, List.length_append, List.countP_append,
      List.length_cons, ih]
    rcases wf_cases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · obtain ⟨-, -, -, -, -, f1⟩ := facts1 a hw
      simp [units, f1]; omega
    · obtain ⟨-, -, -, -, -, -, -, -, f1, f2⟩ := facts2 a b hw
      simp [units, f1, f2]; omega
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, f1, f2, f3⟩ := facts3 a b c hw
      simp [units, f1, f2, f3]; omega
    · rw [wfChar4] at hw
      have hab : (isC c && pre4 a b) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact ⟨hw.1.1, hw.2⟩
      have hcd : (isC c && isC d) = true := by simp only [Bool.and_eq_true] at hw ⊢; exact hw.1
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, f1, f2, f3⟩ := facts4a a b c hab
      obtain ⟨-, -, -, -, -, f4⟩ := facts4b c d hcd
      simp [units, f1, f2, f3, f4]; omega

/-- For a valid string, `length(transcode(UInt16, s)) == length(s) + count(≥(0xf0), codeunits(s))`:
one code unit per character plus one more for each character outside the BMP
(whose UTF-8 lead byte is `≥ 0xf0`). -/
def Utf16Length : Prop :=
  ∀ s : JStr, ValidUtf8 s.bytes → ∃ us, transcode16 s.bytes = .ok us ∧
    (us.length : Int) = (length s).val + s.bytes.countP (fun b => decide (0xf0 ≤ b))

theorem utf16Length_proven : Utf16Length := by
  intro s ⟨cs, hc, hs⟩
  refine ⟨_, hs ▸ transcode16_valid cs hc, ?_⟩
  rw [count_units cs hc, length_of_valid s cs hc hs, hs]
  push_cast; omega

theorem mapM_length {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.mapM_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    rw [List.mapM_cons] at h
    cases hf : f x with
    | error e => simp [hf, bind, Except.bind] at h
    | ok b =>
      cases hm : xs.mapM f with
      | error e => simp [hf, hm, bind, Except.bind] at h
      | ok bs =>
        simp only [hf, hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [ih bs hm]

/-- When `transcode(UInt32, s)` returns, it has one element per character:
`length(transcode(UInt32, s)) == length(s)`, for any byte string. -/
def Utf32Length : Prop :=
  ∀ (s : JStr) (v : List UInt32), transcode32 s = .ok v → (v.length : Int) = (length s).val

theorem utf32Length_proven : Utf32Length := by
  intro s v h
  obtain ⟨xs, ht, -, hc⟩ := chars_trace s
  rw [lengthIterateSteps_proven s xs ht, mapM_length _ _ _ h, hc, List.length_map]

/-! ## NUL checks -/

/-- `containsnul(s::String)` (a `memchr` for a zero byte) agrees with
`containsnul(s::AbstractString) = '\0' in s`. -/
def ContainsnulAgree : Prop := ∀ s : JStr, containsnulStr s = containsnulAbs s

theorem containsnulAgree_proven : ContainsnulAgree := containsnul_agree

/-- `unsafe_convert(Cstring, s::String)` throws `ArgumentError` exactly when
`'\0' in s`; otherwise the C function receives all of `s`'s bytes, none of
them NUL (so `strlen` sees the whole string). -/
def CstringNulCheck : Prop :=
  ∀ s : JStr,
    ((∃ msg, unsafeConvertCstring s = .error (.jl (.argumentError msg))) ↔ containsnulAbs s = true) ∧
    (containsnulAbs s = false → unsafeConvertCstring s = .ok s.bytes ∧ (0 : UInt8) ∉ s.bytes)

theorem cstringNulCheck_proven : CstringNulCheck := by
  intro s
  rw [← containsnul_agree]
  unfold unsafeConvertCstring containsnulStr
  constructor
  · constructor
    · intro ⟨msg, h⟩
      cases hc : s.bytes.contains 0
      · rw [hc] at h; simp at h
      · rfl
    · intro hc; rw [hc]; exact ⟨_, rfl⟩
  · intro hc
    rw [hc]
    refine ⟨rfl, ?_⟩
    intro hm
    have : s.bytes.contains 0 = true := List.elem_iff.mpr hm
    rw [hc] at this; cases this

theorem cconvertCwVec_ok {α : Type} [BEq α] [LawfulBEq α] [OfNat α 0] (v w : List α)
    (h : cconvertCwVec v = .ok w) : w = v ∧ v.getLast? = some 0 ∧ (0 : α) ∉ v.dropLast := by
  unfold cconvertCwVec at h
  by_cases hz : v.dropLast.any (· == 0) = true
  · simp only [hz, ↓reduceIte] at h; cases h
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    cases hl : v.getLast? with
    | none => simp only [hl] at h; cases h
    | some x =>
      simp only [hl] at h
      by_cases hx : (x == 0) = true
      · simp only [hx, ↓reduceIte, Except.ok.injEq] at h
        subst h
        refine ⟨rfl, by rw [eq_of_beq hx], ?_⟩
        intro hm
        exact hz (List.any_eq_true.mpr ⟨0, hm, by simp⟩)
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- `cconvert(Cwstring, s)` never passes data with an embedded NUL to C, and the
data it passes is NUL-terminated: on Windows (`Cwchar_t = UInt16`) and on Linux
and macOS (`Cwchar_t = Int32`). -/
def CwstringNulTerminated : Prop :=
  (∀ (s : JStr) (v : List UInt16), cconvertCwstringWin s = .ok v →
      v.getLast? = some 0 ∧ (0 : UInt16) ∉ v.dropLast) ∧
  (∀ (s : JStr) (v : List UInt32), cconvertCwstringUnix s = .ok v →
      v.getLast? = some 0 ∧ (0 : UInt32) ∉ v.dropLast)

theorem cwstringNulTerminated_proven : CwstringNulTerminated := by
  constructor
  · intro s v h
    unfold cconvertCwstringWin at h
    cases ht : transcode16 s.bytes with
    | error e => rw [ht] at h; cases h
    | ok w =>
      rw [ht] at h
      obtain ⟨rfl, h1, h2⟩ := cconvertCwVec_ok _ _ h
      exact ⟨h1, h2⟩
  · intro s v h
    unfold cconvertCwstringUnix at h
    cases ht : transcode32 s with
    | error e => rw [ht] at h; cases h
    | ok w =>
      rw [ht] at h
      obtain ⟨rfl, h1, h2⟩ := cconvertCwVec_ok _ _ h
      exact ⟨h1, h2⟩

/-- `Base.cwstring(s)` returns UTF-16 data whose only NUL is the terminator. -/
def CwstringNoEmbeddedNul : Prop :=
  ∀ (s : JStr) (w : List UInt16), cwstring s = .ok w → (0 : UInt16) ∉ w.dropLast

/-- `"\xc0\x80"`, the overlong encoding of NUL. -/
def strC080 : JStr := ⟨[0xc0, 0x80], by decide⟩

theorem cwstringNoEmbeddedNul_refuted : ¬ CwstringNoEmbeddedNul := by
  intro h
  have e : cwstring strC080 = .ok [0, 0] := rfl
  have := h strC080 [0, 0] e
  exact this (by decide)

/-- `cconvert(Cwstring, v::Vector{Cwchar_t})` throws the documented
`ArgumentError` for data that is not NUL-terminated. -/
def CwstringVectorCheck : Prop :=
  ∀ v : List UInt32, v.getLast? ≠ some 0 → ∃ msg, cconvertCwVec v = .error (.jl (.argumentError msg))

theorem cwstringVectorCheck_refuted : ¬ CwstringVectorCheck := by
  intro h
  obtain ⟨msg, hm⟩ := h [] (by simp)
  have e : cconvertCwVec ([] : List UInt32) = .error boundsErr := rfl
  rw [e] at hm
  cases hm

/-! ## `unsafe_string(p::Ptr{UInt16})` -/

/-- `unsafe_load(p, n)` on the readable memory `mem` starting at `p`; a read
outside it is modelled as `BoundsError` (Julia would fault). -/
def loadAt (mem : List UInt16) (n : JInt64) : SJl UInt16 :=
  if 1 ≤ n.val ∧ n.val ≤ mem.length then .ok (mem.getD (n.val.toNat - 1) 0) else .error boundsErr

/-- `n = 1; while unsafe_load(p, n) != 0; n += 1; end`, `base/strings/cstring.jl:325-328`. -/
def nulScan (mem : List UInt16) : Nat → JInt64 → SJl JInt64
  | 0, _ => .error .assertion
  | k + 1, n => do
    let x ← loadAt mem n
    if x != 0 then nulScan mem k (n + ix 1) else .ok n

/-- `unsafe_string(p::Ptr{UInt16})`, `base/strings/cstring.jl:324-330`, which calls
`unsafe_string(p, n - 1) = transcode(String, unsafe_wrap(Array, p, n - 1))` (`:321-323`). -/
def unsafeString16 (mem : List UInt16) : SJl Out := do
  let n ← nulScan mem (mem.length + 1) (ix 1)
  transcode8 (mem.take (n - ix 1).val.toNat)

theorem nulScan_spec (pre post : List UInt16) (hz : (0 : UInt16) ∉ pre)
    (hn : (pre ++ 0 :: post).length < 2 ^ 60) :
    ∀ (d j : Nat) (k : Nat) (n : JInt64), pre.length - j = d → j ≤ pre.length → n.val = j + 1 →
      pre.length - j < k →
      ∃ N : JInt64, nulScan (pre ++ 0 :: post) k n = .ok N ∧ N.val = pre.length + 1 := by
  intro d
  induction d with
  | zero =>
    intro j k n h hj hv hk
    have hj' : j = pre.length := by omega
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hl : loadAt (pre ++ 0 :: post) n = .ok 0 := by
      unfold loadAt
      rw [ite_cond_eq_true _ _ (eq_true (by simp at hn ⊢; omega))]
      have : n.val.toNat - 1 = pre.length := by omega
      rw [this]; simp
    exact ⟨n, by simp only [nulScan, hl, bind, Except.bind]; rfl, by omega⟩
  | succ d ih =>
    intro j k n h hj hv hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hx : (pre ++ 0 :: post).getD j 0 = pre[j]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]
      rfl
    have hne : (pre[j]'(by omega) != 0) = true := by
      have : pre[j]'(by omega) ≠ 0 := fun e => hz (e ▸ List.getElem_mem _)
      simpa using this
    have hl : loadAt (pre ++ 0 :: post) n = .ok (pre[j]'(by omega)) := by
      unfold loadAt
      rw [ite_cond_eq_true _ _ (eq_true (by simp at hn ⊢; omega))]
      have : n.val.toNat - 1 = j := by omega
      rw [this, hx]
    have e1 : (n + ix 1).val = n.val + 1 := add_val _ _ (by simp; omega) (by simp at hn ⊢; omega)
    obtain ⟨N, e2, e3⟩ := ih (j + 1) k (n + ix 1) (by omega) (by omega) (by rw [e1, hv]; omega) (by omega)
    exact ⟨N, by simp only [nulScan, hl, bind, Except.bind, hne, ↓reduceIte]; exact e2, e3⟩

/-- `unsafe_string(p::Ptr{UInt16})` reads the code units up to the first NUL and
nothing after it: the result is `transcode(String, ...)` of the units before the
NUL, whatever follows. -/
def UnsafeStringNul : Prop :=
  ∀ pre post : List UInt16, (0 : UInt16) ∉ pre → (pre ++ 0 :: post).length < 2 ^ 60 →
    unsafeString16 (pre ++ 0 :: post) = transcode8 pre

theorem unsafeStringNul_proven : UnsafeStringNul := by
  intro pre post hz hn
  have hp : pre.length < 2 ^ 60 := by simp at hn; omega
  obtain ⟨N, e1, e2⟩ := nulScan_spec pre post hz hn _ 0 ((pre ++ 0 :: post).length + 1) (ix 1) rfl
    (by omega) (by simp) (by simp; omega)
  have e3 : (N - ix 1).val.toNat = pre.length := by
    rw [sub_val _ _ (by simp; omega) (by simp; omega)]; simp; omega
  simp only [unsafeString16, e1, bind, Except.bind, e3]
  simp

end JuliaLean.Transcode
