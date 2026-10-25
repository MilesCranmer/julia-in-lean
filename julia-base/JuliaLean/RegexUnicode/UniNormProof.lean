import JuliaLean.RegexUnicode.UniNormalize

/-!
# `isequal_normalized(s, s)` without `stripmark`

Without `STRIPMARK` every decomposition is nonempty, so `decompose_next_chars!` only
reads buffer positions it wrote in the same call. The two buffers then agree on the
positions `1:n` the main loop compares, whatever their uninitialized contents, and the
loop compares each written position with itself.
-/

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- Property (`isequal_normalized` docstring, `stdlib/Unicode/src/Unicode.jl:230-268`;
canonical equivalence is reflexive): without `stripmark`, `isequal_normalized(s, s)` is
`true` for every string of code points, every `casefold`, any uninitialized buffer
contents and every utf8proc table with the documented decomposition behaviour. -/
def IsequalNormalizedReflexive : Prop :=
  ∀ P : Utf8proc, P.DecompAxioms → ∀ (mem1 mem2 : Nat → UInt32) (s : JStr) (casefold : Bool),
    validCps s = true → isequalNormalized P mem1 mem2 s s casefold false = .ok true

/-- The buffers have the same length and agree at positions `1:n`. -/
def Agree (n : Nat) (a b : Buf) : Prop := a.len = b.len ∧ ∀ k, 1 ≤ k → k ≤ n → a.get k = b.get k

theorem Agree.mono {n m : Nat} {a b : Buf} (h : Agree n a b) (hm : m ≤ n) : Agree m a b :=
  ⟨h.1, fun k h1 h2 => h.2 k h1 (Nat.le_trans h2 hm)⟩

theorem Agree.resize {n : Nat} {a b : Buf} (h : Agree n a b) (m : Nat) :
    Agree n (a.resize m) (b.resize m) :=
  ⟨rfl, fun k h1 h2 => h.2 k h1 h2⟩

theorem Agree.set {n : Nat} {a b : Buf} (h : Agree n a b) (k : Nat) (v : UInt32) :
    Agree n (a.set k v) (b.set k v) := by
  refine ⟨h.1, fun i h1 h2 => ?_⟩
  simp only [Buf.get, Buf.set]
  split
  · rfl
  · exact h.2 i h1 h2

theorem Agree.setNext {n : Nat} {a b : Buf} (h : Agree n a b) (v : UInt32) :
    Agree (n + 1) (a.set (n + 1) v) (b.set (n + 1) v) := by
  refine ⟨h.1, fun i h1 h2 => ?_⟩
  simp only [Buf.get, Buf.set]
  by_cases hi : i = n + 1
  · simp [hi]
  · simp only [hi, if_false]; exact h.2 i h1 (by omega)

theorem Agree.swap {n : Nat} {a b : Buf} (h : Agree n a b) {i j : Nat} (hi1 : 1 ≤ i)
    (hi2 : i ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ n) : Agree n (a.swap i j) (b.swap i j) := by
  unfold Buf.swap
  rw [h.2 i hi1 hi2, h.2 j hj1 hj2]
  exact (h.set _ _).set _ _

theorem writeList_len (d : Buf) (p : Nat) (l : List UInt32) (r : Nat) :
    (d.writeList p l r).len = d.len := by
  induction l generalizing d p r with
  | nil => cases r <;> rfl
  | cons v l ih =>
    cases r with
    | zero => rfl
    | succ r => simp only [Buf.writeList]; rw [ih]; rfl

theorem Agree.writeList {p : Nat} {a b : Buf} (h : Agree p a b) (l : List UInt32) (r : Nat) :
    Agree (p + min l.length r) (a.writeList p l r) (b.writeList p l r) := by
  induction l generalizing p a b r with
  | nil => cases r <;> simpa [Buf.writeList] using h
  | cons v l ih =>
    cases r with
    | zero => simpa [Buf.writeList] using h
    | succ r =>
      simp only [Buf.writeList, List.length_cons]
      have e : p + min (l.length + 1) (r + 1) = p + 1 + min l.length r := by omega
      rw [e]
      exact ih (h.setNext v) r

theorem decomposeCharBang_ok {P : Utf8proc} {c : UInt32} {d : Buf} {offset options : Nat}
    {l : List UInt32} (hl : P.decomposeChar c options = .ok l) :
    decomposeCharBang P c d offset options =
      .ok (l.length, d.writeList offset l (d.len - offset)) := by
  simp only [decomposeCharBang, hl]

theorem decomposeRetry_succ (P : Utf8proc) (c : UInt32) (offset options f : Nat) (d : Buf) :
    decomposeRetry P c offset options (f + 1) d =
      match decomposeCharBang P c d offset options with
      | .error e => .error e
      | .ok (ret, d) =>
        if ret + offset > d.len then decomposeRetry P c offset options f (d.resize (2 * (ret + offset)))
        else .ok (ret + offset, d) := rfl

/-- The decompose-and-retry loop stores the decomposition at `offset+1 : offset+length`. -/
theorem decomposeRetry_agree {P : Utf8proc} {c : UInt32} {offset options : Nat}
    {l : List UInt32} {a b : Buf} (hl : P.decomposeChar c options = .ok l)
    (h : Agree offset a b) :
    ∃ a' b', decomposeRetry P c offset options 2 a = .ok (l.length + offset, a') ∧
      decomposeRetry P c offset options 2 b = .ok (l.length + offset, b') ∧
      Agree (l.length + offset) a' b' := by
  have hw := h.writeList l (a.len - offset)
  rw [show (2 : Nat) = 1 + 1 from rfl, decomposeRetry_succ, decomposeRetry_succ,
    decomposeCharBang_ok hl, decomposeCharBang_ok hl]
  simp only [writeList_len]
  rw [← h.1]
  by_cases hn : l.length + offset > a.len
  · simp only [hn, if_true]
    rw [decomposeRetry_succ, decomposeRetry_succ, decomposeCharBang_ok hl, decomposeCharBang_ok hl]
    have hr := ((hw.mono (m := offset) (by omega)).resize (2 * (l.length + offset))).writeList l
      (2 * (l.length + offset) - offset)
    simp only [writeList_len, Buf.resize]
    have hnot : ¬ (l.length + offset > 2 * (l.length + offset)) := by omega
    simp only [hnot, if_false]
    refine ⟨_, _, rfl, rfl, ?_⟩
    have e : offset + min l.length (2 * (l.length + offset) - offset) = l.length + offset := by
      omega
    rw [e] at hr
    exact hr
  · simp only [hn, if_false]
    refine ⟨_, _, rfl, rfl, ?_⟩
    have e : offset + min l.length (a.len - offset) = l.length + offset := by omega
    rw [e] at hw
    exact hw

/-- The character converts to a code point below `0x110000`. -/
def cpOK (c : UInt32) : Prop := ∃ u, codepoint c = .ok u ∧ u < 0x110000

/-- Sum of `dlen` over a list. -/
def dsum (P : Utf8proc) (options : Nat) : List UInt32 → Nat
  | [] => 0
  | c :: cs => dlen P options id c + dsum P options cs

theorem dsum_append (P : Utf8proc) (options : Nat) (l r : List UInt32) :
    dsum P options (l ++ r) = dsum P options l + dsum P options r := by
  induction l with
  | nil => simp [dsum]
  | cons c l ih => simp only [List.cons_append, dsum, ih]; omega

theorem loopBound_append (P : Utf8proc) (options : Nat) (l r : List UInt32) :
    loopBound P options id (l ++ r) = dsum P options l + l.length + loopBound P options id r := by
  induction l with
  | nil => simp [dsum]
  | cons c l ih => simp only [List.cons_append, loopBound, dsum, ih, List.length_cons]; omega

theorem chunkLoop_eq (P : Utf8proc) (casefold : Bool) (options : Nat) (ct : UInt32 → UInt32)
    (rest : List UInt32) (ch : UInt32) (offset : Nat) (d : Buf) :
    chunkLoop P casefold options ct rest ch offset d =
      match codepoint ch with
      | .error e => .error (.str e)
      | .ok u =>
        if ct u < 0x80 then
          .ok (1 + offset, (if 1 + offset > d.len then d.resize (2 * (1 + offset)) else d).set
            (1 + offset) (if casefold then (if inRange 0x41 0x5a (ct u) then ct u + 0x20 else ct u)
              else ct u), rest)
        else
          match decomposeRetry P (ct u) offset options 2 d with
          | .error e => .error e
          | .ok (n, d) =>
            if ccOf P (d.get n) == 0 then .ok (n, d, rest)
            else
              match rest with
              | [] => .ok (n, d, [])
              | ch' :: rest' => chunkLoop P casefold options ct rest' ch' n d := by
  rw [chunkLoop]; rfl

/-- The ASCII fast path stores at `1 + offset`, after growing the buffer if needed. -/
theorem ascii_agree {offset : Nat} {a b : Buf} (h : Agree offset a b) (v : UInt32) :
    Agree (1 + offset)
      ((if 1 + offset > a.len then a.resize (2 * (1 + offset)) else a).set (1 + offset) v)
      ((if 1 + offset > b.len then b.resize (2 * (1 + offset)) else b).set (1 + offset) v) := by
  rw [Nat.add_comm 1 offset]
  by_cases hc : offset + 1 > a.len
  · have hc' : offset + 1 > b.len := h.1 ▸ hc
    simp only [hc, hc', if_true]; exact (h.resize _).setNext _
  · have hc' : ¬ (offset + 1 > b.len) := h.1 ▸ hc
    simp only [hc, hc', if_false]; exact h.setNext _

/-- One chunk: both buffers produce the same `n` and state and agree on `1:n`; the chunk
consumes a nonempty prefix `pre` and `n` is `offset` plus its decomposition length. -/
theorem chunkLoop_agree {P : Utf8proc} (hP : P.DecompAxioms) (casefold : Bool) {options : Nat}
    (h6 : options.testBit 6 = false) (h13 : options.testBit 13 = false) :
    ∀ (rest : List UInt32) (ch : UInt32) (offset : Nat) (a b : Buf), Agree offset a b →
      (∀ c ∈ ch :: rest, cpOK c) →
      ∃ n a' b' pre r, chunkLoop P casefold options id rest ch offset a = .ok (n, a', r) ∧
        chunkLoop P casefold options id rest ch offset b = .ok (n, b', r) ∧ Agree n a' b' ∧
        ch :: rest = pre ++ r ∧ pre ≠ [] ∧ n = offset + dsum P options pre ∧ offset < n := by
  intro rest
  induction rest with
  | nil =>
    intro ch offset a b h hv
    obtain ⟨u, hu, hlt⟩ := hv ch (List.mem_cons_self ..)
    rw [chunkLoop_eq, chunkLoop_eq]
    simp only [hu, id]
    by_cases ha : u < 0x80
    · simp only [ha, if_true]
      refine ⟨_, _, _, [ch], [], rfl, rfl, ascii_agree h _, rfl, by simp, ?_, by omega⟩
      simp [dsum, dlen, hu, ha]; omega
    · obtain ⟨l, hl⟩ := hP.ok u options hlt h6
      have hne := hP.nonempty u options l h13 hl
      have hlen : 0 < l.length := by cases l with | nil => exact absurd rfl hne | cons _ _ => simp
      obtain ⟨a', b', ea, eb, hab⟩ := decomposeRetry_agree hl h
      simp only [ha, if_false, ea, eb]
      rw [hab.2 _ (by omega) (Nat.le_refl _)]
      have hd : dsum P options [ch] = l.length := by simp [dsum, dlen, hu, ha, hl]
      split
      · exact ⟨_, _, _, [ch], [], rfl, rfl, hab, rfl, by simp, by rw [hd]; omega, by omega⟩
      · exact ⟨_, _, _, [ch], [], rfl, rfl, hab, rfl, by simp, by rw [hd]; omega, by omega⟩
  | cons ch' rest' ih =>
    intro ch offset a b h hv
    obtain ⟨u, hu, hlt⟩ := hv ch (List.mem_cons_self ..)
    rw [chunkLoop_eq, chunkLoop_eq]
    simp only [hu, id]
    by_cases ha : u < 0x80
    · simp only [ha, if_true]
      refine ⟨_, _, _, [ch], ch' :: rest', rfl, rfl, ascii_agree h _, rfl, by simp, ?_, by omega⟩
      simp [dsum, dlen, hu, ha]; omega
    · obtain ⟨l, hl⟩ := hP.ok u options hlt h6
      have hne := hP.nonempty u options l h13 hl
      have hlen : 0 < l.length := by cases l with | nil => exact absurd rfl hne | cons _ _ => simp
      obtain ⟨a', b', ea, eb, hab⟩ := decomposeRetry_agree hl h
      simp only [ha, if_false, ea, eb]
      rw [hab.2 _ (by omega) (Nat.le_refl _)]
      have hd : dsum P options [ch] = l.length := by simp [dsum, dlen, hu, ha, hl]
      split
      · exact ⟨_, _, _, [ch], ch' :: rest', rfl, rfl, hab, rfl, by simp, by rw [hd]; omega, by omega⟩
      · obtain ⟨n, a2, b2, pre, r, e1, e2, hag, hsplit, hpre, hn, hlt2⟩ :=
          ih ch' (l.length + offset) a' b' hab (fun c hc => hv c (List.mem_cons_of_mem _ hc))
        refine ⟨n, a2, b2, ch :: pre, r, e1, e2, hag, by rw [hsplit]; rfl, by simp, ?_, by omega⟩
        have : dsum P options (ch :: pre) = l.length + dsum P options pre := by
          simp only [dsum]; rw [← hd]; simp [dsum]
        rw [this]; omega

/-! ## The sorts touch only positions `1:n` -/

theorem insInner_agree {P : Utf8proc} {cc n : Nat} :
    ∀ (k : Nat) (a b : Buf), k ≤ n → Agree n a b →
      Agree n (insInner P cc k a) (insInner P cc k b)
  | 0, _, _, _, h => h
  | 1, _, _, _, h => h
  | k + 2, a, b, hk, h => by
    simp only [insInner]
    rw [h.2 (k + 1) (by omega) (by omega)]
    split
    · exact h
    · exact insInner_agree (k + 1) _ _ (by omega) (h.swap (by omega) (by omega) (by omega) (by omega))

theorem insOuter_agree {P : Utf8proc} {n : Nat} :
    ∀ (k j1 : Nat) (a b : Buf), 2 ≤ j1 → j1 + k ≤ n + 1 → Agree n a b →
      Agree n (insOuter P k j1 a) (insOuter P k j1 b)
  | 0, _, _, _, _, _, h => h
  | k + 1, j1, a, b, h2, hk, h => by
    simp only [insOuter]
    rw [h.2 j1 (by omega) (by omega)]
    apply insOuter_agree k (j1 + 1) _ _ (by omega) (by omega)
    by_cases hc : (ccOf P (b.get j1) == 0) = true
    · rw [if_pos hc, if_pos hc]; exact h
    · rw [if_neg hc, if_neg hc]; exact insInner_agree j1 a b (by omega) h

theorem readList_agree {n : Nat} {a b : Buf} (h : Agree n a b) :
    ∀ (len p : Nat), 1 ≤ p → p + len ≤ n + 1 → a.readList p len = b.readList p len
  | 0, _, _, _ => rfl
  | len + 1, p, hp, hl => by
    simp only [Buf.readList]
    rw [h.2 p hp (by omega), readList_agree h len (p + 1) (by omega) (by omega)]

theorem writeAt_agree {n : Nat} :
    ∀ (l : List UInt32) (p : Nat) (a b : Buf), Agree n a b → Agree n (a.writeAt p l) (b.writeAt p l)
  | [], _, _, _, h => h
  | v :: l, p, a, b, h => writeAt_agree l (p + 1) _ _ (h.set p v)

theorem scanZero_agree {P : Utf8proc} {n : Nat} {a b : Buf} (h : Agree n a b) :
    ∀ (k p : Nat), 1 ≤ p → scanZero P a n k p = scanZero P b n k p
  | 0, _, _ => rfl
  | k + 1, p, hp => by
    simp only [scanZero]
    by_cases hpn : p > n
    · simp only [hpn, if_true]
    · rw [h.2 p hp (by omega), scanZero_agree h k (p + 1) (by omega)]

theorem scanZero_bounds (P : Utf8proc) (d : Buf) (n : Nat) :
    ∀ (k p : Nat), 1 ≤ p → 1 ≤ scanZero P d n k p ∧ scanZero P d n k p ≤ n + 1
  | 0, _, _ => ⟨by simp [scanZero], by simp [scanZero]⟩
  | k + 1, p, hp => by
    simp only [scanZero]
    split
    · omega
    · split
      · omega
      · exact scanZero_bounds P d n k (p + 1) (by omega)

theorem segLoop_agree {P : Utf8proc} {n : Nat} :
    ∀ (f j : Nat) (a b : Buf), 1 ≤ j → Agree n a b →
      Agree n (segLoop P n f j a) (segLoop P n f j b)
  | 0, _, _, _, _, h => h
  | f + 1, j, a, b, hj, h => by
    simp only [segLoop]
    split
    · rw [scanZero_agree h (n - j) (j + 1) (by omega)]
      have hb := scanZero_bounds P b n (n - j) (j + 1) (by omega)
      apply segLoop_agree f _ _ _ hb.1
      unfold sortRange
      rw [readList_agree h _ j hj (by omega)]
      exact writeAt_agree _ _ _ _ h
    · exact h

/-- `decompose_next_chars!` on two buffers of equal length. -/
theorem decomposeNext_agree {P : Utf8proc} (hP : P.DecompAxioms) (casefold : Bool) {options : Nat}
    (h6 : options.testBit 6 = false) (h13 : options.testBit 13 = false)
    (ch : UInt32) (rest : List UInt32) (a b : Buf) (hlen : a.len = b.len)
    (hv : ∀ c ∈ ch :: rest, cpOK c) :
    ∃ n a' b' pre r, decomposeNext P casefold options id ch rest a = .ok (n, a', r) ∧
      decomposeNext P casefold options id ch rest b = .ok (n, b', r) ∧ Agree n a' b' ∧
      ch :: rest = pre ++ r ∧ pre ≠ [] ∧ n = dsum P options pre ∧ 0 < n := by
  obtain ⟨n, a', b', pre, r, e1, e2, hag, hs, hpre, hn, hpos⟩ :=
    chunkLoop_agree hP casefold h6 h13 rest ch 0 a b ⟨hlen, fun k h1 h2 => by omega⟩ hv
  refine ⟨n, if n < 32 then insertionSort P n a' else segLoop P n n 1 a',
    if n < 32 then insertionSort P n b' else segLoop P n n 1 b', pre, r, ?_, ?_, ?_, hs, hpre,
    by omega, hpos⟩
  · simp only [decomposeNext, e1]
  · simp only [decomposeNext, e2]
  · by_cases h32 : n < 32
    · simp only [h32, if_true]
      exact insOuter_agree (n - 1) 2 a' b' (Nat.le_refl _) (by omega) hag
    · simp only [h32, if_false]
      exact segLoop_agree n 1 a' b' (Nat.le_refl _) hag

theorem dsum_pos_bound (P : Utf8proc) (options : Nat) (pre : List UInt32) (h : pre ≠ []) :
    1 ≤ pre.length := by
  cases pre with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- The main loop with both sides in the same state. -/
theorem isEqLoop_refl {P : Utf8proc} (hP : P.DecompAxioms) (casefold : Bool) {options : Nat}
    (h6 : options.testBit 6 = false) (h13 : options.testBit 13 = false) :
    ∀ (f : Nat) (d1 d2 : Buf) (n j : Nat) (i : List UInt32), Agree n d1 d2 → 1 ≤ j →
      j ≤ n + 1 → (∀ c ∈ i, cpOK c) → loopBound P options id i + (n + 1 - j) ≤ f →
      isEqLoop P casefold options id f d1 n j i d2 n j i = .ok true := by
  intro f
  induction f with
  | zero =>
    intro d1 d2 n j i _ _ _ _ hf
    cases i <;> simp [loopBound] at hf
  | succ f ih =>
    intro d1 d2 n j i h hj1 hj2 hv hf
    by_cases hjn : j > n
    · cases i with
      | nil =>
        simp only [isEqLoop, hjn, if_true, List.isEmpty_nil, decide_true, Bool.and_self]
      | cons c r =>
        obtain ⟨n', a', b', pre, r', e1, e2, hag, hs, hpre, hn, hpos⟩ :=
          decomposeNext_agree hP casefold h6 h13 c r d1 d2 h.1 hv
        simp only [isEqLoop, hjn, if_true, e1, e2]
        rw [hag.2 1 (Nat.le_refl _) (by omega)]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        apply ih a' b' n' 2 r' hag (by omega) (by omega)
        · intro x hx; exact hv x (by rw [hs]; exact List.mem_append_right _ hx)
        · rw [hs, loopBound_append] at hf
          have := dsum_pos_bound P options pre hpre
          omega
    · simp only [isEqLoop, hjn, if_false]
      rw [h.2 j hj1 (by omega)]
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      exact ih d1 d2 n (j + 1) i h (by omega) (by omega) hv (by omega)

theorem cpOK_of_validCps {s : JStr} (hv : validCps s = true) : ∀ c ∈ chars s, cpOK c := by
  intro c hc
  have := List.all_eq_true.mp hv c hc
  revert this
  cases h : codepoint c with
  | error e => simp
  | ok u => intro hu; exact ⟨u, h, by simpa using hu⟩

theorem isequalNormalizedReflexive_proven : IsequalNormalizedReflexive := by
  intro P hP m1 m2 s casefold hv
  have h6 : (eqOptions casefold false).testBit 6 = false := by cases casefold <;> decide
  have h13 : (eqOptions casefold false).testBit 13 = false := by cases casefold <;> decide
  unfold isequalNormalized
  exact isEqLoop_refl hP casefold h6 h13 _ _ _ 0 1 _ ⟨rfl, fun k h1 h2 => by omega⟩
    (Nat.le_refl _) (by omega) (cpOK_of_validCps hv) (by omega)

end JuliaLean.RegexUnicode.Uni
