import JuliaLean.Base64Uuid.DecodeGroup

/-!
`read_until_end` on clean input: it decodes the pending characters group by group,
whatever the buffer refills, fast or slow paths, and routes the bytes to the caller's
memory until it is full and to `pipe.rest` after that.

`Q` is every byte produced by the call (including those popped from `pipe.rest`); the
caller's memory holds `Q.take room` and `pipe.rest` is `Q.drop room`.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

theorem ign_ign : (CODE_IGN == CODE_IGN) = true := by decide

theorem ne_ign_of_isCode {d : Byte} (h : isCode d = true) : (d == CODE_IGN) = false := by
  cases hd : (d == CODE_IGN) with
  | false => rfl
  | true => rw [beq_iff_eq] at hd; subst hd; exact absurd h (by decide)

theorem ne_ign_pad : (CODE_PAD == CODE_IGN) = false := by decide
theorem ne_ign_end : (CODE_END == CODE_IGN) = false := by decide
theorem isCode_end : isCode CODE_END = false := by decide
theorem padOrEnd_end : padOrEnd CODE_END = true := by decide
theorem end_end : (CODE_END == CODE_END) = true := by decide

/-- A character of a clean group does not decode to `CODE_IGN`. -/
def NotIgn (c : Byte) : Prop := (decode c == CODE_IGN) = false

theorem notIgn_of_isCode {c : Byte} (h : isCode (decode c) = true) : NotIgn c := ne_ign_of_isCode h
theorem notIgn_of_pad {c : Byte} (h : decode c = CODE_PAD) : NotIgn c := by
  unfold NotIgn; rw [h]; exact ne_ign_pad

theorem fullG_notIgn {c1 c2 c3 c4 : Byte} (h : FullG c1 c2 c3 c4) :
    NotIgn c1 ∧ NotIgn c2 ∧ NotIgn c3 ∧ NotIgn c4 :=
  ⟨notIgn_of_isCode h.1, notIgn_of_isCode h.2.1, notIgn_of_isCode h.2.2.1, notIgn_of_isCode h.2.2.2⟩

theorem padG_notIgn {c1 c2 c3 c4 : Byte} (h : PadG c1 c2 c3 c4) :
    NotIgn c1 ∧ NotIgn c2 ∧ NotIgn c3 ∧ NotIgn c4 := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact ⟨notIgn_of_isCode h1, notIgn_of_isCode h2, notIgn_of_isCode h3, notIgn_of_pad h4⟩
  · exact ⟨notIgn_of_isCode h1, notIgn_of_isCode h2, notIgn_of_pad h3, notIgn_of_pad h4⟩

/-! ### The ignore-skipping loop -/

theorem skip_step (fuel : Nat) (b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (io : List Byte)
    (c : Byte) (P : List Byte) (hP : buf.drop i ++ io = c :: P) (hi0 : i ≤ buf.length) :
    ∃ i' io', buf.drop i' ++ io' = P ∧ i' ≤ buf.length ∧
      skipIgn (fuel + 1) CODE_IGN b2 b3 b4 buf i io = skipIgn fuel b2 b3 b4 (decode c) buf i' io' := by
  by_cases hi : i + 1 ≤ buf.length
  · have hlt : i < buf.length := by omega
    rw [List.drop_eq_getElem_cons hlt] at hP
    simp only [List.cons_append, List.cons.injEq] at hP
    obtain ⟨hc, hp⟩ := hP
    refine ⟨i + 1, io, hp, hi, ?_⟩
    simp only [skipIgn, ign_ign, ↓reduceIte, hi]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, hc]
  · have hd : buf.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd, List.nil_append] at hP
    subst hP
    refine ⟨i, P, by rw [hd, List.nil_append], by omega, ?_⟩
    simp only [skipIgn, ign_ign, ↓reduceIte, hi]

theorem skip_end (fuel : Nat) (b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (io : List Byte)
    (hP : buf.drop i ++ io = []) :
    skipIgn (fuel + 1) CODE_IGN b2 b3 b4 buf i io = skipIgn fuel b2 b3 b4 CODE_END buf i [] := by
  obtain ⟨hd, hio⟩ := List.append_eq_nil_iff.mp hP
  subst hio
  have hi : ¬ (i + 1 ≤ buf.length) := by have := List.drop_eq_nil_iff.mp hd; omega
  simp only [skipIgn, ign_ign, ↓reduceIte, hi]

theorem skip_done (fuel : Nat) (d1 d2 d3 d4 : Byte) (buf : List Byte) (i : Nat) (io : List Byte)
    (h1 : (d1 == CODE_IGN) = false) (h2 : (d2 == CODE_IGN) = false) (h3 : (d3 == CODE_IGN) = false)
    (h4 : (d4 == CODE_IGN) = false) :
    skipIgn (fuel + 1) d1 d2 d3 d4 buf i io = some (d1, d2, d3, d4, i, io) := by
  simp only [skipIgn, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]

theorem fresh_read4 (f : Nat) (buf : List Byte) (i : Nat) (io : List Byte) (c1 c2 c3 c4 : Byte)
    (P : List Byte) (hP : buf.drop i ++ io = c1 :: c2 :: c3 :: c4 :: P) (hi0 : i ≤ buf.length)
    (h1 : NotIgn c1) (h2 : NotIgn c2) (h3 : NotIgn c3) (h4 : NotIgn c4) :
    ∃ i' io', buf.drop i' ++ io' = P ∧ i' ≤ buf.length ∧
      skipIgn (f + 5) CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io =
        some (decode c1, decode c2, decode c3, decode c4, i', io') := by
  obtain ⟨i1, io1, hP1, hi1, e1⟩ := skip_step (f + 4) CODE_IGN CODE_IGN CODE_IGN buf i io c1 _ hP hi0
  obtain ⟨i2, io2, hP2, hi2, e2⟩ := skip_step (f + 3) CODE_IGN CODE_IGN (decode c1) buf i1 io1 c2 _ hP1 hi1
  obtain ⟨i3, io3, hP3, hi3, e3⟩ := skip_step (f + 2) CODE_IGN (decode c1) (decode c2) buf i2 io2 c3 _ hP2 hi2
  obtain ⟨i4, io4, hP4, hi4, e4⟩ := skip_step (f + 1) (decode c1) (decode c2) (decode c3) buf i3 io3 c4 _ hP3 hi3
  refine ⟨i4, io4, hP4, hi4, ?_⟩
  rw [show f + 5 = f + 4 + 1 from rfl, e1, e2, e3, e4, skip_done f _ _ _ _ buf i4 io4 h1 h2 h3 h4]

theorem fresh_end (f : Nat) (buf : List Byte) (i : Nat) (io : List Byte) (hP : buf.drop i ++ io = []) :
    skipIgn (f + 5) CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io =
      some (CODE_END, CODE_END, CODE_END, CODE_END, i, []) := by
  have hd : buf.drop i ++ [] = [] := by rw [List.append_nil]; exact (List.append_eq_nil_iff.mp hP).1
  rw [show f + 5 = f + 4 + 1 from rfl, skip_end _ _ _ _ _ _ _ hP, skip_end _ _ _ _ _ _ _ hd,
    skip_end _ _ _ _ _ _ _ hd, skip_end _ _ _ _ _ _ _ hd,
    skip_done f _ _ _ _ _ _ _ ne_ign_end ne_ign_end ne_ign_end ne_ign_end]

/-! ### Routing output bytes -/

theorem output_route (b : Byte) (Q : List Byte) (room : Nat) :
    output b (Q.take room) (Q.drop room) room = ((Q ++ [b]).take room, (Q ++ [b]).drop room) := by
  unfold output
  split
  · rename_i h
    rw [List.length_take] at h
    have hq : Q.length < room := by omega
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega),
      List.drop_of_length_le (by omega), List.drop_of_length_le (by simp; omega)]
  · rename_i h
    rw [List.length_take] at h
    have hq : room ≤ Q.length := by omega
    rw [List.take_append_of_le_length hq, List.drop_append_of_le_length hq]

/-- `decode_slow` on a clean group whose characters were read by the skip loop. -/
theorem decodeSlow_group (b1 b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (io : List Byte)
    (Q : List Byte) (room : Nat) (c1 c2 c3 c4 : Byte) (i' : Nat) (io' : List Byte)
    (hg : FullG c1 c2 c3 c4 ∨ PadG c1 c2 c3 c4)
    (hs : skipIgn (buf.length - i + io.length + 6) b1 b2 b3 b4 buf i io =
      some (decode c1, decode c2, decode c3, decode c4, i', io')) :
    decodeSlow b1 b2 b3 b4 buf i io (Q.take room) room (Q.drop room) =
      some (.ok ⟨i', (Q ++ specDec [c1, c2, c3, c4]).take room, (Q ++ specDec [c1, c2, c3, c4]).drop room,
        io', false⟩) := by
  unfold decodeSlow
  rw [hs]
  simp only [specDec, List.append_nil]
  rcases hg with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
  · simp only [quadBytes, h1, h2, h3, h4, Bool.and_self, ↓reduceIte, Option.getD_some]
    simp +decide only [↓reduceIte, output_route, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  · simp only [quadBytes, h1, h2, h3, h4, isCode_pad, padOrEnd_pad, Bool.and_self, Bool.and_true,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    simp +decide only [↓reduceIte, output_route, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  · simp only [quadBytes, h1, h2, h3, h4, isCode_pad, padOrEnd_pad, Bool.and_self, Bool.and_true,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    simp +decide only [↓reduceIte, output_route, List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-! ### One iteration -/

theorem isCode_ign : isCode CODE_IGN = false := by decide

theorem rueStep_fresh (buf : List Byte) (i : Nat) (io Q : List Byte) (room : Nat)
    (c1 c2 c3 c4 : Byte) (R : List Byte) (hP : buf.drop i ++ io = c1 :: c2 :: c3 :: c4 :: R)
    (hi : i ≤ buf.length) (hg : FullG c1 c2 c3 c4 ∨ PadG c1 c2 c3 c4) :
    ∃ i1 io1, buf.drop i1 ++ io1 = R ∧ i1 ≤ buf.length ∧
      rueStep CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io (Q.take room) room (Q.drop room) =
        some (.ok (i1, io1, (Q ++ specDec [c1, c2, c3, c4]).take room,
          (Q ++ specDec [c1, c2, c3, c4]).drop room, false)) := by
  have hn := hg.elim fullG_notIgn padG_notIgn
  obtain ⟨i1, io1, hR, hi1, hs⟩ := fresh_read4 (buf.length - i + io.length + 1) buf i io c1 c2 c3 c4 R
    hP hi hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  refine ⟨i1, io1, hR, hi1, ?_⟩
  have hd := decodeSlow_group CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io Q room c1 c2 c3 c4 i1 io1 hg hs
  simp only [rueStep, isCode_ign, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hd]

theorem rueStep_end (buf : List Byte) (i : Nat) (io Q : List Byte) (room : Nat)
    (hP : buf.drop i ++ io = []) :
    rueStep CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io (Q.take room) room (Q.drop room) =
      some (.ok (i, [], Q.take room, Q.drop room, true)) := by
  have hs := fresh_end (buf.length - i + io.length + 1) buf i io hP
  simp only [rueStep, isCode_ign, Bool.false_and, Bool.false_eq_true, ↓reduceIte, decodeSlow]
  rw [show buf.length - i + io.length + 6 = buf.length - i + io.length + 1 + 5 from rfl, hs]
  simp +decide only [isCode_end, padOrEnd_end, end_end, Bool.false_and, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem rueStep_loaded (buf : List Byte) (i : Nat) (io Q : List Byte) (room : Nat)
    (c1 c2 c3 c4 : Byte) (hg : FullG c1 c2 c3 c4 ∨ PadG c1 c2 c3 c4) :
    rueStep (decode c1) (decode c2) (decode c3) (decode c4) buf i io (Q.take room) room (Q.drop room) =
      some (.ok (i, io, (Q ++ specDec [c1, c2, c3, c4]).take room,
        (Q ++ specDec [c1, c2, c3, c4]).drop room, false)) := by
  have hn := hg.elim fullG_notIgn padG_notIgn
  have hs := skip_done (buf.length - i + io.length + 5) _ _ _ _ buf i io hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  have hd := decodeSlow_group (decode c1) (decode c2) (decode c3) (decode c4) buf i io Q room
    c1 c2 c3 c4 i io hg hs
  unfold rueStep
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hroom⟩ := hc
    rw [List.length_take] at hroom
    have hq : Q.length + 3 ≤ room := by omega
    simp only [specDec, quadBytes, h1, h2, h3, h4, Bool.and_self, ↓reduceIte, Option.getD_some,
      List.append_nil]
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega),
      List.drop_of_length_le (by omega), List.drop_of_length_le (by simp; omega)]
  · rw [hd]

/-! ### The loop -/

/-- What `read_until_end`'s loop returns for clean pending characters `P`: it has
decoded a prefix `P1` of whole groups, and either decoded everything or filled the
caller's memory. -/
def RuePost (r : Option (Jle (Nat × List Byte × List Byte × List Byte × List Byte)))
    (P Q : List Byte) (room : Nat) : Prop :=
  ∃ i' buf' io' P1 P', r = some (.ok (i', buf', io', (Q ++ specDec P1).take room,
      (Q ++ specDec P1).drop room)) ∧
    P = P1 ++ P' ∧ P1.length % 4 = 0 ∧ buf'.drop i' ++ io' = P' ∧ i' ≤ buf'.length ∧ Clean P' ∧
    (P' = [] ∨ room ≤ (Q ++ specDec P1).length)

def RueSpec (n : Nat) : Prop :=
  ∀ (fuel : Nat) (P Q : List Byte) (room : Nat), P.length = 4 * n → Clean P → n + 2 ≤ fuel →
    (∀ buf i io, buf.drop i ++ io = P → i ≤ buf.length →
      RuePost (rueLoop fuel CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf i io (Q.take room) room
        (Q.drop room)) P Q room) ∧
    (∀ c1 c2 c3 c4 R buf i io, P = c1 :: c2 :: c3 :: c4 :: R → buf.drop i ++ io = R → i ≤ buf.length →
      RuePost (rueLoop fuel (decode c1) (decode c2) (decode c3) (decode c4) buf i io (Q.take room) room
        (Q.drop room)) P Q room)

theorem spec_cons (Q P1 : List Byte) (c1 c2 c3 c4 : Byte) :
    Q ++ specDec (c1 :: c2 :: c3 :: c4 :: P1) = Q ++ specDec [c1, c2, c3, c4] ++ specDec P1 := by
  simp only [specDec, List.append_nil, List.append_assoc]

theorem post_cons (r : Option (Jle (Nat × List Byte × List Byte × List Byte × List Byte)))
    (c1 c2 c3 c4 : Byte) (R Q : List Byte) (room : Nat)
    (h : RuePost r R (Q ++ specDec [c1, c2, c3, c4]) room) :
    RuePost r (c1 :: c2 :: c3 :: c4 :: R) Q room := by
  obtain ⟨i', buf', io', P1, P', hr, hR, hP1, hb, hi, hc, hs⟩ := h
  refine ⟨i', buf', io', c1 :: c2 :: c3 :: c4 :: P1, P', ?_, by simp [hR], by simp; omega, hb, hi, hc, ?_⟩
  · rw [hr, spec_cons Q P1]
  · rw [spec_cons Q P1]; exact hs

theorem drop_getD (L : List Byte) (i : Nat) (h : i < L.length) :
    L.drop i = L.getD i (b8 0) :: L.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem readToBuffer_pend (B O : List Byte) :
    (readToBuffer B O).1.drop 0 ++ (readToBuffer B O).2 = B ++ O := by
  unfold readToBuffer
  split
  · simp
  · simp only [List.drop_zero, List.append_assoc, List.take_append_drop]

theorem rue_cont (n : Nat) (ih : RueSpec n) (f : Nat) (hf : n + 2 ≤ f) (c1 c2 c3 c4 : Byte)
    (R Q : List Byte) (room : Nat) (hR : R.length = 4 * n) (hcR : Clean R)
    (b1 b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (io : List Byte) (i1 : Nat) (io1 : List Byte)
    (hR1 : buf.drop i1 ++ io1 = R) (hi1 : i1 ≤ buf.length)
    (hstep : rueStep b1 b2 b3 b4 buf i io (Q.take room) room (Q.drop room) =
      some (.ok (i1, io1, (Q ++ specDec [c1, c2, c3, c4]).take room,
        (Q ++ specDec [c1, c2, c3, c4]).drop room, false))) :
    RuePost (rueLoop (f + 1) b1 b2 b3 b4 buf i io (Q.take room) room (Q.drop room))
      (c1 :: c2 :: c3 :: c4 :: R) Q room := by
  simp only [rueLoop, hstep, Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · rename_i h4
      apply post_cons
      have e : buf.drop i1 = buf.getD i1 (b8 0) :: buf.getD (i1 + 1) (b8 0) :: buf.getD (i1 + 2) (b8 0) ::
          buf.getD (i1 + 3) (b8 0) :: buf.drop (i1 + 4) := by
        rw [drop_getD buf i1 (by omega), drop_getD buf (i1 + 1) (by omega),
          drop_getD buf (i1 + 2) (by omega), drop_getD buf (i1 + 3) (by omega)]
      rw [e] at hR1
      exact (ih f R _ room hR hcR hf).2 _ _ _ _ (buf.drop (i1 + 4) ++ io1) buf (i1 + 4) io1
        (by rw [← hR1]; rfl) rfl h4
    · apply post_cons
      have hp := readToBuffer_pend (buf.drop i1) io1
      rw [hR1] at hp
      generalize readToBuffer (buf.drop i1) io1 = rb at hp
      obtain ⟨buf', io'⟩ := rb
      exact (ih f R _ room hR hcR hf).1 buf' 0 io' hp (Nat.zero_le _)
  · rename_i hfull
    rw [List.length_take] at hfull
    exact ⟨i1, buf, io1, [c1, c2, c3, c4], R, rfl, rfl, by simp, hR1, hi1, hcR, Or.inr (by omega)⟩

theorem rue_main : ∀ n, RueSpec n := by
  intro n
  induction n with
  | zero =>
    intro fuel P Q room hl _ hf
    have hP : P = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hP
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨fun buf i io hb hi => ?_, fun c1 c2 c3 c4 R buf i io h => absurd h (by simp)⟩
    refine ⟨i, buf, [], [], [], ?_, rfl, rfl, by rw [List.append_nil]; exact (List.append_eq_nil_iff.mp hb).1, hi, trivial, Or.inl rfl⟩
    simp only [rueLoop, rueStep_end buf i io Q room hb, ↓reduceIte, specDec, List.append_nil]
  | succ n ih =>
    intro fuel P Q room hl hc hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    match P, hl, hc with
    | c1 :: c2 :: c3 :: c4 :: R, hl, hc =>
      have hR : R.length = 4 * n := by simp at hl; omega
      have hg : FullG c1 c2 c3 c4 ∨ PadG c1 c2 c3 c4 := by
        rcases hc with ⟨h, _⟩ | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr h
      have hcR : Clean R := by
        rcases hc with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · subst h; trivial
      refine ⟨fun buf i io hb hi => ?_, fun d1 d2 d3 d4 R' buf i io hP hb hi => ?_⟩
      · obtain ⟨i1, io1, hR1, hi1, hs⟩ := rueStep_fresh buf i io Q room c1 c2 c3 c4 R hb hi hg
        exact rue_cont n ih f (by omega) c1 c2 c3 c4 R Q room hR hcR _ _ _ _ buf i io i1 io1 hR1 hi1 hs
      · simp only [List.cons.injEq] at hP
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hP
        exact rue_cont n ih f (by omega) c1 c2 c3 c4 R Q room hR hcR _ _ _ _ buf i io i io hb hi
          (rueStep_loaded buf i io Q room c1 c2 c3 c4 hg)
    | [], hl, _ => exact absurd hl (by simp)
    | [_], hl, _ => exact absurd hl (by simp; omega)
    | [_, _], hl, _ => exact absurd hl (by simp; omega)
    | [_, _, _], hl, _ => exact absurd hl (by simp; omega)

end JuliaLean.Base64Uuid
