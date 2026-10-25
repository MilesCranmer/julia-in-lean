import JuliaLean.Base64Uuid.DecodeSim

/-!
`base64decode(base64encode(x)) == x`.

`base64decode` reads with `readbytes!` into buffers of 1024, 2048, 4096, ... bytes. A
call to `read_until_end` stops when the buffer is full and leaves the undecoded
characters in the pipe buffer, which `eof` ignores; the loop would then stop early if
`pipe.rest` were empty. That needs the bytes decoded so far, `1024 * 2^j`, to end on a
group boundary, i.e. to be a multiple of 3, which they never are while complete
groups remain. (With a padded group in the middle the count can be a multiple of 3:
`base64uuid-decode-padding-midstream`.)
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-! ### Clean character lists -/

theorem clean_len : ∀ P : List Byte, Clean P → P.length % 4 = 0
  | [], _ => rfl
  | [_], h => absurd h id
  | [_, _], h => absurd h id
  | [_, _, _], h => absurd h id
  | _ :: _ :: _ :: _ :: R, h => by
    have : R.length % 4 = 0 := by
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · exact clean_len R h
      · subst h; rfl
    simp; omega

theorem specDec_append : ∀ (A B : List Byte), A.length % 4 = 0 → specDec (A ++ B) = specDec A ++ specDec B
  | [], B, _ => rfl
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h
  | c1 :: c2 :: c3 :: c4 :: A, B, h => by
    simp only [List.cons_append, specDec, List.append_assoc]
    rw [specDec_append A B (by simp at h; omega)]

theorem quad_len (d1 d2 d3 d4 : Byte) : ((quadBytes d1 d2 d3 d4).getD []).length ≤ 3 := by
  unfold quadBytes
  repeat' split
  all_goals simp

theorem full_quad_len {c1 c2 c3 c4 : Byte} (h : FullG c1 c2 c3 c4) :
    ((quadBytes (decode c1) (decode c2) (decode c3) (decode c4)).getD []).length = 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [quadBytes, h1, h2, h3, h4]

theorem pad_quad_ne {c1 c2 c3 c4 : Byte} (h : PadG c1 c2 c3 c4) :
    (quadBytes (decode c1) (decode c2) (decode c3) (decode c4)).getD [] ≠ [] := by
  obtain ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := h
  · simp [quadBytes, h1, h2, h3, h4, isCode_pad, padOrEnd_pad]
  · simp [quadBytes, h1, h2, h3, h4, isCode_pad, padOrEnd_pad]

theorem specDec_len_le : ∀ P : List Byte, (specDec P).length ≤ P.length
  | [] => by simp [specDec]
  | [_] => by simp [specDec]
  | [_, _] => by simp [specDec]
  | [_, _, _] => by simp [specDec]
  | c1 :: c2 :: c3 :: c4 :: R => by
    have := quad_len (decode c1) (decode c2) (decode c3) (decode c4)
    have := specDec_len_le R
    simp only [specDec, List.length_append, List.length_cons]
    omega

theorem specDec_ne_nil : ∀ P : List Byte, Clean P → P ≠ [] → specDec P ≠ []
  | [], _, h => absurd rfl h
  | [_], h, _ => absurd h id
  | [_, _], h, _ => absurd h id
  | [_, _, _], h, _ => absurd h id
  | c1 :: c2 :: c3 :: c4 :: R, h, _ => by
    simp only [specDec]
    intro he
    have hq := (List.append_eq_nil_iff.mp he).1
    rcases h with ⟨hf, _⟩ | ⟨_, hp⟩
    · have := full_quad_len hf; rw [hq] at this; simp at this
    · exact pad_quad_ne hp hq

theorem clean_prefix_full : ∀ (A B : List Byte), Clean (A ++ B) → A.length % 4 = 0 → B ≠ [] →
    (specDec A).length = 3 * (A.length / 4)
  | [], _, _, _, _ => rfl
  | [_], _, _, h, _ => by simp at h
  | [_, _], _, _, h, _ => by simp at h
  | [_, _, _], _, _, h, _ => by simp at h
  | c1 :: c2 :: c3 :: c4 :: A, B, hc, hA, hB => by
    simp only [List.cons_append] at hc
    rcases hc with ⟨hf, hc⟩ | ⟨he, _⟩
    · have ih := clean_prefix_full A B hc (by simp at hA; omega) hB
      simp only [specDec, List.length_append, full_quad_len hf, ih, List.length_cons]
      simp at hA
      omega
    · exact absurd (List.append_eq_nil_iff.mp he).2 hB

theorem clean_encFull : ∀ (full T : List Byte), full.length % 3 = 0 → Clean T → Clean (encFull full ++ T)
  | [], T, _, h => by simpa [encFull] using h
  | [_], _, h, _ => by simp at h
  | [_, _], _, h, _ => by simp at h
  | b1 :: b2 :: b3 :: full, T, h, hT => by
    simp only [encFull, enc4, List.cons_append, List.nil_append, List.append_assoc]
    refine Or.inl ⟨?_, clean_encFull full T (by simp at h; omega) hT⟩
    simp only [FullG, decode_encode, isCode_band63, and_self]

theorem clean_close (tail : List Byte) (ht : tail.length ≤ 2) : Clean (close ⟨[], tail⟩) := by
  match tail, ht with
  | [], _ => trivial
  | [b1], _ =>
    simp only [close, loadtriplet]
    refine Or.inr ⟨rfl, ?_⟩
    simp only [PadG, decode_encode, isCode_band63, decode_pad, and_self, or_true, true_and]
  | [b1, b2], _ =>
    simp only [close, loadtriplet]
    refine Or.inr ⟨rfl, ?_⟩
    simp only [PadG, decode_encode, isCode_band63, decode_pad, and_self, true_or, true_and]

theorem clean_base64encode (x : List Byte) : Clean (base64encode x) := by
  obtain ⟨full, tail, -, hf, ht, he⟩ := base64encode_split x
  rw [he]
  exact clean_encFull full _ hf (clean_close tail ht)

theorem pow2_mod3 : ∀ j : Nat, 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2
  | 0 => Or.inl rfl
  | j + 1 => by rw [Nat.pow_succ]; rcases pow2_mod3 j with h | h <;> omega

theorem buflen_not_mul3 (j : Nat) : (1024 * 2 ^ j) % 3 ≠ 0 := by
  rcases pow2_mod3 j with h | h <;> omega

/-! ### `read_until_end` -/

theorem take_min_len (l : List Byte) (k : Nat) : l.take (min k l.length) = l.take k := by
  by_cases h : k ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

theorem drop_min_len (l : List Byte) (k : Nat) : l.drop (min k l.length) = l.drop k := by
  by_cases h : k ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_of_length_le (by omega)]

theorem rue_spec (pipe : DPipe) (room : Nat) (hc : Clean (pipe.buf ++ pipe.io)) :
    ∃ P1 P' pipe', readUntilEnd (rueFuel pipe) pipe room =
        some (.ok ((pipe.rest ++ specDec P1).take room, pipe')) ∧
      pipe'.rest = (pipe.rest ++ specDec P1).drop room ∧ pipe.buf ++ pipe.io = P1 ++ P' ∧
      P1.length % 4 = 0 ∧ pipe'.buf ++ pipe'.io = P' ∧ Clean P' ∧
      (P' = [] ∨ room ≤ (pipe.rest ++ specDec P1).length) := by
  have hl := clean_len _ hc
  have hlen : (pipe.buf ++ pipe.io).length = 4 * ((pipe.buf ++ pipe.io).length / 4) := by omega
  obtain ⟨i', buf', io', P1, P', hr, hP, hP1, hb, -, hcP, hs⟩ :=
    (rue_main _ (rueFuel pipe) (pipe.buf ++ pipe.io) pipe.rest room hlen hc
      (by simp only [rueFuel, List.length_append] at hlen ⊢; omega)).1 pipe.buf 0 pipe.io rfl (Nat.zero_le _)
  refine ⟨P1, P', ⟨io', buf'.drop i', (pipe.rest ++ specDec P1).drop room⟩, ?_, rfl, hP, hP1, hb, hcP, hs⟩
  simp only [readUntilEnd, take_min_len, drop_min_len, hr]

/-! ### The `readbytes!` loop of `read(pipe)` -/

/-- Loop invariant of `readbytes!(pipe, b, typemax(Int))` on the clean source `s`. -/
def OInv (s : List Byte) (pipe : DPipe) (data : Vec) (filled : Nat) : Prop :=
  ∃ Pc j, s = Pc ++ (pipe.buf ++ pipe.io) ∧ Pc.length % 4 = 0 ∧ Clean (pipe.buf ++ pipe.io) ∧
    data.pre ++ pipe.rest = specDec Pc ∧ data.pre.length = filled ∧ filled ≤ data.len ∧
    data.len = 1024 * 2 ^ j ∧ data.len ≤ 2 ^ 49 ∧ (pipe.rest ≠ [] → filled = data.len) ∧
    (pipe.buf ++ pipe.io = [] ∨ filled = data.len ∨ pipe.io ≠ [])

theorem typemax_eq : typemaxInt = 9223372036854775807 := rfl

theorem p48 : (2 : Nat) ^ 48 = 281474976710656 := rfl
theorem p49 : (2 : Nat) ^ 49 = 562949953421312 := rfl

theorem loop_spec (s : List Byte) (hs : Clean s) (hsz : (specDec s).length < 2 ^ 48) :
    ∀ (F : Nat) (pipe : DPipe) (data : Vec) (filled : Nat), OInv s pipe data filled →
      (specDec (pipe.buf ++ pipe.io)).length + pipe.rest.length + 2 ≤ F →
      ∀ nb : Int, nb = typemaxInt → ∃ pipe' data', readbytesLoop F pipe data filled nb =
        some (.ok (pipe', data', (specDec s).length)) ∧ data'.pre = specDec s := by
  rw [p48] at hsz
  intro F
  induction F with
  | zero => intro _ _ _ _ h; omega
  | succ F ih =>
    intro pipe data filled hinv hF nb hnb
    obtain ⟨Pc, j, hsP, hPc, hcl, hpre, hfill, hle, hlen, hlen49, hrest, hend⟩ := hinv
    rw [p49] at hlen49
    have hsplit : specDec s = specDec Pc ++ specDec (pipe.buf ++ pipe.io) := by
      rw [hsP, specDec_append _ _ hPc]
    have hfs : filled ≤ (specDec s).length := by
      rw [hsplit, ← hpre]; simp; omega
    simp only [readbytesLoop, rbStep]
    by_cases heof : eof pipe = true
    · -- the loop stops: everything has been decoded
      have heof2 := heof
      simp only [eof, Bool.and_eq_true, List.isEmpty_iff] at heof2
      obtain ⟨hr0, hio0⟩ := heof2
      have hpend : pipe.buf ++ pipe.io = [] := by
        rcases hend with h | h | h
        · exact h
        · by_cases hne : pipe.buf ++ pipe.io = []
          · exact hne
          · have h3 := clean_prefix_full Pc _ (hsP ▸ hs) hPc hne
            rw [← hpre, hr0, List.append_nil, hfill, h, hlen] at h3
            exact absurd (by omega) (buflen_not_mul3 j)
        · exact absurd hio0 h
      have hpre' : data.pre = specDec s := by
        rw [hsplit, hpend, ← hpre, hr0]; simp [specDec]
      simp only [heof, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨pipe, data, ?_, hpre'⟩
      rw [← hfill, hpre']
    · have hne : ¬ (pipe.rest = [] ∧ pipe.io = []) := fun ⟨h1, h2⟩ => heof (by simp [eof, h1, h2])
      have heof' : eof pipe = false := by simpa using heof
      have hlt : (filled : Int) < nb := by rw [hnb, typemax_eq]; omega
      simp only [heof', hlt, Bool.not_false, Bool.and_true, decide_true, ↓reduceIte]
      -- the destination after the possible doubling
      have hdata : ∃ len' j', (if (data.len == filled) = true then
            ({ len := (min (2 * (data.len : Int)) nb).toNat, pre := data.pre } : Vec) else data) =
          ⟨len', data.pre⟩ ∧ len' = 1024 * 2 ^ j' ∧ filled < len' ∧ len' ≤ 562949953421312 ∧
          (min (len' : Int) nb) = len' := by
        by_cases hq : data.len = filled
        · refine ⟨2 * data.len, j + 1, ?_, by rw [hlen, Nat.pow_succ]; omega, ?_, ?_, ?_⟩
          · simp only [hq, beq_self_eq_true, ↓reduceIte]
            congr 1; rw [hnb, typemax_eq]; omega
          · have : 0 < data.len := by rw [hlen]; exact Nat.mul_pos (by decide) (Nat.two_pow_pos j)
            omega
          · omega
          · rw [hnb, typemax_eq]; omega
        · refine ⟨data.len, j, ?_, hlen, by omega, hlen49, by rw [hnb, typemax_eq]; omega⟩
          simp only [beq_iff_eq, hq, ↓reduceIte]
      obtain ⟨len', j', hd, hlen', hfl, hl49, hmin⟩ := hdata
      rw [hd]
      dsimp only
      rw [hmin]
      have hroom : ((len' : Int) - filled).toNat = len' - filled := by omega
      rw [hroom]
      obtain ⟨P1, P', pipe', hrue, hrest', hsplit1, hP1, hpend', hcl', hstop⟩ :=
        rue_spec pipe (len' - filled) hcl
      rw [hrue]
      dsimp only
      have hpre_take : data.pre.take filled = data.pre := by rw [← hfill]; exact List.take_length
      rw [hpre_take]
      have hQ := List.take_append_drop (len' - filled) (pipe.rest ++ specDec P1)
      have hinv' : OInv s pipe' ⟨len', data.pre ++ (pipe.rest ++ specDec P1).take (len' - filled)⟩
          (filled + ((pipe.rest ++ specDec P1).take (len' - filled)).length) := by
        refine ⟨Pc ++ P1, j', ?_, by simp; omega, hpend' ▸ hcl', ?_, by simp [hfill], by simp; omega,
          hlen', by rw [p49]; exact hl49, ?_, ?_⟩
        · rw [hsP, hsplit1, hpend', List.append_assoc]
        · rw [hrest', List.append_assoc, hQ, ← List.append_assoc, hpre, specDec_append _ _ hPc]
        · intro hr
          rw [hrest'] at hr
          have : len' - filled ≤ (pipe.rest ++ specDec P1).length := by
            by_cases h : len' - filled ≤ (pipe.rest ++ specDec P1).length
            · exact h
            · exact absurd (List.drop_of_length_le (by omega)) hr
          simp only [List.length_take]; omega
        · rcases hstop with h | h
          · exact Or.inl (hpend'.trans h)
          · exact Or.inr (Or.inl (by simp only [List.length_take]; omega))
      -- the measure decreases
      have hm : (specDec (pipe.buf ++ pipe.io)).length =
          (specDec P1).length + (specDec (pipe'.buf ++ pipe'.io)).length := by
        rw [hsplit1, specDec_append _ _ hP1, hpend']; simp
      have hdrop : pipe'.rest.length = pipe.rest.length + (specDec P1).length - (len' - filled) := by
        rw [hrest']; simp
      have hpos : 0 < (specDec (pipe.buf ++ pipe.io)).length + pipe.rest.length := by
        by_cases hr : pipe.rest = []
        · have hio : pipe.io ≠ [] := fun h => hne ⟨hr, h⟩
          have hp : pipe.buf ++ pipe.io ≠ [] := by simp [hio]
          have := List.length_pos_iff.mpr (specDec_ne_nil _ hcl hp)
          omega
        · have := List.length_pos_iff.mpr hr; omega
      have hmeas : (specDec (pipe'.buf ++ pipe'.io)).length + pipe'.rest.length + 2 ≤ F := by
        simp only [List.length_append] at hstop
        rcases hstop with h | h
        · have : (specDec (pipe'.buf ++ pipe'.io)).length = 0 := by rw [hpend', h]; rfl
          omega
        · omega
      exact ih pipe' _ _ hinv' hmeas nb hnb

theorem encodeDecodeRoundtrip_proven : EncodeDecodeRoundtrip := by
  intro x hx
  have hc := clean_base64encode x
  have hsd := specDec_base64encode x
  have hsz : (specDec (base64encode x)).length < 2 ^ 48 := by rw [hsd]; exact hx
  have hinv : OInv (base64encode x) (DPipe.new (base64encode x)) ⟨1024, []⟩ 0 :=
    ⟨[], 0, by simp [DPipe.new], rfl, by simpa [DPipe.new] using hc, by simp [DPipe.new, specDec], rfl,
      by decide, rfl, by decide, by simp [DPipe.new], by
        by_cases h : base64encode x = []
        · exact Or.inl (by simp [DPipe.new, h])
        · exact Or.inr (Or.inr (by simpa [DPipe.new] using h))⟩
  have hfuel : (specDec ((DPipe.new (base64encode x)).buf ++ (DPipe.new (base64encode x)).io)).length +
      (DPipe.new (base64encode x)).rest.length + 2 ≤
      rbFuel (DPipe.new (base64encode x)) ⟨1024, []⟩ := by
    have := specDec_len_le (base64encode x)
    simp only [DPipe.new, List.nil_append, List.length_nil, rbFuel] at this ⊢
    omega
  obtain ⟨pipe', data', hloop, hpre⟩ := loop_spec _ hc hsz _ _ _ _ hinv hfuel typemaxInt rfl
  have h1 : ¬ (typemaxInt < 0) := by rw [typemax_eq]; decide
  simp only [base64decode, readAll, readN, h1, ↓reduceIte, beq_self_eq_true, readbytesF, hloop, hpre, hsd,
    List.take_length]

end JuliaLean.Base64Uuid
