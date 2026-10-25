import JuliaLean.Printf.Props

/-!
Proofs of the Printf properties that hold.
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float

/-! ## Flags -/

/-- The flags of `fl` added to `s0`, then `zero` cleared by `-`. -/
private def applyFlags (s0 : Spec) (fl : Bytes) : Spec :=
  { s0 with
    leftalign := s0.leftalign || fl.contains 45
    plus := s0.plus || fl.contains 43
    space := s0.space || fl.contains 32
    hash := s0.hash || fl.contains 35
    zero := (s0.zero || fl.contains 48) && !(s0.leftalign || fl.contains 45) }

/-- The flag loop with any starting `Spec`. -/
private theorem parseFlags_list (b : Nat) (r : Bytes) (hb : isFlag b = false) :
    ∀ (fl : Bytes), (∀ c ∈ fl, isFlag c = true) → ∀ (s0 : Spec) (x : Nat) (rest : Bytes),
    x :: rest = fl ++ b :: r → parseFlags s0 x rest = .ok (applyFlags s0 fl, b, r) := by
  simp only [isFlag, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hb
  obtain ⟨⟨⟨⟨h45, h43⟩, h32⟩, h48⟩, h35⟩ := hb
  intro fl
  induction fl with
  | nil =>
    intro _ s0 x rest h
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [parseFlags.eq_def]
    simp [h45, h43, h32, h48, h35, applyFlags]
  | cons c fl ih =>
    intro hfl s0 x rest h
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc : isFlag x = true := hfl x (by simp)
    have ih := ih (fun d hd => hfl d (by simp [hd]))
    obtain ⟨y, rest2, hy⟩ : ∃ y rest2, fl ++ b :: r = y :: rest2 := by
      cases fl <;> simp
    rw [hy, parseFlags.eq_def]
    simp only [isFlag, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with (((hc | hc) | hc) | hc) | hc <;> subst hc <;>
      simp only [Nat.reduceBEq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true] <;>
      rw [ih _ y rest2 hy.symm] <;> cases s0 <;> simp [applyFlags]

/-- C99 p4: flags in any order. -/
theorem flagsAnyOrder_proven : FlagsAnyOrder := by
  intro fl b r hfl hb
  rw [parseFlags_list b r hb fl hfl {} _ _ (by cases fl <;> simp)]
  simp [flagSpec, applyFlags]

/-! ## Int64 arithmetic and the buffer -/

theorem i64_min : IntTy.min .i64 = -9223372036854775808 := by rfl
theorem i64_max : IntTy.max .i64 = 9223372036854775807 := by rfl

theorem I_bounds (a : I) : -9223372036854775808 ≤ a.val ∧ a.val ≤ 9223372036854775807 := by
  have := a.2; have := i64_min; have := i64_max; omega

theorem in_i64 (n : Int) (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64 := by
  have := i64_min; have := i64_max; omega

theorem ix_val (n : Int) (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    (ix n).val = n :=
  wrapInt_of_inRange .i64 n (in_i64 n h1 h2)

theorem ix_zero : (ix 0).val = 0 := rfl
theorem ix_natzero : (ix ((0 : Nat) : Int)).val = 0 := rfl

theorem ix_of_val (a : I) : ix a.val = a :=
  Subtype.ext (wrapInt_of_inRange .i64 a.val a.2)

theorem sub_val (a b : I) (h1 : -9223372036854775808 ≤ a.val - b.val)
    (h2 : a.val - b.val ≤ 9223372036854775807) : (a - b).val = a.val - b.val :=
  wrapInt_of_inRange .i64 _ (in_i64 _ h1 h2)

theorem add_val (a b : I) (h1 : -9223372036854775808 ≤ a.val + b.val)
    (h2 : a.val + b.val ≤ 9223372036854775807) : (a + b).val = a.val + b.val :=
  wrapInt_of_inRange .i64 _ (in_i64 _ h1 h2)

theorem imax_val (a b : I) : (imax a b).val = if a.val < b.val then b.val else a.val := by
  unfold imax; split <;> rfl

theorem cadd_ok (a b : I) (h1 : -9223372036854775808 ≤ a.val + b.val)
    (h2 : a.val + b.val ≤ 9223372036854775807) : cadd a b = .ok (ix (a.val + b.val)) := by
  unfold cadd
  simp [in_i64 _ h1 h2]

theorem put_ok (c : Bool) (bs : Bytes) (st : St) (h : st.out.length + bs.length ≤ st.cap) :
    put c bs st = .ok {st with out := st.out ++ bs} := by
  unfold put; simp only [h, ↓reduceIte]

theorem rmdynamic_static (s : Spec) (args : List Arg) (hw : s.dynamicWidth = false)
    (hp : s.dynamicPrecision = false) : rmdynamic s args = .ok (s, args) := by
  cases s
  simp_all [rmdynamic, bind, Except.bind, pure, Except.pure]

theorem rep_nat (b : Nat) (W w : Nat) : rep b ((W : Int) - w) = List.replicate (W - w) b := by
  unfold rep; congr 1; omega

/-- `computelen` of a single static conversion without literal text. -/
theorem computelen1 (s : Spec) (a : Arg) (l : I) (hw : s.dynamicWidth = false)
    (hp : s.dynamicPrecision = false) (hl : plengthArg s a = .ok l) :
    computelen ⟨[[], []], [s], 1⟩ [a] = .ok l := by
  have hb := I_bounds l
  have hsum : (([[], []] : List Bytes).map List.length).sum = 0 := rfl
  have hc : cadd (ix ((0 : Nat) : Int)) l = .ok l := by
    rw [cadd_ok _ _ (by rw [ix_natzero]; omega) (by rw [ix_natzero]; omega), ix_natzero, Int.zero_add,
      ix_of_val]
  unfold computelen
  rw [hsum]
  simp only [computelen.go, rmdynamic_static s _ hw hp, hl, hc, bind, Except.bind, pure, Except.pure]

/-- A single static conversion: compute the buffer length, then format into it. -/
theorem run1_eq (s : Spec) (a : Arg) (l : I) (hw : s.dynamicWidth = false)
    (hp : s.dynamicPrecision = false) (hl : plengthArg s a = .ok l) (h0 : 0 ≤ l.val) :
    run1 s a = (do let st ← fmtArg s a ⟨[], l.val.toNat⟩; let st ← put true [] st; pure st.out) := by
  have h0' : ¬ l.val < 0 := by omega
  have hput : put true [] ⟨[], l.val.toNat⟩ = .ok ⟨[], l.val.toNat⟩ := by
    rw [put_ok _ _ _ (by simp)]; rfl
  unfold run1 format
  simp only [computelen1 s a l hw hp hl, List.length_singleton, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, h0', List.headD, List.tail, litBytes, hput, bind, Except.bind, pure, Except.pure,
    formatLoop, rmdynamic_static s _ hw hp]
  cases fmtArg s a ⟨[], l.val.toNat⟩ <;> simp only []
  rename_i st
  cases put true [] st <;> rfl

/-! ## Characters -/

theorem ok_bind {α β : Type} (a : α) (f : α → Result β) : ((Except.ok a : Result α) >>= f) = f a := rfl

theorem rep_len (b : Nat) (n : Int) : (rep b n).length = n.toNat := by simp [rep]

/-- `%Wc`/`%-Wc` pad to `W` textwidth columns. -/
theorem charWidth_proven : CharWidth := by
  intro left W g hW hw hlen
  have hWv : (ix (W : Int)).val = W := ix_val _ (by omega) (by omega)
  have hwv : (ix (g.width : Int)).val = g.width := ix_val _ (by omega) (by omega)
  have hlv : (ix (g.bytes.length : Int)).val = g.bytes.length := ix_val _ (by omega) (by omega)
  have hsub : (ix (g.bytes.length : Int) - ix (g.width : Int)).val = (g.bytes.length : Int) - g.width := by
    rw [sub_val _ _ (by rw [hlv, hwv]; omega) (by rw [hlv, hwv]; omega), hlv, hwv]
  have hmax : (imax (ix (W : Int)) (ix (g.width : Int))).val =
      if (W : Int) < g.width then (g.width : Int) else W := by
    rw [imax_val, hWv, hwv]
  have hl : plengthArg {conv := cc, leftalign := left, width := ix W, precision := ix (-1)} (.chr g) =
      .ok (ix ((if (W : Int) < g.width then (g.width : Int) else W) + ((g.bytes.length : Int) - g.width))) := by
    simp only [plengthArg, isChars, cc, beq_self_eq_true, Bool.true_or, ↓reduceIte, pure_bind]
    rw [cadd_ok _ _ (by rw [hmax, hsub]; split <;> omega) (by rw [hmax, hsub]; split <;> omega), hmax, hsub]
  have hLv : (ix ((if (W : Int) < g.width then (g.width : Int) else W) +
      ((g.bytes.length : Int) - g.width))).val =
      (if (W : Int) < g.width then (g.width : Int) else W) + ((g.bytes.length : Int) - g.width) :=
    ix_val _ (by split <;> omega) (by split <;> omega)
  rw [run1_eq _ _ _ rfl rfl hl (by rw [hLv]; split <;> omega), hLv]
  simp only [fmtArg, isChars, cc, beq_self_eq_true, Bool.true_or, ↓reduceIte, fmtChar, hWv]
  cases left <;> by_cases hgt : (W : Int) > g.width <;>
    simp only [hgt, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, decide_true, decide_false,
      ↓reduceIte, Bool.false_eq_true, pure_bind]
  all_goals
    repeat (first
      | rw [pure_bind]
      | rw [ok_bind]
      | rw [put_ok _ _ _ (by simp only [rep_len, List.length_append, List.length_nil]; split <;> omega)])
  all_goals simp only [rep_nat, List.nil_append, List.append_nil, pure, Except.pure]
  all_goals first | rfl | (rw [Nat.sub_eq_zero_of_le (by omega)]; simp)

theorem ix_neg_one : (ix (-1)).val = -1 := rfl

theorem textwidth_cons (g : Glyph) (gs : List Glyph) : textwidth (g :: gs) = g.width + textwidth gs := by
  simp [textwidth]

/-- With at least `textwidth gs` columns left, the loop writes every character. -/
theorem strLoop_all (gs : List Glyph) : ∀ p : Int, (textwidth gs : Int) ≤ p →
    strLoop p gs = (gs.flatMap Glyph.bytes, p - textwidth gs) := by
  induction gs with
  | nil => intro p _; simp [strLoop, textwidth]
  | cons g gs ih =>
    intro p hp
    rw [textwidth_cons] at hp
    have hnn : ¬ (p - g.width < 0) := by omega
    simp only [strLoop, hnn, ↓reduceIte]
    rw [ih _ (by omega)]
    simp [textwidth_cons]
    omega

theorem ix_val_nat (n : Nat) (h : n < 2 ^ 40) : (ix (n : Int)).val = n := ix_val _ (by omega) (by omega)

/-- `plength` of `%Ws` without precision. -/
theorem stringPlength (left : Bool) (W : Nat) (gs : List Glyph) (hW : W < 2 ^ 40)
    (htw : textwidth gs < 2 ^ 40) (hsz : sizeofGlyphs gs < 2 ^ 40) :
    plengthArg {conv := cs, leftalign := left, width := ix W, precision := ix (-1)} (.str gs) =
      .ok (ix ((if (W : Int) < textwidth gs then (textwidth gs : Int) else W) +
        ((sizeofGlyphs gs : Int) - textwidth gs))) := by
  have hWv := ix_val_nat W hW
  have htv := ix_val_nat _ htw
  have hsv := ix_val_nat _ hsz
  have hsub : (ix (sizeofGlyphs gs : Int) - ix (textwidth gs : Int)).val =
      (sizeofGlyphs gs : Int) - textwidth gs := by
    rw [sub_val _ _ (by rw [hsv, htv]; omega) (by rw [hsv, htv]; omega), hsv, htv]
  have hp : cadd (ix (textwidth gs : Int)) (ix 0) = pure (ix (textwidth gs : Int)) := by
    rw [cadd_ok _ _ (by rw [htv, ix_zero]; omega) (by rw [htv, ix_zero]; omega), htv, ix_zero, Int.add_zero]
    rfl
  have hmax : (imax (ix (W : Int)) (ix (textwidth gs : Int))).val =
      if (W : Int) < textwidth gs then (textwidth gs : Int) else W := by
    rw [imax_val, hWv, htv]
  have hpre : ((ix (-1)).val == -1) = true := rfl
  simp only [plengthArg, isChars, isStrings, cs, cc, cC, cS, Nat.reduceBEq, beq_self_eq_true,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, pure_bind, hpre, hp]
  rw [cadd_ok _ _ (by rw [hmax, hsub]; split <;> omega) (by rw [hmax, hsub]; split <;> omega), hmax, hsub]

/-- `fmt` of `%Ws` without precision into a buffer of exactly `plength` bytes. -/
theorem stringFmt (left : Bool) (W : Nat) (gs : List Glyph) (hW : W < 2 ^ 40) (cap : Nat)
    (hcap1 : sizeofGlyphs gs ≤ cap) (hcap2 : (W : Int) - textwidth gs + sizeofGlyphs gs ≤ cap) :
    (fmtArg {conv := cs, leftalign := left, width := ix W, precision := ix (-1)} (.str gs) ⟨[], cap⟩ >>=
      fun st => put true [] st >>= fun st => pure st.out) =
      .ok (if left then gs.flatMap Glyph.bytes ++ List.replicate (W - textwidth gs) 32
           else List.replicate (W - textwidth gs) 32 ++ gs.flatMap Glyph.bytes) := by
  have hWv := ix_val_nat W hW
  have hflat : (gs.flatMap Glyph.bytes).length = sizeofGlyphs gs := by
    simp [sizeofGlyphs, List.length_flatMap]
  have hloop : strLoop (textwidth gs : Int) gs = (gs.flatMap Glyph.bytes, 0) := by
    rw [strLoop_all gs _ (Int.le_refl _), Int.sub_self]
  have hpre : ((ix (-1)).val == -1) = true := rfl
  simp only [fmtArg, isChars, isStrings, cs, cc, cC, cS, Nat.reduceBEq, beq_self_eq_true,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, fmtString, hWv, hpre, Bool.false_and,
    Int.add_zero]
  cases left <;> by_cases hgt : (W : Int) > textwidth gs <;>
    simp only [hgt, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, decide_true, decide_false,
      ↓reduceIte, Bool.false_eq_true, pure_bind]
  all_goals
    repeat (first
      | rw [pure_bind]
      | rw [ok_bind]
      | rw [put_ok _ _ _ (by simp only [rep_len, List.length_append, List.length_nil, hflat, hloop]; omega)]
      | simp only [hloop])
  all_goals simp only [rep_nat, List.nil_append, List.append_nil, pure, Except.pure]
  all_goals first | rfl | (rw [Nat.sub_eq_zero_of_le (by omega)]; simp)

/-- `%Ws`/`%-Ws` pad the whole string to `W` textwidth columns. -/
theorem stringWidth_proven : StringWidth := by
  intro left W gs hW htw hsz
  have hLv : (ix ((if (W : Int) < textwidth gs then (textwidth gs : Int) else W) +
      ((sizeofGlyphs gs : Int) - textwidth gs))).val =
      (if (W : Int) < textwidth gs then (textwidth gs : Int) else W) + ((sizeofGlyphs gs : Int) - textwidth gs) :=
    ix_val _ (by split <;> omega) (by split <;> omega)
  rw [run1_eq _ _ _ rfl rfl (stringPlength left W gs hW htw hsz) (by rw [hLv]; split <;> omega), hLv]
  exact stringFmt left W gs hW _ (by split <;> omega) (by split <;> omega)

/-! ## Literal text and `%%` -/

theorem escapePercent_append (a b : Bytes) :
    escapePercent (a ++ b) = escapePercent a ++ escapePercent b := by
  induction a with
  | nil => rfl
  | cons c r ih =>
    simp only [List.cons_append, escapePercent]
    split <;> simp [ih]

theorem escapePercent_length (s : Bytes) : (escapePercent s).length ≤ 2 * s.length := by
  induction s with
  | nil => simp [escapePercent]
  | cons c r ih =>
    simp only [escapePercent]
    split <;> simp <;> omega

theorem litBytes_append (e : Bool) (a b : Bytes) :
    litBytes e (a ++ b) =
      ((litBytes e a).1 ++ (litBytes (litBytes e a).2 b).1, (litBytes (litBytes e a).2 b).2) := by
  induction a generalizing e with
  | nil => simp [litBytes]
  | cons c r ih => cases e <;> simp [litBytes, ih]

theorem litBytes_length (e : Bool) (a : Bytes) : (litBytes e a).1.length ≤ a.length := by
  induction a generalizing e with
  | nil => simp [litBytes]
  | cons c r ih =>
    cases e
    · simp only [litBytes, Bool.not_false, ↓reduceIte, List.length_cons]
      have := ih (c == 37); omega
    · simp only [litBytes, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have := ih false; omega

theorem litBytes_escape (s : Bytes) : litBytes false (escapePercent s) = (s, false) := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    by_cases h : c = 37
    · subst h; simp [escapePercent, litBytes, ih]
    · have hc : (c == 37) = false := by simp [h]
      simp [escapePercent, hc, litBytes, ih]

theorem scanLoop_cons (acc : Bytes) (b c : Nat) (r : Bytes) (h : c ≠ 37) :
    scanLoop acc b (c :: r) = scanLoop (acc ++ [c]) c r := by
  cases r <;> simp [scanLoop, h]

theorem getLastD_cons' (a d : Nat) (l : List Nat) : (a :: l).getLastD d = l.getLastD a := by
  cases l <;> rfl

theorem getLastD_concat' (l : List Nat) (a d : Nat) : (l ++ [a]).getLastD d = a := by
  simp [List.getLastD_eq_getLast?]

theorem scanLoop_escape (s : Bytes) : ∀ (acc : Bytes) (b : Nat),
    scanLoop acc b (escapePercent s) = .ok (acc ++ escapePercent s, (escapePercent s).getLastD b, none) := by
  induction s with
  | nil => intro acc b; simp [escapePercent, scanLoop]
  | cons c r ih =>
    intro acc b
    by_cases h : c = 37
    · subst h
      simp only [escapePercent, beq_self_eq_true, ↓reduceIte]
      rw [scanLoop, ih, getLastD_cons', getLastD_cons']
      simp
    · have hc : (c == 37) = false := by simp [h]
      simp only [escapePercent, hc, Bool.false_eq_true, ↓reduceIte]
      rw [scanLoop_cons _ _ _ _ h, ih, getLastD_cons']
      simp

theorem range_escape (s : Bytes) :
    (litBytes false (range (escapePercent s) ((escapePercent s).getLastD 0))).1 = s := by
  rcases List.eq_nil_or_concat s with h | ⟨s, c, h⟩
  · subst h; rfl
  · subst h
    rw [List.concat_eq_append, escapePercent_append]
    by_cases h : c = 37
    · subst h
      have he : escapePercent [37] = [37] ++ [37] := rfl
      rw [he, ← List.append_assoc, getLastD_concat']
      simp only [range, beq_self_eq_true, ↓reduceIte, List.dropLast_concat]
      rw [litBytes_append, litBytes_escape]
      rfl
    · have hc : (c == 37) = false := by simp [h]
      have he : escapePercent [c] = [c] := by simp [escapePercent, hc]
      rw [he, getLastD_concat']
      simp only [range, hc, Bool.false_eq_true, ↓reduceIte]
      rw [litBytes_append, litBytes_escape]
      simp [litBytes, hc]

/-- C99 p8 `%`: text without conversions prints with each `%%` as `%`. -/
theorem literalPercent_proven : LiteralPercent := by
  intro s hs
  have hesc := escapePercent_length s
  let lit := range (escapePercent s) ((escapePercent s).getLastD 0)
  have hlit : lit.length ≤ (escapePercent s).length := by
    simp only [lit, range]; split <;> simp
  have hval : (ix (lit.length : Int)).val = lit.length := ix_val _ (by omega) (by omega)
  have hout := range_escape s
  have hlen := litBytes_length false lit
  have hparse : parseBytes (escapePercent s) = .ok ⟨[lit], [], 0⟩ := by
    simp only [parseBytes, scanLoop_escape s [] 0, List.nil_append]
    rfl
  rw [hparse, ok_bind]
  simp only [format, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, computelen,
    computelen.go, List.map, List.sum_cons, List.sum_nil, Nat.add_zero, pure_bind, ok_bind, hval,
    List.headD, formatLoop]
  have hnn : ¬ ((lit.length : Int) < 0) := by omega
  simp only [hnn, ↓reduceIte]
  rcases hlb : litBytes false lit with ⟨o, e⟩
  rw [hlb] at hout hlen
  simp only at hout hlen
  rw [put_ok _ _ _ (by simp; omega)]
  subst hout
  rfl

/-! ## Docstring examples -/

/-- The `@printf` and `@sprintf` docstring examples, evaluated on the model. -/
theorem docstringExamples_proven : DocstringExamples := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end JuliaLean.Printf
