import JuliaLean.ShellCmd.Props

namespace JuliaLean.ShellCmd
namespace SplitProof

private theorem ctzAux_lt (n x : Nat) (hx : 0 < x) (hb : x < 2 ^ n) :
    Strings.ctzAux x n < n := by
  induction n generalizing x with
  | zero => simp at hb; omega
  | succ n ih =>
    simp only [Strings.ctzAux]
    split
    · omega
    · rename_i he
      have hmod : x % 2 = 0 := by omega
      have hpos : 0 < x / 2 := by omega
      have hbound : x / 2 < 2 ^ n := by
        simp only [Nat.pow_succ] at hb
        omega
      have := ih (x / 2) hpos hbound
      omega

private theorem ncuC_pos (c : JC) : 0 < ncuC c := by
  unfold ncuC Strings.ncodeunitsChar Strings.ctz32
  split
  · simp_all
  · rename_i hc
    have hp : 0 < c.toNat := by
      have : c.toNat ≠ 0 := by
        intro h
        apply hc
        exact UInt32.toNat_inj.mp (by simpa using h)
      omega
    have hb : c.toNat < 2 ^ 32 := c.toNat_lt
    have := ctzAux_lt 32 c.toNat hp hb
    omega

@[simp] private theorem ncu_nil : ncu [] = 0 := rfl
@[simp] private theorem ncu_cons (c : JC) (s : JS) :
    ncu (c :: s) = ncuC c + ncu s := by simp [ncu]
@[simp] private theorem ncu_append (s t : JS) : ncu (s ++ t) = ncu s + ncu t := by
  simp [ncu, List.sum_append]

@[simp] private theorem pairs_length (p : Nat) (s : JS) :
    (pairsFrom p s).length = s.length := by
  induction s generalizing p with
  | nil => rfl
  | cons c cs ih => simp [pairsFrom, ih]

@[simp] private theorem pairs_snd (p : Nat) (s : JS) :
    (pairsFrom p s).map Prod.snd = s := by
  induction s generalizing p with
  | nil => rfl
  | cons c cs ih => simp [pairsFrom, ih]

private theorem pairs_append (p : Nat) (s t : JS) :
    pairsFrom p (s ++ t) = pairsFrom p s ++ pairsFrom (p + ncu s) t := by
  induction s generalizing p with
  | nil => simp [pairsFrom]
  | cons c cs ih => simp [pairsFrom, ih, Nat.add_assoc]

private theorem pairs_bounds (p : Nat) (s : JS) (q : Nat × JC)
    (hq : q ∈ pairsFrom p s) : p ≤ q.1 ∧ q.1 < p + ncu s := by
  induction s generalizing p with
  | nil => simp [pairsFrom] at hq
  | cons c cs ih =>
    simp only [pairsFrom, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have := ncuC_pos c
      simp only [ncu_cons]
      omega
    · obtain ⟨hl, hu⟩ := ih (p + ncuC c) hq
      simp only [ncu_cons]
      omega

private theorem getLast_some (q : Nat × JC) (qs : List (Nat × JC)) :
    ∃ r, (q :: qs).getLast? = some r := by
  induction qs generalizing q with
  | nil => exact ⟨q, rfl⟩
  | cons r rs ih => exact ih r

private theorem fold_last (qs : List (Nat × JC)) (z : Int) :
    qs.foldl (fun _ q => (q.1 : Int)) z =
      ((qs.getLast?).map (fun q => (q.1 : Int))).getD z := by
  induction qs generalizing z with
  | nil => rfl
  | cons q qs ih =>
    cases qs with
    | nil => rfl
    | cons r rs =>
      obtain ⟨last, hl⟩ := getLast_some r rs
      simpa [hl] using ih (q.1 : Int)

private theorem prevind_cut (pre post : JS) :
    prevind (pre ++ post) (1 + ncu pre) = lastindex pre := by
  unfold prevind lastindex
  rw [pairs_append]
  simp only [List.filter_append]
  have hpre : (pairsFrom 1 pre).filter (fun q => decide ((q.1 : Int) < (1 + ncu pre : Nat))) =
      pairsFrom 1 pre := by
    apply List.filter_eq_self.mpr
    intro q hq
    have := (pairs_bounds 1 pre q hq).2
    simp only [decide_eq_true_eq]
    exact_mod_cast this
  have hpost : (pairsFrom (1 + ncu pre) post).filter
      (fun q => decide ((q.1 : Int) < (1 + ncu pre : Nat))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have := (pairs_bounds (1 + ncu pre) post q hq).1
    simp only [Bool.not_eq_true, decide_eq_false_iff_not, Int.not_lt]
    exact_mod_cast this
  simp only [Int.natCast_add, Int.natCast_one] at hpre hpost
  rw [hpre, hpost, List.append_nil]
  exact fold_last _ _

private theorem lastindex_append_char (pre : JS) (c : JC) :
    lastindex (pre ++ [c]) = (1 + ncu pre : Nat) := by
  simp [lastindex, pairs_append, pairsFrom]

private theorem lastindex_lt_end (s : JS) : lastindex s < (1 + ncu s : Nat) := by
  cases h : (pairsFrom 1 s).getLast? with
  | none => simp [lastindex, h]; omega
  | some q =>
    have hm : q ∈ pairsFrom 1 s := List.mem_of_getLast? h
    have := (pairs_bounds 1 s q hm).2
    simp only [lastindex, h, Option.map_some, Option.getD_some]
    exact_mod_cast this

private theorem slice_cut (pre mid post : JS) :
    slice (pre ++ mid ++ post) (1 + ncu pre)
      (prevind (pre ++ mid ++ post) (1 + ncu (pre ++ mid))) = .ok mid := by
  rw [prevind_cut]
  cases hm : mid.reverse with
  | nil =>
    have hm' : mid = [] := List.reverse_eq_nil_iff.mp hm
    subst mid
    simp only [List.append_nil]
    unfold slice
    have := lastindex_lt_end pre
    rw [ite_eq_left (by omega)]
  | cons c rev =>
    have hm' : mid = rev.reverse ++ [c] := by
      have := congrArg List.reverse hm
      simpa using this
    subst mid
    have hkidx : lastindex (pre ++ (rev.reverse ++ [c])) = (1 + ncu (pre ++ rev.reverse) : Nat) := by
      rw [← List.append_assoc, lastindex_append_char]
    rw [hkidx]
    let k := 1 + ncu (pre ++ rev.reverse)
    change slice (pre ++ (rev.reverse ++ [c]) ++ post) (1 + (ncu pre : Int)) (k : Int) = .ok (rev.reverse ++ [c])
    have hlo : (1 : Int) ≤ 1 + (ncu pre : Int) := by omega
    have hki : 1 + (ncu pre : Int) ≤ (k : Int) := by simp [k]; omega
    have hkb : (k : Int) ≤ (ncu (pre ++ (rev.reverse ++ [c]) ++ post) : Nat) := by
      have := ncuC_pos c
      simp [k]
      omega
    have hi : isStart (pre ++ (rev.reverse ++ [c]) ++ post) (1 + ncu pre) = true := by
      unfold isStart
      apply List.any_eq_true.mpr
      cases hr : rev.reverse with
      | nil =>
        refine ⟨(1 + ncu pre, c), ?_, by simp⟩
        simp [pairs_append, pairsFrom]
      | cons d ds =>
        refine ⟨(1 + ncu pre, d), ?_, by simp⟩
        simp [pairs_append, pairsFrom]
    have hk : isStart (pre ++ (rev.reverse ++ [c]) ++ post) k = true := by
      unfold isStart
      apply List.any_eq_true.mpr
      refine ⟨(k, c), ?_, by simp⟩
      simp [k, pairs_append, pairsFrom, Nat.add_assoc]
    unfold slice
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [hi, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [pairs_append, pairs_append]
    simp only [List.filter_append, List.map_append]
    have hp : (pairsFrom 1 pre).filter
        (fun q => decide (1 + (ncu pre : Int) ≤ (q.1 : Int) ∧ (q.1 : Int) ≤ (k : Int))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      have := (pairs_bounds 1 pre q hq).2
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    have ht : (pairsFrom (1 + ncu (pre ++ (rev.reverse ++ [c]))) post).filter
        (fun q => decide (1 + (ncu pre : Int) ≤ (q.1 : Int) ∧ (q.1 : Int) ≤ (k : Int))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      have := (pairs_bounds (1 + ncu (pre ++ (rev.reverse ++ [c]))) post q hq).1
      have := ncuC_pos c
      dsimp [k] at *
      simp only [ncu_append, ncu_cons, ncu_nil, Nat.add_zero] at *
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    have hm : (pairsFrom (1 + ncu pre) (rev.reverse ++ [c])).filter
        (fun q => decide (1 + (ncu pre : Int) ≤ (q.1 : Int) ∧ (q.1 : Int) ≤ (k : Int))) =
          pairsFrom (1 + ncu pre) (rev.reverse ++ [c]) := by
      apply List.filter_eq_self.mpr
      intro q hq
      have hl := (pairs_bounds (1 + ncu pre) (rev.reverse ++ [c]) q hq).1
      have hu : q.1 ≤ k := by
        rw [pairs_append] at hq
        simp only [List.mem_append, pairsFrom, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl
        · have := (pairs_bounds (1 + ncu pre) rev.reverse q hq).2
          dsimp [k]
          simp only [ncu_append]
          omega
        · simp [k, Nat.add_assoc]
      simp only [decide_eq_true_eq]
      constructor <;> exact_mod_cast ‹_›
    rw [hp, hm, ht]
    simp

private def finishWords (args : List JS) (cur : JS) (whs : Bool) : List JS :=
  if !cur.isEmpty || whs then args ++ [cur] else args

private def isEscaped (c : JC) : Bool :=
  c == A '"' || c == A '$' || c == A '\\'

private def doubleText (w : JS) : JS :=
  w.flatMap (fun c => if isEscaped c then [A '\\', c] else [c])

private inductive Steps : JS → Bool → Bool → List JS → JS → Bool → List JS → Prop
  | done : Steps [] false false args cur whs (finishWords args cur whs)
  | literal
      (hw : (!sq && !dq && isspace c) = false)
      (hs : (!dq && (c == A '\'')) = false)
      (hd : (!sq && (c == A '"')) = false)
      (hb : (!sq && (c == A '\\')) = false)
      (next : Steps cs sq dq args (cur ++ [c]) whs out) :
      Steps (c :: cs) sq dq args cur whs out
  | single (next : Steps cs (!sq) false args cur true out) :
      Steps (A '\'' :: cs) sq false args cur whs out
  | double (next : Steps cs false (!dq) args cur true out) :
      Steps (A '"' :: cs) false dq args cur whs out
  | escape (hn : c ≠ A '\n') (hr : c ≠ A '\r')
      (hp : dq = false ∨ isEscaped c = true)
      (next : Steps cs false dq args (cur ++ [c]) true out) :
      Steps (A '\\' :: c :: cs) false dq args cur whs out
  | space (hw : isspace c = true) (hd : isspace d = false)
      (next : Steps (d :: ds) false false (finishWords args cur whs) [] false out) :
      Steps (c :: d :: ds) false false args cur whs out

private theorem scan_single (w : JS) (hw : ∀ c ∈ w, c ≠ A '\'')
    (rest cur : JS) (args : List JS) (whs : Bool) (out : List JS)
    (next : Steps rest true false args (cur ++ w) whs out) :
    Steps (w ++ rest) true false args cur whs out := by
  induction w generalizing cur with
  | nil => simpa using next
  | cons c cs ih =>
    apply Steps.literal (by simp) (by simpa using hw c (by simp)) (by simp) (by simp)
    apply ih (by intro d hd; exact hw d (by simp [hd])) (cur ++ [c])
    simpa [List.append_assoc] using next

private theorem scan_plain (w special : JS) (hw : w.any (wordSpecial special) = false)
    (rest cur : JS) (args : List JS) (whs : Bool) (out : List JS)
    (next : Steps rest false false args (cur ++ w) whs out) :
    Steps (w ++ rest) false false args cur whs out := by
  induction w generalizing cur with
  | nil => simpa using next
  | cons c cs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hw
    have hc := hw.1
    simp only [wordSpecial, Bool.or_eq_false_iff] at hc
    apply Steps.literal (by simpa using hc.1.1.1.1.1)
      (by simpa using hc.1.1.1.2) (by simpa using hc.1.1.2)
      (by simpa using hc.1.1.1.1.2)
    apply ih hw.2 (cur ++ [c])
    simpa [List.append_assoc] using next

private theorem scan_double (w : JS) (rest cur : JS) (args : List JS)
    (out : List JS)
    (next : Steps rest false true args (cur ++ w) true out) :
    Steps (doubleText w ++ rest) false true args cur true out := by
  induction w generalizing cur with
  | nil => simpa [doubleText] using next
  | cons c cs ih =>
    by_cases hp : isEscaped c = true
    · have hn : c ≠ A '\n' := by intro h; subst c; exact (by decide : isEscaped (A '\n') ≠ true) hp
      have hr : c ≠ A '\r' := by intro h; subst c; exact (by decide : isEscaped (A '\r') ≠ true) hp
      simp only [doubleText, List.flatMap_cons, hp, ↓reduceIte, List.cons_append,
        List.nil_append]
      apply Steps.escape hn hr (Or.inr hp)
      apply ih (cur ++ [c])
      simpa [List.append_assoc] using next
    · have hp' : isEscaped c = false := Bool.eq_false_iff.mpr hp
      have hc : (c == A '"') = false ∧ (c == A '\\') = false := by
        have h := hp'
        simp only [isEscaped, Bool.or_eq_false_iff] at h
        exact ⟨h.1.1, h.2⟩
      simp only [doubleText, List.flatMap_cons, hp', Bool.false_eq_true,
        ↓reduceIte, List.cons_append, List.nil_append]
      apply Steps.literal (by simp) (by simp) (by simpa using hc.1) (by simpa using hc.2)
      apply ih (cur ++ [c])
      simpa [List.append_assoc] using next

private theorem word_steps (w special : JS) :
    ∃ b : Bool, (w = [] → b = true) ∧
      ∀ (rest : JS) (args out : List JS),
        Steps rest false false args w b out →
        Steps (printShellWord w special ++ rest) false false args [] false out := by
  by_cases he : w = []
  · subst w
    refine ⟨true, by simp, ?_⟩
    intro rest args out next
    simpa [printShellWord, S] using Steps.single (Steps.single next)
  · cases hs : w.any (wordSpecial special) with
    | false =>
      refine ⟨false, by simp [he], ?_⟩
      intro rest args out next
      simpa [printShellWord, he, hs] using scan_plain w special hs rest [] args false out next
    | true =>
      cases hsingle : w.any (fun c => wordSpecial special c && c == A '\'') with
      | false =>
        refine ⟨true, by simp, ?_⟩
        intro rest args out next
        have hn : ∀ c ∈ w, c ≠ A '\'' := by
          intro c hc h
          subst c
          have ht : w.any (fun c => wordSpecial special c && c == A '\'') = true :=
            List.any_eq_true.mpr ⟨A '\'', hc, by simp [wordSpecial]⟩
          rw [hsingle] at ht
          contradiction
        have hclose : Steps (A '\'' :: rest) true false args w true out := Steps.single next
        have hbody := scan_single w hn (A '\'' :: rest) [] args true out (by simpa using hclose)
        simpa [printShellWord, he, hs, hsingle, List.append_assoc] using Steps.single hbody
      | true =>
        refine ⟨true, by simp, ?_⟩
        intro rest args out next
        have hclose : Steps (A '"' :: rest) false true args w true out := Steps.double next
        have hbody := scan_double w (A '"' :: rest) [] args out (by simpa using hclose)
        have hopen : Steps (A '"' :: (doubleText w ++ A '"' :: rest)) false false args [] false out :=
          Steps.double hbody
        simpa [printShellWord, he, hs, hsingle, doubleText, isEscaped, List.append_assoc] using hopen

private theorem word_first (w special : JS) :
    ∃ c cs, printShellWord w special = c :: cs ∧ isspace c = false := by
  unfold printShellWord
  dsimp only
  split
  · exact ⟨A '\'', [A '\''], rfl, by decide⟩
  · rename_i he
    split
    · rename_i hs
      cases w with
      | nil => simp at he
      | cons c cs =>
        refine ⟨c, cs, rfl, ?_⟩
        have hn : wordSpecial special c = false := by
          have hh : (c :: cs).any (wordSpecial special) = false := by simpa using hs
          exact (Bool.or_eq_false_iff.mp hh).1
        simp only [wordSpecial, Bool.or_eq_false_iff] at hn
        exact hn.1.1.1.1.1
    · split
      · exact ⟨A '\'', _, rfl, by decide⟩
      · exact ⟨A '"', _, rfl, by decide⟩

private theorem words_steps (xs : List JS) (special : JS) (args : List JS) :
    Steps (shellEscape xs special) false false args [] false (args ++ xs) := by
  induction xs generalizing args with
  | nil => simpa [shellEscape, joinSp, finishWords] using (Steps.done (args := args) (cur := []) (whs := false))
  | cons w ws ih =>
    obtain ⟨b, hb, hword⟩ := word_steps w special
    cases ws with
    | nil =>
      have hf : finishWords args w b = args ++ [w] := by
        cases w with
        | nil => simp [finishWords, hb rfl]
        | cons c cs => simp [finishWords]
      have h := hword [] args (args ++ [w])
        (by simpa [hf] using (Steps.done (args := args) (cur := w) (whs := b)))
      simpa [shellEscape, joinSp] using h
    | cons v vs =>
      have htail := ih (args ++ [w])
      obtain ⟨c, cs, hc, hn⟩ := word_first v special
      have hstart : shellEscape (v :: vs) special =
          c :: (cs ++ vs.flatMap (fun a => A ' ' :: printShellWord a special)) := by
        simp [shellEscape, joinSp, hc, List.flatMap_map]
      have hf : finishWords args w b = args ++ [w] := by
        cases w with
        | nil => simp [finishWords, hb rfl]
        | cons c cs => simp [finishWords]
      have hspace : Steps (A ' ' :: shellEscape (v :: vs) special) false false args w b
          (args ++ w :: v :: vs) := by
        rw [hstart]
        apply Steps.space (by decide) hn
        simpa [hf, hstart, List.append_assoc] using htail
      have h := hword (A ' ' :: shellEscape (v :: vs) special) args (args ++ w :: v :: vs) hspace
      simpa [shellEscape, joinSp, List.flatMap_map, List.append_assoc] using h

private theorem word_last (w special : JS) :
    ∃ pre c, printShellWord w special = pre ++ [c] ∧ isspace c = false := by
  unfold printShellWord
  dsimp only
  split
  · exact ⟨[A '\''], A '\'', rfl, by decide⟩
  · rename_i he
    split
    · rename_i hs
      cases hr : w.reverse with
      | nil => have : w = [] := List.reverse_eq_nil_iff.mp hr; simp [this] at he
      | cons c cs =>
        have hw : w = cs.reverse ++ [c] := by
          have := congrArg List.reverse hr
          simpa using this
        refine ⟨cs.reverse, c, hw, ?_⟩
        have ha : w.any (wordSpecial special) = false := by simpa using hs
        have hfalse : wordSpecial special c = false := by
          by_cases ht : wordSpecial special c = true
          · have ht' : w.any (wordSpecial special) = true :=
              List.any_eq_true.mpr ⟨c, by simp [hw], ht⟩
            rw [ha] at ht'
            contradiction
          · exact Bool.eq_false_iff.mpr ht
        simp only [wordSpecial, Bool.or_eq_false_iff] at hfalse
        exact hfalse.1.1.1.1.1
    · split
      · exact ⟨A '\'' :: w, A '\'', rfl, by decide⟩
      · exact ⟨A '"' :: doubleText w, A '"', rfl, by decide⟩

private theorem escape_first (w : JS) (ws : List JS) (special : JS) :
    ∃ c cs, shellEscape (w :: ws) special = c :: cs ∧ isspace c = false := by
  obtain ⟨c, cs, hc, hn⟩ := word_first w special
  exact ⟨c, cs ++ (ws.map (printShellWord · special)).flatMap (fun a => A ' ' :: a),
    by simp [shellEscape, joinSp, hc], hn⟩

private theorem escape_last (w : JS) (ws : List JS) (special : JS) :
    ∃ pre c, shellEscape (w :: ws) special = pre ++ [c] ∧ isspace c = false := by
  induction ws generalizing w with
  | nil => simpa [shellEscape, joinSp] using word_last w special
  | cons v vs ih =>
    obtain ⟨pre, c, hc, hn⟩ := ih v
    refine ⟨printShellWord w special ++ A ' ' :: pre, c, ?_, hn⟩
    have ht : shellEscape (w :: v :: vs) special =
        printShellWord w special ++ A ' ' :: shellEscape (v :: vs) special := by
      simp [shellEscape, joinSp]
    rw [ht, hc]
    simp [List.append_assoc]

private theorem escape_lstrip (w : JS) (ws : List JS) (special : JS) :
    (lstripOff (shellEscape (w :: ws) special)).2 = shellEscape (w :: ws) special := by
  obtain ⟨c, cs, hc, hn⟩ := escape_first w ws special
  simp [lstripOff, hc, hn]

private theorem escape_rstrip (w : JS) (ws : List JS) (special : JS) :
    rstripShell (shellEscape (w :: ws) special) = shellEscape (w :: ws) special := by
  obtain ⟨pre, c, hc, hn⟩ := escape_last w ws special
  rw [hc]
  simp only [rstripShell, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  simp only [rstripKeep, show ((none : Option JC) == some (A ' ')) = false from rfl,
    Bool.and_false, hn, Bool.not_false, ↓reduceIte, List.length_reverse]
  simpa using (List.take_length (l := pre ++ [c]))

@[simp] private theorem sh_bind_ok {α β : Type} (x : α) (f : α → SH β) :
    ((.ok x : SH α) >>= f) = f x := rfl

@[simp] private theorem sh_map_ok {α β : Type} (x : α) (f : α → β) :
    f <$> (.ok x : SH α) = (.ok (f x) : SH β) := rfl

private def cursor (s pre tail : JS) : Int :=
  if tail.isEmpty then lastindex s + 1 else (1 + ncu pre : Nat)

@[simp] private theorem cursor_append_cons (s pre mid : JS) (c : JC) (cs : JS) :
    cursor s pre (mid ++ c :: cs) = (1 + ncu pre : Nat) := by
  cases mid <;> simp [cursor]

@[simp] private theorem peek_pairs (s pre tail : JS) :
    peekIdx s (pairsFrom (1 + ncu pre) tail) = cursor s pre tail := by
  cases tail <;> simp [pairsFrom, peekIdx, cursor]

private theorem consume_at (s pre mid : JS) (c : JC) (cs : JS) (arg : List JS)
    (hs : s = pre ++ mid ++ c :: cs) :
    consumeUpto s (pairsFrom (1 + ncu (pre ++ mid ++ [c])) cs) arg
      (cursor s pre (mid ++ c :: cs)) (1 + ncu (pre ++ mid)) =
    .ok (pushNonempty arg mid, cursor s (pre ++ mid ++ [c]) cs) := by
  unfold consumeUpto
  rw [cursor_append_cons]
  have hslice := slice_cut pre mid (c :: cs)
  rw [← hs] at hslice
  simp only [Int.natCast_add, Int.natCast_one]
  rw [hslice]
  simp only [sh_bind_ok, peek_pairs, pure, Except.pure]

private theorem flatten_push (arg : List JS) (mid : JS) :
    (pushNonempty arg mid).flatten = arg.flatten ++ mid := by
  cases mid <;> simp [pushNonempty, List.flatten_append]

private theorem map_appendWord (args : List (List JS)) (arg : List JS) :
    (append2to1 args arg).map List.flatten = args.map List.flatten ++ [arg.flatten] := by
  cases arg <;> simp [append2to1]

private def finish (s : JS) (σ : PState) : SH (List JS) := do
  if σ.inSQ then .error (.error "unterminated single quote")
  else if σ.inDQ then .error (.error "unterminated double quote")
  else do
    let x ← slice s σ.i (lastindex s)
    let arg := pushNonempty σ.arg x
    pure ((if !arg.isEmpty || σ.whs then append2to1 σ.args arg else σ.args).map List.flatten)

private theorem slice_final (s pre mid : JS) (hs : s = pre ++ mid) :
    slice s (cursor s pre mid) (lastindex s) = .ok mid := by
  cases mid with
  | nil => simp only [cursor, List.isEmpty_nil, ↓reduceIte, slice]; rw [ite_eq_left (by omega)]
  | cons c cs =>
    have h := slice_cut pre (c :: cs) []
    rw [prevind_cut] at h
    simp only [List.append_nil] at h
    rw [← hs] at h
    simpa [cursor] using h

private theorem finish_ok (s pre mid : JS) (args : List (List JS)) (arg : List JS)
    (whs : Bool) (hs : s = pre ++ mid) (ha : whs = false → arg = []) :
    finish s { inSQ := false, inDQ := false, args := args, arg := arg,
               i := cursor s pre mid, whs := whs } =
      .ok (finishWords (args.map List.flatten) (arg.flatten ++ mid) whs) := by
  simp only [finish, Bool.false_eq_true, ↓reduceIte]
  rw [slice_final s pre mid hs]
  cases whs with
  | false =>
    have he := ha rfl
    subst arg
    cases mid <;> simp [pushNonempty, finishWords, map_appendWord]
  | true => simp [finishWords, map_appendWord, flatten_push]

@[simp] private theorem sq_space : isspace (A '\'') = false := by decide
@[simp] private theorem dq_space : isspace (A '"') = false := by decide
@[simp] private theorem bs_space : isspace (A '\\') = false := by decide
@[simp] private theorem dq_sq : (A '"' == A '\'') = false := by decide
@[simp] private theorem bs_sq : (A '\\' == A '\'') = false := by decide
@[simp] private theorem bs_dq : (A '\\' == A '"') = false := by decide

private theorem close_parts (args : List (List JS)) (arg : List JS) (mid : JS)
    (whs : Bool) (ha : whs = false → arg = []) :
    ∃ args', (if !(pushNonempty arg mid).isEmpty || whs
        then (append2to1 args (pushNonempty arg mid), [])
        else (args, pushNonempty arg mid)) = (args', []) ∧
      args'.map List.flatten = finishWords (args.map List.flatten) (arg.flatten ++ mid) whs := by
  cases whs with
  | false =>
    have he := ha rfl
    subst arg
    cases mid with
    | nil => exact ⟨args, by simp [pushNonempty], by simp [finishWords]⟩
    | cons c cs =>
      refine ⟨append2to1 args [c :: cs], by simp [pushNonempty], ?_⟩
      simp [map_appendWord, finishWords]
  | true =>
    refine ⟨append2to1 args (pushNonempty arg mid), by simp, ?_⟩
    simp [map_appendWord, flatten_push, finishWords]

private theorem steps_sound (str s : JS) {rest : JS} {sq dq : Bool}
    {rargs : List JS} {cur : JS} {whs : Bool} {out : List JS}
    (cert : Steps rest sq dq rargs cur whs out)
    (pre mid : JS) (args : List (List JS)) (arg : List JS)
    (heq : s = pre ++ mid ++ rest) (hargs : args.map List.flatten = rargs)
    (hcur : arg.flatten ++ mid = cur) (harg : whs = false → arg = [])
    (n : Nat) (hn : rest.length ≤ n) :
    (do
      let σ ← parseLoop str s [] n (pairsFrom (1 + ncu (pre ++ mid)) rest)
        { inSQ := sq, inDQ := dq, args := args, arg := arg,
          i := cursor s pre (mid ++ rest), whs := whs }
      finish s σ) = .ok out := by
  induction cert generalizing pre mid args arg n with
  | done =>
    simp only [pairsFrom, parseLoop, List.append_nil, bind, Except.bind]
    rw [finish_ok s pre mid args arg _ (by simpa using heq) harg, hargs, hcur]
  | @literal sq dq c cs rargs cur whs out hw hsq hd hb next ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have run := ih pre (mid ++ [c]) args arg
        (by simpa [List.append_assoc] using heq) hargs
        (by simpa [List.append_assoc] using congrArg (· ++ [c]) hcur)
        harg n (by simpa using hn)
      simp only [pairsFrom, parseLoop, hw, hsq, hd, hb, Bool.false_eq_true,
        ↓reduceIte, cin, List.contains_nil, Bool.and_false]
      simpa [List.append_assoc, Nat.add_assoc] using run
  | @single cs sq rargs cur out whs next ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc := consume_at s pre mid (A '\'') cs arg heq
      have run := ih (pre ++ mid ++ [A '\'']) [] args (pushNonempty arg mid)
        (by simpa [List.append_assoc] using heq) hargs
        (by simpa [flatten_push] using hcur) (by simp) n (by simpa using hn)
      simp only [pairsFrom, parseLoop, sq_space, Bool.and_false, Bool.not_false,
        Bool.true_and, beq_self_eq_true, ↓reduceIte]
      have hc' : consumeUpto s (pairsFrom (1 + ncu (pre ++ mid) + ncuC (A '\'')) cs) arg
          (cursor s pre (mid ++ A '\'' :: cs)) (1 + ncu (pre ++ mid)) =
          .ok (pushNonempty arg mid, cursor s (pre ++ mid ++ [A '\'']) cs) := by
        simpa [Nat.add_assoc] using hc
      simp only [Int.natCast_add, Int.natCast_one]
      rw [hc']
      simpa [Nat.add_assoc, List.append_assoc, bind, Except.bind] using run
  | @double cs dq rargs cur out whs next ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc := consume_at s pre mid (A '"') cs arg heq
      have run := ih (pre ++ mid ++ [A '"']) [] args (pushNonempty arg mid)
        (by simpa [List.append_assoc] using heq) hargs
        (by simpa [flatten_push] using hcur) (by simp) n (by simpa using hn)
      simp only [pairsFrom, parseLoop, dq_space, dq_sq, Bool.and_false, Bool.not_false,
        Bool.true_and, beq_self_eq_true, ↓reduceIte]
      have hc' : consumeUpto s (pairsFrom (1 + ncu (pre ++ mid) + ncuC (A '"')) cs) arg
          (cursor s pre (mid ++ A '"' :: cs)) (1 + ncu (pre ++ mid)) =
          .ok (pushNonempty arg mid, cursor s (pre ++ mid ++ [A '"']) cs) := by
        simpa [Nat.add_assoc] using hc
      simp only [Int.natCast_add, Int.natCast_one]
      rw [hc']
      simpa [Nat.add_assoc, List.append_assoc, bind, Except.bind] using run
  | @escape c dq cs rargs cur out whs hnl hcr hp next ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc := consume_at s pre mid (A '\\') (c :: cs) arg heq
      have run := ih (pre ++ mid ++ [A '\\']) [c] args (pushNonempty arg mid)
        (by simpa [List.append_assoc] using heq) hargs
        (by simpa [flatten_push, List.append_assoc] using congrArg (· ++ [c]) hcur)
        (by simp) n (by simp at hn ⊢; omega)
      have hc' : consumeUpto s
          (pairsFrom (1 + ncu (pre ++ mid) + ncuC (A '\\')) (c :: cs)) arg
          (cursor s pre (mid ++ A '\\' :: c :: cs)) (1 + ncu (pre ++ mid)) =
          .ok (pushNonempty arg mid, cursor s (pre ++ mid ++ [A '\\']) (c :: cs)) := by
        simpa [Nat.add_assoc] using hc
      have hnl' : (c == A '\n') = false := by simp [hnl]
      have hcr' : (c == A '\r') = false := by simp [hcr]
      simp only [pairsFrom] at hc'
      cases dq with
      | false =>
        simp only [pairsFrom, parseLoop, bs_space, bs_sq, bs_dq, Bool.and_false,
          Bool.not_false, Bool.true_and, beq_self_eq_true, ↓reduceIte]
        simp only [hnl', hcr', Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [Int.natCast_add, Int.natCast_one]
        rw [hc']
        simpa [pairsFrom, List.append_assoc, Nat.add_assoc] using run
      | true =>
        have hp' : isEscaped c = true := hp.resolve_left (by decide)
        simp only [pairsFrom, parseLoop, bs_space, bs_sq, bs_dq, Bool.and_false,
          Bool.not_false, Bool.not_true, Bool.true_and,
          beq_self_eq_true, ↓reduceIte]
        simp only [hnl', hcr', Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        have hp'' : (c == A '"' || c == A '$' || c == A '\\') = true := hp'
        rw [hp'']
        simp only [↓reduceIte]
        simp only [Int.natCast_add, Int.natCast_one]
        rw [hc']
        simpa [pairsFrom, List.append_assoc, Nat.add_assoc] using run
  | @space c d ds rargs cur whs out hw hd next ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc := consume_at s pre mid c (d :: ds) arg heq
      obtain ⟨args', hpair, hmap⟩ := close_parts args arg mid whs harg
      have run := ih (pre ++ mid ++ [c]) [] args' []
        (by simpa [List.append_assoc] using heq)
        (by simpa [hargs, hcur] using hmap) (by simp) (by simp)
        n (by simpa using hn)
      simp only [pairsFrom, parseLoop, Bool.not_false, Bool.true_and, hw, ↓reduceIte]
      have hc' : consumeUpto s (pairsFrom (1 + ncu (pre ++ mid) + ncuC c) (d :: ds)) arg
          (cursor s pre (mid ++ c :: d :: ds)) (1 + ncu (pre ++ mid)) =
          .ok (pushNonempty arg mid, cursor s (pre ++ mid ++ [c]) (d :: ds)) := by
        simpa [Nat.add_assoc] using hc
      simp only [pairsFrom] at hc'
      simp only [Int.natCast_add, Int.natCast_one]
      rw [hc']
      simp only [bind, Except.bind]
      rw [hpair]
      simp only [skipSpaces, hd, Bool.false_eq_true, ↓reduceIte]
      simpa [cursor, pairsFrom, List.append_assoc, Nat.add_assoc, bind, Except.bind] using run

private theorem finish_after (s : JS) (r : SH PState) :
    (do let σ ← r; finish s σ) =
    (do
      let words ← (do
        let σ ← r
        if σ.inSQ then .error (.error "unterminated single quote")
        else if σ.inDQ then .error (.error "unterminated double quote")
        else do
          let x ← slice s σ.i (lastindex s)
          let arg := pushNonempty σ.arg x
          pure (if !arg.isEmpty || σ.whs then append2to1 σ.args arg else σ.args))
      pure (words.map List.flatten)) := by
  cases r with
  | error e => rfl
  | ok σ =>
    cases hsq : σ.inSQ <;> cases hdq : σ.inDQ <;>
      cases hx : slice s σ.i (lastindex s) <;>
      simp [finish, hsq, hdq, hx, bind, pure, Except.bind, Except.pure]

end SplitProof

theorem shellSplitEscape_proven : ShellSplitEscape := by
  intro xs special
  cases xs with
  | nil => rfl
  | cons w ws =>
    have cert := SplitProof.words_steps (w :: ws) special []
    have run := SplitProof.steps_sound (shellEscape (w :: ws) special)
      (shellEscape (w :: ws) special) cert [] [] [] []
      (by simp) rfl (by simp) (by simp)
      ((shellEscape (w :: ws) special).length + 1) (by omega)
    obtain ⟨c, cs, hstart, hn⟩ := SplitProof.escape_first w ws special
    have hne : (shellEscape (w :: ws) special).isEmpty = false := by simp [hstart]
    simp only [List.nil_append, SplitProof.ncu_nil, Nat.add_zero] at run
    have hi : SplitProof.cursor (shellEscape (w :: ws) special) [] (shellEscape (w :: ws) special) = 1 := by
      simp [SplitProof.cursor, hne]
    rw [hi] at run
    rw [SplitProof.finish_after] at run
    simpa only [shellSplit, shellParse, SplitProof.escape_lstrip, SplitProof.escape_rstrip,
      hne, SplitProof.pairs_length, Bool.false_eq_true, ↓reduceIte] using run

end JuliaLean.ShellCmd
