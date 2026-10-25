import JuliaLean.ShellCmd.Props

set_option linter.unusedSimpArgs false

namespace JuliaLean.ShellCmd
namespace ProofShow

@[simp] private theorem tick_escape : S "\\`" = [A '\\', A '`'] := by decide
@[simp] private theorem bs_tick : A '\\' ≠ A '`' := by decide
@[simp] private theorem tick_bs : A '`' ≠ A '\\' := by decide
@[simp] private theorem dq_tick : A '"' ≠ A '`' := by decide
@[simp] private theorem dollar_tick : A '$' ≠ A '`' := by decide
@[simp] private theorem space_tick : A ' ' ≠ A '`' := by decide
@[simp] private theorem dq_bs : A '"' ≠ A '\\' := by decide
@[simp] private theorem dollar_bs : A '$' ≠ A '\\' := by decide
@[simp] private theorem valid_dq : Strings.isvalidChar (A '"') = true := by decide
@[simp] private theorem valid_dollar : Strings.isvalidChar (A '$') = true := by decide
@[simp] private theorem tick_bs_bool : (A '`' == A '\\') = false := by decide
@[simp] private theorem dq_bs_bool : (A '"' == A '\\') = false := by decide
@[simp] private theorem dollar_bs_bool : (A '$' == A '\\') = false := by decide

private def Plain (s : JS) : Prop :=
  ∀ c ∈ s, Strings.isvalidChar c = true ∧ c ≠ A '\r' ∧ c ≠ A '\\'

private inductive Safe : JS → Prop where
  | nil : Safe []
  | char {c : JC} {s : JS} : Strings.isvalidChar c = true → c ≠ A '\r' →
      c ≠ A '\\' → Safe s → Safe (c :: s)
  | escape {c : JC} {s : JS} : (c = A '"' ∨ c = A '$') → Safe s →
      Safe (A '\\' :: c :: s)

private theorem safe_append {s t : JS} (hs : Safe s) (ht : Safe t) : Safe (s ++ t) := by
  induction hs with
  | nil => exact ht
  | char hv hr hb _ ih => exact .char hv hr hb ih
  | escape hc _ ih => exact .escape hc ih

private theorem safe_plain {s : JS} (h : Plain s) : Safe s := by
  induction s with
  | nil => exact .nil
  | cons c cs ih =>
    have hc := h c (by simp)
    exact .char hc.1 hc.2.1 hc.2.2 (ih (fun d hd => h d (by simp [hd])))

private theorem safe_double {s : JS} (h : Plain s) :
    Safe (s.flatMap (fun c =>
      if c == A '"' || c == A '$' || c == A '\\' then [A '\\', c] else [c])) := by
  induction s with
  | nil => exact .nil
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    by_cases hq : c = A '"'
    · subst c
      simpa using Safe.escape (Or.inl rfl) ht
    · by_cases hd : c = A '$'
      · subst c
        simpa using Safe.escape (Or.inr rfl) ht
      · simpa [hq, hd, hc.2.2] using Safe.char hc.1 hc.2.1 hc.2.2 ht

private theorem safe_print {s special : JS} (h : Plain s) : Safe (printShellWord s special) := by
  dsimp only [printShellWord]
  split
  · exact .char (by decide) (by decide) (by decide)
      (.char (by decide) (by decide) (by decide) .nil)
  · split
    · exact safe_plain h
    · split
      · exact .char (by decide) (by decide) (by decide)
          (safe_append (safe_plain h) (.char (by decide) (by decide) (by decide) .nil))
      · exact .char (by decide) (by decide) (by decide)
          (safe_append (safe_double h) (.char (by decide) (by decide) (by decide) .nil))

private theorem safe_join {ss : List JS} (h : ∀ s ∈ ss, Safe s) : Safe (joinSp ss) := by
  cases ss with
  | nil => exact .nil
  | cons s ss =>
    apply safe_append (h s (by simp))
    have ht : Safe (ss.flatMap (fun a => A ' ' :: a)) := by
      induction ss with
      | nil => exact .nil
      | cons t ts ih =>
        exact safe_append (.char (by decide) (by decide) (by decide) (h t (by simp)))
          (ih (fun a ha => h a (by
            rcases List.mem_cons.mp ha with ha | ha
            · exact List.mem_cons.mpr (Or.inl ha)
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr ha))))))
    exact ht

private theorem replace_length (u : JS) : u.length ≤ (replaceC u (A '`') (S "\\`")).length := by
  induction u with
  | nil => simp [replaceC]
  | cons c cs ih =>
    by_cases hc : c = A '`'
    · simp [replaceC, hc] at *
      omega
    · simp [replaceC, hc] at *
      omega

private theorem lex_safe {u : JS} (h : Safe u) (n : Nat) (acc : JS)
    (hn : u.length < n) :
    lexCmd n (replaceC u (A '`') (S "\\`") ++ [A '`']) acc = some (acc ++ u, []) := by
  induction h generalizing n acc with
  | nil =>
    cases n with
    | zero => simp at hn
    | succ n => simp [replaceC, lexCmd]
  | @char c cs hv hr hb hs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : cs.length < n := by simpa using hn
      by_cases hc : c = A '`'
      · subst c
        simpa [replaceC, lexCmd, List.takeWhile, List.drop, List.append_assoc] using
          ih n (acc ++ [A '`']) hn'
      · simpa [replaceC, hc, hb, hr, hv, lexCmd, List.append_assoc] using
          ih n (acc ++ [c]) hn'
  | @escape c cs hc hs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : cs.length < n := by simp at hn; omega
      rcases hc with hc | hc
      · subst c
        simpa [replaceC, lexCmd, List.takeWhile, List.drop, List.append_assoc] using
          ih n (acc ++ [A '\\', A '"']) hn'
      · subst c
        simpa [replaceC, lexCmd, List.takeWhile, List.drop, List.append_assoc] using
          ih n (acc ++ [A '\\', A '$']) hn'

private theorem replace_join (ss : List JS) :
    joinSp (ss.map (fun s => replaceC s (A '`') (S "\\`"))) =
      replaceC (joinSp ss) (A '`') (S "\\`") := by
  cases ss with
  | nil => rfl
  | cons s ss =>
    simp only [List.map_cons, joinSp, replaceC, List.flatMap_append]
    congr 1
    induction ss with
    | nil => rfl
    | cons t ts ih =>
      simp [List.flatMap_cons]
      simpa only [tick_escape, beq_iff_eq] using ih

private theorem cstr_ok {s : JS} (h : A '\x00' ∉ s) : cstr s = .ok s := by
  simp [cstr, h]

private theorem map_cstr {ss : List JS} (h : ∀ s ∈ ss, A '\x00' ∉ s) :
    ss.mapM cstr = .ok ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.mapM_cons, cstr_ok (h s (by simp)),
      ih (fun t ht => h t (by simp [ht])), bind, pure, Except.bind, Except.pure]

private theorem iter_ok {ss : List JS} (h : ∀ s ∈ ss, A '\x00' ∉ s) :
    argGen1 (.iter (ss.map .val)) = .ok ss := by
  change (ss.map Elem.val).mapM (fun e => do let s ← interp1 e; cstr s) = .ok ss
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih (fun t ht => h t (by simp [ht]))]
    simp only [interp1, bind, pure, Except.bind, Except.pure, cstr_ok (h s (by simp))]

end ProofShow

open ProofShow in
 theorem showLexesPlain_proven : ShowLexesPlain := by
  intro exec h
  have hs : Safe (showBody exec) := by
    apply safe_join
    intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
    exact safe_print (h w hw)
  have hr : joinSp (exec.map showWord) = replaceC (showBody exec) (A '`') (S "\\`") := by
    change joinSp (exec.map (fun w => replaceC (showWordRaw w) (A '`') (S "\\`"))) = _
    simpa only [List.map_map, Function.comp_def, showBody] using replace_join (exec.map showWordRaw)
  simp only [showExec, lexCmdLiteral, BEq.rfl, ite_true]
  rw [hr]
  apply lex_safe hs
  have hl := replace_length (showBody exec)
  have ha : (replaceC (showBody exec) (A '`') (S "\\`") ++ [A '`']).length =
      (replaceC (showBody exec) (A '`') (S "\\`")).length + 1 := List.length_append
  change (showBody exec).length < (replaceC (showBody exec) (A '`') (S "\\`") ++ [A '`']).length + 1
  rw [ha]
  omega

open ProofShow in
 theorem interpSplice_proven : InterpSplice := by
  intro pre post sep xs ys h
  have hp : A '\x00' ∉ pre := h pre (by simp)
  have hq : A '\x00' ∉ post := h post (by simp)
  have hs : A '\x00' ∉ sep := h sep (by simp)
  have hx : ∀ s ∈ xs, A '\x00' ∉ s := fun s ht => h s (by simp [ht])
  have hy : ∀ s ∈ ys, A '\x00' ∉ s := fun s ht => h s (by simp [ht])
  have hxpost : ∀ s ∈ xs.map (fun x => x ++ post), A '\x00' ∉ s := by
    intro s ht
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp ht
    simp [hx x hm, hq]
  have hprexpost : ∀ s ∈ (xs.map (fun x => pre ++ x ++ post)), A '\x00' ∉ s := by
    intro s ht
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp ht
    simp [hp, hx x hm, hq]
  have hsepy : ∀ s ∈ ys.map (fun y => sep ++ y), A '\x00' ∉ s := by
    intro s ht
    obtain ⟨y, hm, rfl⟩ := List.mem_map.mp ht
    simp [hs, hy y hm]
  have hprod : ∀ s ∈ xs.flatMap (fun x => ys.map (fun y => x ++ sep ++ y)), A '\x00' ∉ s := by
    intro s ht
    obtain ⟨x, hm, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨y, hn, rfl⟩ := List.mem_map.mp ht
    simp [hx x hm, hs, hy y hn]
  constructor
  · exact iter_ok hx
  constructor
  · simp only [argGen]
    rw [iter_ok hx]
    simp only [argGen1, cstr_ok hp, cstr_ok hq, bind, pure, Except.bind, Except.pure,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
    change (do
      let tail ← (xs.flatMap (fun x => [x ++ post])).mapM cstr
      (tail.map (fun t => pre ++ t)).mapM cstr) = _
    have hflat : ∀ zs : List JS, zs.flatMap (fun x => [x ++ post]) = zs.map (fun x => x ++ post) := by
      intro zs
      induction zs with
      | nil => rfl
      | cons x zs ih => simp [ih]
    rw [hflat xs, map_cstr hxpost]
    change ((xs.map (fun x => x ++ post)).map (fun t => pre ++ t)).mapM cstr = _
    simpa only [List.map_map, Function.comp_def, List.append_assoc] using map_cstr hprexpost
  · simp only [argGen]
    rw [iter_ok hx, iter_ok hy]
    simp only [argGen1, cstr_ok hs, bind, pure, Except.bind, Except.pure,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
    change (do
      let tail ← (ys.map (fun y => sep ++ y)).mapM cstr
      (xs.flatMap (fun x => tail.map (fun t => x ++ t))).mapM cstr) = _
    rw [map_cstr hsepy]
    change (xs.flatMap (fun x => (ys.map (fun y => sep ++ y)).map (fun t => x ++ t))).mapM cstr = _
    simpa only [List.map_map, Function.comp_def, List.append_assoc] using map_cstr hprod

end JuliaLean.ShellCmd
