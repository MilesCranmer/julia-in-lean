import JuliaLean.Paths.Props

/-!
# Proofs of the splitting and joining properties of POSIX paths
-/

namespace JuliaLean.Paths.SplitLemmas

open JuliaLean

theorem span_loop {α : Type} (q : α → Bool) : ∀ (l acc : List α),
    List.span.loop q l acc = (acc.reverse ++ l.takeWhile q, l.dropWhile q)
  | [], acc => by simp [List.span.loop]
  | a :: l, acc => by
    cases h : q a
    · simp [List.span.loop, h]
    · simp [List.span.loop, h, span_loop q l (a :: acc)]

theorem span_eq {α : Type} (q : α → Bool) (l : List α) : l.span q = (l.takeWhile q, l.dropWhile q) := by
  unfold List.span
  rw [span_loop]
  simp

theorem dw_all {α : Type} {q : α → Bool} : ∀ {l : List α}, (∀ c ∈ l, q c = true) → l.dropWhile q = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.dropWhile_cons, ite_eq_left (h a (by simp))]
    exact dw_all (fun c hc => h c (by simp [hc]))

theorem nil_or_concat {α : Type} : ∀ l : List α, l = [] ∨ ∃ L b, l = L ++ [b]
  | [] => Or.inl rfl
  | a :: l => by
    rcases nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · exact Or.inr ⟨[], a, rfl⟩
    · exact Or.inr ⟨a :: L, b, rfl⟩

/-- Either no character satisfies `pred`, or `s` splits at the last one that does. -/
theorem decomp (pred : Char → Bool) : ∀ s : Str,
    (∀ c ∈ s, pred c = false) ∨ ∃ b x a, s = b ++ x :: a ∧ pred x = true ∧ ∀ c ∈ a, pred c = false
  | [] => Or.inl (by simp)
  | c :: s => by
    rcases decomp pred s with h | ⟨b, x, a, rfl, hx, ha⟩
    · cases hc : pred c
      · left
        intro d hd
        simp at hd
        rcases hd with rfl | hd
        · exact hc
        · exact h d hd
      · right
        exact ⟨[], c, s, rfl, hc, h⟩
    · right
      exact ⟨c :: b, x, a, rfl, hx, ha⟩

theorem splitLast_some {pred : Char → Bool} {b : Str} {x : Char} {a : Str} (hx : pred x = true)
    (ha : ∀ c ∈ a, pred c = false) : splitLast pred (b ++ x :: a) = some (b, a) := by
  have ha' : ∀ c ∈ a.reverse, (!pred c) = true := by
    intro c hc
    simp [ha c (List.mem_reverse.mp hc)]
  unfold splitLast
  rw [span_eq]
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [List.takeWhile_append_of_pos ha', List.dropWhile_append_of_pos ha']
  simp [hx]

theorem splitLast_none {pred : Char → Bool} {s : Str} (h : ∀ c ∈ s, pred c = false) :
    splitLast pred s = none := by
  have hs : s.reverse.dropWhile (fun c => !pred c) = [] :=
    dw_all (fun c hc => by simp [h c (List.mem_reverse.mp hc)])
  unfold splitLast
  simp only [span_eq, hs]

theorem isSep_slash : isSep '/' = true := by simp [isSep]

theorem ne_slash {y : Char} (hy : isSep y = false) : y ≠ '/' := by
  intro h
  subst h
  simp [isSep] at hy

theorem allSep_iff {l : Str} : l.all (fun c => !isSep c) = true ↔ ∀ c ∈ l, isSep c = false := by
  simp

theorem not_abs {a : Str} (ha : ∀ c ∈ a, isSep c = false) : isabspath a = false := by
  cases a with
  | nil => rfl
  | cons c r => exact ha c (by simp)

theorem isEmpty_false {α : Type} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem noDoubleSep_tail (z : Char) : ∀ l : Str, noDoubleSep (z :: l) = true → noDoubleSep l = true
  | [], _ => rfl
  | c :: r, h => by
    have e : noDoubleSep (z :: c :: r) = (!(isSep z && isSep c) && noDoubleSep (c :: r)) := rfl
    rw [e, Bool.and_eq_true] at h
    exact h.2

theorem noDoubleSep_suffix : ∀ (l r : Str), noDoubleSep (l ++ r) = true → noDoubleSep r = true
  | [], _, h => h
  | z :: l, r, h => noDoubleSep_suffix l r (noDoubleSep_tail z _ h)

theorem noDoubleSep_prefix : ∀ (l r : Str), noDoubleSep (l ++ r) = true → noDoubleSep l = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | z :: w :: t, r, h => by
    have e1 : noDoubleSep (z :: w :: t ++ r) = (!(isSep z && isSep w) && noDoubleSep (w :: t ++ r)) := rfl
    have e2 : noDoubleSep (z :: w :: t) = (!(isSep z && isSep w) && noDoubleSep (w :: t)) := rfl
    rw [e1, Bool.and_eq_true] at h
    rw [e2, Bool.and_eq_true]
    exact ⟨h.1, noDoubleSep_prefix (w :: t) r h.2⟩

theorem lastNotSep {b' : Str} {y x : Char} {a : Str} (h : noDoubleSep (b' ++ [y] ++ x :: a) = true)
    (hx : isSep x = true) : isSep y = false := by
  rw [List.append_assoc] at h
  have h2 := noDoubleSep_suffix b' _ h
  have e : noDoubleSep ([y] ++ x :: a) = (!(isSep y && isSep x) && noDoubleSep (x :: a)) := rfl
  rw [e, Bool.and_eq_true, hx] at h2
  cases hy : isSep y
  · rfl
  · rw [hy] at h2
    exact absurd h2.1 (by decide)

theorem dirPart_last {path b' : Str} {y : Char} (hy : isSep y = false) :
    dirPart path (b' ++ [y]) = b' ++ [y] := by
  simp [dirPart, hy]

theorem sd_some {b : Str} {x : Char} {a : Str} (hx : isSep x = true) (ha : ∀ c ∈ a, isSep c = false) :
    splitdirNoDrive [] (b ++ x :: a) = ([] ++ dirPart (b ++ x :: a) b, a) := by
  simp only [splitdirNoDrive, splitLast_some hx ha]

theorem sd_noSep {p : Str} (h : ∀ c ∈ p, isSep c = false) : splitdirNoDrive [] p = ([], p) := by
  simp only [splitdirNoDrive, splitLast_none h]

theorem sd_root {a : Str} (ha : ∀ c ∈ a, isSep c = false) :
    splitdirNoDrive [] ('/' :: a) = (['/'], a) :=
  sd_some (b := []) isSep_slash ha

theorem sd_mid {b' : Str} {y : Char} {a : Str} (hy : isSep y = false) (ha : ∀ c ∈ a, isSep c = false) :
    splitdirNoDrive [] (b' ++ [y] ++ '/' :: a) = (b' ++ [y], a) := by
  simp only [sd_some isSep_slash ha, dirPart_last hy, List.nil_append]

theorem joinStep_nil {t : Str} : joinStep [] t = t := by
  simp [joinStep]

theorem joinStep_slash {d t : Str} (ht : isabspath t = false) (hl : d.getLast? = some '/') :
    joinStep d t = d ++ t := by
  simp [joinStep, ht, hl]

theorem joinStep_noSlash {d t : Str} (ht : isabspath t = false) (hne : d ≠ [])
    (hl : d.getLast? ≠ some '/') : joinStep d t = d ++ '/' :: t := by
  simp [joinStep, ht, hne, hl]

/-- The separator `joinStep path p` puts between `path` and a relative `p`. -/
def sepIf (x : Str) : Str := if x.isEmpty || x.getLast? == some '/' then [] else ['/']

theorem sepIf_nil : sepIf [] = [] := rfl

theorem joinStep_abs {x y : Str} (h : isabspath y = true) : joinStep x y = y := by
  simp [joinStep, h]

theorem joinStep_rel {x y : Str} (h : isabspath y = false) : joinStep x y = x ++ sepIf x ++ y := by
  by_cases hc : (x.isEmpty || x.getLast? == some '/') = true
  · have e : sepIf x = [] := by unfold sepIf; exact ite_eq_left hc
    rw [e]
    simp only [joinStep, h, Bool.false_eq_true, ite_false, ite_eq_left hc, List.append_nil]
  · have e : sepIf x = ['/'] := by unfold sepIf; exact ite_eq_right hc
    rw [e]
    simp only [joinStep, h, Bool.false_eq_true, ite_false, ite_eq_right hc, List.append_assoc,
      List.singleton_append]

theorem sepIf_idem (x : Str) : sepIf (x ++ sepIf x) = [] := by
  by_cases hc : (x.isEmpty || x.getLast? == some '/') = true
  · have e : sepIf x = [] := by unfold sepIf; exact ite_eq_left hc
    rw [e, List.append_nil]
    exact e
  · have e : sepIf x = ['/'] := by unfold sepIf; exact ite_eq_right hc
    rw [e]
    simp [sepIf]

theorem sepIf_concat (x b' : Str) (y : Char) : sepIf (x ++ (b' ++ [y])) = sepIf (b' ++ [y]) := by
  simp [sepIf]

theorem abs_rel {b c : Str} (hb : isabspath b = false) (hc : isabspath c = false) :
    isabspath (b ++ sepIf b ++ c) = false := by
  cases b with
  | nil => exact hc
  | cons z b => exact hb

theorem joinStep_assoc (a b c : Str) : joinStep (joinStep a b) c = joinStep a (joinStep b c) := by
  cases hc : isabspath c
  · cases hb : isabspath b
    · rw [joinStep_rel hb, joinStep_rel (x := a ++ sepIf a ++ b) hc, joinStep_rel (x := b) hc,
        joinStep_rel (abs_rel hb hc)]
      rcases nil_or_concat b with rfl | ⟨b', y, rfl⟩
      · simp [sepIf_idem, sepIf_nil]
      · rw [sepIf_concat]
        simp
    · have hbc : isabspath (joinStep b c) = true := by
        rw [joinStep_rel hc]
        cases b with
        | nil => exact absurd hb (by decide)
        | cons z b => exact hb
      rw [joinStep_abs hb, joinStep_abs hbc]
  · simp only [joinStep_abs hc]

theorem loop_nil (n : Nat) (out : List Str) : splitpathLoop n [] out = out := by
  cases n <;> simp [splitpathLoop]

theorem loop_stop {m : Nat} {p base : Str} {out : List Str} (hp : p ≠ [])
    (hs : splitdirNoDrive [] p = (p, base)) : splitpathLoop (m + 1) p out = p :: out := by
  simp [splitpathLoop, hs, hp]

theorem loop_go {m : Nat} {p d a : Str} {out : List Str} (hp : p ≠ [])
    (hs : splitdirNoDrive [] p = (d, a)) (hd : d ≠ p) (ha : a ≠ []) :
    splitpathLoop (m + 1) p out = splitpathLoop m d (a :: out) := by
  simp [splitpathLoop, hs, hp, hd, ha]

theorem splitpath_ne {p : Str} (hp : p ≠ []) : splitpath p = splitpathLoop (p.length + 1) p [] := by
  cases p with
  | nil => exact absurd rfl hp
  | cons c r => rfl

/-- The loop of `splitpath` on a canonical nonempty path yields components that
`joinpath` folds back into the path. -/
theorem loop_canonical : ∀ (n : Nat) (p : Str) (out : List Str), p ≠ [] → p.length < n →
    noDoubleSep p = true → (p = ['/'] ∨ p.getLast? ≠ some '/') →
    ∃ h t, splitpathLoop n p out = h :: (t ++ out) ∧ t.foldl joinStep h = p
  | 0, _, _, _, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | m + 1, p, out, hp, hl, hnd, hc => by
    rcases decomp isSep p with hs | ⟨b, x, a, rfl, hx, ha⟩
    · exact ⟨p, [], (loop_go hp (sd_noSep hs) (fun heq => hp heq.symm) hp).trans (loop_nil _ _), rfl⟩
    · have hx' : x = '/' := by simpa [isSep] using hx
      subst hx'
      rcases nil_or_concat b with rfl | ⟨b', y, rfl⟩
      · show ∃ h t, splitpathLoop (m + 1) ('/' :: a) out = h :: (t ++ out) ∧ t.foldl joinStep h = '/' :: a
        by_cases ha0 : a = []
        · subst ha0
          exact ⟨['/'], [], loop_stop (by simp) (sd_root (a := []) (by simp)), rfl⟩
        · have hlen : 0 < a.length := List.length_pos_iff.mpr ha0
          have hl' : ('/' :: a).length < m + 1 := hl
          obtain ⟨h, t, e, f⟩ := loop_canonical m ['/'] (a :: out) (by simp)
            (by simp at hl' ⊢; omega) rfl (Or.inl rfl)
          refine ⟨h, t ++ [a], ?_, ?_⟩
          · rw [loop_go (by simp) (sd_root ha)
              (fun heq => ha0 (by injection heq with _ e2; exact e2.symm)) ha0, e]
            simp
          · rw [List.foldl_append, f]
            show joinStep ['/'] a = '/' :: a
            exact joinStep_slash (not_abs ha) rfl
      · have hy : isSep y = false := lastNotSep hnd hx
        have ha0 : a ≠ [] := by
          rintro rfl
          rcases hc with hc | hc
          · have := congrArg List.length hc
            simp at this <;> omega
          · exact hc List.getLast?_concat
        have hl' : (b' ++ [y]).length < m := by
          simp at hl ⊢
          omega
        have hlast : (b' ++ [y]).getLast? ≠ some '/' := by
          rw [List.getLast?_concat]
          intro h
          exact ne_slash hy (Option.some.inj h)
        have hd : b' ++ [y] ≠ b' ++ [y] ++ '/' :: a := by
          intro heq
          have := congrArg List.length heq
          simp at this <;> omega
        obtain ⟨h, t, e, f⟩ := loop_canonical m (b' ++ [y]) (a :: out) (by simp) hl'
          (noDoubleSep_prefix _ _ hnd) (Or.inr hlast)
        refine ⟨h, t ++ [a], ?_, ?_⟩
        · rw [loop_go (by simp) (sd_mid hy ha) hd ha0, e]
          simp
        · rw [List.foldl_append, f]
          show joinStep (b' ++ [y]) a = b' ++ [y] ++ '/' :: a
          exact joinStep_noSlash (not_abs ha) (by simp) hlast

/-- Joining a component list gives a path whose last character is no separator
(or the root), and the loop of `splitpath` recovers the components from it. -/
theorem comp_loop (h : Str) (hh : h = ['/'] ∨ (h ≠ [] ∧ ∀ c ∈ h, isSep c = false)) :
    ∀ (k : Nat) (t : List Str), t.length = k → (∀ x ∈ t, x ≠ [] ∧ ∀ c ∈ x, isSep c = false) →
    (t.foldl joinStep h = ['/'] ∨ ∃ q y, t.foldl joinStep h = q ++ [y] ∧ isSep y = false) ∧
    ∀ n out, (t.foldl joinStep h).length < n →
      splitpathLoop n (t.foldl joinStep h) out = h :: (t ++ out)
  | 0, [], _, _ => by
    show (h = ['/'] ∨ ∃ q y, h = q ++ [y] ∧ isSep y = false) ∧
      ∀ n out, h.length < n → splitpathLoop n h out = h :: out
    refine ⟨?_, fun n out hn => ?_⟩
    · rcases hh with hh | ⟨hne, hsep⟩
      · exact Or.inl hh
      · rcases nil_or_concat h with h0 | ⟨q, y, rfl⟩
        · exact absurd h0 hne
        · exact Or.inr ⟨q, y, rfl, hsep y (by simp)⟩
    · cases n with
      | zero => exact absurd hn (Nat.not_lt_zero _)
      | succ m =>
        rcases hh with rfl | ⟨hne, hsep⟩
        · exact loop_stop (by simp) (sd_root (a := []) (by simp))
        · exact (loop_go hne (sd_noSep hsep) (fun heq => hne heq.symm) hne).trans (loop_nil _ _)
  | 0, _ :: _, hk, _ => by simp at hk
  | k + 1, t, hk, ht => by
    rcases nil_or_concat t with rfl | ⟨t', x, rfl⟩
    · simp at hk
    · have hk' : t'.length = k := by
        simp at hk
        omega
      have ht' : ∀ z ∈ t', z ≠ [] ∧ ∀ c ∈ z, isSep c = false := fun z hz => ht z (by simp [hz])
      obtain ⟨hxne, hxsep⟩ := ht x (by simp)
      obtain ⟨hshape, hloop⟩ := comp_loop h hh k t' hk' ht'
      have habs : isabspath x = false := not_abs hxsep
      obtain ⟨x', z, rfl, hz⟩ : ∃ x' z, x = x' ++ [z] ∧ isSep z = false := by
        rcases nil_or_concat x with h0 | ⟨x', z, rfl⟩
        · exact absurd h0 hxne
        · exact ⟨x', z, rfl, hxsep z (by simp)⟩
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      revert hshape hloop
      generalize t'.foldl joinStep h = q
      intro hshape hloop
      rcases hshape with rfl | ⟨q', y, rfl, hy⟩
      · have e : joinStep ['/'] (x' ++ [z]) = '/' :: (x' ++ [z]) := joinStep_slash habs rfl
        rw [e]
        refine ⟨Or.inr ⟨'/' :: x', z, rfl, hz⟩, fun n out hn => ?_⟩
        cases n with
        | zero => exact absurd hn (Nat.not_lt_zero _)
        | succ m =>
          rw [loop_go (by simp) (sd_root hxsep)
              (fun heq => hxne (by injection heq with _ e2; exact e2.symm)) hxne,
            hloop m _ (by simp at hn ⊢; omega)]
          simp
      · have hlast : (q' ++ [y]).getLast? ≠ some '/' := by
          rw [List.getLast?_concat]
          intro h'
          exact ne_slash hy (Option.some.inj h')
        have e : joinStep (q' ++ [y]) (x' ++ [z]) = q' ++ [y] ++ '/' :: (x' ++ [z]) :=
          joinStep_noSlash habs (by simp) hlast
        rw [e]
        refine ⟨Or.inr ⟨q' ++ [y] ++ '/' :: x', z, by simp, hz⟩, fun n out hn => ?_⟩
        cases n with
        | zero => exact absurd hn (Nat.not_lt_zero _)
        | succ m =>
          have hd : q' ++ [y] ≠ q' ++ [y] ++ '/' :: (x' ++ [z]) := by
            intro heq
            have := congrArg List.length heq
            simp at this <;> omega
          rw [loop_go (by simp) (sd_mid hy hxsep) hd hxne, hloop m _ (by simp at hn ⊢; omega)]
          simp

end JuliaLean.Paths.SplitLemmas

namespace JuliaLean.Paths

open JuliaLean SplitLemmas

theorem dirnameBasename_proven : DirnameBasename := by
  intro p
  refine ⟨rfl, ?_⟩
  rcases decomp isSep p with hs | ⟨b, x, a, rfl, hx, ha⟩
  · have e : basename p = p := congrArg Prod.snd (sd_noSep hs)
    rw [e]
    exact ⟨allSep_iff.mpr hs, [], rfl⟩
  · have e : basename (b ++ x :: a) = a := congrArg Prod.snd (sd_some hx ha)
    rw [e]
    exact ⟨allSep_iff.mpr ha, b ++ [x], by simp⟩

theorem joinSplitdir_proven : JoinSplitdir := by
  intro p hnd
  suffices h : joinStep (dirname p) (basename p) = p by
    show (Except.ok (joinStep (dirname p) (basename p)) : Jl Str) = Except.ok p
    rw [h]
  rcases decomp isSep p with hs | ⟨b, x, a, rfl, hx, ha⟩
  · show joinStep (splitdirNoDrive [] p).1 (splitdirNoDrive [] p).2 = p
    rw [sd_noSep hs]
    exact joinStep_nil
  · have hx' : x = '/' := by simpa [isSep] using hx
    subst hx'
    rcases nil_or_concat b with rfl | ⟨b', y, rfl⟩
    · show joinStep (splitdirNoDrive [] ('/' :: a)).1 (splitdirNoDrive [] ('/' :: a)).2 = '/' :: a
      rw [sd_root ha]
      show joinStep ['/'] a = '/' :: a
      exact joinStep_slash (not_abs ha) rfl
    · have hy : isSep y = false := lastNotSep hnd hx
      show joinStep (splitdirNoDrive [] (b' ++ [y] ++ '/' :: a)).1
        (splitdirNoDrive [] (b' ++ [y] ++ '/' :: a)).2 = b' ++ [y] ++ '/' :: a
      rw [sd_mid hy ha]
      show joinStep (b' ++ [y]) a = b' ++ [y] ++ '/' :: a
      refine joinStep_noSlash (not_abs ha) (by simp) ?_
      rw [List.getLast?_concat]
      intro h
      exact ne_slash hy (Option.some.inj h)

theorem splitpathJoinpath_proven : SplitpathJoinpath := by
  refine ⟨fun p hcan => ?_, fun parts hparts => ?_⟩
  · obtain ⟨hnd, hc⟩ := hcan
    by_cases hp : p = []
    · subst hp
      rfl
    · obtain ⟨h, t, e, f⟩ := loop_canonical (p.length + 1) p [] hp (by omega) hnd hc
      rw [splitpath_ne hp, e, List.append_nil]
      simp only [joinpath, f]
  · cases parts with
    | nil => exact False.elim hparts
    | cons h t =>
      obtain ⟨hh, ht⟩ := hparts
      have hh' : h = ['/'] ∨ (h ≠ [] ∧ ∀ c ∈ h, isSep c = false) := by
        rcases hh with hh | ⟨hne, hall⟩
        · exact Or.inl hh
        · exact Or.inr ⟨hne, allSep_iff.mp hall⟩
      have ht' : ∀ x ∈ t, x ≠ [] ∧ ∀ c ∈ x, isSep c = false :=
        fun x hx => ⟨(ht x hx).1, allSep_iff.mp (ht x hx).2⟩
      obtain ⟨hshape, hloop⟩ := comp_loop h hh' t.length t rfl ht'
      have hq : t.foldl joinStep h ≠ [] := by
        rcases hshape with e | ⟨q, y, e, _⟩ <;> rw [e] <;> simp
      refine ⟨t.foldl joinStep h, rfl, ?_⟩
      rw [splitpath_ne hq, hloop ((t.foldl joinStep h).length + 1) [] (by omega), List.append_nil]

theorem splitextConcat_proven : SplitextConcat := by
  intro p
  rcases decomp (· == '.') p with h | ⟨b, x, a, rfl, hx, ha⟩
  · have e : splitext p = (p, []) := by simp [splitext, splitLast_none h]
    rw [e]
    exact ⟨by simp, Or.inl rfl⟩
  · have hx' : x = '.' := by simpa using hx
    subst hx'
    have hs : splitLast (· == '.') (b ++ '.' :: a) = some (b, a) := splitLast_some hx ha
    have key : splitext (b ++ '.' :: a) = (b ++ '.' :: a, []) ∨
        (splitext (b ++ '.' :: a) = (b, '.' :: a) ∧ a.all (fun c => c != '/' && c != '.') = true) := by
      cases hany : a.any isSep
      · cases hlast : b.getLast? with
        | none =>
          left
          simp [splitext, hs, hany, hlast]
        | some c =>
          cases hc : isSep c
          · right
            refine ⟨by simp [splitext, hs, hany, hlast, hc], ?_⟩
            rw [List.all_eq_true]
            intro d hd
            have h1 : isSep d = false := by
              cases h : isSep d
              · rfl
              · have : a.any isSep = true := List.any_eq_true.mpr ⟨d, hd, h⟩
                rw [hany] at this
                exact absurd this (by decide)
            have h2 := ha d hd
            simp [isSep] at h1
            simp at h2
            simp [h1, h2]
          · left
            simp [splitext, hs, hany, hlast, hc]
      · left
        simp [splitext, hs, hany]
    rcases key with e | ⟨e, hall⟩
    · rw [e]
      exact ⟨by simp, Or.inl rfl⟩
    · rw [e]
      exact ⟨rfl, Or.inr ⟨a, rfl, hall⟩⟩

theorem joinpathLaws_proven : JoinpathLaws := by
  refine ⟨fun a b hb => ?_, fun a b c => ⟨rfl, ?_⟩⟩
  · show (Except.ok (joinStep a b) : Jl Str) = Except.ok b
    rw [joinStep_abs hb]
  · show (Except.ok (joinStep (joinStep a b) c) : Jl Str) = Except.ok (joinStep a (joinStep b c))
    rw [joinStep_assoc]

theorem expanduserDoc_proven : ExpanduserDoc := by
  intro home lookup userChar p
  refine ⟨fun hp => ?_, fun hp => ?_, fun user rest hu hsep hrest hl => ?_⟩
  · rcases hp with rfl | hp
    · simp [expanduser, span_eq]
    · cases p with
      | nil => simp at hp
      | cons c r =>
        simp at hp
        subst hp
        simp [expanduser, span_eq, isSep]
  · cases p with
    | nil => rfl
    | cons c r =>
      have hc : c ≠ '~' := fun h => hp (by simp [h])
      simp [expanduser, hc]
  · have hall : ∀ c ∈ user, (!isSep c) = true := by
      intro c hc
      simp [allSep_iff.mp hsep c hc]
    have hs : (user ++ rest).span (fun x => !isSep x) = (user, rest) := by
      rw [span_eq, List.takeWhile_append_of_pos hall, List.dropWhile_append_of_pos hall]
      rcases hrest with rfl | hrest
      · simp
      · cases rest with
        | nil => simp
        | cons c r =>
          simp at hrest
          subst hrest
          simp [isSep]
    have hne : user.isEmpty = false := isEmpty_false hu
    simp [expanduser, hs, hne, hl]

theorem isdirpathTrailing_proven : IsdirpathTrailing := by
  intro p
  have e := sd_some (b := p) (a := []) isSep_slash (by simp)
  simp only [isdirpath, e]
  try rfl

end JuliaLean.Paths
