import JuliaLean.Platforms.DlName

/-!
# Declarative semantics of the backtracking matcher

`Mt r s c s' c'`: the pattern `r` can consume the subject `s` down to the suffix
`s'`, turning the captures `c` into `c'` (a star iteration must consume a
character). `matchFuel` only returns the captures of such a derivation
(`matchFuel_sound`), and returns some result whenever a derivation exists and the
fuel exceeds the subject length (`matchFuel_complete`). Together they reduce a
question about `matchRe` to one about the derivations of a pattern.
-/

namespace JuliaLean.Platforms

open JuliaLean.VersionNumbers (Re Caps Kont step matchFuel matchRe capture)
open JuliaLean.VersionNumbers.Re

inductive Mt : Re → List Char → Caps → List Char → Caps → Prop
  | cls {p : Char → Bool} {x : Char} {t : List Char} {c : Caps} :
      p x = true → Mt (.cls p) (x :: t) c t c
  | eps {s : List Char} {c : Caps} : Mt .eps s c s c
  | seq {a b : Re} {s s1 s2 : List Char} {c c1 c2 : Caps} :
      Mt a s c s1 c1 → Mt b s1 c1 s2 c2 → Mt (.seq a b) s c s2 c2
  | altL {a b : Re} {s s' : List Char} {c c' : Caps} : Mt a s c s' c' → Mt (.alt a b) s c s' c'
  | altR {a b : Re} {s s' : List Char} {c c' : Caps} : Mt b s c s' c' → Mt (.alt a b) s c s' c'
  | starNil {a : Re} {s : List Char} {c : Caps} : Mt (.star a) s c s c
  | starCons {a : Re} {s s1 s2 : List Char} {c c1 c2 : Caps} :
      Mt a s c s1 c1 → s1.length < s.length → Mt (.star a) s1 c1 s2 c2 → Mt (.star a) s c s2 c2
  | group {i : Nat} {a : Re} {s s' : List Char} {c c' : Caps} :
      Mt a s c s' c' → Mt (.group i a) s c s' ((i, s.take (s.length - s'.length)) :: c')
  | eol {s : List Char} {c : Caps} : (s = [] ∨ s = ['\n']) → Mt .eol s c s c

/-! ## Soundness and completeness of `matchFuel` -/

theorem step_alt (rec : Re → List Char → Caps → Kont → Option Caps) (a b : Re) (s : List Char)
    (c : Caps) (k : Kont) : step rec (.alt a b) s c k = (step rec a s c k).or (step rec b s c k) := by
  simp only [step]
  split <;> rename_i h <;> simp [h]

theorem step_star (rec : Re → List Char → Caps → Kont → Option Caps) (a : Re) (s : List Char)
    (c : Caps) (k : Kont) : step rec (.star a) s c k =
      (step rec a s c (fun s' c' => if s'.length < s.length then rec (.star a) s' c' k else none)).or
        (k s c) := by
  simp only [step]
  split <;> rename_i h <;> simp [h]

theorem step_sound (n : Nat)
    (ih : ∀ r s c k x, matchFuel n r s c k = some x → ∃ s' c', Mt r s c s' c' ∧ k s' c' = some x) :
    ∀ r s c k x, step (matchFuel n) r s c k = some x → ∃ s' c', Mt r s c s' c' ∧ k s' c' = some x := by
  intro r
  induction r with
  | cls p =>
    intro s c k x h
    cases s with
    | nil => simp [step] at h
    | cons y t =>
      simp only [step] at h
      by_cases hp : p y = true
      · rw [if_pos hp] at h
        exact ⟨t, c, .cls hp, h⟩
      · rw [if_neg hp] at h
        cases h
  | eps => intro s c k x h; exact ⟨s, c, .eps, h⟩
  | seq a b iha ihb =>
    intro s c k x h
    obtain ⟨s1, c1, h1, h2⟩ := iha s c _ x h
    obtain ⟨s2, c2, h3, h4⟩ := ihb s1 c1 k x h2
    exact ⟨s2, c2, .seq h1 h3, h4⟩
  | alt a b iha ihb =>
    intro s c k x h
    rw [step_alt, Option.or_eq_some_iff] at h
    rcases h with h | ⟨-, h⟩
    · obtain ⟨s', c', h1, h2⟩ := iha s c k x h
      exact ⟨s', c', .altL h1, h2⟩
    · obtain ⟨s', c', h1, h2⟩ := ihb s c k x h
      exact ⟨s', c', .altR h1, h2⟩
  | star a iha =>
    intro s c k x h
    rw [step_star, Option.or_eq_some_iff] at h
    rcases h with h | ⟨-, h⟩
    · obtain ⟨s1, c1, h1, h2⟩ := iha s c _ x h
      split at h2
      · rename_i hlt
        obtain ⟨s2, c2, h3, h4⟩ := ih (.star a) s1 c1 k x h2
        exact ⟨s2, c2, .starCons h1 hlt h3, h4⟩
      · cases h2
    · exact ⟨s, c, .starNil, h⟩
  | group i a iha =>
    intro s c k x h
    obtain ⟨s', c', h1, h2⟩ := iha s c _ x h
    exact ⟨s', _, .group h1, h2⟩
  | eol =>
    intro s c k x h
    simp only [step] at h
    split at h
    · exact ⟨s, c, .eol ‹_›, h⟩
    · cases h

theorem matchFuel_sound : ∀ (n : Nat) (r : Re) (s : List Char) (c : Caps) (k : Kont) (x : Caps),
    matchFuel n r s c k = some x → ∃ s' c', Mt r s c s' c' ∧ k s' c' = some x
  | 0, _, _, _, _, _, h => by simp [matchFuel] at h
  | n + 1, r, s, c, k, x, h => step_sound n (matchFuel_sound n) r s c k x h

theorem Mt.suffix {r : Re} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt r s c s' c') : ∃ u, s = u ++ s' := by
  induction h with
  | cls => exact ⟨[_], rfl⟩
  | eps => exact ⟨[], rfl⟩
  | seq _ _ ih1 ih2 =>
    obtain ⟨u, hu⟩ := ih1
    obtain ⟨v, hv⟩ := ih2
    exact ⟨u ++ v, by rw [hu, hv, List.append_assoc]⟩
  | altL _ ih => exact ih
  | altR _ ih => exact ih
  | starNil => exact ⟨[], rfl⟩
  | starCons _ _ _ ih1 ih2 =>
    obtain ⟨u, hu⟩ := ih1
    obtain ⟨v, hv⟩ := ih2
    exact ⟨u ++ v, by rw [hu, hv, List.append_assoc]⟩
  | group _ ih => exact ih
  | eol => exact ⟨[], rfl⟩

theorem Mt.length_le {r : Re} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt r s c s' c') : s'.length ≤ s.length := by
  obtain ⟨u, hu⟩ := h.suffix
  rw [hu, List.length_append]
  omega

theorem matchFuel_complete {r : Re} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt r s c s' c') : ∀ (n : Nat) (k : Kont) (y : Caps), s.length < n → k s' c' = some y →
      ∃ x, matchFuel n r s c k = some x := by
  induction h with
  | @cls p x t c hp =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨y, ?_⟩
    show step (matchFuel n) (.cls p) (x :: t) c k = some y
    simp only [step]
    rw [if_pos hp]
    exact hk
  | @eps s c =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨y, hk⟩
  | @seq a b s s1 s2 c c1 c2 h1 _ ih1 ih2 =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hl := h1.length_le
    obtain ⟨y2, hy2⟩ := ih2 (n + 1) k y (by omega) hk
    obtain ⟨x, hx⟩ := ih1 (n + 1) (fun s' c' => matchFuel (n + 1) b s' c' k) y2 hn hy2
    exact ⟨x, hx⟩
  | @altL a b s s' c c' _ ih =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨x, hx⟩ := ih (n + 1) k y hn hk
    refine ⟨x, ?_⟩
    show step (matchFuel n) (.alt a b) s c k = some x
    rw [step_alt]
    exact Option.or_eq_some_iff.2 (.inl hx)
  | @altR a b s s' c c' _ ih =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨x, hx⟩ := ih (n + 1) k y hn hk
    show ∃ x, step (matchFuel n) (.alt a b) s c k = some x
    rw [step_alt]
    cases ha : step (matchFuel n) a s c k with
    | some r => exact ⟨r, rfl⟩
    | none => exact ⟨x, hx⟩
  | @starNil a s c =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show ∃ x, step (matchFuel n) (.star a) s c k = some x
    rw [step_star]
    cases (step (matchFuel n) a s c
        (fun s' c' => if s'.length < s.length then matchFuel n (.star a) s' c' k else none)) with
    | some r => exact ⟨r, rfl⟩
    | none => exact ⟨y, hk⟩
  | @starCons a s s1 s2 c c1 c2 _ hlt _ ih1 ih2 =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨y2, hy2⟩ := ih2 n k y (by omega) hk
    obtain ⟨x, hx⟩ := ih1 (n + 1)
      (fun s' c' => if s'.length < s.length then matchFuel n (.star a) s' c' k else none) y2 hn
      (by simp only [if_pos hlt]; exact hy2)
    refine ⟨x, ?_⟩
    show step (matchFuel n) (.star a) s c k = some x
    rw [step_star]
    exact Option.or_eq_some_iff.2 (.inl hx)
  | @group i a s s' c c' _ ih =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨x, hx⟩ := ih (n + 1)
      (fun s'' c'' => k s'' ((i, s.take (s.length - s''.length)) :: c'')) y hn hk
    exact ⟨x, hx⟩
  | @eol s c hs =>
    intro n k y hn hk
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨y, ?_⟩
    show step (matchFuel n) .eol s c k = some y
    simp only [step]
    rw [if_pos hs]
    exact hk

theorem matchRe_sound {r : Re} {s : List Char} {x : Caps} (h : matchRe r s = some x) :
    ∃ s', Mt r s [] s' x := by
  obtain ⟨s', c', h1, h2⟩ := matchFuel_sound _ _ _ _ _ _ h
  simp only [Option.some.injEq] at h2
  subst h2
  exact ⟨s', h1⟩

theorem matchRe_complete {r : Re} {s s' : List Char} {c' : Caps} (h : Mt r s [] s' c') :
    ∃ x, matchRe r s = some x :=
  matchFuel_complete h (s.length + 1) _ c' (Nat.lt_succ_self _) rfl

/-! ## Inversion -/

section Inv
variable {s s' : List Char} {c c' : Caps}

theorem Mt_cls_inv {p : Char → Bool} (h : Mt (.cls p) s c s' c') :
    ∃ x, s = x :: s' ∧ p x = true ∧ c' = c := by
  cases h with
  | cls hp => exact ⟨_, rfl, hp, rfl⟩

theorem Mt_chr_inv {a : Char} (h : Mt (chr a) s c s' c') : s = a :: s' ∧ c' = c := by
  obtain ⟨x, rfl, hx, rfl⟩ := Mt_cls_inv h
  simp only [beq_iff_eq] at hx
  subst hx
  exact ⟨rfl, rfl⟩

theorem Mt_eps_inv (h : Mt .eps s c s' c') : s' = s ∧ c' = c := by
  cases h
  exact ⟨rfl, rfl⟩

theorem Mt_seq_inv {a b : Re} (h : Mt (.seq a b) s c s' c') :
    ∃ s1 c1, Mt a s c s1 c1 ∧ Mt b s1 c1 s' c' := by
  cases h with
  | seq h1 h2 => exact ⟨_, _, h1, h2⟩

theorem Mt_alt_inv {a b : Re} (h : Mt (.alt a b) s c s' c') : Mt a s c s' c' ∨ Mt b s c s' c' := by
  cases h with
  | altL h => exact .inl h
  | altR h => exact .inr h

theorem Mt_opt_inv {a : Re} (h : Mt (opt a) s c s' c') : Mt a s c s' c' ∨ (s' = s ∧ c' = c) := by
  rcases Mt_alt_inv h with h | h
  · exact .inl h
  · exact .inr (Mt_eps_inv h)

theorem Mt_group_inv {i : Nat} {a : Re} (h : Mt (.group i a) s c s' c') :
    ∃ c1, Mt a s c s' c1 ∧ c' = (i, s.take (s.length - s'.length)) :: c1 := by
  cases h with
  | group h => exact ⟨_, h, rfl⟩

theorem Mt_eol_inv (h : Mt .eol s c s' c') : s' = s ∧ c' = c ∧ (s = [] ∨ s = ['\n']) := by
  cases h with
  | eol hs => exact ⟨rfl, rfl, hs⟩

end Inv

/-- A star whose iterations consume words of a language `L` closed under
prepending an iteration consumes a word of `L` and keeps the captures. -/
theorem Mt_star_lang {a : Re} {L : List Char → Prop} (h0 : L [])
    (ha : ∀ s c s' c', Mt a s c s' c' → c' = c ∧ ∃ u, s = u ++ s' ∧ ∀ v, L v → L (u ++ v)) :
    ∀ {s c s' c'}, Mt (.star a) s c s' c' → c' = c ∧ ∃ u, s = u ++ s' ∧ L u := by
  intro s c s' c' h
  generalize hr : Re.star a = r at h
  induction h with
  | starNil => exact ⟨rfl, [], rfl, h0⟩
  | starCons h1 _ _ _ ih2 =>
    cases hr
    obtain ⟨rfl, u, rfl, hu⟩ := ha _ _ _ _ h1
    obtain ⟨rfl, v, rfl, hv⟩ := ih2 rfl
    exact ⟨rfl, u ++ v, by simp, hu v hv⟩
  | _ => cases hr

theorem Mt_star_cls {p : Char → Bool} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt (.star (.cls p)) s c s' c') : c' = c ∧ ∃ u, s = u ++ s' ∧ ∀ x ∈ u, p x = true :=
  Mt_star_lang (L := fun u => ∀ x ∈ u, p x = true) (by simp) (fun s c s' c' h => by
    obtain ⟨x, rfl, hx, rfl⟩ := Mt_cls_inv h
    refine ⟨rfl, [x], rfl, fun v hv y hy => ?_⟩
    simp only [List.singleton_append, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hv y hy) h

theorem Mt_plus_cls {p : Char → Bool} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt (plus (.cls p)) s c s' c') : c' = c ∧ ∃ u, s = u ++ s' ∧ u ≠ [] ∧ ∀ x ∈ u, p x = true := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨x, rfl, hx, rfl⟩ := Mt_cls_inv h1
  obtain ⟨rfl, u, rfl, hu⟩ := Mt_star_cls h2
  refine ⟨rfl, x :: u, rfl, by simp, fun y hy => ?_⟩
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hu y hy

/-! ## Construction -/

theorem Mt_chr_mk (a : Char) (s : List Char) (c : Caps) : Mt (chr a) (a :: s) c s c :=
  .cls (by simp)

theorem Mt_star_cls_mk {p : Char → Bool} : ∀ (u s : List Char) (c : Caps), (∀ x ∈ u, p x = true) →
    Mt (.star (.cls p)) (u ++ s) c s c
  | [], _, _, _ => .starNil
  | x :: u, s, c, hu =>
    .starCons (.cls (hu x (by simp))) (by simp)
      (Mt_star_cls_mk u s c (fun y hy => hu y (by simp [hy])))

theorem Mt_plus_cls_mk {p : Char → Bool} (u s : List Char) (c : Caps) (hne : u ≠ [])
    (hu : ∀ x ∈ u, p x = true) : Mt (plus (.cls p)) (u ++ s) c s c := by
  obtain ⟨x, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact .seq (.cls (hu x (by simp))) (Mt_star_cls_mk u s c (fun y hy => hu y (by simp [hy])))

/-! ## Literals -/

theorem Mt_litD : ∀ (l : List Char) {s : List Char} {c : Caps} {s' : List Char} {c' : Caps},
    l ≠ [] → Mt (litD l) s c s' c' → s = l ++ s' ∧ c' = c
  | [], _, _, _, _, hl, _ => absurd rfl hl
  | [a], s, c, s', c', _, h => by
    change Mt (chr a) s c s' c' at h
    exact Mt_chr_inv h
  | a :: b :: t, s, c, s', c', _, h => by
    change Mt (.seq (chr a) (litD (b :: t))) s c s' c' at h
    obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
    obtain ⟨rfl, rfl⟩ := Mt_chr_inv h1
    obtain ⟨rfl, rfl⟩ := Mt_litD (b :: t) (by simp) h2
    exact ⟨rfl, rfl⟩

theorem Mt_litD_mk : ∀ (l : List Char) (s : List Char) (c : Caps), l ≠ [] → Mt (litD l) (l ++ s) c s c
  | [], _, _, hl => absurd rfl hl
  | [a], s, c, _ => by
    change Mt (chr a) (a :: s) c s c
    exact Mt_chr_mk a s c
  | a :: b :: t, s, c, _ => by
    change Mt (.seq (chr a) (litD (b :: t))) (a :: (b :: t ++ s)) c s c
    exact .seq (Mt_chr_mk a _ c) (Mt_litD_mk (b :: t) s c (by simp))

theorem Mt_litCI : ∀ (l : List Char) {s : List Char} {c : Caps} {s' : List Char} {c' : Caps},
    l ≠ [] → Mt (litCI l) s c s' c' → c' = c ∧ ∃ u, s = u ++ s' ∧ u.length = l.length
  | [], _, _, _, _, hl, _ => absurd rfl hl
  | [a], s, c, s', c', _, h => by
    change Mt (.cls fun d => asciiLower d == asciiLower a) s c s' c' at h
    obtain ⟨x, rfl, -, rfl⟩ := Mt_cls_inv h
    exact ⟨rfl, [x], rfl, rfl⟩
  | a :: b :: t, s, c, s', c', _, h => by
    change Mt (.seq (.cls fun d => asciiLower d == asciiLower a) (litCI (b :: t))) s c s' c' at h
    obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
    obtain ⟨x, rfl, -, rfl⟩ := Mt_cls_inv h1
    obtain ⟨rfl, u, rfl, hu⟩ := Mt_litCI (b :: t) (by simp) h2
    exact ⟨rfl, x :: u, rfl, by simp [hu]⟩

theorem Mt_litCI_mk : ∀ (l : List Char) (s : List Char) (c : Caps), l ≠ [] →
    Mt (litCI l) (l ++ s) c s c
  | [], _, _, hl => absurd rfl hl
  | [a], s, c, _ => by
    change Mt (.cls fun d => asciiLower d == asciiLower a) (a :: s) c s c
    exact .cls (by simp)
  | a :: b :: t, s, c, _ => by
    change Mt (.seq (.cls fun d => asciiLower d == asciiLower a) (litCI (b :: t))) (a :: (b :: t ++ s)) c s c
    exact .seq (.cls (by simp)) (Mt_litCI_mk (b :: t) s c (by simp))

/-! ## `lazyMatch` -/

/-- `^(.*?)REST` on `name ++ tail` captures `name` when `REST` matches `tail`
but no suffix `w ++ tail` with `w` a nonempty suffix of `name`. -/
theorem lazyMatch_go_split (R : Re) (tail : List Char) (htail : tail ≠ []) (m : Caps)
    (hm : matchRe R tail = some m) :
    ∀ (name pre : List Char), (∀ u w, name = u ++ w → w ≠ [] → matchRe R (w ++ tail) = none) →
      lazyMatch.go R pre (name ++ tail) = some (pre ++ name, m)
  | [], pre, _ => by
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil htail
    simp only [List.nil_append, lazyMatch.go, hm, List.append_nil]
  | a :: name, pre, h => by
    have h0 : matchRe R (a :: (name ++ tail)) = none := h [] (a :: name) rfl (by simp)
    have ih := lazyMatch_go_split R tail htail m hm name (pre ++ [a])
      (fun u w hu hw => h (a :: u) w (by simp [hu]) hw)
    simp only [List.cons_append, lazyMatch.go, h0]
    simpa using ih

theorem lazyMatch_split (R : Re) (tail : List Char) (htail : tail ≠ []) (m : Caps)
    (hm : matchRe R tail = some m) (name : List Char)
    (h : ∀ u w, name = u ++ w → w ≠ [] → matchRe R (w ++ tail) = none) :
    lazyMatch R (name ++ tail) = some (name, m) := by
  have := lazyMatch_go_split R tail htail m hm name [] h
  simpa [lazyMatch] using this

/-! ## List facts -/

theorem take_cap (u r : List Char) : (u ++ r).take ((u ++ r).length - r.length) = u := by
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left' rfl

theorem dot_unique : ∀ (u u' v v' : List Char), u ++ '.' :: v = u' ++ '.' :: v' →
    (∀ y ∈ u, y ≠ '.') → (∀ y ∈ u', y ≠ '.') → u = u' ∧ v = v'
  | [], [], v, v', h, _, _ => by
    simp only [List.nil_append, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | [], y :: u', v, v', h, _, hu' => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1.symm (hu' y (by simp))
  | y :: u, [], v, v', h, hu, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1 (hu y (by simp))
  | y :: u, y' :: u', v, v', h, hu, hu' => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := dot_unique u u' v v' h (fun z hz => hu z (by simp [hz]))
      (fun z hz => hu' z (by simp [hz]))
    exact ⟨rfl, rfl⟩

theorem last_dot : ∀ (w : List Char), '.' ∈ w → ∃ pre ds, w = pre ++ '.' :: ds ∧ ∀ y ∈ ds, y ≠ '.'
  | [], h => by simp at h
  | a :: w, h => by
    by_cases hw : '.' ∈ w
    · obtain ⟨pre, ds, rfl, hds⟩ := last_dot w hw
      exact ⟨a :: pre, ds, rfl, hds⟩
    · have ha : a = '.' := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact h.symm
        · exact absurd h hw
      subst ha
      exact ⟨[], w, rfl, fun y hy hy' => hw (hy' ▸ hy)⟩

/-- A dot-free suffix `Z` of `A ++ '.' :: D` is a suffix of `D`. -/
theorem suffix_nodot {Y Z A D : List Char} (h : Y ++ Z = A ++ '.' :: D) (hZ : ∀ y ∈ Z, y ≠ '.') :
    ∃ E, D = E ++ Z := by
  have h' : Y ++ Z = (A ++ ['.']) ++ D := by simpa using h
  rcases List.append_eq_append_iff.1 h' with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · rcases List.eq_nil_or_concat as with rfl | ⟨l', b, rfl⟩
    · exact ⟨[], by simpa using h2.symm⟩
    · have h3 : A ++ ['.'] = (Y ++ l') ++ [b] := by simpa using h1
      have hb : b = '.' := by
        have := (List.append_inj' h3 rfl).2
        simp only [List.cons.injEq, and_true] at this
        exact this.symm
      exact absurd hb (hZ b (by rw [h2]; simp))
  · exact ⟨bs, h2⟩

theorem no_nl {P P' : List Char} {a : Char} (ha : a ≠ '\n') (h : P ++ [a] = P' ++ ['\n']) : False := by
  have := (List.append_inj' h rfl).2
  simp only [List.cons.injEq, and_true] at this
  exact ha this

end JuliaLean.Platforms
