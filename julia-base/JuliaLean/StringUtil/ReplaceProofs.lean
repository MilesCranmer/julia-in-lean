import JuliaLean.StringUtil.ReplaceModel

/-!
# Proofs for the `replace` model (`JuliaLean/StringUtil/ReplaceModel.lean`)

The main lemma `loop_ref` runs the loop of `_replace_finish` in lockstep with the
reference scan: at the head of every iteration the cached range of each pattern is
its first occurrence at a character index `≥ i` (or the sentinel `e1+1:0`), so the
range `argmin` selects starts at the first position where some pattern occurs and
belongs to the first such pattern in argument order.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-! ## `count == 0` and `count < 0` -/

theorem replaceCountEdge : ReplaceCountEdge := by
  intro s ps count
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [replace, replaceN, h]
  · have h0 : ¬ count.val = 0 := by omega
    simp [replace, replaceN, replaceInit, h0, h]

/-! ## List helpers -/

theorem getD_lt {α : Type} (l : List α) (d : α) (y : Nat) (h : y < l.length) :
    l.getD y d = l[y] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem find?_first {α : Type} (P : α → Bool) :
    ∀ (l : List α) (x : Nat) (hx : x < l.length), P l[x] = true →
      (∀ y (hy : y < x), P (l[y]'(by omega)) = false) → l.find? P = some l[x]
  | [], _, hx, _, _ => by simp at hx
  | a :: l, 0, _, hp, _ => by
    simp only [List.getElem_cons_zero] at hp
    simp [List.find?_cons, hp]
  | a :: l, x + 1, hx, hp, hy => by
    have ha : P a = false := hy 0 (by omega)
    have ih := find?_first P l x (by simp at hx; omega) (by simpa using hp)
      (fun y h => by simpa using hy (y + 1) (by omega))
    simp [List.find?_cons, ha, ih]

/-! ## `argmin` returns the first minimal index -/

theorem argminAux_spec (l : List JInt64) (d : JInt64) :
    ∀ (xs : List JInt64) (k im : Nat) (fm : JInt64), l.drop k = xs → k ≤ l.length → im < k →
      l.getD im d = fm → (∀ y, y < k → fm.val ≤ (l.getD y d).val) →
      (∀ y, y < im → fm.val < (l.getD y d).val) →
      argminAux xs k im fm < l.length ∧
      (∀ y, y < l.length → (l.getD (argminAux xs k im fm) d).val ≤ (l.getD y d).val) ∧
      (∀ y, y < argminAux xs k im fm →
        (l.getD (argminAux xs k im fm) d).val < (l.getD y d).val)
  | [], k, im, fm, hd, _, him, hfm, hle, hlt => by
    have hlen : l.length ≤ k := by
      have := congrArg List.length hd; simp at this; omega
    simp only [argminAux]
    refine ⟨by omega, fun y hy => ?_, fun y hy => ?_⟩
    · rw [hfm]; exact hle y (by omega)
    · rw [hfm]; exact hlt y hy
  | x :: xs, k, im, fm, hd, _, him, hfm, hle, hlt => by
    have hkl : k < l.length := by
      have := congrArg List.length hd; simp at this; omega
    have hx : l.getD k d = x := by
      have h0 := congrArg (fun t => t[0]?) hd
      simp at h0
      simp [List.getD_eq_getElem?_getD, h0]
    have hd' : l.drop (k + 1) = xs := by
      have := congrArg List.tail hd; simpa [List.tail_drop] using this
    simp only [argminAux]
    split
    · rename_i hlt'
      exact argminAux_spec l d xs (k + 1) k x hd' (by omega) (by omega) hx
        (fun y hy => by
          by_cases hyk : y = k
          · subst hyk; rw [hx]; omega
          · have := hle y (by omega); omega)
        (fun y hy => by have := hle y hy; omega)
    · rename_i hge
      exact argminAux_spec l d xs (k + 1) im fm hd' (by omega) (by omega) hfm
        (fun y hy => by
          by_cases hyk : y = k
          · subst hyk; rw [hx]; omega
          · exact hle y (by omega))
        hlt

theorem argmin_spec (l : List JInt64) (d : JInt64) (h : 0 < l.length) :
    argmin l < l.length ∧
    (∀ y, y < l.length → (l.getD (argmin l) d).val ≤ (l.getD y d).val) ∧
    (∀ y, y < argmin l → (l.getD (argmin l) d).val < (l.getD y d).val) := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [argmin]
    exact argminAux_spec (x :: xs) d xs 1 0 x (by simp) (by simp) (by omega) (by simp)
      (fun y hy => by
        have : y = 0 := by omega
        subst this; simp)
      (fun y hy => by omega)

/-! ## Index facts -/

/-- No character index lies after `thisZ s n`. -/
theorem noValid_after_last (s : JStr) (hL : 1 ≤ s.bytes.length) (r : Int)
    (h1 : thisZ s s.bytes.length < r) (h2 : r ≤ s.bytes.length) : ¬ validZ s r := by
  intro hv
  by_cases ht : thisZ s s.bytes.length < s.bytes.length
  · have hc := leadZ_covers s s.bytes.length (by omega) (Int.le_refl _) ht
    by_cases hr : r = s.bytes.length
    · subst hr; have := hv.2.2; omega
    · have := leadZ_inside s (thisZ s s.bytes.length) r hc.2.2.1 ⟨hc.1, hc.2.1⟩ h1 (by omega)
      have := hv.2.2; omega
  · have := (thisZ_le s s.bytes.length).1; omega

/-- The body of `lastindex` (`base/strings/string.jl:249`) with its discriminant as a
parameter. It mentions `thisind s (ncodeunits s)` so that it has the same definitional
height as `lastindex`: the kernel then unfolds both together and compares the matcher
arguments, instead of reducing the matcher on `thisind s (ncodeunits s)` (which it
cannot evaluate for a symbolic `s`). -/
def liAt (s : JStr) (t : SJl JInt64) : JInt64 :=
  let _u := thisind s (ncodeunits s)
  isvalidAt.match_1 (fun _ => JInt64) t (fun j => j) (fun _ => ix 0)

theorem lastindex_of (s : JStr) (j : JInt64) (hj : thisind s (ncodeunits s) = .ok j) :
    lastindex s = j := by
  have h1 : liAt s (thisind s (ncodeunits s)) = j := by rw [hj]; rfl
  exact h1

/-- What `lastindex(s)` is. -/
def LastSpec (s : JStr) (li : JInt64) : Prop :=
  (s.bytes.length = 0 ∧ li.val = 0) ∨ (1 ≤ s.bytes.length ∧ li.val = thisZ s s.bytes.length)

theorem lastindex_spec (s : JStr) : LastSpec s (lastindex s) := by
  by_cases hL : s.bytes.length = 0
  · left
    refine ⟨hL, ?_⟩
    have h0 : (ncodeunits s).val = 0 := by rw [ncu_val, hL]; rfl
    have ht : thisind s (ncodeunits s) = .ok (ix 0) := by
      unfold thisind; rw [if_pos h0]
    rw [lastindex_of s _ ht]
    exact ix0
  · right
    obtain ⟨j, hj, hv⟩ := thisind_mid s (ncodeunits s) (by rw [ncu_val]; omega)
      (by rw [ncu_val]; exact Int.le_refl _)
    refine ⟨by omega, ?_⟩
    rw [lastindex_of s _ hj, hv, ncu_val]

/-- `e1 = nextind(str, lastindex(str))` is `ncodeunits(str) + 1`. -/
theorem e1_spec (s : JStr) (li : JInt64) (hli : LastSpec s li) :
    ∃ e1, nextind s li = .ok e1 ∧ e1.val = s.bytes.length + 1 := by
  rcases hli with ⟨hL, hl⟩ | ⟨hL, hl⟩
  · refine ⟨ix 1, ?_, by simp [hL]⟩
    unfold nextind
    simp [hl]
  · have hp1 := thisZ_pos s s.bytes.length (by omega)
    have hp2 := (thisZ_le s s.bytes.length).1
    obtain ⟨q, hq, hqv⟩ := nextind_mid s li (by omega) (by omega)
    refine ⟨q, hq, ?_⟩
    have hnv := nextZ_nextValid s li.val (by omega) (by omega)
    rw [← hqv] at hnv
    obtain ⟨ha, hb, _, hd⟩ := hnv
    by_cases hqL : q.val ≤ s.bytes.length
    · exact absurd (hd hqL) (noValid_after_last s hL q.val (by omega) hqL)
    · omega

/-- `SubString(str, i, li)` with `li = lastindex(str)`, at a character index or at
`ncodeunits(str) + 1`. -/
theorem subFrom (s : JStr) (li : JInt64) (hli : LastSpec s li) (i : JInt64) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ s.bytes.length + 1) (hv : i.val ≤ s.bytes.length → validZ s i.val) :
    ∃ sub, substring s i li = .ok sub ∧
      sub.view.bytes = s.bytes.drop (i.val - 1).toNat := by
  have hs := ncu_small s
  by_cases hgt : li.val < i.val
  · have hiL : i.val = s.bytes.length + 1 := by
      by_cases hne : i.val ≤ s.bytes.length
      · exfalso
        have hv' := hv hne
        rcases hli with ⟨hL, _⟩ | ⟨hL, hl⟩
        · have := hv'.2.1; omega
        · exact noValid_after_last s hL i.val (by omega) hv'.2.1 hv'
      · omega
    refine ⟨⟨s, ix 0, ix 0⟩, ?_, ?_⟩
    · unfold substring
      have : ¬ i.val ≤ li.val := by omega
      simp [this]
    · have : (i.val - 1).toNat = s.bytes.length := by omega
      rw [this, List.drop_length]
      simp [JSub.view, JStr.slice]
  · have hle : i.val ≤ li.val := by omega
    have hli' := hli
    rcases hli' with ⟨hL, hl⟩ | ⟨hL, hl⟩
    · omega
    have hp2 := (thisZ_le s s.bytes.length).1
    have hiL : i.val ≤ s.bytes.length := by omega
    have hvi := hv hiL
    have hvl : validZ s li.val := by
      rw [hl]; exact ⟨thisZ_pos s _ (by omega), hp2, thisZ_idem s _⟩
    obtain ⟨e, he, hev⟩ := e1_spec s li hli
    refine ⟨⟨s, i - ix 1, e - i⟩, ?_, ?_⟩
    · unfold substring
      have c1 : li.val ≤ (ncodeunits s).val := by rw [ncu_val]; omega
      have c2 : isvalidAt s i = true := (isvalidAt_iff s i).mpr hvi
      have c3 : isvalidAt s li = true := (isvalidAt_iff s _).mpr hvl
      simp [hle, h1, c1, c2, c3, he]
    · have e1' : (i - ix 1).val = i.val - 1 := sub_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega)
      have e2' : (e - i).val = s.bytes.length + 1 - i.val := by
        rw [sub_val _ _ (by omega) (by omega), hev]
      simp only [JSub.view, JStr.slice, e1', e2']
      apply List.take_of_length_le
      rw [List.length_drop]; omega

/-- A successful `nextind(s, l)` from `l ≥ 1` lands on the next character index. -/
theorem nextind_ok (s : JStr) (l q : JInt64) (h1 : 1 ≤ l.val) (h : nextind s l = .ok q) :
    l.val ≤ s.bytes.length ∧ NextValid s l.val q.val := by
  by_cases hl : l.val ≤ s.bytes.length
  · obtain ⟨q', hq', hv⟩ := nextind_mid s l h1 hl
    rw [hq'] at h
    injection h with h
    subst h
    rw [hv]
    exact ⟨hl, nextZ_nextValid s l.val h1 hl⟩
  · exfalso
    have hz : ¬ l.val = 0 := by omega
    have hb : betweenI l (ix 1) (ncodeunits s) = false := by
      unfold betweenI; rw [ncu_val, ix1]; simp; omega
    unfold nextind at h
    simp [hz, hb] at h

theorem copyOut_ok (s : JStr) (i j : JInt64) (hi : 1 ≤ i.val) (hij : i.val ≤ j.val)
    (hj : j.val ≤ s.bytes.length + 1) :
    copyOut s i (j - i) = .ok ((s.bytes.drop (i.val - 1).toNat).take (j.val - i.val).toNat) := by
  have hs := ncu_small s
  have e : (j - i).val = j.val - i.val := sub_val _ _ (by omega) (by omega)
  unfold copyOut
  simp only [e]
  split
  · omega
  · rfl

/-! ## Cached ranges -/

/-- The cached range `r` of a pattern with bytes `t` at position `i`: the sentinel
`e1+1:0` when `t` occurs at no character index `≥ i`, else the first occurrence. -/
def RngOk (s : JStr) (t : List UInt8) (i : Int) (r : Rng) : Prop :=
  (r.1.val = s.bytes.length + 2 ∧ NoOcc s t i) ∨ MatchOk s t i r.1 r.2

/-- Every cached range is correct at position `i`. -/
def AllOk (s : JStr) (qs : List (List UInt8 × Pair)) (i : Int) (rs : List Rng) : Prop :=
  rs.length = qs.length ∧ ∀ y (h1 : y < rs.length) (h2 : y < qs.length), RngOk s qs[y].1 i rs[y]

theorem rngOk_no_before {s : JStr} {t : List UInt8} {i : Int} {r : Rng} (h : RngOk s t i r) :
    ∀ p, i ≤ p → p < r.1.val → validZ s p → occursAt s t p = false := by
  intro p h1 h2 hv
  rcases h with ⟨_, hno⟩ | ⟨⟨_, _, _, hleast⟩, _⟩
  · exact hno p h1 hv
  · exact hleast p h1 h2 hv

theorem rngOk_match {s : JStr} {t : List UInt8} {i : Int} {r : Rng} (h : RngOk s t i r)
    (hr : r.1.val ≤ s.bytes.length + 1) : MatchOk s t i r.1 r.2 := by
  rcases h with ⟨he, _⟩ | hm
  · omega
  · exact hm

theorem rngOk_big {s : JStr} {t : List UInt8} {i : Int} {r : Rng} (h : RngOk s t i r)
    (hr : (s.bytes.length : Int) < r.1.val) : NoOcc s t i := by
  rcases h with ⟨_, hno⟩ | ⟨⟨_, hv, _⟩, _⟩
  · exact hno
  · exact absurd hv.2.1 (by omega)

theorem rngOk_mono {s : JStr} {t : List UInt8} {i i' : Int} {r : Rng} (h : RngOk s t i r)
    (hii : i ≤ i') (hr : i' ≤ r.1.val) : RngOk s t i' r := by
  rcases h with ⟨he, hno⟩ | ⟨⟨_, hv, ho, hleast⟩, hjl, hq⟩
  · exact Or.inl ⟨he, fun p hp hv => hno p (by omega) hv⟩
  · exact Or.inr ⟨⟨hr, hv, ho, fun p h1 h2 hv => hleast p (by omega) h2 hv⟩, hjl, hq⟩

theorem findRange_ok (s : JStr) (t : List UInt8) (p : Pair) (e1 : JInt64)
    (he1 : e1.val = s.bytes.length + 1) (k : JInt64) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ s.bytes.length + 1) (hf : FinderSpec s t p.find) :
    ∃ r, findRange p e1 k = .ok r ∧ RngOk s t k.val r := by
  have hs := ncu_small s
  obtain ⟨fr, hfr, hspec⟩ := hf k hk1 hk2
  have hsent : (e1 + ix 1).val = s.bytes.length + 2 := by
    rw [add_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega), ix1, he1]; omega
  unfold findRange
  rw [hfr]
  cases fr with
  | nothing => exact ⟨_, rfl, Or.inl ⟨hsent, hspec⟩⟩
  | idx i =>
    have hm : MatchOk s t k.val i i := hspec
    have hi : ¬ i.val = 0 := by have := hm.1.1; omega
    exact ⟨(i, i), by simp [toRange, hi], Or.inr hm⟩
  | range a b =>
    have hm : MatchOk s t k.val a b := hspec
    have ha : ¬ a.val = 0 := by have := hm.1.1; omega
    exact ⟨(a, b), by simp [toRange, ha], Or.inr hm⟩

theorem findAll_ok (s : JStr) (e1 a : JInt64) (he1 : e1.val = s.bytes.length + 1)
    (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ s.bytes.length + 1) :
    ∀ qs : List (List UInt8 × Pair), (∀ q ∈ qs, FinderSpec s q.1 q.2.find) →
      ∃ rs, findAll e1 a (qs.map (·.2)) = .ok rs ∧ AllOk s qs a.val rs
  | [], _ => ⟨[], rfl, rfl, fun y h1 _ => by simp at h1⟩
  | q :: qs, hq => by
    obtain ⟨r, hr, hok⟩ := findRange_ok s q.1 q.2 e1 he1 a ha1 ha2 (hq q (by simp))
    obtain ⟨rs, hrs, hlen, hall⟩ :=
      findAll_ok s e1 a he1 ha1 ha2 qs (fun q' h => hq q' (by simp [h]))
    refine ⟨r :: rs, ?_, by simp [hlen], fun y h1 h2 => ?_⟩
    · simp [findAll, hr, hrs]
    · cases y with
      | zero => simpa using hok
      | succ y => simpa using hall y (by simp at h1; omega) (by simp at h2; omega)

theorem refresh_ok (s : JStr) (e1 k : JInt64) (he1 : e1.val = s.bytes.length + 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ s.bytes.length + 1) (i : Int) (hik : i ≤ k.val) :
    ∀ (qs : List (List UInt8 × Pair)) (rs : List Rng), (∀ q ∈ qs, FinderSpec s q.1 q.2.find) →
      AllOk s qs i rs → ∃ rs', refresh e1 k (qs.map (·.2)) rs = .ok rs' ∧ AllOk s qs k.val rs'
  | [], [], _, _ => ⟨[], by simp [refresh], rfl, fun y h1 _ => by simp at h1⟩
  | [], _ :: _, _, ⟨hlen, _⟩ => by simp at hlen
  | _ :: _, [], _, ⟨hlen, _⟩ => by simp at hlen
  | q :: qs, r :: rs, hq, ⟨hlen, hall⟩ => by
    have hr0 : RngOk s q.1 i r := hall 0 (by simp) (by simp)
    obtain ⟨rs', hrs', hall'⟩ := refresh_ok s e1 k he1 hk1 hk2 i hik qs rs
      (fun q' h => hq q' (by simp [h]))
      ⟨by simpa using hlen, fun y h1 h2 => by
        exact hall (y + 1) (by simp; omega) (by simp; omega)⟩
    have hr' : ∃ r', (if r.1.val < k.val then findRange q.2 e1 k else .ok r) = .ok r' ∧
        RngOk s q.1 k.val r' := by
      split
      · exact findRange_ok s q.1 q.2 e1 he1 k hk1 hk2 (hq q (by simp))
      · rename_i hge
        exact ⟨r, rfl, rngOk_mono hr0 hik (by omega)⟩
    obtain ⟨r', hr'e, hr'ok⟩ := hr'
    refine ⟨r' :: rs', ?_, ?_⟩
    · simp only [List.map_cons, refresh, hr'e, hrs']
    · refine ⟨by simp [hall'.1], fun y h1 h2 => ?_⟩
      cases y with
      | zero => simpa using hr'ok
      | succ y => simpa using hall'.2 y (by simp at h1; omega) (by simp at h2; omega)

/-! ## The reference scan -/

/-- No pattern of `prs` occurs at a character index in `[a, b)` (when replacements remain). -/
def NoHit (s : JStr) (prs : List (List UInt8 × List UInt8)) (c : Nat) (a b : Int) : Prop :=
  ∀ q, a ≤ q → q < b → validZ s q → 0 < c → ∀ pr ∈ prs, occursAt s pr.1 q = false

theorem refScan_end (s : JStr) (prs : List (List UInt8 × List UInt8)) (f : Nat) (p : Int)
    (c : Nat) (h : (s.bytes.length : Int) < p) : refScan s prs f p c = ([], 0) := by
  cases f <;> simp [refScan, h]

theorem refScan_miss (s : JStr) (prs : List (List UInt8 × List UInt8)) (f : Nat) (p : Int)
    (c : Nat) (hp : p ≤ s.bytes.length)
    (hn : 0 < c → validZ s p → prs.find? (fun pr => occursAt s pr.1 p) = none) :
    refScan s prs (f + 1) p c =
      (s.bytes.getD (p - 1).toNat 0 :: (refScan s prs f (p + 1) c).1,
        (refScan s prs f (p + 1) c).2) := by
  have hpL : ¬ (s.bytes.length : Int) < p := by omega
  have hhit : (if 0 < c ∧ validZ s p then prs.find? (fun pr => occursAt s pr.1 p) else none)
      = none := by
    split
    · rename_i h; exact hn h.1 h.2
    · rfl
  simp only [refScan, hpL, ↓reduceIte, hhit]

theorem refScan_hit (s : JStr) (prs : List (List UInt8 × List UInt8)) (f : Nat) (j : Int)
    (c : Nat) (t r : List UInt8) (hj : j ≤ s.bytes.length) (hc : 0 < c) (hv : validZ s j)
    (hfind : prs.find? (fun pr => occursAt s pr.1 j) = some (t, r)) :
    refScan s prs (f + 1) j c =
      (r ++ (refScan s prs f (j + t.length) (c - 1)).1,
        (refScan s prs f (j + t.length) (c - 1)).2 + 1) := by
  have hjL : ¬ (s.bytes.length : Int) < j := by omega
  have hhit : (if 0 < c ∧ validZ s j then prs.find? (fun pr => occursAt s pr.1 j) else none)
      = some (t, r) := by
    rw [if_pos ⟨hc, hv⟩, hfind]
  simp only [refScan, hjL, ↓reduceIte, hhit]

theorem refScan_skip (s : JStr) (prs : List (List UInt8 × List UInt8)) (c : Nat) (j : Int)
    (hj : j ≤ s.bytes.length + 1) :
    ∀ (n f : Nat) (p : Int), 1 ≤ p → j - p = n → n ≤ f → NoHit s prs c p j →
      refScan s prs f p c =
        ((s.bytes.drop (p - 1).toNat).take n ++ (refScan s prs (f - n) j c).1,
          (refScan s prs (f - n) j c).2)
  | 0, f, p, _, hn, _, _ => by
    have : p = j := by omega
    subst this
    simp
  | n + 1, f, p, hp, hn, hf, hnh => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have ih := refScan_skip s prs c j hj n f' (p + 1) (by omega) (by omega) (by omega)
      (fun q h1 h2 => hnh q (by omega) h2)
    have hlt : (p - 1).toNat < s.bytes.length := by omega
    have hdrop : s.bytes.drop (p - 1).toNat =
        s.bytes.getD (p - 1).toNat 0 :: s.bytes.drop (p + 1 - 1).toNat := by
      rw [List.drop_eq_getElem_cons hlt]
      have : (p + 1 - 1).toNat = (p - 1).toNat + 1 := by omega
      rw [this, getD_lt _ _ _ hlt]
    rw [refScan_miss s prs f' p c (by omega) (fun hc hv => by
      rw [List.find?_eq_none]
      intro pr hpr
      simp [hnh p (Int.le_refl _) (by omega) hv hc pr hpr])]
    rw [ih, hdrop]
    simp

theorem refScan_copyAll (s : JStr) (prs : List (List UInt8 × List UInt8)) (c f : Nat) (p : Int)
    (hp1 : 1 ≤ p) (hp2 : p ≤ s.bytes.length + 1) (hf : (s.bytes.length : Int) + 1 - p ≤ f)
    (hnh : NoHit s prs c p (s.bytes.length + 1)) :
    refScan s prs f p c = (s.bytes.drop (p - 1).toNat, 0) := by
  have h := refScan_skip s prs c _ (Int.le_refl _) (s.bytes.length + 1 - p).toNat f p hp1
    (by omega) (by omega) hnh
  rw [refScan_end s prs (f - (s.bytes.length + 1 - p).toNat) (s.bytes.length + 1) c
    (by omega)] at h
  rw [h, List.take_of_length_le (by rw [List.length_drop]; omega)]
  simp

theorem refScan_count_zero (s : JStr) (prs : List (List UInt8 × List UInt8)) :
    ∀ (f : Nat) (p : Int), (refScan s prs f p 0).2 = 0
  | 0, _ => rfl
  | f + 1, p => by
    by_cases hL : (s.bytes.length : Int) < p
    · rw [refScan_end s prs _ _ _ hL]
    · rw [refScan_miss s prs f p 0 (by omega) (fun h => absurd h (by omega))]
      exact refScan_count_zero s prs f (p + 1)

theorem refScan_min (s : JStr) (prs : List (List UInt8 × List UInt8)) :
    ∀ (f : Nat) (p : Int) (c c' : Nat), c ≤ c' →
      (refScan s prs f p c).2 = min c (refScan s prs f p c').2
  | 0, _, _, _, _ => by simp [refScan]
  | f + 1, p, c, c', hcc => by
    by_cases hL : (s.bytes.length : Int) < p
    · rw [refScan_end s prs _ _ _ hL, refScan_end s prs _ _ _ hL]; simp
    by_cases hc : c = 0
    · subst hc; rw [refScan_count_zero]; simp
    by_cases hm : validZ s p ∧ ∃ tr, prs.find? (fun pr => occursAt s pr.1 p) = some tr
    · obtain ⟨hv, ⟨t, r⟩, hf⟩ := hm
      rw [refScan_hit s prs f p c t r (by omega) (by omega) hv hf,
        refScan_hit s prs f p c' t r (by omega) (by omega) hv hf]
      simp only
      rw [refScan_min s prs f (p + t.length) (c - 1) (c' - 1) (by omega)]
      omega
    · have hn : ∀ d, 0 < d → validZ s p → prs.find? (fun pr => occursAt s pr.1 p) = none := by
        intro d _ hv
        cases h : prs.find? (fun pr => occursAt s pr.1 p) with
        | none => rfl
        | some tr => exact absurd ⟨hv, tr, h⟩ hm
      rw [refScan_miss s prs f p c (by omega) (hn c), refScan_miss s prs f p c' (by omega) (hn c')]
      exact refScan_min s prs f (p + 1) c c' hcc

/-! ## One iteration of the loop -/

theorem replaceOnce_none (s : JStr) (ps : List Pair) (start e1 : JInt64) (rs : List Rng)
    (count n i : JInt64) (io : List UInt8) (nrep : Nat) (x : Nat) (r : Rng)
    (hx : argmin (rs.map (·.1)) = x) (hr : rs.getD x (ix 0, ix 0) = r)
    (hA : e1.val < r.1.val) :
    replaceOnce s ps start e1 rs count n i io nrep = .ok (rs, r, i, io, nrep) := by
  simp only [replaceOnce, hx, hr, gt_iff_lt, hA, ↓reduceIte]

theorem replaceOnce_match (s : JStr) (ps : List Pair) (start e1 : JInt64) (rs : List Rng)
    (count n i : JInt64) (io : List UInt8) (nrep : Nat) (x : Nat) (r : Rng) (q : JInt64)
    (hx : argmin (rs.map (·.1)) = x) (hr : rs.getD x (ix 0, ix 0) = r)
    (hi1 : 1 ≤ i.val) (hij : i.val ≤ r.1.val) (hjl : r.1.val ≤ r.2.val)
    (hje : r.1.val ≤ e1.val) (hjL : r.1.val ≤ s.bytes.length + 1)
    (hq : nextind s r.2 = .ok q) :
    replaceOnce s ps start e1 rs count n i io nrep =
      if n.val = count.val then
        .ok (rs, r, q, io ++ (s.bytes.drop (i.val - 1).toNat).take (r.1.val - i.val).toNat ++
          (ps.getD x default).repl, nrep + 1)
      else
        match refresh e1 q ps rs with
        | .error e => .error e
        | .ok rs' => .ok (rs', r, q, io ++ (s.bytes.drop (i.val - 1).toNat).take
            (r.1.val - i.val).toNat ++ (ps.getD x default).repl, nrep + 1) := by
  have h1 : ¬ e1.val < r.1.val := by omega
  have h2 : i.val = start.val ∨ i.val ≤ r.2.val := Or.inr (by omega)
  have h3 : ¬ r.2.val < r.1.val := by omega
  simp only [replaceOnce, hx, hr, gt_iff_lt, h1, h2, h3, ↓reduceIte,
    copyOut_ok s i r.1 hi1 hij hjL, hq]
  by_cases hnc : n.val = count.val
  · simp only [hnc, ↓reduceIte]
  · simp only [hnc, ↓reduceIte]
    cases refresh e1 q ps rs <;> rfl

theorem finishLoop_stop (s : JStr) (ps : List Pair) (count start e1 : JInt64) (f : Nat)
    (rs : List Rng) (n i : JInt64) (io : List UInt8) (nrep : Nat) (rs' : List Rng) (r : Rng)
    (i' : JInt64) (io' : List UInt8) (nrep' : Nat) (hle : n.val ≤ count.val)
    (hro : replaceOnce s ps start e1 rs count n i io nrep = .ok (rs', r, i', io', nrep'))
    (hr : e1.val ≤ r.1.val) :
    finishLoop s ps count start e1 (f + 1) rs n i io nrep = .ok (i', io', nrep') := by
  simp only [finishLoop, hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hro,
    ge_iff_le, hr]

theorem finishLoop_step (s : JStr) (ps : List Pair) (count start e1 : JInt64) (f : Nat)
    (rs : List Rng) (n i : JInt64) (io : List UInt8) (nrep : Nat) (rs' : List Rng) (r : Rng)
    (i' : JInt64) (io' : List UInt8) (nrep' : Nat) (hle : n.val ≤ count.val)
    (hro : replaceOnce s ps start e1 rs count n i io nrep = .ok (rs', r, i', io', nrep'))
    (hr : r.1.val < e1.val) :
    finishLoop s ps count start e1 (f + 1) rs n i io nrep =
      finishLoop s ps count start e1 f rs' (n + ix 1) i' io' nrep' := by
  have : ¬ e1.val ≤ r.1.val := by omega
  simp only [finishLoop, hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hro,
    ge_iff_le, this]

/-! ## The loop follows the reference scan -/

theorem loop_ref (s : JStr) (qs : List (List UInt8 × Pair)) (hcon : Contract s qs)
    (count e1 : JInt64) (he1 : e1.val = s.bytes.length + 1) (hcmax : count.val ≤ 2 ^ 63 - 1) :
    ∀ (c : Nat) (rs : List Rng) (n i : JInt64) (io : List UInt8) (nrep F : Nat),
      1 ≤ n.val → n.val + c = count.val + 1 →
      1 ≤ i.val → i.val ≤ s.bytes.length + 1 → (i.val ≤ s.bytes.length → validZ s i.val) →
      (0 < c → AllOk s qs i.val rs ∧ 0 < rs.length) →
      (s.bytes.length : Int) + 2 - i.val ≤ F →
      ∃ i' io' nrep',
        finishLoop s (qs.map (·.2)) count (ix 1) e1 c rs n i io nrep = .ok (i', io', nrep') ∧
        1 ≤ i'.val ∧ i'.val ≤ s.bytes.length + 1 ∧ (i'.val ≤ s.bytes.length → validZ s i'.val) ∧
        io' ++ s.bytes.drop (i'.val - 1).toNat =
          io ++ (refScan s (qs.map fun q => (q.1, q.2.repl)) F i.val c).1 ∧
        nrep' = nrep + (refScan s (qs.map fun q => (q.1, q.2.repl)) F i.val c).2
  | 0, rs, n, i, io, nrep, F, _, _, hi1, hi2, hiv, _, hF => by
    have h := refScan_copyAll s (qs.map fun q => (q.1, q.2.repl)) 0 F i.val hi1 hi2 (by omega)
      (fun _ _ _ _ h => absurd h (by omega))
    refine ⟨i, io, nrep, rfl, hi1, hi2, hiv, ?_, ?_⟩
    · simp [h]
    · simp [h]
  | f + 1, rs, n, i, io, nrep, F, hn1, hnc, hi1, hi2, hiv, hinv, hF => by
    have hs := ncu_small s
    obtain ⟨⟨hlen, hall⟩, hpos⟩ := hinv (by omega)
    have hle : n.val ≤ count.val := by omega
    have hspec : ∀ q ∈ qs, FinderSpec s q.1 q.2.find := fun q h => (hcon q h).2
    obtain ⟨hxlt, hxmin, hxfirst⟩ := argmin_spec (rs.map (·.1)) (ix 0) (by simp; omega)
    generalize hx : argmin (rs.map (·.1)) = x at hxlt hxmin hxfirst
    have hxr : x < rs.length := by simpa using hxlt
    have hxq : x < qs.length := by omega
    have hgetD : ∀ y (hy : y < rs.length), (rs.map (·.1)).getD y (ix 0) = rs[y].1 := by
      intro y hy
      rw [getD_lt _ _ _ (by simpa using hy)]
      simp
    have hmin : ∀ y (hy : y < rs.length), rs[x].1.val ≤ rs[y].1.val := by
      intro y hy
      have := hxmin y (by simpa using hy)
      rwa [hgetD x hxr, hgetD y hy] at this
    have hfirst : ∀ y (hy : y < x), rs[x].1.val < (rs[y]'(by omega)).1.val := by
      intro y hy
      have := hxfirst y hy
      rwa [hgetD x hxr, hgetD y (by omega)] at this
    have hr : rs.getD x (ix 0, ix 0) = rs[x] := getD_lt _ _ _ hxr
    have hokx : RngOk s qs[x].1 i.val rs[x] := hall x hxr hxq
    have hnohit : ∀ b : Int, b ≤ rs[x].1.val →
        NoHit s (qs.map fun q => (q.1, q.2.repl)) (f + 1) i.val b := by
      intro b hb p hp1 hp2 hpv _ pr hpr
      obtain ⟨y, hy, rfl⟩ := List.mem_iff_getElem.mp hpr
      have hy' : y < qs.length := by simpa using hy
      rw [List.getElem_map]
      exact rngOk_no_before (hall y (by omega) hy') p hp1
        (by have := hmin y (by omega); omega) hpv
    by_cases hA : e1.val < rs[x].1.val
    · have hro := replaceOnce_none s (qs.map (·.2)) (ix 1) e1 rs count n i io nrep x rs[x] hx hr hA
      have h := refScan_copyAll s (qs.map fun q => (q.1, q.2.repl)) (f + 1) F i.val hi1 hi2
        (by omega) (hnohit _ (by omega))
      refine ⟨i, io, nrep, finishLoop_stop s _ count (ix 1) e1 f rs n i io nrep rs rs[x] i io nrep
        hle hro (by omega), hi1, hi2, hiv, ?_, ?_⟩
      · simp [h]
      · simp [h]
    · have hm : MatchOk s qs[x].1 i.val rs[x].1 rs[x].2 := rngOk_match hokx (by omega)
      obtain ⟨⟨hij, hjv, hjocc, _⟩, hjl, q, hq, hqv⟩ := hm
      have hjL : rs[x].1.val ≤ s.bytes.length := hjv.2.1
      have htne : qs[x].1 ≠ [] := (hcon qs[x] (List.getElem_mem _)).1
      have htlen : 1 ≤ qs[x].1.length := by
        cases h : qs[x].1 with
        | nil => exact absurd h htne
        | cons _ _ => simp
      obtain ⟨hlL, hq1, hq2, _, hq4⟩ := nextind_ok s rs[x].2 q (by omega) hq
      have hro := replaceOnce_match s (qs.map (·.2)) (ix 1) e1 rs count n i io nrep x rs[x] q
        hx hr hi1 hij hjl (by omega) (by omega) hq
      have hps : (qs.map (·.2)).getD x default = qs[x].2 := by
        rw [getD_lt _ _ _ (by simpa using hxq)]
        simp
      rw [hps] at hro
      have hfind : (qs.map fun q => (q.1, q.2.repl)).find? (fun pr => occursAt s pr.1 rs[x].1.val)
          = some (qs[x].1, qs[x].2.repl) := by
        have := find?_first (fun pr : List UInt8 × List UInt8 => occursAt s pr.1 rs[x].1.val)
          (qs.map fun q => (q.1, q.2.repl)) x (by simpa using hxq)
          (by rw [List.getElem_map]; exact hjocc)
          (fun y hy => by
            rw [List.getElem_map]
            exact rngOk_no_before (hall y (by omega) (by omega)) _ hij (hfirst y hy) hjv)
        rw [List.getElem_map] at this
        exact this
      have hskip := refScan_skip s (qs.map fun q => (q.1, q.2.repl)) (f + 1) rs[x].1.val
        (by omega) (rs[x].1.val - i.val).toNat F i.val hi1 (by omega) (by omega)
        (hnohit _ (Int.le_refl _))
      obtain ⟨F1, hF1⟩ : ∃ F1, F - (rs[x].1.val - i.val).toNat = F1 + 1 :=
        ⟨F - (rs[x].1.val - i.val).toNat - 1, by omega⟩
      rw [hF1, refScan_hit s _ F1 rs[x].1.val (f + 1) qs[x].1 qs[x].2.repl hjL (by omega) hjv
        hfind] at hskip
      have hjq : rs[x].1.val + (qs[x].1.length : Int) = q.val := by omega
      rw [hjq, Nat.add_sub_cancel] at hskip
      rw [hskip]
      by_cases hnc' : n.val = count.val
      · have hf0 : f = 0 := by omega
        subst hf0
        simp only [hnc', ↓reduceIte] at hro
        have h := refScan_copyAll s (qs.map fun q => (q.1, q.2.repl)) 0 F1 q.val (by omega) hq2
          (by omega) (fun _ _ _ _ h => absurd h (by omega))
        refine ⟨q, io ++ (s.bytes.drop (i.val - 1).toNat).take (rs[x].1.val - i.val).toNat ++
          qs[x].2.repl, nrep + 1, ?_, by omega, hq2, hq4, ?_, ?_⟩
        · rw [finishLoop_step s _ count (ix 1) e1 0 rs n i io nrep _ _ _ _ _ hle hro (by omega)]
          rfl
        · simp [h, List.append_assoc]
        · simp [h]
      · obtain ⟨rs', hrs', hok'⟩ := refresh_ok s e1 q he1 (by omega) hq2 i.val (by omega) qs rs
          hspec ⟨hlen, hall⟩
        simp only [hnc', ↓reduceIte, hrs'] at hro
        have hn' : (n + ix 1).val = n.val + 1 :=
          add_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega)
        obtain ⟨i', io', nrep', hloop, h1, h2, h3, h4, h5⟩ :=
          loop_ref s qs hcon count e1 he1 hcmax f rs' (n + ix 1) q _ (nrep + 1) F1 (by omega)
            (by omega) (by omega) hq2 hq4 (fun _ => ⟨hok', by rw [hok'.1]; omega⟩) (by omega)
        refine ⟨i', io', nrep', ?_, h1, h2, h3, ?_, ?_⟩
        · rw [finishLoop_step s _ count (ix 1) e1 f rs n i io nrep _ _ _ _ _ hle hro (by omega)]
          exact hloop
        · rw [h4]; simp [List.append_assoc]
        · rw [h5]; omega

/-! ## The whole function -/

theorem count_max (count : JInt64) : count.val ≤ 2 ^ 63 - 1 := by
  have := count.property.2
  simpa [IntTy.max, IntTy.signed, IntTy.bits] using this

theorem replaceInit_ok (s : JStr) (ps : List Pair) (count e1 : JInt64) (rs : List Rng)
    (h0 : 0 ≤ count.val) (he : nextind s (lastindex s) = .ok e1)
    (hrs : findAll e1 (ix 1) ps = .ok rs) :
    replaceInit s ps count = .ok (e1, rs, rs.all fun r => decide (r.1.val > e1.val)) := by
  unfold replaceInit
  generalize lastindex s = li at he ⊢
  rw [if_neg (by omega), he]
  simp only [firstindex, hrs]

theorem writeRest_ok (s : JStr) (i li : JInt64) (io : List UInt8) (nrep : Nat) (sub : JSub)
    (hsub : substring s i li = .ok sub) :
    writeRest s i li io nrep = .ok (io ++ sub.view.bytes, nrep) := by
  simp only [writeRest, hsub]

theorem replaceFinish_ok (s : JStr) (ps : List Pair) (count e1 : JInt64) (rs : List Rng)
    (i' : JInt64) (io' : List UInt8) (nrep' : Nat)
    (hloop : finishLoop s ps count (ix 1) e1 count.val.toNat rs (ix 1) (ix 1) [] 0 =
      .ok (i', io', nrep'))
    (h1 : 1 ≤ i'.val) (h2 : i'.val ≤ s.bytes.length + 1)
    (h3 : i'.val ≤ s.bytes.length → validZ s i'.val) :
    replaceFinish s ps count e1 rs = .ok (io' ++ s.bytes.drop (i'.val - 1).toNat, nrep') := by
  obtain ⟨sub, hsub, hview⟩ := subFrom s (lastindex s) (lastindex_spec s) i' h1 h2 h3
  have hw := writeRest_ok s i' (lastindex s) io' nrep' sub hsub
  rw [hview] at hw
  unfold replaceFinish
  simp only [firstindex, hloop]
  exact hw

/-- No pattern occurs anywhere when every first search found nothing. -/
theorem notfound_nohit (s : JStr) (qs : List (List UInt8 × Pair)) (e1 : JInt64)
    (he1 : e1.val = s.bytes.length + 1) (rs : List Rng) (c : Nat)
    (hok : AllOk s qs (ix 1).val rs)
    (hnf : (rs.all fun r => decide (r.1.val > e1.val)) = true) :
    NoHit s (qs.map fun q => (q.1, q.2.repl)) c 1 (s.bytes.length + 1) := by
  intro p hp1 _ hpv _ pr hpr
  obtain ⟨y, hy, rfl⟩ := List.mem_iff_getElem.mp hpr
  have hy' : y < qs.length := by simpa using hy
  have hyr : y < rs.length := by rw [hok.1]; exact hy'
  have hbig : e1.val < rs[y].1.val := by
    have := List.all_eq_true.mp hnf rs[y] (List.getElem_mem _)
    simpa using this
  have hno := rngOk_big (hok.2 y hyr hy') (by omega)
  rw [List.getElem_map]
  exact hno p (by rw [ix1]; exact hp1) hpv

theorem replaceN_ref (s : JStr) (qs : List (List UInt8 × Pair)) (count : JInt64)
    (h0 : 0 ≤ count.val) (hcon : Contract s qs) :
    replaceN s (qs.map (·.2)) count =
      .ok (refReplace s (qs.map fun q => (q.1, q.2.repl)) count.val.toNat) := by
  have hs := ncu_small s
  have hcmax := count_max count
  have hspec : ∀ q ∈ qs, FinderSpec s q.1 q.2.find := fun q h => (hcon q h).2
  unfold replaceN refReplace
  by_cases hc0 : count.val = 0
  · rw [if_pos hc0, refScan_copyAll s _ count.val.toNat (s.bytes.length + 1) 1 (Int.le_refl _)
      (by omega) (by omega)
      (fun _ _ _ _ h => absurd h (by omega))]
    simp
  · rw [if_neg hc0]
    obtain ⟨e1, he, he1⟩ := e1_spec s (lastindex s) (lastindex_spec s)
    obtain ⟨rs, hrs, hok⟩ := findAll_ok s e1 (ix 1) he1 (by simp) (by simp; omega) qs hspec
    rw [replaceInit_ok s _ count e1 rs h0 he hrs]
    simp only
    by_cases hnf : (rs.all fun r => decide (r.1.val > e1.val)) = true
    · rw [if_pos hnf]
      rw [refScan_copyAll s _ count.val.toNat (s.bytes.length + 1) 1 (Int.le_refl _) (by omega)
        (by omega) (notfound_nohit s qs e1 he1 rs _ hok hnf)]
      simp
    · rw [if_neg hnf]
      have hpos : 0 < rs.length := by
        cases rs with
        | nil => simp at hnf
        | cons _ _ => simp
      have hv1 : (ix 1).val ≤ s.bytes.length → validZ s (ix 1).val := by
        intro h; rw [ix1] at h ⊢; exact valid_one s (by omega)
      obtain ⟨i', io', nrep', hloop, h1, h2, h3, h4, h5⟩ :=
        loop_ref s qs hcon count e1 he1 hcmax count.val.toNat rs (ix 1) (ix 1) [] 0
          (s.bytes.length + 1) (by simp) (by simp; omega) (by simp) (by simp; omega) hv1
          (fun _ => ⟨hok, hpos⟩) (by simp; omega)
      rw [replaceFinish_ok s _ count e1 rs i' io' nrep' hloop h1 h2 h3]
      simp only [ix1] at h4 h5
      rw [h4, h5]
      simp

/-! ## The properties -/

theorem replaceMatchesReference : ReplaceMatchesReference := by
  intro s qs count h0 hcon
  unfold replace
  rw [replaceN_ref s qs count h0 hcon]

theorem replaceCountMin : ReplaceCountMin := by
  intro s qs count h0 hcon
  have hcmax := count_max count
  have ht : typemaxInt.val = 2 ^ 63 - 1 := ix_val _ (by omega) (by omega)
  have htn : typemaxInt.val.toNat = 2 ^ 63 - 1 := by rw [ht]; rfl
  have h1 := replaceN_ref s qs count h0 hcon
  have h2 := replaceN_ref s qs typemaxInt (by omega) hcon
  rw [htn] at h2
  exact ⟨(refReplace s (qs.map fun q => (q.1, q.2.repl)) count.val.toNat).1,
    (refReplace s (qs.map fun q => (q.1, q.2.repl)) count.val.toNat).2,
    (refReplace s (qs.map fun q => (q.1, q.2.repl)) (2 ^ 63 - 1)).1,
    (refReplace s (qs.map fun q => (q.1, q.2.repl)) (2 ^ 63 - 1)).2, h1, h2, rfl,
    refScan_min s _ (s.bytes.length + 1) 1 count.val.toNat (2 ^ 63 - 1) (by omega)⟩

end JuliaLean.StringUtil
