import JuliaLean.StringUtil.Width
import JuliaLean.StringUtil.Split
import JuliaLean.StringUtil.Decode

/-!
# `rtruncate`, `ltruncate`, `ctruncate`, `base/strings/util.jl:586-735`

Master `bbfa0ce4150`, for `str::String`, a `String` replacement (a `Char`
replacement `c` behaves as `string(c)`) and `maxwidth::Int`. Column widths use
`textwidth` from `Width.lean`, parametrised by the utf8proc width `cw`.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings JuliaLean.Registry

inductive TMode where
  | left | right | center
  deriving DecidableEq, Repr

/-- `textwidth(str[i])` (`@inbounds getindex`, `base/strings/string.jl:540-545`). -/
def twAt (cw : UInt32 → Int) (s : JStr) (i : JInt64) : SJl JInt64 :=
  (getindex s i).map fun c => ix (textwidthChar cw c)

/-- The `while true` loop of `string_truncate_boundaries`,
`base/strings/util.jl:710-733`. Each pass moves `left` or `right` by one
character or breaks, except a pass that only sets `force_other`, which is
followed by a moving pass; and the loop breaks before consuming every
character because `textwidth(str) > maxwidth`. So `2 * ncodeunits(str) + 4`
passes are never exhausted. -/
def truncLoop (cw : UInt32 → Int) (s : JStr) (maxw : JInt64) (mode : TMode) (preferLeft : Bool) :
    Nat → JInt64 → JInt64 → JInt64 → JInt64 → JInt64 → Bool → SJl (JInt64 × JInt64)
  | 0, left, right, _, _, _, _ => .ok (left, right)
  | fuel + 1, left, right, width, rmL, rmR, force =>
    let blk1 : SJl (Option (JInt64 × JInt64 × JInt64 × Bool)) :=
      if decide (mode = .left) || (decide (mode = .center) && (!preferLeft || decide (left.val > 1))) then
        match twAt cw s right with
        | .error e => .error e
        | .ok rm =>
          if decide (mode = .left) || (decide (rmR.val ≤ rmL.val) || force) then
            if !decide ((width + rm).val ≤ maxw.val) then .ok none
            else (prevind s right).map fun r => some (r, width + rm, rmR + rm, false)
          else .ok (some (right, width, rmR, true))
      else .ok (some (right, width, rmR, force))
    match blk1 with
    | .error e => .error e
    | .ok none => .ok (left, right)
    | .ok (some (right, width, rmR, force)) =>
      if decide (mode = .right) || decide (mode = .center) then
        match twAt cw s left with
        | .error e => .error e
        | .ok rm =>
          if decide (mode = .left) || (decide (rmL.val ≤ rmR.val) || force) then
            match twAt cw s left with
            | .error e => .error e
            | .ok rm2 =>
              if !decide ((width + rm2).val ≤ maxw.val) then .ok (left, right)
              else
                match nextind s left with
                | .error e => .error e
                | .ok l => truncLoop cw s maxw mode preferLeft fuel l right (width + rm2) (rmL + rm) rmR false
          else truncLoop cw s maxw mode preferLeft fuel left right width rmL rmR true
      else truncLoop cw s maxw mode preferLeft fuel left right width rmL rmR force

/-- The loop of `check_textwidth(str, maxwidth)`, `base/strings/util.jl:687-695`. -/
def checkLoop (cw : UInt32 → Int) (maxw : JInt64) : List UInt32 → JInt64 → Bool
  | [], _ => true
  | c :: cs, tot =>
    if (tot + ix (textwidthChar cw c)).val > maxw.val then false
    else checkLoop cw maxw cs (tot + ix (textwidthChar cw c))

/-- `check_textwidth(str, maxwidth)`: `for c in str` iterates `chars str`. -/
def checkTextwidth (cw : UInt32 → Int) (s : JStr) (maxw : JInt64) : Bool :=
  checkLoop cw maxw (chars s) (ix 0)

/-- `string_truncate_boundaries(str, maxwidth, replacement, Val(mode), prefer_left)`,
`base/strings/util.jl:697-735`. -/
def truncBoundaries (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) (mode : TMode)
    (preferLeft : Bool) : SJl (Option (JInt64 × JInt64)) :=
  if maxw.val < 0 then .error (.jl (.argumentError s!"maxwidth {maxw.val} should be non-negative"))
  else if checkTextwidth cw s maxw then .ok none
  else
    match truncLoop cw s maxw mode preferLeft (2 * s.bytes.length + 4) (ix 1) (lastIdx s)
        (ix (textwidth cw r)) (ix 0) (ix 0) false with
    | .error e => .error e
    | .ok (left, right) =>
      match prevind s left with
      | .error e => .error e
      | .ok pl => (nextind s right).map fun nr => some (pl, nr)

/-- `a * b * ...` on Strings and SubStrings: `string(...)` stores the code units
of each argument in a fresh String (`base/strings/substring.jl:256-283`). -/
def concatStr (parts : List (List UInt8)) : SJl JStr :=
  stringN (parts.map List.length).sum fun _ => parts.flatten

/-- `rtruncate(str, maxwidth, replacement)`, `base/strings/util.jl:609-617`:
`str[begin:left] * replacement` under `@views`, i.e. the checked
`SubString(str, 1, left)`. -/
def rtruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) : SJl JStr :=
  match truncBoundaries cw s r maxw .right true with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (left, _)) =>
    match substring s (ix 1) left with
    | .error e => .error e
    | .ok sub => concatStr [sub.view.bytes, r.bytes]

/-- `ltruncate(str, maxwidth, replacement)`, `base/strings/util.jl:642-650`. -/
def ltruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) : SJl JStr :=
  match truncBoundaries cw s r maxw .left true with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (_, right)) =>
    match substring s right (lastIdx s) with
    | .error e => .error e
    | .ok sub => concatStr [r.bytes, sub.view.bytes]

/-- `ctruncate(str, maxwidth, replacement; prefer_left)`, `base/strings/util.jl:676-684`. -/
def ctruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) (preferLeft : Bool := true) : SJl JStr :=
  match truncBoundaries cw s r maxw .center preferLeft with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (left, right)) =>
    match substring s (ix 1) left with
    | .error e => .error e
    | .ok subL =>
      match substring s right (lastIdx s) with
      | .error e => .error e
      | .ok subR => concatStr [subL.view.bytes, r.bytes, subR.view.bytes]

/-! ## Width sums -/

/-- `mapreduce(textwidth, +, cs; init=0)` over a character list. -/
def twList (cw : UInt32 → Int) (cs : List UInt32) : Int :=
  cs.foldl (fun acc c => acc + textwidthChar cw c) 0

theorem textwidth_eq (cw : UInt32 → Int) (s : JStr) : textwidth cw s = twList cw (decAll s.bytes) := by
  rw [← chars_eq_decAll]; rfl

theorem twList_acc (cw : UInt32 → Int) :
    ∀ (cs : List UInt32) (a : Int), cs.foldl (fun acc c => acc + textwidthChar cw c) a = a + twList cw cs := by
  intro cs
  induction cs with
  | nil => intro a; simp [twList]
  | cons c cs ih =>
    intro a
    simp only [twList, List.foldl_cons]
    rw [ih, ih (0 + textwidthChar cw c)]
    omega

theorem twList_nil (cw : UInt32 → Int) : twList cw [] = 0 := rfl

theorem twList_cons (cw : UInt32 → Int) (c : UInt32) (cs : List UInt32) :
    twList cw (c :: cs) = textwidthChar cw c + twList cw cs := by
  show List.foldl _ (0 + textwidthChar cw c) cs = _
  rw [twList_acc]; omega

theorem twList_append (cw : UInt32 → Int) (xs ys : List UInt32) :
    twList cw (xs ++ ys) = twList cw xs + twList cw ys := by
  unfold twList
  rw [List.foldl_append, twList_acc]
  rfl

theorem twChar_bounds (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (c : UInt32) :
    0 ≤ textwidthChar cw c ∧ textwidthChar cw c ≤ 2 := by
  unfold textwidthChar
  dsimp only
  split
  · split <;> omega
  · split
    · omega
    · split
      · exact hcw _
      · omega

theorem twList_bounds (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) :
    ∀ cs : List UInt32, 0 ≤ twList cw cs ∧ twList cw cs ≤ 2 * cs.length := by
  intro cs
  induction cs with
  | nil => simp [twList_nil]
  | cons c cs ih =>
    rw [twList_cons, List.length_cons]
    have := twChar_bounds cw hcw c
    omega

theorem check_spec (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (maxw : JInt64) :
    ∀ (cs : List UInt32) (tot : JInt64), 0 ≤ tot.val → tot.val ≤ maxw.val →
      tot.val + 2 * cs.length < 2 ^ 63 →
      (checkLoop cw maxw cs tot = true ↔ tot.val + twList cw cs ≤ maxw.val) := by
  intro cs
  induction cs with
  | nil => intro tot _ h _; simp [checkLoop, twList_nil]; omega
  | cons c cs ih =>
    intro tot h0 h1 h2
    have hb := twChar_bounds cw hcw c
    have hl := twList_bounds cw hcw cs
    simp only [List.length_cons] at h2
    have hv : (tot + ix (textwidthChar cw c)).val = tot.val + textwidthChar cw c := by
      rw [add_val _ _ (by rw [ix_val _ (by omega) (by omega)]; omega)
        (by rw [ix_val _ (by omega) (by omega)]; omega), ix_val _ (by omega) (by omega)]
    simp only [checkLoop, hv, twList_cons]
    split
    · simp only [Bool.false_eq_true, false_iff]; omega
    · rw [ih _ (by omega) (by omega) (by omega)]; omega

theorem check_iff (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (s : JStr) (w : JInt64)
    (hw : 0 ≤ w.val) : checkTextwidth cw s w = true ↔ twList cw (decAll s.bytes) ≤ w.val := by
  have hsm := ncu_small s
  have hSl := decAll_length _ s.bytes (Nat.le_refl _)
  unfold checkTextwidth
  rw [check_spec cw hcw w _ _ (Int.le_of_eq ix0.symm) (by rw [ix0]; exact hw)
    (by rw [ix0, chars_eq_decAll]; omega), ix0, chars_eq_decAll, Int.zero_add]

/-! ## Refuted: the result is at most `maxwidth` columns wide -/

/-- `rtruncate(s, w, r)` has `textwidth` at most `w` for every `w ≥ 0`
(docstring, `base/strings/util.jl:589-590`), for every utf8proc width table. -/
def TruncateWidth : Prop :=
  ∀ (cw : UInt32 → Int), (∀ u, 0 ≤ cw u ∧ cw u ≤ 2) →
    ∀ (s r out : JStr) (w : JInt64), 0 ≤ w.val → rtruncate cw s r w = .ok out → textwidth cw out ≤ w.val

/-- `"abcdef"` and `"..."`. -/
def truncAbcdef : JStr := ⟨[0x61, 0x62, 0x63, 0x64, 0x65, 0x66], by decide⟩
def strDots : JStr := ⟨[0x2e, 0x2e, 0x2e], by decide⟩

theorem truncateWidth_refuted : ¬ TruncateWidth := by
  intro h
  have e : rtruncate (fun _ => 1) truncAbcdef strDots (ix 2) = .ok strDots := of_okSat_eq _ _ (by decide)
  have := h (fun _ => 1) (fun _ => ⟨by simp, by simp⟩) truncAbcdef strDots strDots (ix 2) (by decide) e
  revert this; decide

/-! ## Proven: the bound holds when the replacement fits -/

theorem take_full (s : JStr) : s.bytes.take s.bytes.length = s.bytes := List.take_length

/-- The truncation loop in `:right` mode keeps `textwidth(replacement)` plus the
widths of the kept characters at most `maxwidth`. -/
theorem rloop (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (s : JStr) (maxw right : JInt64)
    (R : Int) (hR : 0 ≤ R) (hT : maxw.val < twList cw (decAll s.bytes)) :
    ∀ (fuel : Nat) (left width rmL : JInt64) (force : Bool),
      1 ≤ left.val → left.val ≤ s.bytes.length + 1 → Visits s.bytes (left.val - 1).toNat →
      width.val = R + twList cw (decAll (s.bytes.take (left.val - 1).toNat)) → width.val ≤ maxw.val →
      2 * ((s.bytes.length : Int) + 1 - left.val) + (if force then 1 else 2) ≤ fuel →
      ∃ left' : JInt64, truncLoop cw s maxw .right true fuel left right width rmL (ix 0) force = .ok (left', right) ∧
        1 ≤ left'.val ∧ left'.val ≤ s.bytes.length + 1 ∧ Visits s.bytes (left'.val - 1).toNat ∧
        R + twList cw (decAll (s.bytes.take (left'.val - 1).toNat)) ≤ maxw.val := by
  have hsm := ncu_small s
  have hTn : twList cw (decAll s.bytes) ≤ 2 * s.bytes.length := by
    have := (twList_bounds cw hcw (decAll s.bytes)).2
    have := decAll_length _ s.bytes (Nat.le_refl _)
    omega
  intro fuel
  induction fuel with
  | zero =>
    intro left width rmL force h1 h2 _ _ _ hf
    cases force <;> simp at hf <;> omega
  | succ fuel ih =>
    intro left width rmL force h1 h2 hV hw hwm hf
    have hln : left.val ≤ s.bytes.length := by
      refine Classical.byContradiction fun hc => ?_
      rw [show (left.val - 1).toNat = s.bytes.length by omega, take_full] at hw
      omega
    have hp : (left.val - 1).toNat < s.bytes.length := by omega
    have hv := visits_valid s hV hp
    have hv' : validZ s left.val := by rw [show left.val = (((left.val - 1).toNat : Nat) : Int) + 1 by omega]; exact hv
    obtain ⟨hgi, hnz⟩ := at_valid s left hv'
    have hne : s.bytes.drop (left.val - 1).toNat ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff]; omega
    have hk := dec_len _ hne
    simp only [List.length_drop] at hk
    have htw : twAt cw s left = .ok (ix (textwidthChar cw (dec (s.bytes.drop (left.val - 1).toNat)).1)) := by
      unfold twAt; rw [hgi]; rfl
    have hb := twChar_bounds cw hcw (dec (s.bytes.drop (left.val - 1).toNat)).1
    have hpre := (twList_bounds cw hcw (decAll (s.bytes.take (left.val - 1).toNat))).1
    have hwv : (width + ix (textwidthChar cw (dec (s.bytes.drop (left.val - 1).toNat)).1)).val =
        width.val + textwidthChar cw (dec (s.bytes.drop (left.val - 1).toNat)).1 := by
      rw [add_val _ _ (by rw [ix_val _ (by omega) (by omega)]; omega)
        (by rw [ix_val _ (by omega) (by omega)]; omega), ix_val _ (by omega) (by omega)]
    obtain ⟨tl, htl, htlv⟩ := nextind_mid s left h1 hln
    rw [hnz] at htlv
    simp only [truncLoop, reduceCtorEq, decide_false, decide_true, Bool.false_or, Bool.false_and,
      Bool.true_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, htw]
    by_cases hgo : (decide (rmL.val ≤ (ix 0).val) || force) = true
    · simp only [hgo, ↓reduceIte, hwv]
      by_cases hbr : width.val + textwidthChar cw (dec (s.bytes.drop (left.val - 1).toNat)).1 ≤ maxw.val
      · simp only [hbr, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, htl]
        have hstep := Visits.step hV hp
        have hext := visits_take_step _ _ hV hp
        have htl1 : (tl.val - 1).toNat = (left.val - 1).toNat + (dec (s.bytes.drop (left.val - 1).toNat)).2 := by
          omega
        refine ih tl _ _ false (by omega) (by omega) (by rw [htl1]; exact hstep) ?_ (by rw [hwv]; exact hbr)
          (by cases force <;> simp at hf ⊢ <;> omega)
        rw [hwv, htl1, hext, twList_append, twList_cons, twList_nil, hw]
        omega
      · simp only [hbr, decide_false, Bool.not_false, ↓reduceIte]
        exact ⟨left, rfl, h1, by omega, hV, by omega⟩
    · have hf' : force = false := by cases force <;> simp_all
      subst hf'
      simp only [hgo, Bool.false_eq_true, ↓reduceIte]
      exact ih left width rmL true h1 h2 hV hw hwm (by simp at hf ⊢; omega)

/-- `rtruncate(s, w, r)` has `textwidth` at most `w` when the replacement fits
(`textwidth(r) ≤ w`) and does not start with a UTF-8 continuation byte (true
for every valid replacement, including the default `'…'`), for every utf8proc
width table. -/
def TruncateWidthBound : Prop :=
  ∀ (cw : UInt32 → Int), (∀ u, 0 ≤ cw u ∧ cw u ≤ 2) →
    ∀ (s r out : JStr) (w : JInt64), textwidth cw r ≤ w.val →
      (∀ c t, r.bytes = c :: t → isCont c = false) →
      rtruncate cw s r w = .ok out → textwidth cw out ≤ w.val

/-- `prevind(s, left)` and `SubString(s, 1, prevind(s, left))` at a position the
truncation loop stops at. -/
theorem rtrunc_prefix (s : JStr) (left' : JInt64) (hn1 : 1 ≤ s.bytes.length) (hl1 : 1 ≤ left'.val)
    (hl2 : left'.val ≤ s.bytes.length + 1) (hV : Visits s.bytes (left'.val - 1).toNat) :
    ∃ pl sub, prevind s left' = .ok pl ∧ substring s (ix 1) pl = .ok sub ∧
      sub.view.bytes = s.bytes.take (left'.val - 1).toNat := by
  have hsm := ncu_small s
  obtain ⟨pl, hpl, hplc⟩ := previndN_one s left' hl1 hl2
  refine ⟨pl, ?_⟩
  rcases hplc with ⟨h1, h0⟩ | ⟨h2, hpv⟩
  · refine ⟨_, hpl, split_substring_empty s (ix 1) pl true (by rw [h0]; simp), ?_⟩
    rw [split_view_empty, h1]; rfl
  · have hvl : isvalidAt s left' = true ∨ left'.val = s.bytes.length + 1 := by
      by_cases hlt : (left'.val - 1).toNat < s.bytes.length
      · left; exact (isvalidAt_iff s left').2
          (by rw [show left'.val = (((left'.val - 1).toNat : Nat) : Int) + 1 by omega]; exact visits_valid s hV hlt)
      · right; omega
    obtain ⟨j, hj, hjn⟩ := nextindAfterPrevind_proven s left' h2 hvl
    have ej : j = pl := Except.ok.inj (hj.symm.trans hpl)
    rw [ej] at hjn
    obtain ⟨p1, p2, p3, _⟩ := hpv
    refine ⟨_, hpl, substring_checked s (ix 1) pl left' (by simp) (by rw [ix1]; exact p1) p3.2.1
      ((isvalidAt_iff s _).2 (by rw [ix1]; exact valid_one s hn1)) ((isvalidAt_iff s pl).2 p3) hjn, ?_⟩
    rw [view_bytes, sub_val (ix 1) (ix 1) (by simp) (by simp),
      sub_val left' (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega), ix1]
    simp

theorem rtrunc_fits (cw : UInt32 → Int) (s r : JStr) (w : JInt64) (hw0 : 0 ≤ w.val)
    (hck : checkTextwidth cw s w = true) : rtruncate cw s r w = .ok s := by
  unfold rtruncate truncBoundaries
  rw [if_neg (by omega), if_pos hck]

theorem rtrunc_bounds (cw : UInt32 → Int) (s r : JStr) (w left' pl e : JInt64) (hw0 : 0 ≤ w.val)
    (hck : ¬ checkTextwidth cw s w = true)
    (hloop : truncLoop cw s w .right true (2 * s.bytes.length + 4) (ix 1) (lastIdx s)
      (ix (textwidth cw r)) (ix 0) (ix 0) false = .ok (left', lastIdx s))
    (hpl : prevind s left' = .ok pl) (he : nextind s (lastIdx s) = .ok e) :
    truncBoundaries cw s r w .right true = .ok (some (pl, e)) := by
  unfold truncBoundaries
  rw [if_neg (by omega), if_neg hck, hloop]
  simp only
  rw [hpl]
  simp only
  rw [he]
  rfl

theorem rtrunc_eq (cw : UInt32 → Int) (s r : JStr) (w left' : JInt64) (hw0 : 0 ≤ w.val)
    (hck : ¬ checkTextwidth cw s w = true) (hn1 : 1 ≤ s.bytes.length) (hl1 : 1 ≤ left'.val)
    (hl2 : left'.val ≤ s.bytes.length + 1) (hV : Visits s.bytes (left'.val - 1).toNat)
    (hloop : truncLoop cw s w .right true (2 * s.bytes.length + 4) (ix 1) (lastIdx s)
      (ix (textwidth cw r)) (ix 0) (ix 0) false = .ok (left', lastIdx s)) :
    rtruncate cw s r w = concatStr [s.bytes.take (left'.val - 1).toNat, r.bytes] := by
  obtain ⟨_, _, e, he, _⟩ := lastIdx_pos s hn1
  obtain ⟨pl, sub, hpl, hsub, hsb⟩ := rtrunc_prefix s left' hn1 hl1 hl2 hV
  unfold rtruncate
  rw [rtrunc_bounds cw s r w left' pl e hw0 hck hloop hpl he]
  simp only
  rw [hsub]
  simp only
  rw [hsb]

theorem truncateWidthBound_proven : TruncateWidthBound := by
  intro cw hcw s r out w hrw hrc hout
  have hsm := ncu_small s
  have hrsm := ncu_small r
  rw [textwidth_eq] at hrw
  have hR := twList_bounds cw hcw (decAll r.bytes)
  have hRl := decAll_length _ r.bytes (Nat.le_refl _)
  have hS := twList_bounds cw hcw (decAll s.bytes)
  have hSl := decAll_length _ s.bytes (Nat.le_refl _)
  have hw0 : 0 ≤ w.val := by omega
  by_cases hck : checkTextwidth cw s w = true
  · rw [rtrunc_fits cw s r w hw0 hck] at hout
    have ho : s = out := Except.ok.inj hout
    rw [← ho, textwidth_eq]
    exact (check_iff cw hcw s w hw0).1 hck
  · have hT : w.val < twList cw (decAll s.bytes) :=
      Classical.byContradiction fun h => hck ((check_iff cw hcw s w hw0).2 (by omega))
    have hn1 : 1 ≤ s.bytes.length := by
      refine Classical.byContradiction fun hc => ?_
      rw [List.eq_nil_of_length_eq_zero (by omega : s.bytes.length = 0), decAll_nil, twList_nil] at hT
      omega
    have hRv : (ix (textwidth cw r)).val = twList cw (decAll r.bytes) := by
      rw [textwidth_eq]; exact ix_val _ (by omega) (by omega)
    obtain ⟨left', hloop, hl1, hl2, hV, hW⟩ := rloop cw hcw s w (lastIdx s) _ hR.1 hT
      (2 * s.bytes.length + 4) (ix 1) (ix (textwidth cw r)) (ix 0) false (by simp) (by rw [ix1]; omega)
      (by rw [ix1]; exact .zero) (by rw [hRv, ix1]; simp [decAll_nil, twList_nil]) (by rw [hRv]; omega)
      (by rw [ix1]; simp)
    rw [rtrunc_eq cw s r w left' hw0 hck hn1 hl1 hl2 hV hloop] at hout
    have hob : out.bytes = s.bytes.take (left'.val - 1).toNat ++ r.bytes := by
      have := stringN_ok hout
      simpa [concatStr] using this
    rw [textwidth_eq, hob, decAll_append_noncont r.bytes hrc _ _ (Nat.le_refl _), twList_append]
    omega

/-- Registry entries of the truncation functions. -/
def truncateEntries : List Entry := [
  { id := "stringutil-truncate-width"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["rtruncate(::AbstractString, ::Integer, ::Union{AbstractString,AbstractChar})",
      "ltruncate(::AbstractString, ::Integer, ::Union{AbstractString,AbstractChar})",
      "ctruncate(::AbstractString, ::Integer, ::Union{AbstractString,AbstractChar})"]
    statement := "rtruncate(s, w, r) has textwidth at most w for every string s, replacement r and maxwidth w >= 0, for every utf8proc width table with widths 0..2."
    source := "base/strings/util.jl:589-590 (rtruncate docstring: truncate str to at most maxwidth columns); :622-623, :655-657"
    status := .refuted
    prop := ``TruncateWidth
    thm := some ``truncateWidth_refuted
    issue := "none found (queries: issues: rtruncate; prs: rtruncate; issues: ltruncate; issues: ctruncate; issues: truncate maxwidth; issues: truncate replacement wider)"
    notes := "Counterexample rtruncate(\"abcdef\", 2, \"...\") == \"...\" (ASCII only, so independent of the width table): string_truncate_boundaries starts with width = textwidth(replacement) and never compares it alone with maxwidth. ltruncate and ctruncate behave the same (YAML reproducer). Same on 1.13.2." },
  { id := "stringutil-truncate-width-bound"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["rtruncate(::AbstractString, ::Integer, ::Union{AbstractString,AbstractChar})",
      "check_textwidth(::AbstractString, ::Integer)"]
    statement := "If textwidth(r) <= w and r does not start with a UTF-8 continuation byte, rtruncate(s, w, r) has textwidth at most w, for every byte string s and every utf8proc width table with widths 0..2."
    source := "base/strings/util.jl:589-590 (rtruncate docstring); invariant"
    status := .proven
    prop := ``TruncateWidthBound
    thm := some ``truncateWidthBound_proven
    notes := "Narrowed to rtruncate. The first-byte condition holds for every valid replacement (the default is '…'); it keeps the replacement's first byte from joining the last kept character when the two are concatenated." }
]

end JuliaLean.StringUtil
