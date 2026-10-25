import JuliaLean.RegexUnicode.CoreBasic

/-!
# Proven properties of the regex wrappers

Every statement quantifies over all `Pcre` primitives (any pattern), all
strings and all start indices; two add a hypothesis on where PCRE2 places match
boundaries in UTF mode, stated with its documentation below.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-! ## Hypotheses on PCRE2 in UTF mode -/

/-- Every nonempty match starts at a valid index of the subject. Julia compiles
every regex with `PCRE2_UTF | PCRE2_MATCH_INVALID_UTF` (`base/regex.jl:7`): in
this mode a nonempty match consists of whole valid UTF-8 characters (pcre2unicode,
"Matching in invalid UTF strings": invalid sequences never match), and a valid
character cannot begin inside a Julia character. `\C`, the one item that matches
part of a character, is rejected by the JIT compiler Julia always uses ("PCRE JIT
error: feature is not supported by the JIT compiler" on 1.13.2 and master). -/
def NonemptyAtChar (P : Pcre) : Prop :=
  ∀ (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec), o ≤ s.bytes.length →
    P.run s o opts = some v → v.start < v.stop → validZ s (v.start + 1)

/-- On a valid UTF-8 subject, a match started at a character boundary begins and
ends at character boundaries (pcre2unicode: in UTF mode characters, not code
units, are matched; pcre2api: with `PCRE2_NO_UTF_CHECK` the start offset must be
at a character boundary). Boundaries are zero-based offsets `p` with `p = length`
or Julia index `p + 1` valid. -/
def CharBoundaries (P : Pcre) : Prop :=
  ∀ (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec), isvalidStr s = true →
    o ≤ s.bytes.length → (o = s.bytes.length ∨ validZ s (o + 1)) → P.run s o opts = some v →
    (v.start = s.bytes.length ∨ validZ s (v.start + 1)) ∧
      (v.stop = s.bytes.length ∨ validZ s (v.stop + 1))

theorem hasOpt_or_of (x y b : UInt32) (i : Nat) (hy : y.toBitVec.getLsbD i = true)
    (hb : b.toBitVec.getLsbD i = true) : hasOpt (x ||| y) b = true := by
  unfold hasOpt
  simp only [bne_iff_ne, ne_eq]
  intro h
  have := congrArg (fun z : UInt32 => z.toBitVec.getLsbD i) h
  simp [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or, hy, hb] at this

/-- With `ANCHORED | NOTEMPTY_ATSTART`, a match is nonempty. -/
theorem match_nonempty {re : Regex} {s : JStr} {idx : JInt64} {m : RegexMatch}
    (hN : NonemptyAtChar re.pcre) (h : regexMatch re s idx optsNonempty = .ok (some m)) :
    m.mat.ncu.val ≠ 0 := by
  obtain ⟨v, h1, h2, hr, h0s, hle, hst, _, _, hc⟩ := regexMatch_some h
  have ho : (idx.val - 1).toNat ≤ s.bytes.length := by omega
  have ha := re.pcre.anchored _ _ _ _ ho hr (hasOpt_or_of _ _ _ 31 (by decide) (by decide))
  have hn := re.pcre.notempty_atstart _ _ _ _ ho hr (hasOpt_or_of _ _ _ 3 (by decide) (by decide))
  have hlt : v.start < v.stop := by omega
  exact (capSub_ok s _ _ _ h0s hle hst hc).2 hlt (hN _ _ _ _ ho hr hlt)

/-- The next offset computed from a match, `base/regex.jl:764-772`. -/
theorem next_spec {re : Regex} {s : JStr} {ov : Bool} {idx : JInt64} {opts : UInt32}
    {mat : RegexMatch} {o' : JInt64}
    (hm : regexMatch re s idx opts = .ok (some mat))
    (hn : (if ov then (if !decide (mat.mat.ncu.val = 0) then liftS (nextind s mat.offset)
      else .ok mat.offset) else .ok (mat.offset + mat.mat.ncu)) = .ok o') :
    idx.val ≤ mat.offset.val ∧ mat.offset.val ≤ o'.val ∧ o'.val ≤ s.bytes.length + 1 ∧
      (mat.mat.ncu.val ≠ 0 → mat.offset.val < o'.val) ∧ (ov = false → o' = mat.offset + mat.mat.ncu) := by
  have hs := ncu_small s
  obtain ⟨v, h1, h2, hr, h0s, hle, hst, hge, hoff, hc⟩ := regexMatch_some hm
  have hcs := (capSub_ok s _ _ _ h0s hle hst hc).1
  cases ov with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Except.ok.injEq] at hn
    subst hn
    have e : (mat.offset + mat.mat.ncu).val = mat.offset.val + mat.mat.ncu.val := by
      apply add_val <;> rcases hcs with h0 | ⟨h3, h4, _⟩ <;> omega
    refine ⟨by omega, ?_, ?_, ?_, fun _ => rfl⟩ <;> rw [e]
    · rcases hcs with h0 | ⟨h3, _, _⟩ <;> omega
    · rcases hcs with h0 | ⟨_, h4, _⟩ <;> omega
    · intro hne; rcases hcs with h0 | ⟨h3, _, _⟩ <;> omega
  | true =>
    simp only [ite_true] at hn
    by_cases he : mat.mat.ncu.val = 0
    · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
        Except.ok.injEq] at hn
      subst hn
      exact ⟨by omega, Int.le_refl _, by omega, fun h => absurd he h, fun h => by cases h⟩
    · simp only [he, decide_false, Bool.not_false, ite_true] at hn
      have hn' := liftS_ok hn
      rcases hcs with h0 | ⟨_, _, h5⟩
      · exact absurd h0 he
      · obtain ⟨j, hj, hjv⟩ := nextind_mid s mat.offset (by omega) (by omega)
        rw [hj] at hn'; cases hn'
        obtain ⟨n1, n2, _, _⟩ := nextZ_spec s mat.offset.val (by omega) (by omega)
        exact ⟨by omega, by omega, by omega, fun _ => by omega, fun h => by cases h⟩

/-- Progress of one `iterate` step. -/
theorem iterate_step {re : Regex} {s : JStr} {ov : Bool} {st : State} {m : RegexMatch} {st' : State}
    (hN : NonemptyAtChar re.pcre) (h : iterate re s ov st = .ok (some (m, st'))) :
    st.1.val ≤ m.offset.val ∧ (ov = false → st'.1 = m.offset + m.mat.ncu) ∧
      1 ≤ st.1.val ∧ st.1.val ≤ s.bytes.length + 1 ∧ st'.1.val ≤ s.bytes.length + 1 ∧
      (st.1.val < st'.1.val ∨ (st.1.val = st'.1.val ∧ st.2 = false ∧ st'.2 = true)) := by
  have hs := ncu_small s
  obtain ⟨off, pe⟩ := st
  unfold iterate at h
  dsimp only at h ⊢
  cases pe with
  | false =>
    simp only [iterLoop, Bool.false_eq_true, ite_false, Bool.false_and] at h
    split at h
    · cases h
    · cases h
    · rename_i mat hm
      split at h
      · cases h
      · rename_i o' ho
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        dsimp only
        obtain ⟨n1, n2, n3, n4, n5⟩ := next_spec hm ho
        have hb := regexMatch_bounds hm
        refine ⟨n1, n5, hb.1, hb.2, n3, ?_⟩
        by_cases hlt : off.val < o'.val
        · exact Or.inl hlt
        · right
          refine ⟨by omega, rfl, ?_⟩
          by_cases he : mat.mat.ncu.val = 0
          · simp [he]
          · exact absurd (n4 he) (by omega)
  | true =>
    simp only [iterLoop, ite_true, Bool.true_and] at h
    split at h
    · cases h
    · rename_i hm0
      have hb := regexMatch_bounds hm0
      split at h
      · rename_i hle
        split at h
        · cases h
        · rename_i o1 ho1
          rw [ncu_val] at hle
          obtain ⟨j, hj, hjv⟩ := nextind_mid s off (by omega) (by simpa using hle)
          rw [hj] at ho1; cases ho1
          obtain ⟨n1, n2, _, _⟩ := nextZ_spec s off.val (by omega) (by simpa using hle)
          simp only [Bool.false_eq_true, ite_false, Bool.false_and] at h
          split at h
          · cases h
          · cases h
          · rename_i mat hm
            split at h
            · cases h
            · rename_i o' ho
              simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              dsimp only
              obtain ⟨m1, m2, m3, _, m5⟩ := next_spec hm ho
              exact ⟨by omega, m5, hb.1, hb.2, m3, Or.inl (by omega)⟩
      · cases h
    · rename_i mat hm
      have hne := match_nonempty hN hm
      have hb := regexMatch_bounds hm
      split at h
      · cases h
      · rename_i o' ho
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        dsimp only
        obtain ⟨n1, n2, n3, n4, n5⟩ := next_spec hm ho
        exact ⟨n1, n5, hb.1, hb.2, n3, Or.inl (by have := n4 hne; omega)⟩

/-! ## eachmatch makes progress and terminates -/

/-- `2 (ncodeunits(s) + 1 - offset) + (prevempty ? 0 : 1)`: the offset part
decreases as the offset grows, and a step that keeps the offset turns
`prevempty` from false to true. -/
def progressMeasure (s : JStr) (st : State) : Nat :=
  2 * ((s.bytes.length : Int) + 1 - st.1.val).toNat + (if st.2 then 0 else 1)

theorem measure_lt {re : Regex} {s : JStr} {ov : Bool} {st : State} {m : RegexMatch} {st' : State}
    (hN : NonemptyAtChar re.pcre) (h : iterate re s ov st = .ok (some (m, st'))) :
    progressMeasure s st' < progressMeasure s st := by
  obtain ⟨_, _, _, h2, h3, h4⟩ := iterate_step hN h
  unfold progressMeasure
  rcases h4 with h4 | ⟨h4, h5, h6⟩
  · split <;> split <;> omega
  · rw [h5, h6]; simp only [ite_true, Bool.false_eq_true, ite_false]; omega

theorem eachTrace_exists (re : Regex) (s : JStr) (ov : Bool) (hN : NonemptyAtChar re.pcre)
    (st : State) : ∃ r, EachTrace re s ov st r :=
  match h : iterate re s ov st with
  | .error _ => ⟨_, .err h⟩
  | .ok none => ⟨_, .done h⟩
  | .ok (some (_, st')) =>
    have _hlt : progressMeasure s st' < progressMeasure s st := measure_lt hN h
    match eachTrace_exists re s ov hN st' with
    | ⟨_, hr⟩ => ⟨_, .step h hr⟩
termination_by progressMeasure s st

/-- Each step of `eachmatch(r, s; overlap)` from a state `(offset, prevempty)`
returns a match at or after `offset`; without overlap the next offset is
`m.offset + ncodeunits(m.match)`; the measure `progressMeasure` strictly
decreases, so iteration from any state terminates (with `nothing` or an
exception). Assumes PCRE2's nonempty matches start at valid indices. -/
def EachmatchProgress : Prop :=
  ∀ (re : Regex) (s : JStr) (ov : Bool), NonemptyAtChar re.pcre →
    (∀ (st : State) (m : RegexMatch) (st' : State), iterate re s ov st = .ok (some (m, st')) →
      st.1.val ≤ m.offset.val ∧ (ov = false → st'.1 = m.offset + m.mat.ncu) ∧
      progressMeasure s st' < progressMeasure s st) ∧
    ∀ st : State, ∃ r, EachTrace re s ov st r

theorem eachmatchProgress_proven : EachmatchProgress := by
  intro re s ov hN
  refine ⟨fun st m st' h => ?_, eachTrace_exists re s ov hN⟩
  obtain ⟨h1, h2, _⟩ := iterate_step hN h
  exact ⟨h1, h2, measure_lt hN h⟩

/-! ## count agrees with findall -/

theorem countLoop_findallLoop (find : JInt64 → RJl (Option (JInt64 × JInt64))) (s : JStr)
    (ov : Bool) (e : JInt64) :
    ∀ (f : Nat) (i n : JInt64) (acc : List (JInt64 × JInt64)), n.val = acc.length →
      (acc.length : Int) + f < 2 ^ 63 →
      (countLoop find s ov e f i n).map (·.val) =
        (findallLoop find s ov e f i acc).map (fun l => (l.length : Int)) := by
  intro f
  induction f with
  | zero =>
    intro i n acc hn _
    show Except.ok n.val = Except.ok (acc.length : Int)
    rw [hn]
  | succ f ih =>
    intro i n acc hn hb
    have hn' : (n + ix 1).val = (acc.length : Int) + 1 := by
      rw [add_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega), ix1, hn]
    have hlen : ∀ y : JInt64 × JInt64, ((acc ++ [y]).length : Int) = acc.length + 1 := by
      intro y; simp
    rw [countLoop, findallLoop]
    generalize find i = R
    cases R with
    | error err => rfl
    | ok x =>
      cases x with
      | none =>
        show Except.ok n.val = Except.ok (acc.length : Int)
        rw [hn]
      | some r =>
        dsimp only
        by_cases hj : (if ov || decide (r.2.val < r.1.val) then r.1 else r.2).val > e.val
        · rw [if_pos hj, if_pos hj]
          show Except.ok (n + ix 1).val = Except.ok ((acc ++ [r]).length : Int)
          rw [hn', hlen]
        · rw [if_neg hj, if_neg hj]
          generalize nextind s (if ov || decide (r.2.val < r.1.val) then r.1 else r.2) = N
          cases N with
          | error err => rfl
          | ok i' =>
            exact ih i' _ _ (by rw [hn', hlen]) (by rw [hlen]; omega)

/-- `count(r, s; overlap) == length(findall(r, s; overlap))` (the `count`
docstring: "equivalent to calling `length(findall(pattern, string))`"), including
which exception is thrown. -/
def CountEqLengthFindall : Prop :=
  ∀ (re : Regex) (s : JStr) (ov : Bool),
    (count re s ov).map (·.val) = (findall re s ov).map (fun l => (l.length : Int))

theorem countEqLengthFindall_proven : CountEqLengthFindall := by
  intro re s ov
  have hs := ncu_small s
  exact countLoop_findallLoop (findnextRe re s) s ov _ _ _ _ [] (by rfl)
    (by simp only [List.length_nil]; omega)

/-! ## findnext returns an indexable range -/

/-- For a valid UTF-8 string and a valid start index `i` (or `ncodeunits(s) + 1`),
`findnext(r, s, i)` returns a range `r` with `first(r) ≥ i`, `first(r)` a valid
index or `ncodeunits(s) + 1`, and `s[r]` defined; assumes PCRE2 matches started
at character boundaries begin and end at character boundaries. -/
def FindnextRange : Prop :=
  ∀ (re : Regex) (s : JStr) (i a b : JInt64), isvalidStr s = true → CharBoundaries re.pcre →
    (isvalidAt s i = true ∨ i.val = s.bytes.length + 1) →
    findnextRe re s i = .ok (some (a, b)) →
    i.val ≤ a.val ∧ (isvalidAt s a = true ∨ a.val = s.bytes.length + 1) ∧
      ∃ t, getindexRange s a b = .ok t

theorem findnextReFrom_some {re : Regex} {s : JStr} {i a b : JInt64} (E : SJl JInt64)
    (h : findnextReFrom re s i E = .ok (some (a, b))) :
    ∃ v b0, exec re.pcre s (i - ix 1) re.matchOptions = .ok (some v) ∧
      prevind s (ix (v.stop + 1)) = .ok b0 ∧ a = ix (v.start + 1) ∧
      b = (if b0.val ≥ (ix (v.start + 1)).val then b0 else ix (v.start + 1) - ix 1) := by
  unfold findnextReFrom at h
  cases E
  · cases h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · cases h
  rename_i v hex
  generalize hb0 : prevind s (ix (v.stop + 1)) = B at h
  cases B
  · cases h
  rename_i b0
  dsimp only at h
  simp only [Except.ok.injEq, Option.some.injEq, mkRange, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨v, b0, hex, hb0, rfl, rfl⟩

/-- What a successful `findnext` returned. The first argument of
`findnextReFrom`, which contains `ncodeunits s = ix ↑length`, stays abstract: the
kernel must not evaluate a wrapped cast natural (it would unfold
`Nat.ble 2^64 (length + 2^63)` one step at a time). -/
theorem findnextRe_some {re : Regex} {s : JStr} {i a b : JInt64}
    (h : findnextRe re s i = .ok (some (a, b))) :
    ∃ v b0, exec re.pcre s (i - ix 1) re.matchOptions = .ok (some v) ∧
      prevind s (ix (v.stop + 1)) = .ok b0 ∧ a = ix (v.start + 1) ∧
      b = (if b0.val ≥ (ix (v.start + 1)).val then b0 else ix (v.start + 1) - ix 1) :=
  findnextReFrom_some (nextind s (lastindex s)) h

theorem getindexRange_nonempty (s : JStr) (A j : JInt64) (hA : isvalidAt s A = true)
    (hj : isvalidAt s j = true) (hle : A.val ≤ j.val) : ∃ t, getindexRange s A j = .ok t := by
  have hAv := (isvalidAt_iff s A).1 hA
  have hjv := (isvalidAt_iff s j).1 hj
  obtain ⟨j', hj', _⟩ := nextind_mid s j (by omega) hjv.2.1
  unfold getindexRange
  have c0 : ¬ j.val < A.val := by omega
  have c1 : (decide (1 ≤ A.val) && decide (j.val ≤ (ncodeunits s).val)) = true := by
    rw [ncu_val]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [c0, c1, hA, hj, hj', if_false, Bool.not_true, Bool.false_eq_true]
  exact ⟨_, rfl⟩

theorem getindexRange_empty (s : JStr) (A B : JInt64) (h : B.val < A.val) :
    ∃ t, getindexRange s A B = .ok t :=
  ⟨JStr.empty, by unfold getindexRange; rw [if_pos h]⟩

theorem findnextRange_proven : FindnextRange := by
  intro re s i a b hvs hCB hi h
  have hs := ncu_small s
  have hi1 : 1 ≤ i.val ∧ i.val ≤ s.bytes.length + 1 := by
    rcases hi with hi | hi
    · have := (isvalidAt_iff s i).1 hi; omega
    · omega
  obtain ⟨v, b0, hex, hb0, rfl, rfl⟩ := findnextRe_some h
  obtain ⟨h0, h1, hr⟩ := exec_ok hex
  have e1 := sub1_val i h0 (by omega)
  have ho : (i - ix 1).val.toNat ≤ s.bytes.length := by omega
  have hge := re.pcre.start_ge _ _ _ _ ho hr
  have hle := re.pcre.start_le_stop _ _ _ _ ho hr
  have hst := re.pcre.stop_le _ _ _ _ ho hr
  have hob : (i - ix 1).val.toNat = s.bytes.length ∨ validZ s ((i - ix 1).val.toNat + 1) := by
    rcases hi with hi | hi
    · right
      have := (isvalidAt_iff s i).1 hi
      have e : ((i - ix 1).val.toNat : Int) + 1 = i.val := by omega
      rw [e]; exact this
    · left; omega
  obtain ⟨hcs, _⟩ := hCB _ _ _ _ hvs ho hob hr
  have ea : (ix (v.start + 1)).val = v.start + 1 := ix_val _ (by omega) (by omega)
  have eb : (ix (v.stop + 1)).val = v.stop + 1 := ix_val _ (by omega) (by omega)
  obtain ⟨j, hj, hj'⟩ := previndN_one s (ix (v.stop + 1)) (by omega) (by omega)
  have hj2 : prevind s (ix (v.stop + 1)) = .ok j := hj
  rw [hj2] at hb0
  simp only [Except.ok.injEq] at hb0
  subst hb0
  generalize ix (v.start + 1) = A at ea ⊢
  have hav : isvalidAt s A = true ∨ A.val = s.bytes.length + 1 := by
    rcases hcs with hc | hc
    · right; rw [ea]; omega
    · left; rw [isvalidAt_iff, ea]; exact hc
  refine ⟨by omega, hav, ?_⟩
  by_cases hb : j.val ≥ A.val
  · rw [if_pos hb]
    rcases hj' with ⟨_, hz⟩ | ⟨_, hpv⟩
    · omega
    · rw [eb] at hpv
      have hav' : isvalidAt s A = true := by
        rcases hav with hav | hav
        · exact hav
        · have := hpv.2.1; omega
      exact getindexRange_nonempty s A j hav' ((isvalidAt_iff s j).2 hpv.2.2.1) hb
  · rw [if_neg hb]
    exact getindexRange_empty s A _
      (by rw [sub_val _ _ (by rw [ea, ix1]; omega) (by rw [ea, ix1]; omega), ea, ix1]; omega)

end JuliaLean.RegexUnicode.Core
