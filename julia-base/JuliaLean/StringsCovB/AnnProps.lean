import JuliaLean.StringsCovB.Ann

/-!
# Properties of the `base/strings/annotated.jl` models
-/

namespace JuliaLean.StringsCovB.Ann

open JuliaLean JuliaLean.Strings

/-! ## Lemmas -/

theorem beq_comm' {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem rangeEq_refl (r : Region) : rangeEq r r = true := by
  unfold rangeEq; cases h : isemptyR r <;> simp

theorem rangeEq_symm (r s : Region) : rangeEq r s = rangeEq s r := by
  unfold rangeEq
  rw [beq_comm' r.1 s.1, beq_comm' r.2 s.2]
  cases h1 : isemptyR r <;> cases h2 : isemptyR s <;> simp

theorem jeq_refl (a : RA) : a.jeq a = true := by
  simp [RA.jeq, rangeEq_refl]

theorem jeq_symm (a b : RA) : a.jeq b = b.jeq a := by
  unfold RA.jeq; rw [rangeEq_symm, beq_comm' a.label, beq_comm' a.value]

theorem annsEq_refl : ∀ l : List RA, annsEq l l = true
  | [] => rfl
  | a :: t => by simp [annsEq, jeq_refl, annsEq_refl t]

theorem annsEq_symm : ∀ l m : List RA, annsEq l m = annsEq m l
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: t, b :: u => by simp only [annsEq, jeq_symm a b, annsEq_symm t u]

/-! ## Constructors and conversions -/

/-- The constructors store the given string and annotations and never wrap an
`AnnotatedString` inside another: an `AnnotatedString` argument contributes its
string and annotations, followed by the new ones. Conversions are the identity
on annotated values and add no annotations to plain ones. -/
def CtorContract : Prop :=
  (∀ s annots, ctorVector (.plain s) annots = ⟨s, annots.map RA.ofTup⟩) ∧
  (∀ a annots, ctorVector (.ann a) annots = ⟨a.str, a.anns ++ annots.map RA.ofTup⟩) ∧
  (∀ s annots, ctorIter s annots = ctorVector s annots) ∧
  (∀ a b c, ctorRA (.ann (ctorRA (.ann a) b)) c = ctorRA (.ann a) (b ++ c)) ∧
  (∀ c annots, cctorVector (.plain c) annots = ⟨c, annots.map Ann.ofTup⟩) ∧
  (∀ a annots, cctorVector (.ann a) annots = ⟨a.char, a.anns ++ annots.map Ann.ofTup⟩) ∧
  (∀ c annots, cctorIter c annots = cctorVector c annots) ∧
  (∀ a b c, cctorA (.ann (cctorA (.ann a) b)) c = cctorA (.ann a) (b ++ c)) ∧
  (∀ s, toString s = s.str) ∧
  (∀ s, convertAS s = s) ∧
  (∀ s, convertASOf (.plain s) = ⟨s, []⟩ ∧ ofS (.plain s) = ⟨s, []⟩) ∧
  (∀ a, ofS (.ann a) = a ∧ convertASOf (.ann a) = a) ∧
  (∀ c, convertAC c = c) ∧
  (∀ c, ofChar c = ⟨c, []⟩ ∧ convertACOf c = ⟨c, []⟩) ∧
  (∀ u, ofU32 u = (charOfU32 u).map ofChar ∧ ofU32C u = ofU32 u) ∧
  (∀ a b, promoteRule (.annotatedString a) b = .annotatedStringAll)

theorem ctorContract : CtorContract := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩, ?_, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩, ?_, fun _ _ => rfl⟩
  · intro a b c; simp [ctorRA]
  · intro a b c; simp [cctorA]
  · intro a; simp [ofS, convertASOf, convertASOfS, ctorRA]
  · intro u
    refine ⟨?_, rfl⟩
    unfold ofU32; cases charOfU32 u <;> rfl

/-! ## The `AbstractString` and `AbstractChar` interfaces -/

/-- The code-unit methods of an `AnnotatedString` are those of its `String`,
`eltype(AnnotatedString{String})` is `AnnotatedChar{Char}`, `s[i]` is the
character `s.string[i]` carrying exactly the labels and values of
`annotations(s, i)` (and throws `BoundsError` outside `1:ncodeunits(s)`),
iteration stops after `lastindex(s)` and otherwise yields `s[i]` and
`nextind(s, i)`, and `unannotate` returns the underlying code units. -/
def InterfaceContract : Prop :=
  (∀ s, ncodeunitsA s = ncodeunits s.str ∧ codeunitsA s = s.str.bytes ∧ codeunitTyA s = 8 ∧
    firstindexA s = ix 1 ∧ lastindexA s = lastindex s.str) ∧
  (∀ s i, codeunitA s i = codeunit s.str i ∧ isvalidA s i = isvalidAt s.str i) ∧
  eltypeAS .string = .annotatedChar .char ∧
  (∀ s i c, getindexA s i = .ok c →
    getindex s.str i = .ok c.char ∧ c.anns = (annotationsAt s i).map RA.toAnn) ∧
  (∀ s i, ¬ (1 ≤ i.val ∧ i.val ≤ s.str.bytes.length) → getindexA s i = .error boundsErr) ∧
  (∀ s i, (lastindex s.str).val < i.val → iterateA s i = .ok none) ∧
  (∀ s i, i.val ≤ (lastindex s.str).val →
    iterateA s i = (do let c ← getindexA s i; let j ← nextindA s i; pure (some (c, j)))) ∧
  (∀ s, unannotate s = s.str) ∧
  (∀ x, (unannotateSub x).view = (JSub.view ⟨x.parent.str, x.offset, x.ncu⟩)) ∧
  (∀ c, ncodeunitsC c = ncodeunitsChar c.char ∧ codepointC c = codepoint c.char)

theorem interfaceContract : InterfaceContract := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_,
    fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  · intro s i c h
    unfold getindexA at h
    split at h
    · cases h
    · split at h
      · cases hg : getindex s.str i with
        | error e => rw [hg] at h; cases h
        | ok c' =>
          rw [hg] at h
          simp only [bind, Except.bind, pure, Except.pure] at h
          cases h
          exact ⟨rfl, rfl⟩
      · cases h
  · intro s i h
    unfold getindexA
    rw [if_pos]
    rw [ncu_val]
    by_cases h1 : 1 ≤ i.val
    · have h2 : ¬ i.val ≤ (s.str.bytes.length : Int) := fun h2 => h ⟨h1, h2⟩
      simp [h1, h2]
    · simp [h1]
  · intro s i h
    unfold iterateA
    rw [if_neg (by omega)]
  · intro s i h
    unfold iterateA
    rw [if_pos h]

/-! ## `show` -/

/-- The two-argument `show` prints the type, the `String` and the annotations as
tuples, in that order between parentheses; the `text/plain` show prints only the
characters, so it does not depend on the annotations. -/
def ShowContract : Prop :=
  (∀ T showStr showTups s, showAS T showStr showTups s =
    T ++ [0x28] ++ showStr s.str ++ [0x2c, 0x20] ++
      showTups (s.anns.map fun a => (a.region, a.label, a.value)) ++ [0x29]) ∧
  (∀ showChars s anns, showPlainAS showChars ⟨s, anns⟩ = showPlainAS showChars ⟨s, []⟩ ∧
    showPlainAS showChars ⟨s, anns⟩ = showChars (chars s))

theorem showContract : ShowContract := ⟨fun _ _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-! ## Comparison and equality -/

/-- `cmp` ignores annotations; `==` between AnnotatedStrings compares strings and
annotation vectors and is reflexive and symmetric; the mixed methods agree in both
argument orders; an AnnotatedString equals a plain String exactly when it has no
annotations and the same code units. -/
def EqContract : Prop :=
  (∀ a b, cmpAS a b = Strings.cmp a.str b) ∧
  (∀ a b, cmpSA a b = Strings.cmp a b.str) ∧
  (∀ a, eqAA a a = true) ∧
  (∀ a b, eqAA a b = eqAA b a) ∧
  (∀ a b, eqAS a b = eqSA b a) ∧
  (∀ a b, eqAS a b = true ↔ a.anns = [] ∧ a.str = b) ∧
  (∀ u, eqUU u u = true) ∧
  (∀ u v, eqUU u v = eqUU v u) ∧
  (∀ u b, eqSU b u = eqUS u b) ∧
  (∀ u a, eqAU a u = eqUA u a)

theorem eqContract : EqContract := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro a; simp [eqAA, annsEq_refl]
  · intro a b; unfold eqAA; rw [annsEq_symm, beq_comm' a.str]
  · intro a b; unfold eqAS eqSA; rw [beq_comm' b]
  · intro a b; unfold eqAS; simp
  · intro u; simp [eqUU, subEq, annsEq_refl]
  · intro u v; unfold eqUU subEq; rw [annsEq_symm, beq_comm' (unannotateSub u).view.bytes]

/-! ## `annotatedstring` -/

/-- `"x"`. -/
def strX : JStr := ⟨[0x78], by decide⟩
/-- `'é'`, bit pattern `0xc3a90000`. -/
def charE : UInt32 := 0xc3a90000

/-- Every annotation of an `AnnotatedChar` argument covers exactly the code units
of that character in the result: after a String of `n` code units, an
`AnnotatedChar` `c` gets the region `n+1:n+ncodeunits(c)`. -/
def AnnotatedstringCharRegion : Prop :=
  ∀ (s : JStr) (c : AC) (r : AS), annotatedstring [.str ⟨s, []⟩, .achar c] = .ok r →
    r.anns = c.anns.map (RA.ofAnn (urange (ncodeunits s + ix 1) (ncodeunits s + ix (ncodeunitsC c))))

theorem annotatedstringCharRegion_refuted : ¬ AnnotatedstringCharRegion := by
  intro h
  have := h strX ⟨charE, [⟨0, some 1⟩]⟩ _ rfl
  revert this; decide

/-- The one-argument methods: `annotatedstring(s::AnnotatedString)` is `s`, and
`annotatedstring(c::AnnotatedChar)` is the string of `c` with every annotation of
`c` on the region `1:ncodeunits(c)`. -/
def AnnotatedstringForms : Prop :=
  (∀ s, annotatedstringAS s = s) ∧
  (∀ c r, annotatedstringAC c = .ok r →
    stringOfChars [c.char] = .ok r.str ∧
      r.anns = c.anns.map (RA.ofAnn (urange (ix 1) (ix (ncodeunitsC c)))))

theorem annotatedstringForms : AnnotatedstringForms := by
  refine ⟨fun _ => rfl, ?_⟩
  intro c r h
  unfold annotatedstringAC at h
  cases hs : stringOfChars [c.char] with
  | error e => rw [hs] at h; cases h
  | ok t =>
    rw [hs] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases h
    exact ⟨rfl, rfl⟩

/-! ## `repeat` -/

theorem rem_u64_val (r : JInt64) (h : 0 ≤ r.val) : (JInt.rem .u64 r).val = r.val := by
  show wrapInt .u64 r.val = r.val
  apply wrapInt_of_inRange
  have hb := r.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
  constructor <;> simp <;> omega

/-- The code units of `repeat(str, r)` are those of `repeat(str.string, r)`, and
`repeat` of a SubString repeats its conversion to an AnnotatedString. -/
def RepeatString : Prop :=
  (∀ str r t, repeatAS str r = .ok t → repeatStr str.str r = .ok t.str) ∧
  (∀ str r, repeatSub str r = (do let a ← ofSub str; repeatAS a r))

theorem repeatString : RepeatString := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro str r t h
  unfold repeatAS at h
  by_cases h0 : r.val = 0
  · rw [if_pos h0] at h
    cases h
    unfold repeatStr
    rw [if_neg (by omega)]
    simp only []
    rw [if_pos (by rw [rem_u64_val r (by omega)]; exact h0)]
    rfl
  · rw [if_neg h0] at h
    by_cases h1 : r.val = 1
    · rw [if_pos h1] at h
      cases h
      unfold repeatStr
      rw [if_neg (by omega)]
      simp only []
      rw [if_neg (by rw [rem_u64_val r (by omega)]; exact h0)]
      rw [if_pos (by rw [rem_u64_val r (by omega)]; exact h1)]
    · rw [if_neg h1] at h
      cases hr : repeatStr str.str r with
      | error e => rw [hr] at h; cases h
      | ok u =>
        rw [hr] at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · split at h
            · cases h
            · cases h; rfl

/-- `repeat(c::AnnotatedChar, r)` equals `repeat` of the equivalent
`AnnotatedString` `annotatedstring(c)` for every `r ≥ 0`. -/
def RepeatCharAsString : Prop :=
  ∀ (c : AC) (r : JInt64) (a : AS), 0 ≤ r.val → annotatedstringAC c = .ok a →
    repeatAC c r = repeatAS a r

/-- `'a'`. -/
def charA : UInt32 := 0x61000000

theorem repeatCharAsString_refuted : ¬ RepeatCharAsString := by
  intro h
  let a : AS := ⟨⟨[0x61], by decide⟩, [⟨ix 1, ix 1, 0, some 1⟩]⟩
  have ha : annotatedstringAC ⟨charA, [⟨0, some 1⟩]⟩ = .ok a := rfl
  have e1 : repeatAC ⟨charA, [⟨0, some 1⟩]⟩ (ix 0) = .ok ⟨JStr.empty, [⟨ix 1, ix 0, 0, some 1⟩]⟩ := rfl
  have e2 : repeatAS a (ix 0) = .ok oneAS := rfl
  have := (e1.symm.trans (h _ (ix 0) a (by decide) ha)).trans e2
  have := congrArg (fun x => match x with | .ok (v : AS) => v.anns.length | .error _ => 0) this
  simp [oneAS] at this

/-- `reverse` of a SubString of an AnnotatedString reverses its conversion. -/
def ReverseSub : Prop :=
  ∀ s r, reverseSub s = .ok r → ∃ a, ofSub s = .ok a ∧ r = reverseAS a ∧ r.str = Strings.reverse a.str

theorem reverseSub_proven : ReverseSub := by
  intro s r h
  cases ho : ofSub s with
  | error e => simp only [reverseSub, ho, bind, Except.bind] at h; exact absurd h (by intro h'; cases h')
  | ok a =>
    have hr : reverseAS a = r := by
      have h2 : reverseSub s = .ok (reverseAS a) := by
        simp only [reverseSub, ho, bind, Except.bind, pure, Except.pure]
      exact Except.ok.inj (h2.symm.trans h)
    exact ⟨a, rfl, hr.symm, by rw [← hr]; simp only [reverseAS]⟩

/-! ## `annotate!` -/

/-- `annotate!` with a value appends exactly that annotation; with `nothing` it
removes exactly the annotations of that label whose region equals the range and
keeps the others in order. The whole-string forms use `firstindex:lastindex`
(or `1:ncodeunits` of a SubString), SubString forms shift the range by the offset
into the parent, and `annotate!(c::AnnotatedChar, ...)` appends the pair. -/
def AnnotateContract : Prop :=
  (∀ l r lab v, v ≠ none → annotateBang l r lab v = l ++ [⟨r.1, r.2, lab, v⟩]) ∧
  (∀ l r lab, annotateBang l r lab none =
    l.filter (fun a => !(rangeEq a.region r && a.label == lab))) ∧
  (∀ l r lab a, a ∈ annotateBang l r lab none → ¬ (rangeEq a.region r = true ∧ a.label = lab)) ∧
  (∀ l r lab a, a ∈ l → ¬ (rangeEq a.region r = true ∧ a.label = lab) → a ∈ annotateBang l r lab none) ∧
  (∀ s r lab v, (annotateAS s r lab v).anns = annotateBang s.anns r lab v ∧ (annotateAS s r lab v).str = s.str) ∧
  (∀ s lab v, annotateASAll s lab v = annotateAS s (urange (firstindex s.str) (lastindex s.str)) lab v) ∧
  (∀ x r lab v, (annotateSub x r lab v).parent = annotateAS x.parent (shiftRegion x.offset r) lab v) ∧
  (∀ x lab v, (annotateSubAll x lab v).parent =
    annotateAS x.parent (shiftRegion x.offset (urange (ix 1) x.ncu)) lab v) ∧
  (∀ c lab v, annotateAC c lab v = ⟨c.char, c.anns ++ [⟨lab, v⟩]⟩)

theorem annotateContract : AnnotateContract := by
  refine ⟨?_, fun _ _ _ => rfl, ?_, ?_, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · intro l r lab v hv
    cases v with
    | none => exact absurd rfl hv
    | some n => rfl
  · intro l r lab a ha
    simp only [annotateBang, List.mem_filter] at ha
    intro ⟨h1, h2⟩
    have := ha.2
    simp [h1, h2] at this
  · intro l r lab a ha hn
    simp only [annotateBang, List.mem_filter]
    refine ⟨ha, ?_⟩
    cases h1 : rangeEq a.region r
    · simp
    · have : a.label ≠ lab := fun e => hn ⟨h1, e⟩
      simp [this]

/-- `"abc"`. -/
def strAbc : JStr := ⟨[0x61, 0x62, 0x63], by decide⟩

/-- Documented behaviour of `annotate!(s, range, label, nothing)`: afterwards no
`label` annotation overlaps `range` ("To remove existing label annotations, use
a value of nothing"). -/
def AnnotateNothingRemoves : Prop :=
  ∀ (s : AS) (r : Region) (lab : Nat), ∀ a ∈ (annotateAS s r lab none).anns, a.label = lab →
    isemptyR (urange (imax r.1 a.lo) (imin r.2 a.hi)) = true

theorem annotateNothingRemoves_refuted : ¬ AnnotateNothingRemoves := by
  intro h
  have := h ⟨strAbc, [⟨ix 1, ix 2, 7, some 1⟩]⟩ (ix 1, ix 3) 7 ⟨ix 1, ix 2, 7, some 1⟩
    (by decide) rfl
  revert this; decide

/-! ## `annotations` -/

theorem mem_annsRange (pos : Region) : ∀ (l : List RA) (b : RA), b ∈ annsRange pos l →
    ∃ a ∈ l, b = a.setR (urange (imax pos.1 a.lo) (imin pos.2 a.hi)) ∧
      isemptyR (urange (imax pos.1 a.lo) (imin pos.2 a.hi)) = false
  | [], b, hb => by simp [annsRange] at hb
  | a :: t, b, hb => by
    unfold annsRange at hb
    split at hb
    · rename_i hne
      rcases List.mem_cons.mp hb with e | hb
      · exact ⟨a, List.mem_cons_self .., e, by simpa using hne⟩
      · obtain ⟨a', ha', e, hne'⟩ := mem_annsRange pos t b hb
        exact ⟨a', List.mem_cons_of_mem _ ha', e, hne'⟩
    · obtain ⟨a', ha', e, hne'⟩ := mem_annsRange pos t b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', e, hne'⟩

/-- `annotations(s)` and `annotations(c)` return the stored vectors, and every
annotation returned by `annotations(s, pos)` comes from an annotation of `s` with
the same label and value whose region overlaps `pos`, clamped to `pos`: its region
is nonempty and lies inside both `pos` and the original region. -/
def AnnotationsContract : Prop :=
  (∀ s, annotations s = s.anns) ∧ (∀ c, annotationsC c = c.anns) ∧
  (∀ s pos b, b ∈ annotationsRange s pos → ∃ a ∈ s.anns,
    b.label = a.label ∧ b.value = a.value ∧
    pos.1.val ≤ b.lo.val ∧ a.lo.val ≤ b.lo.val ∧ b.lo.val ≤ b.hi.val ∧
    b.hi.val ≤ pos.2.val ∧ b.hi.val ≤ a.hi.val)

theorem annotationsContract : AnnotationsContract := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro s pos b hb
  obtain ⟨a, ha, rfl, hne⟩ := mem_annsRange pos s.anns b hb
  refine ⟨a, ha, rfl, rfl, ?_⟩
  have hne2 : StringUtil.isemptyR (StringUtil.urange (imax pos.1 a.lo) (imin pos.2 a.hi)) = false := hne
  rw [StringUtil.isemptyR_urange] at hne2
  have hne' : ¬ (imin pos.2 a.hi).val < (imax pos.1 a.lo).val := by simpa using hne2
  rw [StringUtil.imax_val, StringUtil.imin_val] at hne'
  have e : (urange (imax pos.1 a.lo) (imin pos.2 a.hi)) = (imax pos.1 a.lo, imin pos.2 a.hi) := by
    show StringUtil.urange _ _ = _
    unfold StringUtil.urange
    rw [if_pos (by rw [StringUtil.imax_val, StringUtil.imin_val]; omega)]
  rw [e]
  simp only [RA.setR, StringUtil.imax_val, StringUtil.imin_val]
  omega

/-! ## `annotated_chartransform` -/

/-- `"ab"`. -/
def strAb : JStr := ⟨[0x61, 0x62], by decide⟩

/-- An annotation covering exactly the code units of one character covers exactly
the code units of the transformed character ("adjusting annotation regions as
appropriate"). -/
def ChartransformAligned : Prop :=
  ∀ (g : UInt32 → UInt32) (s : JStr) (i : JInt64) (c : UInt32) (t : AS),
    isvalidAt s i = true → getindex s i = .ok c →
    annotatedChartransform (fun (st : Unit) d => .ok (g d, st))
      ⟨s, [⟨i, i + ix (ncodeunitsChar c) - ix 1, 0, none⟩]⟩ () = .ok t →
    ∀ a ∈ t.anns, (t.str.bytes.drop (a.lo.val.toNat - 1)).take (a.hi.val - a.lo.val + 1).toNat =
      charBytes (g c)

theorem chartransformAligned_refuted : ¬ ChartransformAligned := by
  intro h
  have := h (fun d => if d = 0x62000000 then charE else d) strAb (ix 2) 0x62000000 _
    (by decide) rfl rfl ⟨ix 3, ix 3, 0, none⟩ (by decide)
  revert this; decide

/-! ## `RegionIterator` -/

/-- `length(si)` is the number of regions; for a `RegionIterator` whose vectors
have the same length (as `eachregion` builds them) both `@inbounds` reads of
`iterate(si, i)` are in bounds for every `1 ≤ i ≤ length(si)`, iteration ends
after `length(si)`, and the element type is `Tuple{SubString{S}, Vector{Annotation}}`. -/
def RegionIterContract : Prop :=
  (∀ si, riLength si = si.regions.length) ∧
  (∀ si i, si.annotations.length = si.regions.length → 1 ≤ i.val → i.val ≤ si.regions.length →
    riIterate si i = (do
      let r := si.regions.getD (i.val.toNat - 1) (ix 0, ix 0)
      let sub ← substring si.str r.1 r.2
      pure (some ((sub, si.annotations.getD (i.val.toNat - 1) []), i + ix 1)))) ∧
  (∀ si i, (si.regions.length : Int) < i.val → riIterate si i = .ok none) ∧
  (riEltype .string = (.subString .string, "Vector{Annotation}"))

theorem regionIterContract : RegionIterContract := by
  refine ⟨fun _ => rfl, ?_, ?_, rfl⟩
  · intro si i hl h1 h2
    unfold riIterate
    rw [if_pos h2, if_pos ⟨h1, by omega⟩]
  · intro si i h
    unfold riIterate
    rw [if_neg (by omega)]

/-! ## `annotation_events` -/

abbrev PosLe (a b : StringUtil.Event) : Prop := a.pos.val ≤ b.pos.val

theorem mem_insertByPos (e : StringUtil.Event) : ∀ (l : List StringUtil.Event) x,
    x ∈ StringUtil.insertByPos e l → x = e ∨ x ∈ l
  | [], x, h => by simp [StringUtil.insertByPos] at h; exact Or.inl h
  | f :: fs, x, h => by
    unfold StringUtil.insertByPos at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self ..)
      · rcases mem_insertByPos e fs x h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem insertByPos_sorted (e : StringUtil.Event) : ∀ l : List StringUtil.Event,
    l.Pairwise PosLe → (StringUtil.insertByPos e l).Pairwise PosLe
  | [], _ => by simp [StringUtil.insertByPos]
  | f :: fs, h => by
    have hf := List.pairwise_cons.mp h
    unfold StringUtil.insertByPos
    split
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨?_, insertByPos_sorted e fs hf.2⟩
      intro x hx
      rcases mem_insertByPos e fs x hx with rfl | hx
      · exact Int.le_of_lt hlt
      · exact hf.1 x hx
    · rename_i hge
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.not_lt.mp hge
      · exact Int.le_trans (Int.not_lt.mp hge) (hf.1 x hx)

theorem sortByPos_sorted : ∀ l : List StringUtil.Event, (StringUtil.sortByPos l).Pairwise PosLe
  | [] => by simp [StringUtil.sortByPos]
  | e :: es => insertByPos_sorted e _ (sortByPos_sorted es)

/-- The change events returned by `annotation_events` are sorted by position, as
`eachregion` requires. -/
def EventsSorted : Prop :=
  ∀ (s : JStr) (annots : List RA) (sub : Region) evs,
    annotationEvents s annots sub = .ok evs → evs.Pairwise PosLe

theorem eventsSorted : EventsSorted := by
  intro s annots sub evs h
  unfold annotationEvents StringUtil.annotationEvents at h
  cases hl : StringUtil.eventsLoop s sub 1 (annots.map RA.toU) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases h
    exact sortByPos_sorted l

/-- The AnnotatedString method passes its string and annotations. -/
def EventsForward : Prop :=
  ∀ s sub, annotationEventsAS s sub = annotationEvents s.str s.anns sub

theorem eventsForward : EventsForward := fun _ _ => rfl

end JuliaLean.StringsCovB.Ann
