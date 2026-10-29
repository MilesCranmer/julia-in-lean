import JuliaLean.base.strings.util
import JuliaLean.Registry.Types
import JuliaLean.base.int

/-!
# Properties of `base/strings/util.jl`

Specifications and registry entries for the source-mirrored string utility methods.
-/

namespace JuliaLean.Proofs.base.strings.util

open JuliaLean.Registry

open JuliaLean.base.strings.basic
open JuliaLean.base.strings.util
instance {E A : Type} [DecidableEq E] [DecidableEq A] : DecidableEq (Except E A)
  | .ok a, .ok b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun he => h (Except.ok.inj he))
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun he => h (Except.error.inj he))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

deriving instance DecidableEq for ReplaceRange


/-! An iterator trace relates a finite character sequence to the external `iterate` interface.
The trace records successful iteration and termination, without specifying any utility method. -/
inductive CharacterTrace {C E State : Type}
    (next : State → Except E (Option (C × State))) :
    Option (C × State) → List C → Prop where
  | nil : CharacterTrace next none []
  | cons {c : C} {k : State} {current : Option (C × State)} {rest : List C}
      (step : next k = .ok current) (tail : CharacterTrace next current rest) :
      CharacterTrace next (some (c, k)) (c :: rest)

/-! ## Character-sequence specifications for affix removal -/

private theorem chopPrefixLoop_correct
    {S P R C E : Type} [BEq C] [LawfulBEq C]
    (iterateS : S → Index → Except E (Option (C × Index)))
    (iterateP : P → Index → Except E (Option (C × Index)))
    (empty : S → Except E R) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (observe : R → List C) (s : S) (pre : P)
    (original : List C)
    (hempty : ∃ out, empty s = .ok out ∧ observe out = [])
    (hwhole : ∃ out, whole s = .ok out ∧ observe out = original)
    (hslice : ∀ k current chars,
      iterateS s k = .ok current → CharacterTrace (iterateS s) current chars →
      ∃ out, subFrom s k = .ok out ∧ observe out = chars) :
    ∀ (patChars remaining : List C) (fuel : Nat) (k : Index)
      (i j : Option (C × Index)),
      iterateS s k = .ok i →
      CharacterTrace (iterateS s) i remaining →
      CharacterTrace (iterateP pre) j patChars →
      patChars.length < fuel →
      ∃ out,
        chopprefix.loop iterateS iterateP empty subFrom whole (fun c d => c == d) s pre
          fuel k i j = .ok out ∧
        observe out = if patChars.isPrefixOf remaining then remaining.drop patChars.length else original := by
  intro patChars
  induction patChars with
  | nil =>
    intro remaining fuel k i j hcurrent hi hj hf
    cases hj
    cases fuel with
    | zero => omega
    | succ n =>
      cases hi with
      | nil =>
        obtain ⟨out, ho, hv⟩ := hempty
        exact ⟨out, by simpa [chopprefix.loop] using ho, by simpa using hv⟩
      | cons hstep htail =>
        obtain ⟨out, ho, hv⟩ := hslice k _ _ hcurrent (.cons hstep htail)
        exact ⟨out, by simpa [chopprefix.loop] using ho, by simpa using hv⟩
  | cons d patChars ih =>
    intro remaining fuel k i j hcurrent hi hj hf
    cases hj with
    | cons hstepP htailP =>
      cases fuel with
      | zero => omega
      | succ n =>
        cases hi with
        | nil =>
          obtain ⟨out, ho, hv⟩ := hwhole
          exact ⟨out, by simpa [chopprefix.loop] using ho,
            by simpa [List.isPrefixOf] using hv⟩
        | @cons c next current rest hstepS htailS =>
          by_cases heq : c = d
          · subst d
            obtain ⟨out, ho, hv⟩ := ih rest n next current _ hstepS htailS htailP
              (by simp at hf; omega)
            refine ⟨out, ?_, ?_⟩
            · simpa [chopprefix.loop, hstepS, hstepP, bind, Except.bind] using ho
            · have hself : (c == c) = true := (beq_iff_eq).mpr rfl
              simp only [List.isPrefixOf, List.length_cons, List.drop_succ_cons]
              rw [hself]
              cases h : patChars.isPrefixOf rest <;> simpa [h] using hv
          · have hcd : (c == d) = false := by simp [beq_iff_eq, heq]
            have hdc : (d == c) = false := by simp [beq_iff_eq, Ne.symm heq]
            obtain ⟨out, ho, hv⟩ := hwhole
            exact ⟨out, by simpa [chopprefix.loop, hcd] using ho,
              by simpa [List.isPrefixOf, hdc] using hv⟩

def ChopPrefixSequence : Prop :=
  ∀ {S P R C E : Type} [BEq C] [LawfulBEq C]
    (firstS : S → Except E (Option (C × Index)))
    (firstP : P → Except E (Option (C × Index)))
    (iterateS : S → Index → Except E (Option (C × Index)))
    (iterateP : P → Index → Except E (Option (C × Index)))
    (boundS : S → Nat) (boundP : P → Nat) (firstindex : S → Index)
    (empty : S → Except E R) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (observe : R → List C) (s : S) (pre : P)
    (source patChars : List C) (i j : Option (C × Index)),
    firstS s = .ok i → firstP pre = .ok j →
    iterateS s (firstindex s) = .ok i →
    CharacterTrace (iterateS s) i source →
    CharacterTrace (iterateP pre) j patChars →
    patChars.length ≤ boundP pre →
    (∃ out, empty s = .ok out ∧ observe out = []) →
    (∃ out, whole s = .ok out ∧ observe out = source) →
    (∀ k current chars,
      iterateS s k = .ok current → CharacterTrace (iterateS s) current chars →
      ∃ out, subFrom s k = .ok out ∧ observe out = chars) →
    ∃ out,
      chopprefix firstS firstP iterateS iterateP boundS boundP firstindex
        empty subFrom whole (fun c d => c == d) s pre = .ok out ∧
      observe out = if patChars.isPrefixOf source then source.drop patChars.length else source

theorem chopPrefixSequence_proven : ChopPrefixSequence := by
  intro S P R C E inst lawful firstS firstP iterateS iterateP boundS boundP firstindex
    empty subFrom whole observe s pre source patChars i j ha hb hc hi hj hf he hw hs
  obtain ⟨out, ho, hv⟩ := chopPrefixLoop_correct iterateS iterateP empty subFrom whole observe
    s pre source he hw hs patChars source (boundS s + boundP pre + 1)
    (firstindex s) i j hc hi hj (by omega)
  refine ⟨out, ?_, hv⟩
  simpa [chopprefix, ha, hb, bind, Except.bind] using ho

def ChopPrefixCharacter : Prop :=
  ∀ {S R C E : Type} [BEq C] [LawfulBEq C]
    (isempty : S → Bool) (first : S → Except E C) (firstindex : S → Index)
    (nextind : S → Index → Except E Index) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (observe : R → List C)
    (s : S) (c : C) (source : List C),
    isempty s = source.isEmpty →
    (∃ out, whole s = .ok out ∧ observe out = source) →
    (∀ head tail, source = head :: tail →
      first s = .ok head ∧
      ∃ next out, nextind s (firstindex s) = .ok next ∧
        subFrom s next = .ok out ∧ observe out = tail) →
    ∃ out,
      chopprefixChar isempty first firstindex nextind subFrom whole
        (fun a b => a == b) s c = .ok out ∧
      observe out = match source with
        | [] => []
        | head :: tail => if head == c then tail else head :: tail

theorem chopPrefixCharacter_proven : ChopPrefixCharacter := by
  intro S R C E inst lawful isempty first firstindex nextind subFrom whole observe s c source
    hi hw hs
  cases source with
  | nil =>
    obtain ⟨out, ho, hv⟩ := hw
    refine ⟨out, ?_, hv⟩
    simp only [List.isEmpty_nil] at hi
    simp [chopprefixChar, hi, ho, bind, Except.bind]
  | cons head tail =>
    obtain ⟨hfirst, next, out, hn, ho, hv⟩ := hs head tail rfl
    simp only [List.isEmpty_cons] at hi
    cases heq : (head == c) with
    | true =>
      refine ⟨out, ?_, ?_⟩
      · simp [chopprefixChar, hi, hfirst, heq, hn, ho, bind, pure, Except.bind, Except.pure]
      · simpa [heq] using hv
    | false =>
      obtain ⟨out, ho, hv⟩ := hw
      refine ⟨out, ?_, ?_⟩
      · simp [chopprefixChar, hi, hfirst, heq, ho, bind, Except.bind]
      · simpa [heq] using hv

def ChopSuffixSequence : Prop :=
  ∀ {S P RS RP R C E : Type} [BEq C] [LawfulBEq C]
    (reverseS : S → RS) (reverseP : P → RP)
    (firstS : RS → Except E (Option (C × Index)))
    (firstP : RP → Except E (Option (C × Index)))
    (iterateS : RS → Index → Except E (Option (C × Index)))
    (iterateP : RP → Index → Except E (Option (C × Index)))
    (boundS : RS → Nat) (boundP : RP → Nat) (lastindex firstindex : S → Index)
    (empty : S → Except E R) (through : S → Index → Index → Except E R)
    (whole : S → Except E R) (observe : R → List C) (s : S) (suf : P)
    (source sufChars : List C) (i j : Option (C × Index)),
    firstS (reverseS s) = .ok i → firstP (reverseP suf) = .ok j →
    iterateS (reverseS s) (lastindex s) = .ok i →
    CharacterTrace (iterateS (reverseS s)) i source.reverse →
    CharacterTrace (iterateP (reverseP suf)) j sufChars.reverse →
    sufChars.length ≤ boundP (reverseP suf) →
    (∃ out, empty s = .ok out ∧ (observe out).reverse = []) →
    (∃ out, whole s = .ok out ∧ observe out = source) →
    (∀ k current chars,
      iterateS (reverseS s) k = .ok current →
      CharacterTrace (iterateS (reverseS s)) current chars →
      ∃ out, through s (firstindex s) k = .ok out ∧ (observe out).reverse = chars) →
    ∃ out,
      chopsuffix reverseS reverseP firstS firstP iterateS iterateP boundS boundP
        lastindex firstindex empty through whole (fun c d => c == d) s suf = .ok out ∧
      (observe out).reverse =
        if sufChars.reverse.isPrefixOf source.reverse then source.reverse.drop sufChars.length
        else source.reverse

theorem chopSuffixSequence_proven : ChopSuffixSequence := by
  intro S P RS RP R C E inst lawful reverseS reverseP firstS firstP iterateS iterateP
    boundS boundP lastindex firstindex empty through whole observe s suf source sufChars
    i j ha hb hc hi hj hf he hw hs
  have loops : ∀ fuel k i j,
      chopsuffix.loop iterateS iterateP firstindex empty through whole (fun c d => c == d)
        s (reverseS s) (reverseP suf) fuel k i j =
      chopprefix.loop iterateS iterateP (fun _ => empty s)
        (fun _ k => through s (firstindex s) k) (fun _ => whole s)
        (fun c d => c == d) (reverseS s) (reverseP suf) fuel k i j := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ n ih =>
      intro k i j
      cases j with
      | none => cases i <;> rfl
      | some p =>
        cases i with
        | none => rfl
        | some q => simp [chopsuffix.loop, chopprefix.loop, ih]
  have hwhole : ∃ out, whole s = .ok out ∧ (observe out).reverse = source.reverse := by
    obtain ⟨out, ho, hv⟩ := hw
    exact ⟨out, ho, congrArg List.reverse hv⟩
  obtain ⟨out, ho, hv⟩ := chopPrefixLoop_correct iterateS iterateP (fun _ => empty s)
    (fun _ k => through s (firstindex s) k) (fun _ => whole s)
    (fun out => (observe out).reverse) (reverseS s) (reverseP suf) source.reverse
    he hwhole hs sufChars.reverse source.reverse
    (boundS (reverseS s) + boundP (reverseP suf) + 1)
    (lastindex s) i j hc hi hj (by simp only [List.length_reverse]; omega)
  refine ⟨out, ?_, ?_⟩
  · simp only [chopsuffix, ha, hb, bind, Except.bind, loops]
    exact ho
  · simpa only [List.length_reverse] using hv

def ChopSuffixCharacter : Prop :=
  ∀ {S R C E : Type} [BEq C] [LawfulBEq C]
    (isempty : S → Bool) (last : S → Except E C) (firstindex lastindex : S → Index)
    (prevind : S → Index → Except E Index)
    (through : S → Index → Index → Except E R) (whole : S → Except E R)
    (observe : R → List C) (s : S) (c : C) (source : List C),
    isempty s = source.isEmpty →
    (∃ out, whole s = .ok out ∧ observe out = source) →
    (∀ head tail, source.reverse = head :: tail →
      last s = .ok head ∧
      ∃ previous out, prevind s (lastindex s) = .ok previous ∧
        through s (firstindex s) previous = .ok out ∧ (observe out).reverse = tail) →
    ∃ out,
      chopsuffixChar isempty last firstindex lastindex prevind through whole
        (fun a b => a == b) s c = .ok out ∧
      (observe out).reverse = match source.reverse with
        | [] => []
        | head :: tail => if head == c then tail else head :: tail

theorem chopSuffixCharacter_proven : ChopSuffixCharacter := by
  intro S R C E inst lawful isempty last firstindex lastindex prevind through whole observe
    s c source hi hw hs
  have hwhole : ∃ out, whole s = .ok out ∧ (observe out).reverse = source.reverse := by
    obtain ⟨out, ho, hv⟩ := hw
    exact ⟨out, ho, congrArg List.reverse hv⟩
  have h := chopPrefixCharacter_proven isempty last lastindex prevind
    (fun s i => through s (firstindex s) i) whole (fun out => (observe out).reverse)
    s c source.reverse (by simpa using hi) hwhole hs
  exact h

private theorem prefixLoop_correct
    {S T RA RB C CU1 CU2 CT1 CT2 E : Type} [BEq C] [LawfulBEq C]
    (opsA : StringOps S RA C CU1 CT1 E) (opsB : StringOps T RB C CU2 CT2 E)
    (a : S) (b : T) :
    ∀ (pre source : List C) (fuel : Nat)
      (i j : Option (C × Index)),
      CharacterTrace (opsA.iterateAt a) i source →
      CharacterTrace (opsB.iterateAt b) j pre →
      pre.length < fuel →
      startswith.loop opsA opsB (fun c d => c == d) a b fuel i j =
        .ok (pre.isPrefixOf source) := by
  intro pre
  induction pre with
  | nil =>
    intro source fuel i j hi hj hf
    cases hj
    cases fuel with
    | zero => omega
    | succ n => simp [startswith.loop]
  | cons d pre ih =>
    intro source fuel i j hi hj hf
    cases hj with
    | cons hb htailB =>
      cases fuel with
      | zero => omega
      | succ n =>
        cases hi with
        | nil => simp [startswith.loop, List.isPrefixOf]
        | @cons c k current rest ha htailA =>
          have hsym : (d == c) = (c == d) := by
            apply Bool.eq_iff_iff.mpr
            constructor
            · intro h
              have he : d = c := eq_of_beq h
              subst d
              simp
            · intro h
              have he : c = d := eq_of_beq h
              subst d
              simp
          cases heq : (c == d) with
          | false =>
            simp [startswith.loop, heq, List.isPrefixOf, hsym]
          | true =>
            have hrec := ih rest n current _ htailA htailB (by simp at hf; omega)
            simpa [startswith.loop, heq, ha, hb, List.isPrefixOf, hsym,
              bind, pure, Except.bind, Except.pure] using hrec

def PrefixSequence : Prop :=
  ∀ {S T RA RB C CU1 CU2 CT1 CT2 E : Type} [BEq C] [LawfulBEq C]
    (opsA : StringOps S RA C CU1 CT1 E) (opsB : StringOps T RB C CU2 CT2 E)
    (a : S) (b : T) (source pre : List C) (i j : Option (C × Index)),
    opsA.iterateFirst a = .ok i →
    opsB.iterateFirst b = .ok j →
    CharacterTrace (opsA.iterateAt a) i source →
    CharacterTrace (opsB.iterateAt b) j pre →
    pre.length ≤ opsB.iterationBound b →
    startswith opsA opsB (fun c d => c == d) a b = .ok (pre.isPrefixOf source)

theorem prefixSequence_proven : PrefixSequence := by
  intro S T RA RB C CU1 CU2 CT1 CT2 E inst lawful opsA opsB a b source pre i j ha hb hi hj hf
  simp only [startswith, ha, hb, bind, Except.bind]
  exact prefixLoop_correct opsA opsB a b pre source _ i j hi hj (by omega)

def SuffixSequence : Prop :=
  ∀ {S T RA RB R1 R2 C CU1 CU2 CT1 CT2 E : Type} [BEq C] [LawfulBEq C]
    (reverseA : S → RA) (reverseB : T → RB)
    (opsA : StringOps RA R1 C CU1 CT1 E) (opsB : StringOps RB R2 C CU2 CT2 E)
    (a : S) (b : T) (source suffix : List C) (i j : Option (C × Index)),
    opsA.iterateFirst (reverseA a) = .ok i →
    opsB.iterateFirst (reverseB b) = .ok j →
    CharacterTrace (opsA.iterateAt (reverseA a)) i source.reverse →
    CharacterTrace (opsB.iterateAt (reverseB b)) j suffix.reverse →
    suffix.length ≤ opsB.iterationBound (reverseB b) →
    endswith reverseA reverseB opsA opsB (fun c d => c == d) a b =
      .ok (suffix.reverse.isPrefixOf source.reverse)

theorem suffixSequence_proven : SuffixSequence := by
  intro S T RA RB R1 R2 C CU1 CU2 CT1 CT2 E inst lawful reverseA reverseB
    opsA opsB a b source suffix i j ha hb hi hj hf
  have hmodel :
      endswith reverseA reverseB opsA opsB (fun c d => c == d) a b =
      startswith opsA opsB (fun c d => c == d) (reverseA a) (reverseB b) := by
    have loops : ∀ fuel i j,
        endswith.loop opsA opsB (fun c d => c == d) (reverseA a) (reverseB b) fuel i j =
        startswith.loop opsA opsB (fun c d => c == d) (reverseA a) (reverseB b) fuel i j := by
      intro fuel
      induction fuel with
      | zero => intros; rfl
      | succ n ih =>
        intro i j
        cases j with
        | none => rfl
        | some p =>
          cases i with
          | none => rfl
          | some q =>
            simp [endswith.loop, startswith.loop, ih]
    simp only [endswith, startswith, ha, hb, bind, Except.bind]
    apply loops
  rw [hmodel]
  exact prefixSequence_proven opsA opsB (reverseA a) (reverseB b)
    source.reverse suffix.reverse i j ha hb hi hj (by simpa using hf)

/-! ## Empty prefixes and character sets -/

def StartsWithEmptyPrefix : Prop :=
  ∀ {S T RA RB C D CU1 CU2 CT1 CT2 E : Type}
    (opsA : StringOps S RA C CU1 CT1 E) (opsB : StringOps T RB D CU2 CT2 E)
    (equalChar : C → D → Bool) (a : S) (b : T) (firstA : Option (C × Index)),
    opsA.iterateFirst a = .ok firstA →
    opsB.iterateFirst b = .ok none →
    startswith opsA opsB equalChar a b = .ok true

theorem startsWithEmptyPrefix_proven : StartsWithEmptyPrefix := by
  intro S T RA RB C D CU1 CU2 CT1 CT2 E opsA opsB equalChar a b firstA ha hb
  simp [startswith, startswith.loop, ha, hb, Bind.bind, Except.bind]

def EndsWithEmptySuffix : Prop :=
  ∀ {S T RA RB R1 R2 C D CU1 CU2 CT1 CT2 E : Type}
    (reverseA : S → RA) (reverseB : T → RB)
    (opsA : StringOps RA R1 C CU1 CT1 E) (opsB : StringOps RB R2 D CU2 CT2 E)
    (equalChar : C → D → Bool) (a : S) (b : T) (firstA : Option (C × Index)),
    opsA.iterateFirst (reverseA a) = .ok firstA →
    opsB.iterateFirst (reverseB b) = .ok none →
    endswith reverseA reverseB opsA opsB equalChar a b = .ok true

theorem endsWithEmptySuffix_proven : EndsWithEmptySuffix := by
  intro S T RA RB R1 R2 C D CU1 CU2 CT1 CT2 E reverseA reverseB opsA opsB equalChar a b firstA ha hb
  simp [endswith, endswith.loop, ha, hb, Bind.bind, Except.bind]

def StartsWithCharsEmpty : Prop :=
  ∀ {S Q C E : Type} (isempty : S → Bool) (first : S → Except E C)
    (member : C → Q → Bool) (str : S) (chars : Q),
    isempty str = true →
    startswithChars isempty first member str chars = .ok false

theorem startsWithCharsEmpty_proven : StartsWithCharsEmpty := by
  intro S Q C E isempty first member str chars h
  unfold startswithChars
  rw [if_pos h]
  rfl

def EndsWithCharsEmpty : Prop :=
  ∀ {S Q C E : Type} (isempty : S → Bool) (last : S → Except E C)
    (member : C → Q → Bool) (str : S) (chars : Q),
    isempty str = true →
    endswithChars isempty last member str chars = .ok false

theorem endsWithCharsEmpty_proven : EndsWithCharsEmpty := by
  intro S Q C E isempty last member str chars h
  unfold endswithChars
  rw [if_pos h]
  rfl

/-! ## Padding and replacement boundaries -/

def StartswithCharacterSet : Prop :=
  ∀ {S Q C E : Type} (isempty : S → Bool) (first : S → Except E C)
    (member : C → Q → Bool) (characters : S → List C) (members : Q → List C),
    (∀ s, isempty s = (characters s).isEmpty) →
    (∀ s c rest, characters s = c :: rest → first s = .ok c) →
    (∀ c q, member c q = true ↔ c ∈ members q) →
    ∀ s q,
    ∃ result, startswithChars isempty first member s q = .ok result ∧
      (result = true ↔ ∃ c rest, characters s = c :: rest ∧ c ∈ members q)

theorem startswithCharacterSet_proven : StartswithCharacterSet := by
  intro S Q C E isempty first member characters members hEmpty hFirst hMember s q
  cases hc : characters s with
  | nil =>
    have hi : isempty s = true := by simpa [hc] using hEmpty s
    exact ⟨false, by simp [startswithChars, hi, pure, Except.pure], by simp [hc]⟩
  | cons c rest =>
    have hi : isempty s = false := by simpa [hc] using hEmpty s
    refine ⟨member c q, ?_, ?_⟩
    · simp [startswithChars, hi, hFirst s c rest hc, bind, Except.bind, pure, Except.pure]
    · constructor
      · intro h
        exact ⟨c, rest, rfl, (hMember c q).mp h⟩
      · intro ⟨c', rest', heq, hm⟩
        cases heq
        exact (hMember c q).mpr hm

def EndswithCharacterSet : Prop :=
  ∀ {S Q C E : Type} (isempty : S → Bool) (last : S → Except E C)
    (member : C → Q → Bool) (reverseCharacters : S → List C) (members : Q → List C),
    (∀ s, isempty s = (reverseCharacters s).isEmpty) →
    (∀ s c rest, reverseCharacters s = c :: rest → last s = .ok c) →
    (∀ c q, member c q = true ↔ c ∈ members q) →
    ∀ s q,
    ∃ result, endswithChars isempty last member s q = .ok result ∧
      (result = true ↔ ∃ c rest, reverseCharacters s = c :: rest ∧ c ∈ members q)

theorem endswithCharacterSet_proven : EndswithCharacterSet := by
  intro S Q C E isempty last member reverseCharacters members hEmpty hLast hMember s q
  simpa [endswithChars, startswithChars] using
    startswithCharacterSet_proven isempty last member reverseCharacters members hEmpty hLast hMember s q

def LpadNoPadding : Prop :=
  ∀ {S C R O N E FS : Type} (ops : PadValueOps S C R O N E)
    (remOps : PadRemainderOps S C R FS E) (s p : PadInput S C) (n : N)
    (converted width : Index),
    ops.toInt n = .ok converted →
    ops.textwidth s = .ok width →
    (ops.signed converted).val ≤ width.val →
    (lpad ops remOps s p n =
      ops.assemble (ops.isAnnotated s || ops.isAnnotated p) [.value s] ∧
    rpad ops remOps s p n =
      ops.assemble (ops.isAnnotated s || ops.isAnnotated p) [.value s])

def lpadOverflowIndex : Index := int (-((2 : Int) ^ 63))

def lpadOverflowOps : PadValueOps Unit Unit Unit String Index String where
  toInt n := .ok n
  signed n := n
  textwidth _ := .ok (int 1)
  isAnnotated _ := false
  repr _ := ""
  ncodeunits _ := 1
  isString _ := true
  codeunitIsUInt8 _ := true
  argumentError message := message
  divrem m l := if l.val == 1 then .ok (m, int 0) else .ok (int 0, int 0)
  repeatPad _ q := if 0 < q.val then .error "OutOfMemoryError" else .ok (.string ())
  assemble _ _ := .ok ""

def lpadOverflowRemainderOps :
    PadRemainderOps Unit Unit Unit Unit String where
  textwidthChar _ := .ok (int 1)
  pairsFirst _ := .ok none
  pairsNext _ _ := .ok none
  pairsBound _ := 0
  viewPrefix _ _ := .ok ()
  whole _ := .ok ()

theorem lpadNoPadding_refuted : ¬ LpadNoPadding := by
  intro h
  let s : PadInput Unit Unit := .string ()
  have hspec := h lpadOverflowOps lpadOverflowRemainderOps s s lpadOverflowIndex
    lpadOverflowIndex (int 1) rfl rfl (by decide)
  have hrun :
      lpad lpadOverflowOps lpadOverflowRemainderOps s s lpadOverflowIndex =
        .error "OutOfMemoryError" := by
    have hsub : (lpadOverflowIndex - int 1).val = 9223372036854775807 := by decide
    have hwidth : (int 1).val = 1 := by decide
    simp only [lpad, Bind.bind, Except.bind, lpadOverflowOps, hsub, hwidth]
    simp [hsub, hwidth]
  have hleft := hspec.1
  rw [hrun] at hleft
  have hfalse : False := by
    have hbad : Except.error "OutOfMemoryError" = Except.ok "" := by
      simpa [lpadOverflowOps] using hleft
    cases hbad
  exact hfalse


def characterHexIterator :
    HexIteratorOps (List UInt32) UInt32 UInt32 (List UInt32) String where
  length xs := int xs.length
  iterateFirst xs := .ok (match xs with
    | [] => none
    | c :: rest => some (.abstractChar c, rest))
  iterateNext _ rest := .ok (match rest with
    | [] => none
    | c :: tail => some (.abstractChar c, tail))

def hexByteArrayOps : ByteArrayOps (List UInt8) Nat String where
  length xs := int xs.length
  eachindex xs := List.range xs.length
  set xs i c := if i < xs.length then .ok (xs.set i c) else .error "BoundsError"

def hexTuple (value : Option (HexDigit UInt32 UInt32 × List UInt32)) :
    Except String (HexDigit UInt32 UInt32 × List UInt32) :=
  match value with
  | some pair => .ok pair
  | none => .error "TypeError"

def charToByte (c : UInt32) : Except String UInt8 :=
  if c.toNat < 256 then .ok (UInt8.ofNat c.toNat) else .error "InexactError"

/-- The `hex2bytes` decoding path for an iterator of characters: allocate the destination
and decode through the source-mirrored `number_from_hex` conversions. -/
def asciiHex2bytes (chars : List UInt32) : Except String (List UInt8) :=
  hex2bytesWrapper (fun xs : List UInt32 => int xs.length)
    (fun n => int (n.val / 2)) (fun n => .ok (List.replicate n.val.toNat (0 : UInt8)))
    (hex2bytesBang hexByteArrayOps characterHexIterator hexTuple
      (fun _ => "ArgumentError") (fun c => .ok c) charToByte true) chars

def Hex2bytesAsciiArgError : Prop :=
  ∀ chars : List UInt32,
    (∀ c ∈ chars, c.toNat < 128) →
    chars.length ≤ JuliaLean.IntTy.i64.max.toNat →
    ∃ out,
      asciiHex2bytes chars = .ok out ∨
      asciiHex2bytes chars = .error "ArgumentError"

/-- Every ASCII character either decodes to a byte through `number_from_hex` or raises
its argument error. -/
private theorem asciiHexDigitDecodes (c : UInt32) (hc : c.toNat < 128) :
    (∃ v : UInt8,
      numberFromHex (fun _ => "ArgumentError") (fun c => .ok c) charToByte
          (HexDigit.abstractChar c) = .ok v) ∨
    numberFromHex (fun _ => "ArgumentError") (fun c => .ok c) charToByte
      (HexDigit.abstractChar c) = .error "ArgumentError" := by
  have hbyte : charToByte c = .ok (UInt8.ofNat c.toNat) := by
    simp only [charToByte]
    rw [if_pos (by omega)]
  simp only [numberFromHex, numberFromHexAbstract, numberFromHexChar, hbyte, bind,
    Except.bind, pure, Except.pure]
  simp only [numberFromHexByte, throw, throwThe, MonadExceptOf.throw]
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl

/-- The character iterator advances from a cons state to its tail. -/
private theorem charIterNext (itr s : List UInt32) (c : UInt32) (t : List UInt32)
    (hs : s = c :: t) :
    characterHexIterator.iterateNext itr s = .ok (some (HexDigit.abstractChar c, t)) := by
  simp [characterHexIterator, hs]

/-- The iterator invariant supplies two input characters per destination byte. -/
private theorem hexAsciiLoopSettles :
    ∀ (indices : List Nat) (itr : List UInt32) (dest : List UInt8) (rem : List UInt32) (c : UInt32),
    (∀ x ∈ c :: rem, x.toNat < 128) →
    rem.length + 1 = 2 * indices.length →
    (∀ i ∈ indices, i < dest.length) →
    ∃ out,
      hex2bytesBang.loop hexByteArrayOps characterHexIterator hexTuple
          (fun _ => "ArgumentError") (fun c => .ok c) charToByte itr
          indices dest (some (HexDigit.abstractChar c, rem)) = .ok out ∨
      hex2bytesBang.loop hexByteArrayOps characterHexIterator hexTuple
          (fun _ => "ArgumentError") (fun c => .ok c) charToByte itr
          indices dest (some (HexDigit.abstractChar c, rem)) =
        .error "ArgumentError" := by
  intro indices
  induction indices with
  | nil =>
    intro itr dest rem c _ _ _
    exact ⟨_, Or.inl rfl⟩
  | cons i is ih =>
    intro itr dest rem c hascii hlen hidx
    obtain ⟨y, rest, hrest⟩ : ∃ y r, rem = y :: r := by
      cases rem with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y r => exact ⟨y, r, rfl⟩
    subst hrest
    have hyascii : y.toNat < 128 := hascii y (by simp)
    have hrestlen : rest.length = 2 * is.length := by
      simp only [List.length_cons] at hlen
      omega
    cases is with
    | nil =>
      have hrestnil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons z r =>
          exfalso
          simp only [List.length_nil, List.length_cons] at hrestlen
          omega
      subst hrestnil
      rcases asciiHexDigitDecodes c (hascii c (by simp)) with ⟨vH, hH⟩ | hH
      · rcases asciiHexDigitDecodes y hyascii with ⟨vL, hL⟩ | hL
        · have hid : i < dest.length := hidx i (by simp)
          refine ⟨dest.set i ((vH <<< 4) + vL), Or.inl ?_⟩
          simp [hex2bytesBang.loop, hexTuple, characterHexIterator, hexByteArrayOps,
            hid, hH, hL, bind, Except.bind, pure, Except.pure]
        · refine ⟨[], Or.inr ?_⟩
          simp [hex2bytesBang.loop, hexTuple, characterHexIterator, hH, hL,
            bind, Except.bind, pure, Except.pure]
      · refine ⟨[], Or.inr ?_⟩
        simp [hex2bytesBang.loop, hexTuple, characterHexIterator, hH,
          bind, Except.bind, pure, Except.pure]
    | cons i' is' =>
      obtain ⟨z, rest', hrest'⟩ : ∃ z r, rest = z :: r := by
        cases rest with
        | nil =>
          exfalso
          rw [List.length_nil] at hrestlen
          simp only [List.length_cons] at hrestlen
          omega
        | cons z r => exact ⟨z, r, rfl⟩
      subst hrest'
      have hzascii : ∀ x ∈ z :: rest', x.toNat < 128 := by
        intro x hx
        exact hascii x (by simp [hx])
      have hzlen : rest'.length + 1 = 2 * (i' :: is').length := by
        simp only [List.length_cons] at hlen ⊢
        omega
      have hnext := charIterNext itr (z :: rest') z rest' rfl
      rcases asciiHexDigitDecodes c (hascii c (by simp)) with ⟨vH, hH⟩ | hH
      · rcases asciiHexDigitDecodes y hyascii with ⟨vL, hL⟩ | hL
        · have hid : i < dest.length := hidx i (by simp)
          have hsetlen : (dest.set i ((vH <<< 4) + vL)).length = dest.length := by simp
          obtain ⟨out, hout⟩ := ih itr (dest.set i ((vH <<< 4) + vL)) rest' z hzascii hzlen
            (by intro j hj; simpa [hsetlen] using hidx j (by simp [hj]))
          rcases hout with houtok | houterr
          · refine ⟨out, Or.inl ?_⟩
            rw [hex2bytesBang.loop]
            simpa [hexTuple, characterHexIterator, hexByteArrayOps, hid, hH, hL,
              bind, Except.bind, pure, Except.pure] using houtok
          · refine ⟨[], Or.inr ?_⟩
            rw [hex2bytesBang.loop]
            simpa [hexTuple, characterHexIterator, hexByteArrayOps, hid, hH, hL,
              bind, Except.bind, pure, Except.pure] using houterr
        · refine ⟨[], Or.inr ?_⟩
          simp [hex2bytesBang.loop, hexTuple, characterHexIterator, hH, hL, hnext,
            bind, Except.bind, pure, Except.pure]
      · refine ⟨[], Or.inr ?_⟩
        simp [hex2bytesBang.loop, hexTuple, characterHexIterator, hH, hnext,
          bind, Except.bind, pure, Except.pure]

private theorem hexLengthVal (n : Nat) (hfit : n ≤ JuliaLean.IntTy.i64.max.toNat) :
    (int n).val = (n : Int) := by
  have hminle : JuliaLean.IntTy.i64.min ≤ (0 : Int) := by decide
  have hmaxge : (0 : Int) ≤ JuliaLean.IntTy.i64.max := by decide
  change JuliaLean.wrapInt .i64 (n : Int) = _
  exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩

private theorem hexAllocationLength (n : Nat) (hfit : n ≤ JuliaLean.IntTy.i64.max.toNat) :
    (int ((int n).val / 2)).val.toNat = n / 2 := by
  calc
    (int ((int n).val / 2)).val.toNat =
        (int ((n : Int) / 2)).val.toNat :=
      congrArg (fun x : Int => (int (x / 2)).val.toNat) (hexLengthVal n hfit)
    _ = (int (((n / 2 : Nat) : Int))).val.toNat :=
      congrArg (fun x : Int => (int x).val.toNat) (by omega)
    _ = (((n / 2 : Nat) : Int)).toNat :=
      congrArg Int.toNat (hexLengthVal (n / 2) (by omega))
    _ = n / 2 := by omega

private theorem hexWrapperAllocation
    (decode : List UInt8 → List UInt32 → Except String (List UInt8))
    (chars : List UInt32) :
    hex2bytesWrapper (fun xs : List UInt32 => int xs.length)
      (fun n => int (n.val / 2))
      (fun n => .ok (List.replicate n.val.toNat (0 : UInt8))) decode chars =
    decode (List.replicate (int ((int chars.length).val / 2)).val.toNat 0) chars := by
  rfl

private theorem asciiHexAllocation (chars : List UInt32)
    (hfit : chars.length ≤ JuliaLean.IntTy.i64.max.toNat) :
    asciiHex2bytes chars =
      hex2bytesBang hexByteArrayOps characterHexIterator hexTuple
        (fun _ => "ArgumentError") (fun c => .ok c) charToByte true
        (List.replicate (chars.length / 2) (0 : UInt8)) chars := by
  exact (hexWrapperAllocation
    (hex2bytesBang hexByteArrayOps characterHexIterator hexTuple
      (fun _ => "ArgumentError") (fun c => .ok c) charToByte true) chars).trans (congrArg
    (fun n : Nat =>
      hex2bytesBang hexByteArrayOps characterHexIterator hexTuple
        (fun _ => "ArgumentError") (fun c => .ok c) charToByte true
        (List.replicate n (0 : UInt8)) chars)
    (hexAllocationLength chars.length hfit))

theorem hex2bytesAsciiArgError_proven : Hex2bytesAsciiArgError := by
  intro chars hascii hfit
  rw [asciiHexAllocation chars hfit]
  have hlen : (characterHexIterator.length chars).val = (chars.length : Int) :=
    hexLengthVal chars.length hfit
  unfold hex2bytesBang
  simp only [hlen]
  split
  · exact ⟨[], Or.inr rfl⟩
  · rename_i heven
    have hmodInt : (chars.length : Int) % 2 = 0 := by simpa using heven
    split
    · exact ⟨[], Or.inr rfl⟩
    · split
      · exact ⟨_, Or.inl rfl⟩
      · rename_i hnonzero
        cases chars with
        | nil => exact False.elim (hnonzero rfl)
        | cons c rem =>
          have hpairlen : rem.length + 1 = 2 * ((c :: rem).length / 2) := by
            simp only [List.length_cons] at hmodInt ⊢
            omega
          obtain ⟨out, hout⟩ := hexAsciiLoopSettles
            (List.range ((c :: rem).length / 2)) (c :: rem)
            (List.replicate ((c :: rem).length / 2) (0 : UInt8)) rem c hascii
            (by simpa using hpairlen)
            (by intro i hi; simpa using List.mem_range.mp hi)
          refine ⟨out, ?_⟩
          simpa only [characterHexIterator, hexByteArrayOps, List.length_replicate,
            bind, Except.bind] using hout

def StreamReplaceCountEdge : Prop :=
  ∀ {S P Q R IO E : Type} (ops : ReplaceEngineOps S P Q R IO IO E)
    (streamBytes : IO → List UInt8) (stringBytes : S → List UInt8),
    (∀ io s, ∃ out, ops.writeString io s = .ok out ∧
      streamBytes out = streamBytes io ++ stringBytes s) →
    ∀ io s pairs count,
    (count.val = 0 →
      ∃ out, replaceIOEngine ops io s pairs count = .ok out ∧
        streamBytes out = streamBytes io ++ stringBytes s) ∧
    (count.val < 0 →
      replaceIOEngine ops io s pairs count = .error (ops.initOps.domainError count))

theorem streamReplaceCountEdge_proven : StreamReplaceCountEdge := by
  intro S P Q R IO E ops streamBytes stringBytes writeLaw io s pairs count
  constructor
  · intro hzero
    obtain ⟨out, ho, hb⟩ := writeLaw io s
    exact ⟨out, by simp [replaceIOEngine, hzero, ho], hb⟩
  · intro hnegative
    have hzero : count.val ≠ 0 := by omega
    simp [replaceIOEngine, replaceInit, hzero, hnegative, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]

def ReplacementShownByteCount : Prop :=
  ∀ {IO R S Pat E : Type}
    (applicablePosition : IO → Bool) (position : IO → Except E Index)
    (print : IO → R → Except E IO) (repr : R → String)
    (write : IO → String → Except E (IO × Index)) (observe : IO → List UInt8)
    (io afterIO : IO) (repl : R) (s : S) (range : ReplaceRange) (pattern : Pat)
    (before after : Index) (printed : List UInt8),
    applicablePosition io = true →
    position io = .ok before →
    print io repl = .ok afterIO →
    position afterIO = .ok after →
    before.val = Int.ofNat (observe io).length →
    after.val = Int.ofNat (observe afterIO).length →
    observe afterIO = observe io ++ printed →
    ∃ count,
      replaceShown applicablePosition position print repr write io repl s range pattern =
        .ok (afterIO, count) ∧
      count.val = Int.ofNat printed.length

theorem replacementShownByteCount_proven : ReplacementShownByteCount := by
  intro IO R S Pat E applicablePosition position print repr write observe io afterIO repl s range
    pattern before after printed happ hp hprint hq hbefore hafter hprinted
  have hbeforeNonnegative : 0 ≤ before.val := by rw [hbefore]; exact Int.ofNat_zero_le _
  have hnonnegative : 0 ≤ after.val - before.val := by
    rw [hafter, hbefore, hprinted]
    simp
    omega
  have hlow : JuliaLean.IntTy.i64.min ≤ after.val - before.val :=
    Int.le_trans (by decide) hnonnegative
  have hhigh : after.val - before.val ≤ JuliaLean.IntTy.i64.max := by
    have hbound := after.property.2
    omega
  have hdelta : (after - before).val = after.val - before.val := by
    change JuliaLean.wrapInt .i64 (after.val - before.val) = _
    exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨hlow, hhigh⟩
  refine ⟨after - before, ?_, ?_⟩
  · simp [replaceShown, happ, hp, hprint, hq, bind, Except.bind, pure, Except.pure]
  · rw [hdelta, hafter, hbefore, hprinted]
    simp
    omega

/-! ## Dense prefix and suffix specifications -/

def DensePrefixExact : Prop :=
  ∀ {S E : Type} (ops : DenseStringOps S E) (a b : S)
    (comparison : Int) (next : Index),
    ops.memcmp a b (ops.sizeof b) = .ok comparison →
    ops.nextind a (ops.ncodeunits b) = .ok next →
    (startswithDense ops a b = .ok true ↔
      (ops.ncodeunits b).val ≤ (ops.ncodeunits a).val ∧
      comparison = 0 ∧ next.val = (ops.ncodeunits b + int 1).val)

theorem densePrefixExact_proven : DensePrefixExact := by
  intro S E ops a b comparison next hc hn
  by_cases hl : (ops.ncodeunits a).val < (ops.ncodeunits b).val
  · have hnot : ¬ (ops.ncodeunits b).val ≤ (ops.ncodeunits a).val := by omega
    simp [startswithDense, hl, hnot, pure, Except.pure]
  · by_cases hz : comparison = 0
    · simp [startswithDense, hl, hc, hz, hn, bind, pure, Except.bind, Except.pure]
      omega
    · simp [startswithDense, hl, hc, hz, bind, pure, Except.bind, Except.pure]

def DenseSuffixExact : Prop :=
  ∀ {S E : Type} (ops : DenseStringOps S E) (a b : S)
    (comparison : Int) (start : Index),
    ops.memcmpFrom a (ops.ncodeunits a - ops.ncodeunits b + int 1) b (ops.sizeof b) =
      .ok comparison →
    ops.thisind a (ops.ncodeunits a - ops.ncodeunits b + int 1) = .ok start →
    (endswithDense ops a b = .ok true ↔
      1 ≤ (ops.ncodeunits a - ops.ncodeunits b + int 1).val ∧
      comparison = 0 ∧ start.val = (ops.ncodeunits a - ops.ncodeunits b + int 1).val)

theorem denseSuffixExact_proven : DenseSuffixExact := by
  intro S E ops a b comparison start hc hn
  by_cases hl : (ops.ncodeunits a - ops.ncodeunits b + int 1).val < 1
  · have hnot : ¬ 1 ≤ (ops.ncodeunits a - ops.ncodeunits b + int 1).val := by omega
    simp [endswithDense, hl, hnot, pure, Except.pure]
  · by_cases hz : comparison = 0
    · simp [endswithDense, hl, hc, hz, hn, bind, pure, Except.bind, Except.pure]
      omega
    · simp [endswithDense, hl, hc, hz, bind, pure, Except.bind, Except.pure]

def DenseFastPrefixExact : Prop :=
  ∀ {D F E : Type} (ops : DenseStringOps D E) (toDense : F → D)
    (a b : F) (comparison : Int) (next : Index),
    ops.memcmp (toDense a) (toDense b) (ops.sizeof (toDense b)) = .ok comparison →
    ops.nextind (toDense a) (ops.ncodeunits (toDense b)) = .ok next →
    (startswithFast ops toDense a b = .ok true ↔
      (ops.ncodeunits (toDense b)).val ≤ (ops.ncodeunits (toDense a)).val ∧
      comparison = 0 ∧ next.val = (ops.ncodeunits (toDense b) + int 1).val)

theorem denseFastPrefixExact_proven : DenseFastPrefixExact := by
  intro D F E ops toDense a b comparison next hc hn
  exact densePrefixExact_proven ops (toDense a) (toDense b) comparison next hc hn

/-! Byte observations give the public contract independently of the comparison's numeric result.
The hypotheses are the documented interfaces of ncodeunits, memcmp and character boundaries. -/
def DensePrefixBytes : Prop :=
  ∀ {S E : Type} (ops : DenseStringOps S E) (bytes : S → List UInt8)
    (boundary : S → Nat → Prop) (a b : S) (comparison : Int) (next : Index),
    (ops.ncodeunits a).val = Int.ofNat (bytes a).length →
    (ops.ncodeunits b).val = Int.ofNat (bytes b).length →
    ops.memcmp a b (ops.sizeof b) = .ok comparison →
    (comparison = 0 ↔ (bytes a).take (bytes b).length = bytes b) →
    ops.nextind a (ops.ncodeunits b) = .ok next →
    (next.val = (ops.ncodeunits b + int 1).val ↔ boundary a (bytes b).length) →
    (startswithDense ops a b = .ok true ↔
      (bytes b).length ≤ (bytes a).length ∧
      (bytes a).take (bytes b).length = bytes b ∧ boundary a (bytes b).length) ∧
    (∀ (F : Type) (toDense : F → S) (fa fb : F),
      toDense fa = a → toDense fb = b →
      (startswithFast ops toDense fa fb = .ok true ↔
        (bytes b).length ≤ (bytes a).length ∧
        (bytes a).take (bytes b).length = bytes b ∧ boundary a (bytes b).length))

theorem densePrefixBytes_proven : DensePrefixBytes := by
  intro S E ops bytes boundary a b comparison next hla hlb hc hcmp hn hboundary
  have hspec := densePrefixExact_proven ops a b comparison next hc hn
  rw [hla, hlb, hcmp, hboundary] at hspec
  have hspec' :
      startswithDense ops a b = .ok true ↔
        (bytes b).length ≤ (bytes a).length ∧
        (bytes a).take (bytes b).length = bytes b ∧ boundary a (bytes b).length := by
    simpa using hspec
  refine ⟨hspec', ?_⟩
  intro F toDense fa fb ha hb
  simpa only [startswithFast, ha, hb] using hspec'

def DenseSuffixBytes : Prop :=
  ∀ {S E : Type} (ops : DenseStringOps S E) (bytes : S → List UInt8)
    (boundary : S → Nat → Prop) (a b : S) (comparison : Int) (start : Index),
    (1 ≤ (ops.ncodeunits a - ops.ncodeunits b + int 1).val ↔
      (bytes b).length ≤ (bytes a).length) →
    ops.memcmpFrom a (ops.ncodeunits a - ops.ncodeunits b + int 1) b (ops.sizeof b) =
      .ok comparison →
    (comparison = 0 ↔
      ((bytes a).drop ((bytes a).length - (bytes b).length)).take (bytes b).length = bytes b) →
    ops.thisind a (ops.ncodeunits a - ops.ncodeunits b + int 1) = .ok start →
    (start.val = (ops.ncodeunits a - ops.ncodeunits b + int 1).val ↔
      boundary a ((bytes a).length - (bytes b).length)) →
    (endswithDense ops a b = .ok true ↔
      (bytes b).length ≤ (bytes a).length ∧
      ((bytes a).drop ((bytes a).length - (bytes b).length)).take (bytes b).length = bytes b ∧
      boundary a ((bytes a).length - (bytes b).length))

theorem denseSuffixBytes_proven : DenseSuffixBytes := by
  intro S E ops bytes boundary a b comparison start hlength hc hcmp hn hboundary
  have hspec := denseSuffixExact_proven ops a b comparison start hc hn
  rw [hlength, hcmp, hboundary] at hspec
  exact hspec

def PrefixBackendLaw {S E : Type} (ops : DenseStringOps S E)
    (bytes : S → List UInt8) (boundary : S → Nat → Prop) : Prop :=
  (∀ s, (ops.ncodeunits s).val = Int.ofNat (bytes s).length) ∧
  ∀ a b, (bytes b).length ≤ (bytes a).length →
    ∃ comparison next,
      ops.memcmp a b (ops.sizeof b) = .ok comparison ∧
      (comparison = 0 ↔ (bytes a).take (bytes b).length = bytes b) ∧
      ops.nextind a (ops.ncodeunits b) = .ok next ∧
      (next.val = (ops.ncodeunits b + int 1).val ↔ boundary a (bytes b).length)

private theorem fastPrefix_characterization
    {S F E : Type} (ops : DenseStringOps S E)
    (bytes : S → List UInt8) (boundary : S → Nat → Prop)
    (hlaw : PrefixBackendLaw ops bytes boundary) (toDense : F → S) (a b : F) :
    ∃ result, startswithFast ops toDense a b = .ok result ∧
      (result = true ↔
        (bytes (toDense b)).length ≤ (bytes (toDense a)).length ∧
        (bytes (toDense a)).take (bytes (toDense b)).length = bytes (toDense b) ∧
        boundary (toDense a) (bytes (toDense b)).length) := by
  by_cases hlen : (bytes (toDense b)).length ≤ (bytes (toDense a)).length
  · obtain ⟨comparison, next, hc, hcmp, hn, hboundary⟩ := hlaw.2 (toDense a) (toDense b) hlen
    have hnot : ¬ (ops.ncodeunits (toDense a)).val < (ops.ncodeunits (toDense b)).val := by
      rw [hlaw.1, hlaw.1]
      simpa using (Nat.not_lt.mpr hlen)
    have htotal : ∃ result, startswithFast ops toDense a b = .ok result := by
      by_cases hz : comparison = 0
      · refine ⟨next.val == (ops.ncodeunits (toDense b) + int 1).val, ?_⟩
        simp [startswithFast, startswithDense, hnot, hc, hz, hn, bind, pure, Except.bind, Except.pure]
      · exact ⟨false, by
          simp [startswithFast, startswithDense, hnot, hc, hz, bind, pure, Except.bind, Except.pure]⟩
    obtain ⟨result, hr⟩ := htotal
    have hspec := (densePrefixBytes_proven ops bytes boundary (toDense a) (toDense b)
      comparison next (hlaw.1 _) (hlaw.1 _) hc hcmp hn hboundary).2 F toDense a b rfl rfl
    refine ⟨result, hr, ?_⟩
    simpa only [hr, Except.ok.injEq] using hspec
  · have hshort : (ops.ncodeunits (toDense a)).val < (ops.ncodeunits (toDense b)).val := by
      rw [hlaw.1, hlaw.1]
      simpa using (Nat.lt_of_not_ge hlen)
    refine ⟨false, ?_, ?_⟩
    · simp [startswithFast, startswithDense, hshort, pure, Except.pure]
    · simp [hlen]

def ChopPrefixFastBytes : Prop :=
  ∀ {D S R E : Type} (ops : DenseStringOps D E)
    (bytes : D → List UInt8) (boundary : D → Nat → Prop) (toDense : S → D)
    (subFrom : S → Index → Except E R) (whole : S → Except E R)
    (readView : R → List UInt8),
    PrefixBackendLaw ops bytes boundary →
    ∀ s pre,
    (∃ out, whole s = .ok out ∧ readView out = bytes (toDense s)) →
    ((bytes (toDense pre)).length ≤ (bytes (toDense s)).length ∧
      (bytes (toDense s)).take (bytes (toDense pre)).length = bytes (toDense pre) ∧
      boundary (toDense s) (bytes (toDense pre)).length →
      ∃ out, subFrom s (int 1 + ops.ncodeunits (toDense pre)) = .ok out ∧
        readView out = (bytes (toDense s)).drop (bytes (toDense pre)).length) →
    ∃ out,
      chopprefixFast (startswithFast ops toDense) (fun p => ops.ncodeunits (toDense p))
        subFrom whole s pre = .ok out ∧
      (startswithFast ops toDense s pre = .ok true →
        readView out = (bytes (toDense s)).drop (bytes (toDense pre)).length) ∧
      (startswithFast ops toDense s pre = .ok false → readView out = bytes (toDense s))

theorem chopPrefixFastBytes_proven : ChopPrefixFastBytes := by
  intro D S R E ops bytes boundary toDense subFrom whole readView hlaw s pre hw hs
  obtain ⟨result, hr, hspec⟩ := fastPrefix_characterization ops bytes boundary hlaw toDense s pre
  cases result with
  | true =>
    obtain ⟨out, ho, hv⟩ := hs (hspec.mp rfl)
    refine ⟨out, ?_, ?_, ?_⟩
    · simp [chopprefixFast, hr, ho, bind, Except.bind]
    · intro _
      exact hv
    · intro hbad
      rw [hr] at hbad
      cases hbad
  | false =>
    obtain ⟨out, ho, hv⟩ := hw
    refine ⟨out, ?_, ?_, ?_⟩
    · simp [chopprefixFast, hr, ho, bind, Except.bind]
    · intro hbad
      rw [hr] at hbad
      cases hbad
    · intro _
      exact hv

def SuffixBackendLaw {S E : Type} (ops : DenseStringOps S E)
    (bytes : S → List UInt8) (boundary : S → Nat → Prop) : Prop :=
  ∀ a b,
    (1 ≤ (ops.ncodeunits a - ops.ncodeunits b + int 1).val ↔
      (bytes b).length ≤ (bytes a).length) ∧
    ((bytes b).length ≤ (bytes a).length →
      ∃ comparison start,
        ops.memcmpFrom a (ops.ncodeunits a - ops.ncodeunits b + int 1) b (ops.sizeof b) =
          .ok comparison ∧
        (comparison = 0 ↔
          ((bytes a).drop ((bytes a).length - (bytes b).length)).take (bytes b).length = bytes b) ∧
        ops.thisind a (ops.ncodeunits a - ops.ncodeunits b + int 1) = .ok start ∧
        (start.val = (ops.ncodeunits a - ops.ncodeunits b + int 1).val ↔
          boundary a ((bytes a).length - (bytes b).length)))

private theorem fastSuffix_characterization
    {S F E : Type} (ops : DenseStringOps S E)
    (bytes : S → List UInt8) (boundary : S → Nat → Prop)
    (hlaw : SuffixBackendLaw ops bytes boundary) (toDense : F → S) (a b : F) :
    ∃ result, endswithFast ops toDense a b = .ok result ∧
      (result = true ↔
        (bytes (toDense b)).length ≤ (bytes (toDense a)).length ∧
        ((bytes (toDense a)).drop ((bytes (toDense a)).length - (bytes (toDense b)).length)).take
          (bytes (toDense b)).length = bytes (toDense b) ∧
        boundary (toDense a) ((bytes (toDense a)).length - (bytes (toDense b)).length)) := by
  by_cases hlen : (bytes (toDense b)).length ≤ (bytes (toDense a)).length
  · obtain ⟨comparison, start, hc, hcmp, hn, hboundary⟩ := (hlaw (toDense a) (toDense b)).2 hlen
    have hnot : ¬ (ops.ncodeunits (toDense a) - ops.ncodeunits (toDense b) + int 1).val < 1 := by
      have := (hlaw (toDense a) (toDense b)).1.mpr hlen
      omega
    have htotal : ∃ result, endswithFast ops toDense a b = .ok result := by
      by_cases hz : comparison = 0
      · refine ⟨start.val == (ops.ncodeunits (toDense a) - ops.ncodeunits (toDense b) + int 1).val, ?_⟩
        simp [endswithFast, endswithDense, hnot, hc, hz, hn, bind, pure, Except.bind, Except.pure]
      · exact ⟨false, by
          simp [endswithFast, endswithDense, hnot, hc, hz, bind, pure, Except.bind, Except.pure]⟩
    obtain ⟨result, hr⟩ := htotal
    have hspec := denseSuffixBytes_proven ops bytes boundary (toDense a) (toDense b)
      comparison start (hlaw (toDense a) (toDense b)).1 hc hcmp hn hboundary
    refine ⟨result, hr, ?_⟩
    change endswithDense ops (toDense a) (toDense b) = .ok result at hr
    simpa only [hr, Except.ok.injEq] using hspec
  · have hshort : (ops.ncodeunits (toDense a) - ops.ncodeunits (toDense b) + int 1).val < 1 := by
      have hn : ¬ 1 ≤ (ops.ncodeunits (toDense a) - ops.ncodeunits (toDense b) + int 1).val :=
        fun h => hlen ((hlaw (toDense a) (toDense b)).1.mp h)
      omega
    exact ⟨false, by simp [endswithFast, endswithDense, hshort, pure, Except.pure], by simp [hlen]⟩

def ChopSuffixFastBytes : Prop :=
  ∀ {D S R E : Type} (ops : DenseStringOps D E)
    (bytes : D → List UInt8) (boundary : D → Nat → Prop) (toDense : S → D)
    (isempty : S → Bool) (firstindex : S → Index) (prevind : S → Index → Except E Index)
    (substring : S → Index → Index → Except E R) (whole : S → Except E R)
    (readView : R → List UInt8),
    SuffixBackendLaw ops bytes boundary →
    ∀ s suf,
    isempty suf = (bytes (toDense suf)).isEmpty →
    (∃ out, whole s = .ok out ∧ readView out = bytes (toDense s)) →
    ((bytes (toDense suf)) ≠ [] ∧
      (bytes (toDense suf)).length ≤ (bytes (toDense s)).length ∧
      ((bytes (toDense s)).drop ((bytes (toDense s)).length - (bytes (toDense suf)).length)).take
        (bytes (toDense suf)).length = bytes (toDense suf) ∧
      boundary (toDense s) ((bytes (toDense s)).length - (bytes (toDense suf)).length) →
      ∃ stop out,
        prevind s (ops.ncodeunits (toDense s) - ops.ncodeunits (toDense suf) + int 1) = .ok stop ∧
        substring s (firstindex s) stop = .ok out ∧
        readView out = (bytes (toDense s)).take ((bytes (toDense s)).length - (bytes (toDense suf)).length)) →
    ∃ out,
      chopsuffixFast isempty (endswithFast ops toDense)
        (fun s => ops.ncodeunits (toDense s)) (fun s => ops.ncodeunits (toDense s))
        firstindex prevind substring whole s suf = .ok out ∧
      (endswithFast ops toDense s suf = .ok true →
        readView out = (bytes (toDense s)).take ((bytes (toDense s)).length - (bytes (toDense suf)).length)) ∧
      (endswithFast ops toDense s suf = .ok false → readView out = bytes (toDense s))

theorem chopSuffixFastBytes_proven : ChopSuffixFastBytes := by
  intro D S R E ops bytes boundary toDense isempty firstindex prevind substring whole readView
    hlaw s suf hi hw hs
  cases hb : bytes (toDense suf) with
  | nil =>
    obtain ⟨out, ho, hv⟩ := hw
    have hempty : isempty suf = true := by simpa [hb] using hi
    refine ⟨out, ?_, ?_, ?_⟩
    · simp [chopsuffixFast, hempty, ho, bind, Except.bind]
    · intro _
      simpa [hb] using hv
    · intro _
      exact hv
  | cons c tail =>
    have hempty : isempty suf = false := by simpa [hb] using hi
    obtain ⟨result, hr, hspec⟩ := fastSuffix_characterization ops bytes boundary hlaw toDense s suf
    cases result with
    | true =>
      obtain ⟨stop, out, hn, ho, hv⟩ := hs ⟨by simp [hb], hspec.mp rfl⟩
      refine ⟨out, ?_, ?_, ?_⟩
      · simp [chopsuffixFast, hempty, hr, hn, ho, bind, Except.bind]
      · intro _
        simpa only [hb] using hv
      · intro hbad
        rw [hr] at hbad
        cases hbad
    | false =>
      obtain ⟨out, ho, hv⟩ := hw
      refine ⟨out, ?_, ?_, ?_⟩
      · simp [chopsuffixFast, hempty, hr, ho, bind, Except.bind]
      · intro hbad
        rw [hr] at hbad
        cases hbad
      · intro _
        exact hv

def ChopSuffixFaithful : Prop :=
  ChopSuffixSequence ∧ ChopSuffixFastBytes ∧ ChopSuffixCharacter

theorem chopSuffixFaithful_proven : ChopSuffixFaithful :=
  ⟨chopSuffixSequence_proven, chopSuffixFastBytes_proven, chopSuffixCharacter_proven⟩

def ChopAffixes : Prop :=
  ChopPrefixSequence ∧ ChopPrefixFastBytes ∧ ChopPrefixCharacter ∧ ChopSuffixFaithful

theorem chopAffixes_proven : ChopAffixes :=
  ⟨chopPrefixSequence_proven, chopPrefixFastBytes_proven, chopPrefixCharacter_proven,
    chopSuffixFaithful_proven⟩

/-! ## Stream prefix behavior

Stream operations belong to other Julia files. Their ordinary mark/read/reset laws are explicit;
the source methods themselves are `startswithIOUTF8` and `startswithIOChars`.
-/

def StartswithIoPeek : Prop :=
  ∀ {IO S E : Type} (ops : PrefixIOOps IO UInt32 E)
    (ncodeunits : S → Index) (codeunits : S → List UInt8)
    (unread : IO → List UInt8) (position : IO → Int) (io marked read reset : IO)
    (pre : S),
    0 ≤ (ncodeunits pre).val →
    (ncodeunits pre).val.toNat = (codeunits pre).length →
    ops.mark io = .ok marked →
    ops.readBytes marked (ncodeunits pre) =
      .ok ((unread io).take (codeunits pre).length, read) →
    ops.reset read = .ok reset →
    position reset = position io →
    startswithIOUTF8 ops ncodeunits codeunits (fun a b => decide (a = b)) io pre =
      .ok (decide ((unread io).take (codeunits pre).length = codeunits pre), reset) ∧
      position reset = position io

theorem startswithIoPeek_proven : StartswithIoPeek := by
  intro IO S E ops ncodeunits codeunits unread position io marked read reset pre _ _ hm hr hs hp
  exact ⟨by simp [startswithIOUTF8, hm, hr, hs, bind, pure, Except.bind, Except.pure], hp⟩

def StartswithIoChecks : Prop :=
  StartswithIoPeek ∧
  (∀ {IO E : Type} (ops : PrefixIOOps IO UInt32 E)
      (io marked read reset : IO) (c : UInt32) (chars : List UInt32),
    ops.mark io = .ok marked →
    ops.readChar marked = .ok (c, read) →
    ops.reset read = .ok reset →
    startswithIOChars ops (fun x xs => xs.contains x) io chars =
      .ok (decide (c ∈ chars), reset))

theorem startswithIoChecks_proven : StartswithIoChecks := by
  refine ⟨startswithIoPeek_proven, ?_⟩
  intro IO E ops io marked read reset c chars hm hr hs
  simp [startswithIOChars, hm, hr, hs, bind, Except.bind, pure, Except.pure]

def StartswithIoEof : Prop :=
  ∀ {IO E : Type} (ops : PrefixIOOps IO UInt32 E)
    (atEnd : IO → Prop) (io : IO) (chars : List UInt32),
    atEnd io →
    ∃ after, startswithIOChars ops (fun c cs => cs.contains c) io chars = .ok (false, after)

theorem startswithIoEof_refuted : ¬ StartswithIoEof := by
  intro h
  let ops : PrefixIOOps Unit UInt32 String :=
    { mark := fun _ => .ok ()
      readChar := fun _ => .error "EOFError"
      readBytes := fun _ _ => .ok ([], ())
      reset := fun _ => .ok () }
  obtain ⟨after, hbad⟩ := h ops (fun _ => True) () [0x61] trivial
  simp [startswithIOChars, ops, bind, Except.bind] at hbad

/-! ## Hexadecimal input errors and digit values -/

def HexadecimalDigits : Prop :=
  ∀ (argumentError : String → String) (c : UInt8),
    (0x30 ≤ c ∧ c ≤ 0x39 →
      numberFromHexByte argumentError c = .ok (c - 0x30)) ∧
    (0x61 ≤ c ∧ c ≤ 0x66 →
      numberFromHexByte argumentError c = .ok (c - 0x61 + 0x0a)) ∧
    (0x41 ≤ c ∧ c ≤ 0x46 →
      numberFromHexByte argumentError c = .ok (c - 0x41 + 0x0a))

set_option maxRecDepth 10000 in
theorem hexadecimalDigits_proven : HexadecimalDigits := by
  intro argumentError c
  have bits : ∀ i : Fin 256, let c := UInt8.ofNat i.val;
      (0x61 ≤ c ∧ c ≤ 0x66 →
        ¬ (0x30 ≤ c ∧ c ≤ 0x39) ∧ c ||| 0x20 = c) ∧
      (0x41 ≤ c ∧ c ≤ 0x46 →
        ¬ (0x30 ≤ c ∧ c ≤ 0x39) ∧
        (0x61 ≤ (c ||| 0x20) ∧ (c ||| 0x20) ≤ 0x66) ∧
        (c ||| 0x20) - 0x61 + 0x0a = c - 0x41 + 0x0a) := by decide
  have hc : c.toNat < 256 := c.toFin.isLt
  have bits := bits ⟨c.toNat, hc⟩
  have hcast : UInt8.ofNat c.toNat = c := by simp
  simp only [hcast] at bits
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    simp [numberFromHexByte, hc.1, hc.2, pure, Except.pure]
  · intro hc
    obtain ⟨hd, hb⟩ := bits.1 hc
    simp [numberFromHexByte, hd, hb, hc.1, hc.2, pure, Except.pure]
  · intro hc
    obtain ⟨hd, hb, hv⟩ := bits.2 hc
    simp [numberFromHexByte, hd, hb.1, hb.2, hv, pure, Except.pure]

inductive ReverseCharacterTrace {C E : Type}
    (getindex : Index → Except E C) (prevind : Index → Except E Index) :
    Index → List C → Prop where
  | nil {i} (nonpositive : i.val < 1) : ReverseCharacterTrace getindex prevind i []
  | cons {i j c rest} (positive : 1 ≤ i.val)
      (character : getindex i = .ok c) (previous : prevind i = .ok j)
      (tail : ReverseCharacterTrace getindex prevind j rest) :
      ReverseCharacterTrace getindex prevind i (c :: rest)

def chompReverseCharacters {C : Type} [BEq C] (newline carriageReturn : C) :
    List C → List C
  | [] => []
  | c :: rest =>
    if c == newline then
      match rest with
      | [] => []
      | d :: tail => if d == carriageReturn then tail.reverse else rest.reverse
    else (c :: rest).reverse

def ChompCharacters : Prop :=
  ∀ {S R C E : Type} [BEq C] [LawfulBEq C]
    (lastindex : S → Index) (getindex : S → Index → Except E C)
    (prevind : S → Index → Except E Index) (substring : S → Index → Index → Except E R)
    (observe : R → List C) (newline carriageReturn : C) (s : S),
    (∀ i chars, ReverseCharacterTrace (getindex s) (prevind s) i chars →
      ∃ out, substring s (int 1) i = .ok out ∧ observe out = chars.reverse) →
    ∀ reverseChars,
    ReverseCharacterTrace (getindex s) (prevind s) (lastindex s) reverseChars →
    ∃ out, chomp lastindex getindex prevind substring (fun a b => a == b)
      newline carriageReturn s = .ok out ∧
      observe out = chompReverseCharacters newline carriageReturn reverseChars

theorem chompCharacters_proven : ChompCharacters := by
  intro S R C E inst lawful lastindex getindex prevind substring observe newline carriageReturn
    s slice reverseChars htrace
  obtain ⟨whole, hwhole, hvwhole⟩ := slice _ _ htrace
  cases htrace with
  | nil hi =>
    exact ⟨whole, by simp [chomp, hi, hwhole], by simpa [chompReverseCharacters] using hvwhole⟩
  | @cons i j c rest hi hc hj tail =>
    have hnot : ¬ (lastindex s).val < 1 := by omega
    cases heq : c == newline with
    | false =>
      refine ⟨whole, ?_, ?_⟩
      · simp [chomp, hnot, hc, heq, hwhole, bind, Except.bind]
      · simpa [chompReverseCharacters, heq] using hvwhole
    | true =>
      obtain ⟨oneLess, hone, hvone⟩ := slice _ _ tail
      cases tail with
      | nil hjneg =>
        refine ⟨oneLess, ?_, ?_⟩
        · simp [chomp, hnot, hc, heq, hj, hjneg, hone, bind, Except.bind]
        · simpa [chompReverseCharacters, heq] using hvone
      | @cons j k d rest hjpos hd hk tail2 =>
        have hjnot : ¬ j.val < 1 := by omega
        cases heqd : d == carriageReturn with
        | false =>
          refine ⟨oneLess, ?_, ?_⟩
          · simp [chomp, hnot, hc, heq, hj, hjnot, hd, heqd, hone, bind, Except.bind]
          · simpa [chompReverseCharacters, heq, heqd] using hvone
        | true =>
          obtain ⟨twoLess, htwo, hvtwo⟩ := slice _ _ tail2
          refine ⟨twoLess, ?_, ?_⟩
          · simp [chomp, hnot, hc, heq, hj, hjnot, hd, heqd, hk, htwo, bind, Except.bind]
          · simpa [chompReverseCharacters, heq, heqd] using hvtwo

def ChompFastCharacters : Prop :=
  ∀ {S R E : Type} (codeunits : S → List UInt8)
    (rawSubstring : S → Index → Nat → Except E R) (observe : R → List UInt8) (s : S),
    (∀ n, n ≤ (codeunits s).length →
      ∃ out, rawSubstring s (int 1) n = .ok out ∧ observe out = (codeunits s).take n) →
    ∃ out, chompFast codeunits rawSubstring s = .ok out ∧
      observe out = chompReverseCharacters (0x0a : UInt8) 0x0d (codeunits s).reverse

theorem chompFastCharacters_proven : ChompFastCharacters := by
  intro S R E codeunits rawSubstring observe s viewLaw
  cases hr : (codeunits s).reverse with
  | nil =>
    have hcu : codeunits s = [] := by
      have h := congrArg List.reverse hr
      simpa using h
    obtain ⟨out, ho, hv⟩ := viewLaw 0 (by omega)
    exact ⟨out, by simp [chompFast, hcu, ho], by simpa [chompReverseCharacters, hr] using hv⟩
  | cons c rest =>
    have hcu : codeunits s = rest.reverse ++ [c] := by
      have h := congrArg List.reverse hr
      simpa using h
    by_cases hc : c = 0x0a
    · subst c
      cases rest with
      | nil =>
        obtain ⟨out, ho, hv⟩ := viewLaw 0 (by omega)
        exact ⟨out, by simp [chompFast, hcu, ho], by simpa [chompReverseCharacters, hr] using hv⟩
      | cons d tail =>
        have hcu' : codeunits s = tail.reverse ++ [d, 0x0a] := by simpa using hcu
        by_cases hd : d = 0x0d
        · subst d
          obtain ⟨out, ho, hv⟩ := viewLaw tail.length (by rw [hcu']; simp)
          refine ⟨out, ?_, ?_⟩
          · simp [chompFast, hcu', ho]
          · simpa [hcu', hr, chompReverseCharacters, List.take_append] using hv
        · obtain ⟨out, ho, hv⟩ := viewLaw (tail.length + 1) (by rw [hcu']; simp)
          refine ⟨out, ?_, ?_⟩
          · simp [chompFast, hcu', hd, ho]
          · have ht : tail.reverse.take (tail.length + 1) = tail.reverse :=
              List.take_of_length_le (by simp)
            simpa [hcu', hr, chompReverseCharacters, hd, List.take_append, ht] using hv
    · obtain ⟨out, ho, hv⟩ := viewLaw (codeunits s).length (Nat.le_refl _)
      have ho' : rawSubstring s (int 1) (rest.length + 1) = .ok out := by simpa [hcu] using ho
      have hv' : observe out = codeunits s := by simpa using hv
      refine ⟨out, ?_, ?_⟩
      · simp [chompFast, hcu, hc, ho']
      · simpa [chompReverseCharacters, hr, hc, hcu] using hv'

def ChompGeneric : Prop :=
  ∀ {S R C E : Type} (codeunits : S → List UInt8)
    (rawSubstring : S → Index → Nat → Except E R)
    (lastindex : S → Index) (getindex : S → Index → Except E C)
    (prevind : S → Index → Except E Index) (substring : S → Index → Index → Except E R)
    (equalChar : C → C → Bool) (newline carriageReturn : C)
    (endIndex : S → Nat → Index) (boundary : S → Nat → Prop) (s : S),
    lastindex s = endIndex s (codeunits s).length →
    boundary s (codeunits s).length →
    (∀ k, k ≤ (codeunits s).length → boundary s k →
      ((endIndex s k).val < 1 ↔ k = 0)) →
    (∀ k, k ≤ (codeunits s).length → boundary s k →
      substring s (int 1) (endIndex s k) = rawSubstring s (int 1) k) →
    (∀ k, 0 < k → k ≤ (codeunits s).length → boundary s k →
      ∃ c, getindex s (endIndex s k) = .ok c ∧
        equalChar c newline = ((codeunits s).getD (k - 1) 0 == 0x0a) ∧
        equalChar c carriageReturn = ((codeunits s).getD (k - 1) 0 == 0x0d)) →
    (∀ k, 0 < k → k ≤ (codeunits s).length → boundary s k →
      ((codeunits s).getD (k - 1) 0 = 0x0a ∨ (codeunits s).getD (k - 1) 0 = 0x0d) →
      prevind s (endIndex s k) = .ok (endIndex s (k - 1)) ∧ boundary s (k - 1)) →
    chomp lastindex getindex prevind substring equalChar newline carriageReturn s =
      chompFast codeunits rawSubstring s

theorem chompGeneric_proven : ChompGeneric := by
  intro S R C E codeunits rawSubstring lastindex getindex prevind substring equalChar newline
    carriageReturn endIndex boundary s hlast hboundary hindex hview hget hprev
  let n := (codeunits s).length
  have hn : n = (codeunits s).length := rfl
  have hbound : n ≤ (codeunits s).length := Nat.le_refl _
  by_cases hzero : n = 0
  · have hi : (endIndex s n).val < 1 := (hindex n hbound hboundary).mpr hzero
    have hs := hview n hbound hboundary
    have hz : (codeunits s).length = 0 := by omega
    calc
      _ = rawSubstring s (int 1) n := by simp [chomp, hlast, ← hn, hi, hs]
      _ = _ := by simp [chompFast, ← hn, hzero]
  · have hnpos : 0 < n := by omega
    have hi : ¬ (endIndex s n).val < 1 := fun h => hzero ((hindex n hbound hboundary).mp h)
    obtain ⟨c, hc, hlf, hcr⟩ := hget n hnpos hbound hboundary
    by_cases hlfByte : (codeunits s).getD (n - 1) 0 = 0x0a
    · have heq : equalChar c newline = true := by rw [hlf, hlfByte]; rfl
      obtain ⟨hp, hb⟩ := hprev n hnpos hbound hboundary (Or.inl hlfByte)
      have hkbound : n - 1 ≤ (codeunits s).length := by omega
      have hv := hview (n - 1) hkbound hb
      by_cases hone : n = 1
      · have hj : (endIndex s (n - 1)).val < 1 := (hindex _ hkbound hb).mpr (by omega)
        have hg : chomp lastindex getindex prevind substring equalChar newline carriageReturn s =
            rawSubstring s (int 1) (n - 1) := by
          simp [chomp, hlast, ← hn, hi, hc, heq, hp, hj, hv, bind, Except.bind]
        rw [hg]
        simp only [chompFast, ← hn, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
        simp only [hlfByte, hzero, hone]
        simp
        change rawSubstring s (int 1) 0 =
          rawSubstring s (int 1) (1 - if (codeunits s).getD 0 0 = 0x0a then 1 else 0)
        have hf : (codeunits s).getD 0 0 = 0x0a := by simpa only [hone, Nat.sub_self] using hlfByte
        rw [if_pos hf]
      · have hkpos : 0 < n - 1 := by omega
        have hj : ¬ (endIndex s (n - 1)).val < 1 := by
          intro h
          have := (hindex _ hkbound hb).mp h
          omega
        obtain ⟨d, hd, hdlf, hdcr⟩ := hget (n - 1) hkpos hkbound hb
        have htwo : 2 ≤ (codeunits s).length := by omega
        have hsub : n - 1 - 1 = n - 2 := by omega
        by_cases hcrByte : (codeunits s).getD (n - 2) 0 = 0x0d
        · have heqd : equalChar d carriageReturn = true := by rw [hdcr, hsub, hcrByte]; rfl
          obtain ⟨hp2, hb2⟩ := hprev (n - 1) hkpos hkbound hb (Or.inr (by simpa [hsub] using hcrByte))
          have hv2 := hview (n - 1 - 1) (by omega) hb2
          have hg : chomp lastindex getindex prevind substring equalChar newline carriageReturn s =
              rawSubstring s (int 1) (n - 1 - 1) := by
            simp [chomp, hlast, ← hn, hi, hc, heq, hp, hj, hd, heqd, hp2, hv2, bind, Except.bind]
          rw [hg]
          simp only [chompFast, ← hn, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
          simp only [hlfByte, hzero, show 2 ≤ n by omega, show 1 < n by omega, hsub, hcrByte]
          simp
          change rawSubstring s (int 1) (n - 2) =
            rawSubstring s (int 1) (n - 1 - if (codeunits s).getD (n - 1 - 1) 0 = 0x0d then 1 else 0)
          rw [hsub, if_pos hcrByte, hsub]
        · have heqd : equalChar d carriageReturn = false := by
            rw [hdcr, hsub]
            cases he : (codeunits s).getD (n - 2) 0 == 0x0d with
            | false => rfl
            | true => exact False.elim (hcrByte (eq_of_beq he))
          have hg : chomp lastindex getindex prevind substring equalChar newline carriageReturn s =
              rawSubstring s (int 1) (n - 1) := by
            simp [chomp, hlast, ← hn, hi, hc, heq, hp, hj, hd, heqd, hv, bind, Except.bind]
          rw [hg]
          simp only [chompFast, ← hn, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
          simp only [hlfByte, hzero, show 2 ≤ n by omega, show 1 < n by omega, hsub, hcrByte]
          simp
          change rawSubstring s (int 1) (n - 1) =
            rawSubstring s (int 1) (n - 1 - if (codeunits s).getD (n - 1 - 1) 0 = 0x0d then 1 else 0)
          rw [hsub, if_neg hcrByte]
          rfl
    · have heq : equalChar c newline = false := by
        rw [hlf]
        cases he : (codeunits s).getD (n - 1) 0 == 0x0a with
        | false => rfl
        | true => exact False.elim (hlfByte (eq_of_beq he))
      have hv := hview n hbound hboundary
      have hg : chomp lastindex getindex prevind substring equalChar newline carriageReturn s =
          rawSubstring s (int 1) n := by
        simp [chomp, hlast, ← hn, hi, hc, heq, hv, bind, Except.bind]
      rw [hg]
      simp only [chompFast, ← hn, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      simp only [hlfByte, hzero]
      simp

def lowerHexDigit (n : Nat) : UInt8 :=
  UInt8.ofNat (if n < 10 then 0x30 + n else 0x61 + n - 10)

def lowerHexBytes (bytes : List UInt8) : List UInt8 :=
  bytes.flatMap (fun x => [lowerHexDigit (x.toNat / 16), lowerHexDigit (x.toNat % 16)])

/-- Relates a lazy `IterSteps` trace to the finite list of elements it yields. -/
inductive IterStepTrace {A St E : Type} : IterSteps A St E → List A → Prop where
  | done : IterStepTrace .done []
  | yield {x : A} {state : St} {next : St → IterSteps A St E} {rest : List A}
      (tail : IterStepTrace (next state) rest) :
      IterStepTrace (.yield x state next) (x :: rest)

private theorem hexIOLoop_correct
    {State IO C E : Type}
    (charOfByte : UInt8 → C) (hexChar : Index → UInt8)
    (print : IO → C → C → Except E IO) (readBytes : IO → List UInt8)
    (table : ∀ x, hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16))
    (printing : ∀ io x y, ∃ out,
      print io (charOfByte x) (charOfByte y) = .ok out ∧
      readBytes out = readBytes io ++ [x, y]) :
    ∀ {steps : IterSteps UInt8 State E} {bytes : List UInt8},
    IterStepTrace steps bytes →
    ∀ io,
    ∃ out, bytes2hexIOLoop hexChar charOfByte print steps io = .ok out ∧
      readBytes out = readBytes io ++ lowerHexBytes bytes := by
  intro steps bytes trace
  induction trace with
  | done =>
    intro io
    exact ⟨io, rfl, by simp [lowerHexBytes]⟩
  | @yield x state next bytes _ ih =>
    intro io
    obtain ⟨nextIO, hp, hb⟩ := printing io (hexChar (hexHighIndex x)) (hexChar (hexLowIndex x))
    obtain ⟨out, ho, hv⟩ := ih nextIO
    refine ⟨out, ?_, ?_⟩
    · simp [bytes2hexIOLoop, hp, ho, bind, Except.bind]
    · simpa [hb, table x, lowerHexBytes, List.append_assoc] using hv

def Bytes2hexIOCharacters : Prop :=
  ∀ {Itr State IO C E : Type}
    (iterate : Itr → IterSteps UInt8 State E)
    (isUInt8Iterator : Itr → Bool) (hexChar : Index → UInt8)
    (charOfByte : UInt8 → C) (print : IO → C → C → Except E IO)
    (argumentError : String → E) (readBytes : IO → List UInt8),
    (∀ x, hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16)) →
    (∀ io x y, ∃ out, print io (charOfByte x) (charOfByte y) = .ok out ∧
      readBytes out = readBytes io ++ [x, y]) →
    (∀ itr io, isUInt8Iterator itr = false →
      bytes2hexIO iterate isUInt8Iterator hexChar charOfByte print argumentError io itr =
        .error (argumentError "eltype of iterator not UInt8")) ∧
    (∀ itr io bytes,
      isUInt8Iterator itr = true →
      IterStepTrace (iterate itr) bytes →
      ∃ out,
        bytes2hexIO iterate isUInt8Iterator hexChar charOfByte print
          argumentError io itr = .ok out ∧
        readBytes out = readBytes io ++ lowerHexBytes bytes)

theorem bytes2hexIOCharacters_proven : Bytes2hexIOCharacters := by
  intro Itr State IO C E iterate isUInt8Iterator hexChar charOfByte print
    argumentError readBytes table printing
  refine ⟨?_, ?_⟩
  · intro itr io hfalse
    simp [bytes2hexIO, hfalse, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro itr io bytes htype htrace
    simpa [bytes2hexIO, htype] using
      hexIOLoop_correct charOfByte hexChar print readBytes table printing htrace io
/-! ## Input-validation guarantees -/

private theorem checkWidthLoop_prefixes
    {C E : Type} (textwidthChar : C → Index) (width : Index) :
    ∀ {steps : IterSteps C Index E} {chars : List C},
    IterStepTrace steps chars →
    ∀ total,
    checkTextwidthLoop textwidthChar width steps total = .ok true ↔
      ∀ n, 0 < n → n ≤ chars.length →
        ((chars.take n).foldl (fun sum c => sum + textwidthChar c) total).val ≤ width.val := by
  intro steps chars htrace
  induction htrace with
  | done =>
    intro total
    simp [checkTextwidthLoop]
    intro n hn hzero
    omega
  | @yield c state next rest _ ih =>
    intro total
    constructor
    · intro h n hn hlen
      have hfirst : (total + textwidthChar c).val ≤ width.val := by
        by_cases hle : (total + textwidthChar c).val ≤ width.val
        · exact hle
        · have hgt : (total + textwidthChar c).val > width.val := by omega
          simp [checkTextwidthLoop, hgt] at h
      have htail := (ih (total + textwidthChar c)).mp (by
        simpa [checkTextwidthLoop, show ¬(total + textwidthChar c).val > width.val by omega] using h)
      cases n with
      | zero => omega
      | succ n =>
        cases n with
        | zero => simpa using hfirst
        | succ n =>
          simpa using htail (n + 1) (by omega) (by simpa using hlen)
    · intro h
      have hfirst : (total + textwidthChar c).val ≤ width.val := by
        simpa using h 1 (by omega) (by simp)
      have htail : checkTextwidthLoop textwidthChar width (next state) (total + textwidthChar c) = .ok true := by
        apply (ih _).mpr
        intro n hn hlen
        simpa using h (n + 1) (by omega) (by simpa using hlen)
      simpa [checkTextwidthLoop, show ¬(total + textwidthChar c).val > width.val by omega] using htail

def TextwidthPrefixCheck : Prop :=
  ∀ {S V R C E : Type} (ops : TruncateOps S V R C E) (s : S) (width : Index),
    (∀ chars, IterStepTrace (ops.iterate s) chars →
      (checkTextwidth ops s width = .ok true ↔
        ∀ n, 0 < n → n ≤ chars.length →
          ((chars.take n).foldl (fun sum c => sum + ops.textwidthChar c) (int 0)).val ≤ width.val)) ∧
    (∀ c state next,
      ops.iterate s = .yield c state next →
      (int 0 + ops.textwidthChar c).val > width.val →
      checkTextwidth ops s width = .ok false)

theorem textwidthPrefixCheck_proven : TextwidthPrefixCheck := by
  intro S V R C E ops s width
  refine ⟨?_, ?_⟩
  · intro chars hchars
    simpa [checkTextwidth] using
      checkWidthLoop_prefixes ops.textwidthChar width hchars (int 0)
  · intro c state next hiter hgt
    simp [checkTextwidth, hiter, checkTextwidthLoop, hgt]
/-! ## Maximal leading and trailing predicate runs -/

inductive PairTrace {C State E : Type}
    (next : State → Except E (Option ((Index × C) × State))) :
    Option ((Index × C) × State) → List (Index × C) → Prop where
  | nil : PairTrace next none []
  | cons {p : Index × C} {k : State} {current : Option ((Index × C) × State)}
      {rest : List (Index × C)} (step : next k = .ok current)
      (tail : PairTrace next current rest) :
      PairTrace next (some (p, k)) (p :: rest)

def pairWidthSum {C : Type} (cw : C → Index) (pairs : List (Index × C)) : Index :=
  pairs.foldl (fun width pair => width + cw pair.2) (int 0)

def MinimalPadPrefix {C : Type} (cw : C → Index) (r : Index)
    (pairs : List (Index × C)) (result : List C) : Prop :=
  ∃ n, n ≤ pairs.length ∧ result = (pairs.take n).map Prod.snd ∧
    (n = pairs.length ∨ (0 < n ∧ r.val ≤ (pairWidthSum cw (pairs.take n)).val)) ∧
    ∀ k, 0 < k → k < n → (pairWidthSum cw (pairs.take k)).val < r.val

private theorem padRemainderLoop_minimal
    {S C R FS E : Type} (ops : PadRemainderOps S C R FS E)
    (cw : C → Index) (observe : R → List C) (p : S) (r : Index)
    (allPairs : List (Index × C))
    (widthLaw : ∀ c, ops.textwidthChar c = .ok (cw c))
    (wholeLaw : ∃ out, ops.whole p = .ok out ∧ observe out = allPairs.map Prod.snd)
    (sliceLaw : ∀ before i c after, allPairs = before ++ (i, c) :: after →
      ∃ out, ops.viewPrefix p i = .ok out ∧ observe out = (before ++ [(i, c)]).map Prod.snd) :
    ∀ fuel seen remaining current total,
    PairTrace (ops.pairsNext p) current remaining →
    allPairs = seen ++ remaining →
    remaining.length < fuel →
    total = pairWidthSum cw seen →
    (∀ k, 0 < k → k ≤ seen.length → (pairWidthSum cw (allPairs.take k)).val < r.val) →
    ∃ out, padRemainderString.loop ops p r fuel current total = .ok out ∧
      MinimalPadPrefix cw r allPairs (observe out) := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen remaining current total trace hall hf
    omega
  | succ fuel ih =>
    intro seen remaining current total trace hall hf htotal hbefore
    cases trace with
    | nil =>
      obtain ⟨out, ho, hv⟩ := wholeLaw
      refine ⟨out, by simp [padRemainderString.loop, ho], allPairs.length, Nat.le_refl _, ?_,
        Or.inl rfl, ?_⟩
      · simpa using hv
      · intro k hk hkl
        apply hbefore k hk
        have : allPairs = seen := by simpa using hall
        rw [← this]
        omega
    | @cons pair state next rest hnext trace =>
      obtain ⟨i, c⟩ := pair
      have htake : allPairs.take (seen.length + 1) = seen ++ [(i, c)] := by
        rw [hall]
        simp [List.take_append]
        exact List.take_of_length_le (by omega)
      have hsum : pairWidthSum cw (seen ++ [(i, c)]) = total + cw c := by
        rw [htotal]
        simp [pairWidthSum, List.foldl_append]
      by_cases hhit : (total + cw c).val ≥ r.val
      · obtain ⟨out, ho, hv⟩ := sliceLaw seen i c rest hall
        refine ⟨out, ?_, seen.length + 1, ?_, ?_, Or.inr ⟨by omega, ?_⟩, ?_⟩
        · simp [padRemainderString.loop, widthLaw, hhit, ho, bind, Except.bind]
        · rw [hall]
          simp
        · rw [htake]
          exact hv
        · rw [htake, hsum]
          exact hhit
        · intro k hk hkl
          exact hbefore k hk (by omega)
      · have hbefore' : ∀ k, 0 < k → k ≤ (seen ++ [(i, c)]).length →
            (pairWidthSum cw (allPairs.take k)).val < r.val := by
          intro k hk hkl
          by_cases hle : k ≤ seen.length
          · exact hbefore k hk hle
          · have heq : k = seen.length + 1 := by simpa using (show k = seen.length + 1 by
              simp only [List.length_append, List.length_singleton] at hkl
              omega)
            rw [heq, htake, hsum]
            omega
        obtain ⟨out, ho, hv⟩ := ih (seen ++ [(i, c)]) rest next (total + cw c) trace
          (by simpa [List.append_assoc] using hall) (by simpa using hf) hsum.symm hbefore'
        exact ⟨out, by
          simp [padRemainderString.loop, widthLaw, hhit, hnext, ho, bind, Except.bind], hv⟩

def PadRemainderMinimal : Prop :=
  ∀ {S C R FS E : Type} (ops : PadRemainderOps S C R FS E)
    (cw : C → Index) (observe : R → List C) (p : S) (r : Index)
    (pairs : List (Index × C)) (first : Option ((Index × C) × FS)),
    ops.pairsFirst p = .ok first →
    PairTrace (ops.pairsNext p) first pairs →
    pairs.length ≤ ops.pairsBound p →
    (∀ c, ops.textwidthChar c = .ok (cw c)) →
    (∃ out, ops.whole p = .ok out ∧ observe out = pairs.map Prod.snd) →
    (∀ before i c after, pairs = before ++ (i, c) :: after →
      ∃ out, ops.viewPrefix p i = .ok out ∧ observe out = (before ++ [(i, c)]).map Prod.snd) →
    ∃ out, padRemainderString ops p r = .ok out ∧ MinimalPadPrefix cw r pairs (observe out)

theorem padRemainderMinimal_proven : PadRemainderMinimal := by
  intro S C R FS E ops cw observe p r pairs first hfirst htrace hbound hwidth hwhole hslice
  obtain ⟨out, ho, hv⟩ := padRemainderLoop_minimal ops cw observe p r pairs hwidth hwhole hslice
    (ops.pairsBound p + 1) [] pairs first (int 0) htrace (by simp) (by omega) rfl
    (by intro k hk hkl; simp at hkl; omega)
  exact ⟨out, by simpa [padRemainderString, hfirst, bind, Except.bind] using ho, hv⟩

def PadPieceBounds {C : Type} (cw : C → Index) (missing padWidth : Int)
    (q : Nat) (all result : List C) : Prop :=
  result.IsPrefix all ∧
    Int.ofNat q * padWidth ≤ missing ∧
    missing ≤ Int.ofNat q * padWidth + (result.map (fun c => (cw c).val)).sum ∧
    ∀ before c, result = before ++ [c] →
      Int.ofNat q * padWidth + (before.map (fun d => (cw d).val)).sum < missing

def PaddingPieces : Prop :=
  ∀ {S C R O N FS E : Type} (ops : PadValueOps S C R O N E)
    (remOps : PadRemainderOps S C R FS E)
    (cw : C → Index) (inputBytes : PadInput S C → List UInt8)
    (viewBytes : R → List UInt8) (viewChars : R → List C) (outBytes : O → List UInt8),
    (∀ flag parts, ∃ out, ops.assemble flag parts = .ok out ∧ outBytes out =
      parts.flatMap (fun part => match part with | .value x => inputBytes x | .view x => viewBytes x)) →
    (∀ p q, 0 ≤ q.val → ∃ repeated, ops.repeatPad p q = .ok repeated ∧
      inputBytes repeated = (List.replicate q.val.toNat (inputBytes p)).flatten) →
    (∀ m l, 0 < m.val → 0 < l.val →
      ∃ q r, ops.divrem m l = .ok (q, r) ∧ 0 ≤ q.val ∧
        0 ≤ r.val ∧ r.val < l.val ∧ m.val = q.val * l.val + r.val) →
    ∀ (s : PadInput S C) (p : S) (n : N) (converted sw pw : Index) pairs first (left : Bool),
    ops.toInt n = .ok converted →
    ops.textwidth s = .ok sw →
    ops.textwidth (.string p) = .ok pw →
    0 ≤ sw.val → 0 < pw.val →
    remOps.pairsFirst p = .ok first →
    PairTrace (remOps.pairsNext p) first pairs →
    pairs.length ≤ remOps.pairsBound p →
    (∀ c, remOps.textwidthChar c = .ok (cw c)) →
    (∃ out, remOps.whole p = .ok out ∧ viewChars out = pairs.map Prod.snd) →
    (∀ before i c after, pairs = before ++ (i,c) :: after →
      ∃ out, remOps.viewPrefix p i = .ok out ∧
        viewChars out = (before ++ [(i,c)]).map Prod.snd) →
    (∀ k, k ≤ pairs.length →
      (pairWidthSum cw (pairs.take k)).val =
        ((pairs.take k).map (fun pair => (cw pair.2).val)).sum) →
    pw.val = (pairs.map (fun pair => (cw pair.2).val)).sum →
    let missing := (ops.signed converted - sw).val
    (ops.signed converted = converted →
      JuliaLean.IntTy.i64.min ≤ converted.val - sw.val →
      missing = converted.val - sw.val) ∧
    ∃ out,
      (if left then lpad ops remOps s (.string p) n else rpad ops remOps s (.string p) n) = .ok out ∧
      ((missing ≤ 0 ∧ outBytes out = inputBytes s) ∨
        (∃ q rem,
          outBytes out = (if left then
            (List.replicate q (inputBytes (.string p))).flatten ++ viewBytes rem ++ inputBytes s
            else inputBytes s ++ (List.replicate q (inputBytes (.string p))).flatten ++ viewBytes rem) ∧
          PadPieceBounds cw missing pw.val q (pairs.map Prod.snd) (viewChars rem)) ∨
        ∃ q, missing = Int.ofNat q * pw.val ∧
          outBytes out = (if left then
            (List.replicate q (inputBytes (.string p))).flatten ++ inputBytes s
            else inputBytes s ++ (List.replicate q (inputBytes (.string p))).flatten))

theorem paddingPieces_proven : PaddingPieces := by
  intro S C R O N FS E ops remOps cw inputBytes viewBytes viewChars outBytes
    assembly repetition division s p n converted sw pw pairs first left
    hn hs hp hsw hpw hfirst htrace hbound hcw hwhole hslice hsum hpad
  dsimp only
  refine ⟨?_, ?_⟩
  · intro hsign hlow
    rw [hsign]
    change JuliaLean.wrapInt .i64 (converted.val - sw.val) = _
    exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨hlow, by have := converted.property.2; omega⟩
  · let flag := ops.isAnnotated s || ops.isAnnotated (.string p)
    by_cases hsmall : (ops.signed converted - sw).val ≤ 0
    · obtain ⟨out, ho, hb⟩ := assembly flag [.value s]
      refine ⟨out, ?_, Or.inl ⟨hsmall, by simpa using hb⟩⟩
      cases left <;> simp [lpad, rpad, hn, hs, hsmall, ho, flag, bind, Except.bind]
    · obtain ⟨q, r, hd, hq, hr, hrl, heq⟩ := division (ops.signed converted - sw) pw (by omega) hpw
      obtain ⟨repeated, hrepeated, hbytes⟩ := repetition (.string p) q hq
      have hnonzero : ¬pw.val = 0 := by omega
      have hqnat : Int.ofNat q.val.toNat = q.val := Int.toNat_of_nonneg hq
      by_cases hz : r.val = 0
      · cases left with
        | false =>
          obtain ⟨out, ho, hb⟩ := assembly flag [.value s, .value repeated]
          refine ⟨out, ?_, Or.inr (Or.inr ⟨q.val.toNat, by rw [hqnat]; omega, ?_⟩)⟩
          · simp [rpad, hn, hs, hsmall, hp, hnonzero, hd, hrepeated, hz, ho, flag,
              bind, Except.bind]
          · simpa [hbytes] using hb
        | true =>
          obtain ⟨out, ho, hb⟩ := assembly flag [.value repeated, .value s]
          refine ⟨out, ?_, Or.inr (Or.inr ⟨q.val.toNat, by rw [hqnat]; omega, ?_⟩)⟩
          · simp [lpad, hn, hs, hsmall, hp, hnonzero, hd, hrepeated, hz, ho, flag,
              bind, Except.bind]
          · simpa [hbytes] using hb
      · obtain ⟨rem, hrem, k, hk, hchars, hhit, hminimal⟩ :=
          padRemainderMinimal_proven remOps cw viewChars p r pairs first
            hfirst htrace hbound hcw hwhole hslice
        have hh : r.val ≤ ((pairs.take k).map (fun pair => (cw pair.2).val)).sum := by
          rcases hhit with hfull | hhit
          · rw [hfull, List.take_length]
            omega
          · rw [← hsum k hk]
            exact hhit.2
        have hpieces : PadPieceBounds cw (ops.signed converted - sw).val pw.val q.val.toNat
            (pairs.map Prod.snd) (viewChars rem) := by
          refine ⟨?_, by rw [hqnat]; omega, ?_, ?_⟩
          · rw [hchars]
            exact ⟨(pairs.drop k).map Prod.snd, by simp [← List.map_append]⟩
          · rw [hchars, List.map_map]
            rw [hqnat]
            change (ops.signed converted - sw).val ≤ q.val * pw.val +
              ((pairs.take k).map (fun pair => (cw pair.2).val)).sum
            omega
          · intro before c hsplit
            have hlen : before.length + 1 = k := by
              have := congrArg List.length hsplit
              rw [hchars] at this
              simp [List.length_take, Nat.min_eq_left hk] at this
              omega
            have hbefore : before = ((pairs.take before.length).map Prod.snd) := by
              have ht := congrArg (List.take before.length) hsplit
              simpa [hchars, List.map_take, List.take_take, Nat.min_eq_left (by omega : before.length ≤ k)]
                using ht.symm
            have hw : (pairWidthSum cw (pairs.take before.length)).val < r.val := by
              by_cases hzero : before.length = 0
              · simp only [hzero, List.take_zero, pairWidthSum, List.foldl_nil]
                change 0 < r.val
                omega
              · exact hminimal before.length (by omega) (by omega)
            rw [hsum before.length (by omega)] at hw
            have hweights : (before.map (fun d => (cw d).val)).sum =
                ((pairs.take before.length).map (fun pair => (cw pair.2).val)).sum := by
              simpa [Function.comp_def] using
                congrArg (fun xs : List C => (xs.map (fun d => (cw d).val)).sum) hbefore
            rw [hweights]
            rw [hqnat]
            omega
        cases left with
        | false =>
          obtain ⟨out, ho, hb⟩ := assembly flag [.value s, .value repeated, .view rem]
          refine ⟨out, ?_, Or.inr (Or.inl ⟨q.val.toNat, rem, ?_, hpieces⟩)⟩
          · simpa [rpad, hn, hs, hsmall, hp, hnonzero, hd, hrepeated, hz,
              padRemainder, hrem, flag, bind, Except.bind, pure, Except.pure] using ho
          · simpa [hbytes, List.append_assoc] using hb
        | true =>
          obtain ⟨out, ho, hb⟩ := assembly flag [.value repeated, .view rem, .value s]
          refine ⟨out, ?_, Or.inr (Or.inl ⟨q.val.toNat, rem, ?_, hpieces⟩)⟩
          · simpa [lpad, hn, hs, hsmall, hp, hnonzero, hd, hrepeated, hz,
              padRemainder, hrem, flag, bind, Except.bind, pure, Except.pure] using ho
          · simpa [hbytes, List.append_assoc] using hb
private theorem reverseSplit_counter
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (state : Option RSplitState)
    (out : R) (next : RSplitState)
    (h : iterateRSplit ops findprev iter state = .ok (some (out, next))) :
    next.2 = (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2 - int 1 := by
  unfold iterateRSplit at h
  dsimp only at h
  split at h
  · simp [pure, Except.pure] at h
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp [pure, Except.pure] at h
      · split at h
        · simp at h
        · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          exact congrArg Prod.snd h.2.symm

private theorem lstripLoop_correct
    {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) (e : Index) :
    ∀ (pairs : List (Index × C)) (fuel : Nat) (current : Option ((Index × C) × FS)),
      PairTrace (ops.pairsNext s) current pairs →
      pairs.length < fuel →
      lstrip.loop ops f s e fuel current =
        ops.substring s
          (((pairs.dropWhile (fun p => f p.2)).head?.map Prod.fst).getD (ops.addOne e)) e := by
  intro pairs
  induction pairs with
  | nil =>
    intro fuel current ht hf
    cases ht
    cases fuel with
    | zero => omega
    | succ n => rfl
  | cons p pairs ih =>
    intro fuel current ht hf
    cases ht with
    | cons hstep htail =>
      cases fuel with
      | zero => omega
      | succ n =>
        cases h : f p.2 with
        | false => simp [lstrip.loop, h]
        | true =>
          simpa [lstrip.loop, h, hstep, bind, Except.bind] using
            ih n _ htail (by simp at hf; omega)

def LstripMaximalRun : Prop :=
  ∀ {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) (pairs : List (Index × C))
    (first : Option ((Index × C) × FS)),
    ops.pairsFirst s = .ok first →
    PairTrace (ops.pairsNext s) first pairs →
    pairs.length ≤ ops.pairsBound s →
    lstrip ops f s =
      ops.substring s
        (((pairs.dropWhile (fun p => f p.2)).head?.map Prod.fst).getD
          (ops.addOne (ops.lastindex s))) (ops.lastindex s)

theorem lstripMaximalRun_proven : LstripMaximalRun := by
  intro S R C FS BS E ops f s pairs first hfirst ht hf
  simp only [lstrip, hfirst, bind, Except.bind]
  exact lstripLoop_correct ops f s _ pairs _ first ht (by omega)

private theorem rstripLoop_correct
    {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) :
    ∀ (pairs : List (Index × C)) (fuel : Nat) (current : Option ((Index × C) × BS)),
      PairTrace (ops.reversePairsNext s) current pairs →
      pairs.length < fuel →
      rstrip.loop ops f s fuel current =
        ops.substring s (int 1)
          (((pairs.dropWhile (fun p => f p.2)).head?.map Prod.fst).getD (int 0)) := by
  intro pairs
  induction pairs with
  | nil =>
    intro fuel current ht hf
    cases ht
    cases fuel with
    | zero => omega
    | succ n => rfl
  | cons p pairs ih =>
    intro fuel current ht hf
    cases ht with
    | cons hstep htail =>
      cases fuel with
      | zero => omega
      | succ n =>
        cases h : f p.2 with
        | false => simp [rstrip.loop, h]
        | true =>
          simpa [rstrip.loop, h, hstep, bind, Except.bind] using
            ih n _ htail (by simp at hf; omega)

def RstripMaximalRun : Prop :=
  ∀ {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) (pairs : List (Index × C))
    (first : Option ((Index × C) × BS)),
    ops.reversePairsFirst s = .ok first →
    PairTrace (ops.reversePairsNext s) first pairs →
    pairs.length ≤ ops.reversePairsBound s →
    rstrip ops f s =
      ops.substring s (int 1)
        (((pairs.dropWhile (fun p => f p.2)).head?.map Prod.fst).getD (int 0))

theorem rstripMaximalRun_proven : RstripMaximalRun := by
  intro S R C FS BS E ops f s pairs first hfirst ht hf
  simp only [rstrip, hfirst, bind, Except.bind]
  exact rstripLoop_correct ops f s pairs _ first ht (by omega)

/-! The slice laws below concern only external iteration and SubString construction.
They quantify over every split of the iterator's character-index sequence, independently
of the stripping predicate. -/
def ForwardSliceLaw {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (readSource : S → List C) (readView : R → List C) : Prop :=
  ∀ s, ∃ pairs first,
    ops.pairsFirst s = .ok first ∧ PairTrace (ops.pairsNext s) first pairs ∧
    pairs.length ≤ ops.pairsBound s ∧ pairs.map Prod.snd = readSource s ∧
    ∀ before tail, pairs = before ++ tail →
      ∃ out,
        ops.substring s ((tail.head?.map Prod.fst).getD (ops.addOne (ops.lastindex s)))
          (ops.lastindex s) = .ok out ∧ readView out = tail.map Prod.snd

def ReverseSliceLaw {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (readSource : S → List C) (readView : R → List C) : Prop :=
  ∀ s, ∃ pairs first,
    ops.reversePairsFirst s = .ok first ∧ PairTrace (ops.reversePairsNext s) first pairs ∧
    pairs.length ≤ ops.reversePairsBound s ∧ pairs.map Prod.snd = (readSource s).reverse ∧
    ∀ before tail, pairs = before ++ tail →
      ∃ out,
        ops.substring s (int 1) ((tail.head?.map Prod.fst).getD (int 0)) = .ok out ∧
        (readView out).reverse = tail.map Prod.snd

private theorem dropWhile_split {A : Type} (f : A → Bool) (xs : List A) :
    ∃ before, xs = before ++ xs.dropWhile f := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    cases h : f x with
    | false => exact ⟨[], by simp [List.dropWhile, h]⟩
    | true =>
      obtain ⟨before, hb⟩ := ih
      exact ⟨x :: before, by simpa [List.dropWhile, h] using congrArg (List.cons x) hb⟩

private theorem mapSnd_dropWhile {C : Type} (f : C → Bool) (pairs : List (Index × C)) :
    (pairs.dropWhile (fun p => f p.2)).map Prod.snd = (pairs.map Prod.snd).dropWhile f := by
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
    cases h : f p.2 <;> simp [List.dropWhile, h, ih]

def LstripChars : Prop :=
  ∀ {S R C Q Str FS BS E : Type} (ops : StripOps S R C FS BS E)
    (readSource : S → List C) (readView : R → List C)
    (member : C → Q → Bool) (argumentError : String → E),
    ForwardSliceLaw ops readSource readView →
    (∀ f s, ∃ out, lstrip ops f s = .ok out ∧
      readView out = (readSource s).dropWhile f) ∧
    (∀ chars s, ∃ out, lstripChars ops member chars s = .ok out ∧
      readView out = (readSource s).dropWhile (fun c => member c chars)) ∧
    (∀ (s : S) (str : Str),
      lstripStringError (R := R) argumentError s str =
        .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

theorem lstripChars_proven : LstripChars := by
  intro S R C Q Str FS BS E ops readSource readView member argumentError hlaw
  have hpred : ∀ f s, ∃ out, lstrip ops f s = .ok out ∧
      readView out = (readSource s).dropWhile f := by
    intro f s
    obtain ⟨pairs, first, hfirst, ht, hbound, hchars, hslice⟩ := hlaw s
    obtain ⟨before, hb⟩ := dropWhile_split (fun p : Index × C => f p.2) pairs
    obtain ⟨out, ho, hv⟩ := hslice before (pairs.dropWhile (fun p => f p.2)) hb
    refine ⟨out, (lstripMaximalRun_proven ops f s pairs first hfirst ht hbound).trans ho, ?_⟩
    rw [mapSnd_dropWhile, hchars] at hv
    exact hv
  exact ⟨hpred, fun chars s => hpred (fun c => member c chars) s, fun _ _ => rfl⟩

def RstripChars : Prop :=
  ∀ {S R C Q Str FS BS E : Type} (ops : StripOps S R C FS BS E)
    (readSource : S → List C) (readView : R → List C)
    (member : C → Q → Bool) (argumentError : String → E),
    ReverseSliceLaw ops readSource readView →
    (∀ f s, ∃ out, rstrip ops f s = .ok out ∧
      (readView out).reverse = (readSource s).reverse.dropWhile f) ∧
    (∀ chars s, ∃ out, rstripChars ops member chars s = .ok out ∧
      (readView out).reverse = (readSource s).reverse.dropWhile (fun c => member c chars)) ∧
    (∀ (s : S) (str : Str),
      rstripStringError (R := R) argumentError s str =
        .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

theorem rstripChars_proven : RstripChars := by
  intro S R C Q Str FS BS E ops readSource readView member argumentError hlaw
  have hpred : ∀ f s, ∃ out, rstrip ops f s = .ok out ∧
      (readView out).reverse = (readSource s).reverse.dropWhile f := by
    intro f s
    obtain ⟨pairs, first, hfirst, ht, hbound, hchars, hslice⟩ := hlaw s
    obtain ⟨before, hb⟩ := dropWhile_split (fun p : Index × C => f p.2) pairs
    obtain ⟨out, ho, hv⟩ := hslice before (pairs.dropWhile (fun p => f p.2)) hb
    refine ⟨out, (rstripMaximalRun_proven ops f s pairs first hfirst ht hbound).trans ho, ?_⟩
    rw [mapSnd_dropWhile, hchars] at hv
    exact hv
  exact ⟨hpred, fun chars s => hpred (fun c => member c chars) s, fun _ _ => rfl⟩

def StripChars : Prop :=
  ∀ {S R T C Q Str FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (readSource : S → List C) (readMiddle : R → List C) (readView : T → List C)
    (member : C → Q → Bool) (argumentError : String → E),
    ReverseSliceLaw opsS readSource readMiddle →
    ForwardSliceLaw opsR readMiddle readView →
    (∀ f s, ∃ out, stripPredicate opsS opsR f s = .ok out ∧
      readView out = (((readSource s).reverse.dropWhile f).reverse).dropWhile f) ∧
    (∀ chars s, ∃ out, stripChars opsS opsR member chars s = .ok out ∧
      readView out = (((readSource s).reverse.dropWhile (fun c => member c chars)).reverse).dropWhile (fun c => member c chars)) ∧
    (∀ (s : S) (str : Str),
      stripStringError (R := T) argumentError s str =
        .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

theorem stripChars_proven : StripChars := by
  intro S R T C Q Str FS BS FS2 BS2 E opsS opsR readSource readMiddle readView member argumentError hr hl
  have hpred : ∀ f s, ∃ out, stripPredicate opsS opsR f s = .ok out ∧
      readView out = (((readSource s).reverse.dropWhile f).reverse).dropWhile f := by
    intro f s
    obtain ⟨right, hright, hcharsRight⟩ := (rstripChars_proven (Q := Unit) (Str := Unit)
      opsS readSource readMiddle (fun _ _ => false) argumentError hr).1 f s
    obtain ⟨out, hout, hchars⟩ := (lstripChars_proven (Q := Unit) (Str := Unit)
      opsR readMiddle readView (fun _ _ => false) argumentError hl).1 f right
    have hcharsRight' :
        readMiddle right = ((readSource s).reverse.dropWhile f).reverse := by
      simpa only [List.reverse_reverse] using congrArg List.reverse hcharsRight
    refine ⟨out, ?_, ?_⟩
    · simp [stripPredicate, hright, hout, bind, Except.bind]
    · simpa only [hcharsRight'] using hchars
  refine ⟨hpred, ?_, fun _ _ => rfl⟩
  intro chars s
  simpa [stripChars, rstripChars, lstripChars, stripPredicate] using
    hpred (fun c => member c chars) s
/-! ## Runtime-confirmed type and truncation refutations -/

private theorem splitTail_counter
    {S R F E : Type} (ops : SplitStringOps S R E) (iter : SplitIteratorModel S F)
    (i k n : Index) (out : R) (nextState : SplitState)
    (h : splitTail ops iter i k n = .ok (some (out, nextState))) :
    nextState.2.2 = n + int 1 ∧ nextState.1 = ops.ncodeunits iter.str + int 2 := by
  unfold splitTail at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩

private theorem splitLoop_counter
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) :
    ∀ fuel i k n range out nextState,
    iterateSplit.loop ops findnext iter fuel i k n range = .ok (some (out, nextState)) →
    nextState.2.2 = n + int 1 ∧
      (n.val = (iter.limit - int 1).val →
        nextState.1 = ops.ncodeunits iter.str + int 2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i k n range out nextState h
    have ht := splitTail_counter ops iter i k n out nextState h
    exact ⟨ht.1, fun _ => ht.2⟩
  | succ fuel ih =>
    intro i k n range out nextState h
    simp only [iterateSplit.loop, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | exact ih _ _ _ _ _ _ h
      | have ht := splitTail_counter ops iter _ _ _ out nextState h
        exact ⟨ht.1, fun _ => ht.2⟩
      | cases h <;> simp_all

private theorem splitIterate_counter
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (state : Option SplitState) (out : R) (nextState : SplitState)
    (h : iterateSplit ops findnext iter state = .ok (some (out, nextState))) :
    let n := (state.getD (ops.firstindex iter.str, ops.firstindex iter.str, int 0)).2.2
    nextState.2.2 = n + int 1 ∧
      (n.val = (iter.limit - int 1).val →
        nextState.1 = ops.ncodeunits iter.str + int 2) := by
  simp only [iterateSplit, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact splitLoop_counter ops findnext iter _ _ _ _ _ out nextState h
    | cases h

private theorem indexSentinel_stops (x : Index) (hx : x.val < JuliaLean.IntTy.i64.max) :
    ((x + int 2) - int 1).val > x.val := by
  have hone : (int 1).val = 1 := by decide
  have htwo : (int 2).val = 2 := by decide
  by_cases hedge : x.val = JuliaLean.IntTy.i64.max - 1
  · have hv : (int (JuliaLean.IntTy.i64.max - 1)).val = JuliaLean.IntTy.i64.max - 1 := by decide
    have heq : x = int (JuliaLean.IntTy.i64.max - 1) := Subtype.ext (by rw [hv]; exact hedge)
    rw [heq]
    decide
  · have bounds := x.property
    have hsum : (x + int 2).val = x.val + 2 := by
      change JuliaLean.wrapInt .i64 (x.val + (int 2).val) = _
      rw [htwo]
      exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
    change JuliaLean.wrapInt .i64 ((x + int 2).val - (int 1).val) > x.val
    rw [hsum, hone, JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩]
    omega

inductive CollectedTrace {R State E : Type}
    (next : Option State → Except E (Option (R × State))) : Option State → List R → Prop where
  | nil {state} (stop : next state = .ok none) : CollectedTrace next state []
  | cons {state out nextState rest} (step : next state = .ok (some (out, nextState)))
      (tail : CollectedTrace next (some nextState) rest) :
      CollectedTrace next state (out :: rest)

private theorem collectedTrace_stopped {R State E : Type}
    {next : Option State → Except E (Option (R × State))}
    {state : Option State} {xs : List R} (stop : next state = .ok none)
    (trace : CollectedTrace next state xs) : xs = [] := by
  cases trace with
  | nil => rfl
  | cons step tail =>
    rw [stop] at step
    cases step

private theorem reverseSplit_zero_stops
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (state : Option RSplitState)
    (out : R) (next : RSplitState)
    (zero : (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val = 0)
    (step : iterateRSplit ops findprev iter state = .ok (some (out, next))) :
    iterateRSplit ops findprev iter (some next) = .ok none := by
  unfold iterateRSplit at step
  dsimp only at step
  split at step
  · simp [pure, Except.pure] at step
  · simp only [iterateRSplit.loop, zero, ite_true, bind, Except.bind, pure, Except.pure] at step
    split at step
    · simp [pure, Except.pure] at step
    · split at step
      · simp at step
      · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
        rw [← step.2]
        simp [iterateRSplit, show (int (-1)).val < 0 by decide, pure, Except.pure]

private theorem reverseSplitTrace_limit
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) {state : Option RSplitState} {xs : List R}
    (trace : CollectedTrace (fun state => iterateRSplit ops findprev iter state) state xs) :
    0 ≤ (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val →
    Int.ofNat xs.length ≤ (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val + 1 := by
  induction trace with
  | nil => intro h; simp; omega
  | @cons state out next rest step tail ih =>
    intro hnonneg
    have counter := reverseSplit_counter ops findprev iter state out next step
    by_cases hz : (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val = 0
    · have stop := reverseSplit_zero_stops ops findprev iter state out next hz step
      have empty := collectedTrace_stopped stop tail
      simp [empty, hz]
    · have hone : (int 1).val = 1 := by decide
      have decrement : next.2.val =
          (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val - 1 := by
        rw [counter]
        change JuliaLean.wrapInt .i64
          ((state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.val - (int 1).val) = _
        rw [hone]
        have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
        have hmax := (state.getD (ops.lastindex iter.str, iter.limit - int 1)).2.property.2
        exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
      have bound := ih (by simpa only [Option.getD_some] using (show 0 ≤ next.2.val by omega))
      simp only [Option.getD_some] at bound
      have hlen : Int.ofNat (out :: rest).length = Int.ofNat rest.length + 1 := by simp
      rw [hlen]
      omega

def ReverseSplitLimit : Prop :=
  ∀ {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (pieces : List R),
    0 < iter.limit.val →
    CollectedTrace (fun state => iterateRSplit ops findprev iter state) none pieces →
    Int.ofNat pieces.length ≤ iter.limit.val

theorem reverseSplitLimit_proven : ReverseSplitLimit := by
  intro S R F E ops findprev iter pieces hpositive trace
  have hone : (int 1).val = 1 := by decide
  have hremaining : (iter.limit - int 1).val = iter.limit.val - 1 := by
    change JuliaLean.wrapInt .i64 (iter.limit.val - (int 1).val) = _
    rw [hone]
    have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
    have hmax := iter.limit.property.2
    exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
  have bound := reverseSplitTrace_limit ops findprev iter trace
    (by simpa [hremaining] using (show 0 ≤ iter.limit.val - 1 by omega))
  simpa [hremaining] using bound

private def splitCount {S R F E : Type} (ops : SplitStringOps S R E)
    (iter : SplitIteratorModel S F) (state : Option SplitState) : Index :=
  (state.getD (ops.firstindex iter.str, ops.firstindex iter.str, int 0)).2.2

private theorem splitTrace_limit
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F)
    (hsize : (ops.ncodeunits iter.str).val < JuliaLean.IntTy.i64.max)
    {state : Option SplitState} {xs : List R}
    (trace : CollectedTrace (fun state => iterateSplit ops findnext iter state) state xs) :
    0 ≤ (splitCount ops iter state).val →
    (splitCount ops iter state).val < iter.limit.val →
    Int.ofNat xs.length ≤ iter.limit.val - (splitCount ops iter state).val := by
  have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
  induction trace with
  | nil =>
    intro hzero hlimit
    simp
    omega
  | @cons state out nextState rest hstep tail ih =>
    intro hzero hlimit
    have hcounter := splitIterate_counter ops findnext iter state out nextState hstep
    change nextState.2.2 = splitCount ops iter state + int 1 ∧ _ at hcounter
    have hlimBounds := iter.limit.property
    have hlimPositive : 1 ≤ iter.limit.val := by omega
    have hlimMinus : (iter.limit - int 1).val = iter.limit.val - 1 := by
      change JuliaLean.wrapInt .i64 (iter.limit.val - (int 1).val) = _
      have hone : (int 1).val = 1 := by decide
      rw [hone]
      exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
    by_cases hedge : (splitCount ops iter state).val = iter.limit.val - 1
    · have hi := hcounter.2 (by rw [hlimMinus]; exact hedge)
      have hstop : iterateSplit ops findnext iter (some nextState) = .ok none := by
        have hs := indexSentinel_stops (ops.ncodeunits iter.str) hsize
        simp [iterateSplit, hi, hs, pure, Except.pure]
      have hempty := collectedTrace_stopped hstop tail
      rw [hempty]
      simp
      omega
    · have hnext : (splitCount ops iter (some nextState)).val = (splitCount ops iter state).val + 1 := by
        change nextState.2.2.val = _
        rw [hcounter.1]
        change JuliaLean.wrapInt .i64 ((splitCount ops iter state).val + (int 1).val) = _
        have hone : (int 1).val = 1 := by decide
        rw [hone]
        exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
      have hrest := ih (by rw [hnext]; omega) (by rw [hnext]; omega)
      rw [hnext] at hrest
      have hlen : Int.ofNat (out :: rest).length = Int.ofNat rest.length + 1 := by simp
      rw [hlen]
      omega

private theorem splitTail_not_none_at_max
    {S R F E : Type} (ops : SplitStringOps S R E) (iter : SplitIteratorModel S F)
    (hsize : (ops.ncodeunits iter.str).val = JuliaLean.IntTy.i64.max)
    (i k n : Index) : splitTail ops iter i k n ≠ .ok none := by
  intro h
  have hnot : ¬ i.val > (ops.ncodeunits iter.str).val := by
    have hb := i.property.2
    rw [hsize]
    omega
  simp only [splitTail, hnot, decide_false, Bool.and_false, Bool.false_eq_true,
    if_false, bind, Except.bind, pure, Except.pure] at h
  split at h <;> cases h

private theorem splitLoop_not_none_at_max
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F)
    (hsize : (ops.ncodeunits iter.str).val = JuliaLean.IntTy.i64.max) :
    ∀ fuel i k n range, iterateSplit.loop ops findnext iter fuel i k n range ≠ .ok none := by
  intro fuel
  induction fuel with
  | zero =>
    intro i k n range
    exact splitTail_not_none_at_max ops iter hsize i k n
  | succ fuel ih =>
    intro i k n range h
    simp only [iterateSplit.loop, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | exact ih _ _ _ _ h
      | exact splitTail_not_none_at_max ops iter hsize _ _ _ h
      | cases h

private theorem splitIterate_not_none_at_max
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F)
    (hsize : (ops.ncodeunits iter.str).val = JuliaLean.IntTy.i64.max)
    (state : Option SplitState) : iterateSplit ops findnext iter state ≠ .ok none := by
  intro h
  have hnot : ¬ ((state.getD (ops.firstindex iter.str, ops.firstindex iter.str, int 0)).1 -
      int 1).val > (ops.ncodeunits iter.str).val := by
    have hb := ((state.getD (ops.firstindex iter.str, ops.firstindex iter.str, int 0)).1 - int 1).property.2
    rw [hsize]
    omega
  simp only [iterateSplit, hnot, if_false, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact splitLoop_not_none_at_max ops findnext iter hsize _ _ _ _ _ h
    | cases h

private theorem collectedTrace_never_stops
    {R State E : Type} {next : Option State → Except E (Option (R × State))}
    (hnext : ∀ state, next state ≠ .ok none) {state : Option State} {xs : List R}
    (trace : CollectedTrace next state xs) : False := by
  induction trace with
  | nil stop => exact hnext _ stop
  | cons step tail ih => exact ih

def SplitLimit : Prop :=
  ∀ {S R F : Type} (ops : SplitStringOps S R JuliaLean.JlError)
    (findnext : F → S → Index → Except JuliaLean.JlError (Option (Index × Index)))
    (methodError : String → JuliaLean.JlError)
    (collect : SplitIteratorModel S F → Except JuliaLean.JlError (List R)),
    (∀ iter xs, collect iter = .ok xs →
      CollectedTrace (fun state => iterateSplit ops findnext iter state) none xs) →
    ∀ s splitter limit keepempty xs, 1 ≤ limit.val →
    splitGeneric (fun _ : Index => true) (JuliaLean.base.int.convert .i64) methodError
      collect s splitter limit keepempty = .ok xs →
    Int.ofNat xs.length ≤ limit.val

theorem splitLimit_proven : SplitLimit := by
  intro S R F ops findnext methodError collect collectLaw s splitter limit keepempty xs hlimit hrun
  have hz : (int 0).val = 0 := by decide
  have hc : JuliaLean.base.int.convert .i64 limit = .ok limit := by
    simp [JuliaLean.base.int.convert, JuliaLean.JInt.convert, limit.property]
  have hcollected : collect ⟨s, splitter, limit, keepempty⟩ = .ok xs := by
    simpa [splitGeneric, eachsplitGeneric, hc, bind, Except.bind, pure, Except.pure] using hrun
  have trace := collectLaw _ _ hcollected
  by_cases hmax : (ops.ncodeunits s).val = JuliaLean.IntTy.i64.max
  · exact False.elim (collectedTrace_never_stops
      (splitIterate_not_none_at_max ops findnext ⟨s, splitter, limit, keepempty⟩ hmax) trace)
  · have hsize : (ops.ncodeunits s).val < JuliaLean.IntTy.i64.max := by
      have hb := (ops.ncodeunits s).property.2
      omega
    have hbound := splitTrace_limit ops findnext ⟨s, splitter, limit, keepempty⟩ hsize trace
      (by simp [splitCount, hz]) (by simpa [splitCount, hz] using (show 0 < limit.val by omega))
    simpa [splitCount, hz] using hbound

def virtualAsciiSplitOps : SplitStringOps Unit (Index × Index) String where
  firstindex _ := int 1
  lastindex _ := int ((2 : Int) ^ 63 - 1)
  ncodeunits _ := int ((2 : Int) ^ 63 - 1)
  iterationBound _ := 2 ^ 63 - 1
  nextind _ i := .ok (i + int 1)
  prevind _ i := .ok (i - int 1)
  substringUnchecked _ i j := .ok (i - int 1, (j + int 1) - i)
  substringFrom _ i := .ok (i - int 1, (int ((2 : Int) ^ 63 - 1) + int 1) - i)
  substringChecked _ i j := .ok (i - int 1, (j + int 1) - i)

def SplitIteratorLimitOne : Prop :=
  ∀ {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (out : R) (state : SplitState),
    iter.limit.val = 1 →
    iterateSplit ops findnext iter none = .ok (some (out, state)) →
    iterateSplit ops findnext iter (some state) = .ok none

theorem splitIteratorLimitOne_refuted : ¬ SplitIteratorLimitOne := by
  intro h
  let iter : SplitIteratorModel Unit Unit := ⟨(), (), int 1, true⟩
  let maxIndex : Index := int ((2 : Int) ^ 63 - 1)
  let terminal : Index := maxIndex + int 2
  have hfirst : iterateSplit virtualAsciiSplitOps (fun _ _ _ => .ok none) iter none =
      .ok (some ((int 0, maxIndex), (terminal, int 1, int 1))) := by
    dsimp only [iter, terminal, maxIndex]
    decide +kernel
  have hstop := h virtualAsciiSplitOps (fun _ _ _ => .ok none) iter
    (int 0, maxIndex) (terminal, int 1, int 1) (by decide) hfirst
  exact splitIterate_not_none_at_max virtualAsciiSplitOps (fun _ _ _ => .ok none) iter
    (by decide) _ hstop


private theorem lowerHexNibble_decodes (byte : UInt8) :
    numberFromHexByte id (lowerHexDigit (byte.toNat / 16)) = .ok (byte >>> 4) ∧
    numberFromHexByte id (lowerHexDigit (byte.toNat % 16)) = .ok (byte &&& 0xf) ∧
    ((byte >>> 4) <<< 4) + (byte &&& 0xf) = byte := by
  have all : ∀ n : Fin 256, let byte := UInt8.ofNat n.val;
      numberFromHexByte id (lowerHexDigit (byte.toNat / 16)) = .ok (byte >>> 4) ∧
      numberFromHexByte id (lowerHexDigit (byte.toNat % 16)) = .ok (byte &&& 0xf) ∧
      ((byte >>> 4) <<< 4) + (byte &&& 0xf) = byte := by decide +kernel
  have hx : byte.toNat < 256 := byte.toFin.isLt
  have hv : UInt8.ofNat byte.toNat = byte := UInt8.ofNat_toNat
  simpa only [hv] using all ⟨byte.toNat, hx⟩

inductive HexByteTrace {A C State E : Type}
    (next : State → Except E (Option (HexDigit A C × State))) :
    Option (HexDigit A C × State) → List UInt8 → Prop where
  | nil : HexByteTrace next none []
  | cons {byte : UInt8} {highState lowState : State}
      {current : Option (HexDigit A C × State)} {rest : List UInt8}
      (low : next highState = .ok (some (.byte (lowerHexDigit (byte.toNat % 16)), lowState)))
      (step : next lowState = .ok current) (tail : HexByteTrace next current rest) :
      HexByteTrace next (some (.byte (lowerHexDigit (byte.toNat / 16)), highState)) (byte :: rest)

private theorem lowerHexNibble_decodes_generic {E : Type} (argumentError : String → E) (byte : UInt8) :
    numberFromHexByte argumentError (lowerHexDigit (byte.toNat / 16)) = .ok (byte >>> 4) ∧
    numberFromHexByte argumentError (lowerHexDigit (byte.toNat % 16)) = .ok (byte &&& 0xf) := by
  have decode_transfer : ∀ digit expected,
      numberFromHexByte id digit = .ok expected →
      numberFromHexByte argumentError digit = .ok expected := by
    intro digit expected h
    unfold numberFromHexByte at h ⊢
    split
    · simp_all [pure, Except.pure]
    · dsimp only at h ⊢
      split
      · simp_all [pure, Except.pure]
      · simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  exact ⟨decode_transfer _ _ (lowerHexNibble_decodes byte).1,
    decode_transfer _ _ (lowerHexNibble_decodes byte).2.1⟩

private theorem hexDecodeLoop_roundtrip
    {Array I Itr A C State E : Type}
    (arrayOps : ByteArrayOps Array I E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (observe : Array → List UInt8) (position : I → Nat)
    (tupleLaw : ∀ value, assertTuple (some value) = .ok value)
    (setLaw : ∀ array index byte before old after,
      observe array = before ++ old :: after → position index = before.length →
      ∃ out, arrayOps.set array index byte = .ok out ∧ observe out = before ++ byte :: after)
    (itr : Itr) :
    ∀ bytes current, HexByteTrace (iterOps.iterateNext itr) current bytes →
    ∀ indices dest before old,
    indices.map position = List.range' before.length bytes.length →
    observe dest = before ++ old →
    old.length = bytes.length →
    ∃ out, hex2bytesBang.loop arrayOps iterOps assertTuple argumentError toChar toUInt8 itr
      indices dest current = .ok out ∧ observe out = before ++ bytes := by
  intro bytes current trace
  induction trace with
  | nil =>
    intro indices dest before old hi hd hl
    have hindices : indices = [] := by
      have := congrArg List.length hi
      simpa using this
    have hold : old = [] := List.eq_nil_of_length_eq_zero hl
    exact ⟨dest, by simp [hindices, hex2bytesBang.loop], by simpa [hold] using hd⟩
  | @cons byte highState lowState current bytes low step trace ih =>
    intro indices dest before old hi hd hl
    cases indices with
    | nil => simp at hi
    | cons index indices =>
      cases old with
      | nil => simp at hl
      | cons oldByte old =>
        have hipos : position index = before.length := by
          have hhead := congrArg List.head? hi
          simpa [List.range'] using hhead
        have hitail : indices.map position = List.range' (before.length + 1) bytes.length := by
          have htail := congrArg List.tail hi
          simpa [List.range'] using htail
        obtain ⟨updated, hu, hv⟩ := setLaw dest index byte before oldByte old hd hipos
        have hnibbles := lowerHexNibble_decodes_generic argumentError byte
        have hcombine := (lowerHexNibble_decodes byte).2.2
        obtain ⟨out, ho, hb⟩ := ih indices updated (before ++ [byte]) old
          (by simpa using hitail) (by simpa [List.append_assoc] using hv) (by simpa using hl)
        refine ⟨out, ?_, ?_⟩
        · simp [hex2bytesBang.loop, tupleLaw, low, step, numberFromHex, hnibbles.1, hnibbles.2,
            hcombine, hu, ho, bind, Except.bind]
        · simpa [List.append_assoc] using hb

def HexDecodeRoundtrip : Prop :=
  ∀ {Array I Itr A C State E : Type}
    (arrayOps : ByteArrayOps Array I E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (observe : Array → List UInt8) (position : I → Nat),
    (∀ value, assertTuple (some value) = .ok value) →
    (∀ array index byte before old after,
      observe array = before ++ old :: after → position index = before.length →
      ∃ out, arrayOps.set array index byte = .ok out ∧ observe out = before ++ byte :: after) →
    ∀ itr dest bytes first,
    iterOps.iterateFirst itr = .ok first →
    HexByteTrace (iterOps.iterateNext itr) first bytes →
    (iterOps.length itr).val = Int.ofNat (2 * bytes.length) →
    (int 2 * arrayOps.length dest).val = (iterOps.length itr).val →
    (arrayOps.eachindex dest).map position = List.range bytes.length →
    (observe dest).length = bytes.length →
    ∃ out, hex2bytesBang arrayOps iterOps assertTuple argumentError toChar toUInt8 true dest itr =
      .ok out ∧ observe out = bytes

theorem hexDecodeRoundtrip_proven : HexDecodeRoundtrip := by
  intro Array I Itr A C State E arrayOps iterOps assertTuple argumentError toChar toUInt8 observe
    position tupleLaw setLaw itr dest bytes first hfirst htrace hlen hsize hind hdest
  by_cases hempty : bytes = []
  · subst bytes
    have hobserve : observe dest = [] := List.eq_nil_of_length_eq_zero hdest
    refine ⟨dest, ?_, hobserve⟩
    simp [hex2bytesBang, hlen, hsize, pure, Except.pure]
  · have hnonzero : (iterOps.length itr).val ≠ 0 := by
      rw [hlen]
      change 2 * (bytes.length : Int) ≠ 0
      have : 0 < bytes.length := List.length_pos_iff.mpr hempty
      omega
    have heven : (iterOps.length itr).val % 2 = 0 := by
      rw [hlen]
      simp
    obtain ⟨out, ho, hv⟩ := hexDecodeLoop_roundtrip arrayOps iterOps assertTuple argumentError
      toChar toUInt8 observe position tupleLaw setLaw itr bytes first htrace
      (arrayOps.eachindex dest) dest [] (observe dest) (by simpa [List.range_eq_range'] using hind) rfl hdest
    refine ⟨out, ?_, by simpa using hv⟩
    simpa [hex2bytesBang, heven, hsize, hnonzero, hfirst, bind, Except.bind] using ho

def HexDecodeLengths : Prop :=
  (∀ {A I T C D State E : Type} (arrayOps : ByteArrayOps A I E)
    (iterOps : HexIteratorOps T C D State E)
    (assertTuple : Option (HexDigit C D × State) → Except E (HexDigit C D × State))
    (argumentError : String → E) (toChar : C → Except E D)
    (toUInt8 : D → Except E UInt8) (dest : A) (itr : T),
    ((iterOps.length itr).val % 2 ≠ 0 →
      hex2bytesBang arrayOps iterOps assertTuple argumentError toChar toUInt8 true dest itr =
        .error (argumentError "length of iterable must be even")) ∧
    ((iterOps.length itr).val % 2 = 0 →
      (int 2 * arrayOps.length dest).val ≠ (iterOps.length itr).val →
      hex2bytesBang arrayOps iterOps assertTuple argumentError toChar toUInt8 true dest itr =
        .error (argumentError "length of output array must be half of the length of input iterable"))) ∧
  HexDecodeRoundtrip

theorem hexDecodeLengths_proven : HexDecodeLengths := by
  refine ⟨?_, hexDecodeRoundtrip_proven⟩
  intro A I T C D State E arrayOps iterOps assertTuple argumentError toChar toUInt8 dest itr
  constructor
  · intro h
    simp [hex2bytesBang, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro h hsize
    simp [hex2bytesBang, h, hsize, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

def HexStringDecode : Prop :=
  ∀ {Array I Itr A C State S E : Type}
    (arrayOps : ByteArrayOps Array I E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (observe : Array → List UInt8) (position : I → Nat)
    (sizeof length : S → Index) (transcode : S → Except E Itr),
    (∀ value, assertTuple (some value) = .ok value) →
    (∀ array index byte before old after,
      observe array = before ++ old :: after → position index = before.length →
      ∃ out, arrayOps.set array index byte = .ok out ∧ observe out = before ++ byte :: after) →
    (∀ s dest, (sizeof s).val ≠ (length s).val →
      hex2bytesString arrayOps iterOps assertTuple argumentError toChar toUInt8 sizeof length transcode true
        dest s = .error (argumentError "input string must consist of hexadecimal characters only")) ∧
    (∀ s dest itr bytes first,
      (sizeof s).val = (length s).val →
      transcode s = .ok itr →
      iterOps.iterateFirst itr = .ok first →
      HexByteTrace (iterOps.iterateNext itr) first bytes →
      (iterOps.length itr).val = Int.ofNat (2 * bytes.length) →
      (int 2 * arrayOps.length dest).val = (iterOps.length itr).val →
      (arrayOps.eachindex dest).map position = List.range bytes.length →
      (observe dest).length = bytes.length →
      ∃ out, hex2bytesString arrayOps iterOps assertTuple argumentError toChar toUInt8 sizeof length
        transcode true dest s = .ok out ∧ observe out = bytes)

theorem hexStringDecode_proven : HexStringDecode := by
  intro Array I Itr A C State S E arrayOps iterOps assertTuple argumentError toChar toUInt8 observe
    position sizeof length transcode tupleLaw setLaw
  constructor
  · intro s dest h
    simp [hex2bytesString, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro s dest itr bytes first hequal ht hfirst htrace hlen hsize hind hdest
    obtain ⟨out, ho, hb⟩ := hexDecodeRoundtrip_proven arrayOps iterOps assertTuple argumentError toChar
      toUInt8 observe position tupleLaw setLaw itr dest bytes first hfirst htrace hlen hsize hind hdest
    exact ⟨out, by simpa [hex2bytesString, hequal, ht, bind, Except.bind] using ho, hb⟩

inductive HexOutputSlots : List (Index × UInt8) → List UInt8 → Nat → Prop where
  | nil {offset} : HexOutputSlots [] [] offset
  | cons {i : Index} {byte : UInt8} {entries : List (Index × UInt8)}
      {bytes : List UInt8} {offset : Nat}
      (high : (int 2 * i - int 1).val = Int.ofNat offset + 1)
      (low : (int 2 * i).val = Int.ofNat offset + 2)
      (tail : HexOutputSlots entries bytes (offset + 2)) :
      HexOutputSlots ((i, byte) :: entries) (byte :: bytes) offset

private theorem bytes2hexStore_correct
    {Itr State S P E : Type} (ops : Bytes2HexOps Itr State S P E)
    (observe : S → List UInt8)
    (table : ∀ x, ops.hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      ops.hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16))
    (storeLaw : ∀ array pointer index byte before old after,
      observe array = before ++ old :: after → index.val = Int.ofNat before.length + 1 →
      ∃ out, ops.store array pointer byte index = .ok out ∧ observe out = before ++ byte :: after)
    (pointer : P) :
    ∀ {steps : IterSteps (Index × UInt8) State E} {entries : List (Index × UInt8)},
    IterStepTrace steps entries →
    ∀ bytes offset, HexOutputSlots entries bytes offset →
    ∀ dest before old, before.length = offset →
    observe dest = before ++ old → old.length = 2 * bytes.length →
    ∃ out, bytes2hexStore ops pointer steps dest = .ok out ∧
      observe out = before ++ lowerHexBytes bytes := by
  intro steps entries htrace
  induction htrace with
  | done =>
    intro bytes offset slots dest before old _ hdest hlen
    cases slots
    have hold : old = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact ⟨dest, rfl, by simpa [lowerHexBytes, hold] using hdest⟩
  | @yield pair state next entries _ ih =>
    intro bytes offset slots dest before old hoff hdest hlen
    cases slots with
    | @cons i byte entries bytes offset hhigh hlow slots =>
      cases old with
      | nil => simp at hlen
      | cons oldHigh old =>
        cases old with
        | nil => simp at hlen; omega
        | cons oldLow old =>
          obtain ⟨highDest, hwriteHigh, hhighBytes⟩ := storeLaw dest pointer
            (int 2 * i - int 1) (ops.hexChar (hexHighIndex byte)) before oldHigh (oldLow :: old)
            hdest (by rw [hoff]; exact hhigh)
          obtain ⟨lowDest, hwriteLow, hlowBytes⟩ := storeLaw highDest pointer
            (int 2 * i) (ops.hexChar (hexLowIndex byte))
            (before ++ [ops.hexChar (hexHighIndex byte)]) oldLow old
            (by simpa [List.append_assoc] using hhighBytes) (by
              simp only [List.length_append, List.length_singleton]
              rw [hoff]
              rw [hlow]
              change Int.ofNat offset + 2 = (Int.ofNat offset + 1) + 1
              omega)
          obtain ⟨out, ho, hb⟩ := ih bytes (offset + 2) slots lowDest
            (before ++ [ops.hexChar (hexHighIndex byte), ops.hexChar (hexLowIndex byte)]) old
            (by simp [hoff]) (by simpa [List.append_assoc] using hlowBytes)
            (by simp only [List.length_cons] at hlen; omega)
          refine ⟨out, ?_, ?_⟩
          · simp [bytes2hexStore, hwriteHigh, hwriteLow, ho, bind, Except.bind]
          · simpa [table byte, lowerHexBytes, List.append_assoc] using hb

def Bytes2hexEncoding : Prop :=
  ∀ {Itr State S P E : Type} (ops : Bytes2HexOps Itr State S P E) (observe : S → List UInt8),
    (∀ x, ops.hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      ops.hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16)) →
    (∀ array pointer index byte before old after,
      observe array = before ++ old :: after → index.val = Int.ofNat before.length + 1 →
      ∃ out, ops.store array pointer byte index = .ok out ∧ observe out = before ++ byte :: after) →
    (∀ itr, ops.isUInt8Iterator itr = false →
      bytes2hex ops itr = .error (ops.argumentError "eltype of iterator not UInt8")) ∧
    (∀ itr bytes entries dest,
      ops.isUInt8Iterator itr = true →
      ops.allocate (int 2 * ops.length itr) = .ok dest →
      (observe dest).length = 2 * bytes.length →
      IterStepTrace (ops.enumerate itr) entries →
      HexOutputSlots entries bytes 0 →
      ∃ out, bytes2hex ops itr = .ok out ∧ observe out = lowerHexBytes bytes)

theorem bytes2hexEncoding_proven : Bytes2hexEncoding := by
  intro Itr State S P E ops observe table storeLaw
  refine ⟨?_, ?_⟩
  · intro itr hfalse
    simp [bytes2hex, hfalse, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro itr bytes entries dest htype halloc hlen henumerate hslots
    obtain ⟨out, ho, hb⟩ := bytes2hexStore_correct ops observe table storeLaw (ops.pointer dest)
      henumerate bytes 0 hslots dest [] (observe dest) rfl rfl hlen
    exact ⟨out, by simpa [bytes2hex, htype, halloc, bind, Except.bind] using ho,
      by simpa using hb⟩

private theorem lowerHexBytes_length (bytes : List UInt8) :
    (lowerHexBytes bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [lowerHexBytes, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil]
    change 2 + (lowerHexBytes bytes).length = 2 * (bytes.length + 1)
    rw [ih]
    omega

private theorem lowerHexBytes_digits (bytes : List UInt8) :
    ∀ digit ∈ lowerHexBytes bytes,
      (0x30 ≤ digit ∧ digit ≤ 0x39) ∨ (0x61 ≤ digit ∧ digit ≤ 0x66) := by
  have digits : ∀ byte : UInt8,
      ((0x30 ≤ lowerHexDigit (byte.toNat / 16) ∧ lowerHexDigit (byte.toNat / 16) ≤ 0x39) ∨
        (0x61 ≤ lowerHexDigit (byte.toNat / 16) ∧ lowerHexDigit (byte.toNat / 16) ≤ 0x66)) ∧
      ((0x30 ≤ lowerHexDigit (byte.toNat % 16) ∧ lowerHexDigit (byte.toNat % 16) ≤ 0x39) ∨
        (0x61 ≤ lowerHexDigit (byte.toNat % 16) ∧ lowerHexDigit (byte.toNat % 16) ≤ 0x66)) := by
    intro byte
    have all : ∀ n : Fin 256, let byte := UInt8.ofNat n.val;
        ((0x30 ≤ lowerHexDigit (byte.toNat / 16) ∧ lowerHexDigit (byte.toNat / 16) ≤ 0x39) ∨
          (0x61 ≤ lowerHexDigit (byte.toNat / 16) ∧ lowerHexDigit (byte.toNat / 16) ≤ 0x66)) ∧
        ((0x30 ≤ lowerHexDigit (byte.toNat % 16) ∧ lowerHexDigit (byte.toNat % 16) ≤ 0x39) ∨
          (0x61 ≤ lowerHexDigit (byte.toNat % 16) ∧ lowerHexDigit (byte.toNat % 16) ≤ 0x66)) := by decide +kernel
    simpa only [UInt8.ofNat_toNat] using all ⟨byte.toNat, byte.toFin.isLt⟩
  intro digit h
  obtain ⟨byte, hbyte, hdigit⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdigit
  rcases hdigit with heq | heq
  · subst digit
    exact (digits byte).1
  · subst digit
    exact (digits byte).2

def Bytes2hexLowercase : Prop :=
  ∀ {Itr State S P E : Type} (ops : Bytes2HexOps Itr State S P E) (observe : S → List UInt8),
    (∀ x, ops.hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      ops.hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16)) →
    (∀ array pointer index byte before old after,
      observe array = before ++ old :: after → index.val = Int.ofNat before.length + 1 →
      ∃ out, ops.store array pointer byte index = .ok out ∧ observe out = before ++ byte :: after) →
    ∀ itr bytes entries dest out,
    ops.isUInt8Iterator itr = true →
    ops.allocate (int 2 * ops.length itr) = .ok dest →
    (observe dest).length = 2 * bytes.length →
    IterStepTrace (ops.enumerate itr) entries →
    HexOutputSlots entries bytes 0 →
    bytes2hex ops itr = .ok out →
    (observe out).length = 2 * bytes.length ∧
      ∀ digit ∈ observe out, (0x30 ≤ digit ∧ digit ≤ 0x39) ∨ (0x61 ≤ digit ∧ digit ≤ 0x66)

theorem bytes2hexLowercase_proven : Bytes2hexLowercase := by
  intro Itr State S P E ops observe table storeLaw itr bytes entries dest out
    htype halloc hlen henumerate hslots hrun
  obtain ⟨encoded, ho, hb⟩ := (bytes2hexEncoding_proven ops observe table storeLaw).2 itr bytes entries dest
    htype halloc hlen henumerate hslots
  rw [hrun] at ho
  cases ho
  rw [hb]
  exact ⟨lowerHexBytes_length bytes, lowerHexBytes_digits bytes⟩

def HexRoundtrip : Prop :=
  ∀ {Itr EncodeState S P Array I DecodeItr A C DecodeState E : Type}
    (encodeOps : Bytes2HexOps Itr EncodeState S P E) (encodedBytes : S → List UInt8)
    (arrayOps : ByteArrayOps Array I E) (decodeOps : HexIteratorOps DecodeItr A C DecodeState E)
    (assertTuple : Option (HexDigit A C × DecodeState) → Except E (HexDigit A C × DecodeState))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (observe : Array → List UInt8) (position : I → Nat)
    (sizeof length : S → Index) (transcode : S → Except E DecodeItr)
    (shiftRightOne : Index → Index) (allocateBytes : Index → Except E Array),
    (∀ x, encodeOps.hexChar (hexHighIndex x) = lowerHexDigit (x.toNat / 16) ∧
      encodeOps.hexChar (hexLowIndex x) = lowerHexDigit (x.toNat % 16)) →
    (∀ array pointer index byte before old after,
      encodedBytes array = before ++ old :: after → index.val = Int.ofNat before.length + 1 →
      ∃ out, encodeOps.store array pointer byte index = .ok out ∧ encodedBytes out = before ++ byte :: after) →
    (∀ value, assertTuple (some value) = .ok value) →
    (∀ array index byte before old after,
      observe array = before ++ old :: after → position index = before.length →
      ∃ out, arrayOps.set array index byte = .ok out ∧ observe out = before ++ byte :: after) →
    (∀ s bytes, encodedBytes s = lowerHexBytes bytes →
      (sizeof s).val = (length s).val ∧
      ∃ itr first, transcode s = .ok itr ∧ decodeOps.iterateFirst itr = .ok first ∧
        HexByteTrace (decodeOps.iterateNext itr) first bytes ∧
        (decodeOps.length itr).val = Int.ofNat (2 * bytes.length)) →
    (∀ s bytes, encodedBytes s = lowerHexBytes bytes →
      ∃ dest, allocateBytes (shiftRightOne (length s)) = .ok dest ∧
        (int 2 * arrayOps.length dest).val = Int.ofNat (2 * bytes.length) ∧
        (arrayOps.eachindex dest).map position = List.range bytes.length ∧
        (observe dest).length = bytes.length) →
    ∀ itr bytes entries storage,
    encodeOps.isUInt8Iterator itr = true →
    encodeOps.allocate (int 2 * encodeOps.length itr) = .ok storage →
    (encodedBytes storage).length = 2 * bytes.length →
    IterStepTrace (encodeOps.enumerate itr) entries →
    HexOutputSlots entries bytes 0 →
    ∃ encoded decoded,
      bytes2hex encodeOps itr = .ok encoded ∧
      hex2bytesWrapper length shiftRightOne allocateBytes
        (hex2bytesString arrayOps decodeOps assertTuple argumentError toChar toUInt8 sizeof length transcode true)
        encoded = .ok decoded ∧
      observe decoded = bytes

theorem hexRoundtrip_proven : HexRoundtrip := by
  intro Itr EncodeState S P Array I DecodeItr A C DecodeState E encodeOps encodedBytes arrayOps
    decodeOps assertTuple argumentError toChar toUInt8 observe position sizeof length transcode
    shiftRightOne allocateBytes table storeLaw tupleLaw setLaw transcodeLaw allocateLaw
    itr bytes entries storage htype halloc hlen henumerate hslots
  obtain ⟨encoded, hencode, hencoded⟩ := (bytes2hexEncoding_proven encodeOps encodedBytes table storeLaw).2
    itr bytes entries storage htype halloc hlen henumerate hslots
  obtain ⟨hequal, decodeItr, first, ht, hfirst, htrace, hdecodedLen⟩ := transcodeLaw encoded bytes hencoded
  obtain ⟨dest, ha, hsize, hind, hdest⟩ := allocateLaw encoded bytes hencoded
  obtain ⟨decoded, hd, hb⟩ := (hexStringDecode_proven arrayOps decodeOps assertTuple argumentError toChar
    toUInt8 observe position sizeof length transcode tupleLaw setLaw).2
    encoded dest decodeItr bytes first hequal ht hfirst htrace hdecodedLen
    (by rw [hdecodedLen]; exact hsize) hind hdest
  exact ⟨encoded, decoded, hencode,
    by simp [hex2bytesWrapper, ha, hd, bind, Except.bind], hb⟩

def joinBytePieces (delimiter : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [piece] => piece
  | piece :: next :: rest => piece ++ delimiter ++ joinBytePieces delimiter (next :: rest)

def ForwardSplitMatchAt {S R E : Type} (ops : SplitStringOps S R E)
    (s : S) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8)
    (i a b : Index) : Prop :=
  ∃ after nextK before out,
    i.val < after.val ∧ after.val ≤ (ops.ncodeunits s).val + 1 ∧
    after.val ≤ nextK.val ∧ nextK.val ≤ (ops.ncodeunits s).val + 2 ∧
    ops.nextind s b = .ok after ∧
    (if after.val ≤ a.val then ops.nextind s a = .ok nextK else nextK = after) ∧
    ops.prevind s a = .ok before ∧
    ops.substringUnchecked s i before = .ok out ∧
    suffix i = observe out ++ delimiter ++ suffix after

def ForwardSplitInterface {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (s : S) (splitter : F) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8) : Prop :=
  (∀ i, 1 ≤ i.val → i.val ≤ (ops.ncodeunits s).val + 1 →
    ∃ out, ops.substringFrom s i = .ok out ∧ observe out = suffix i) ∧
  (∀ i k, 1 ≤ i.val → i.val ≤ (ops.ncodeunits s).val + 1 →
    i.val ≤ k.val → k.val ≤ (ops.ncodeunits s).val + 2 →
    ∃ range, findnext splitter s k = .ok range ∧
      ∀ a b, range = some (a,b) → a.val ≤ (ops.ncodeunits s).val →
        ForwardSplitMatchAt ops s delimiter suffix observe i a b ∨
        (∃ after k_ range2,
          after.val ≤ i.val ∧ after.val ≤ a.val ∧
          ops.nextind s b = .ok after ∧
          ops.nextind s a = .ok k_ ∧
          findnext splitter s k_ = .ok range2 ∧
          ∀ a2 b2, range2 = some (a2,b2) → a2.val ≤ (ops.ncodeunits s).val →
            ForwardSplitMatchAt ops s delimiter suffix observe i a2 b2))

private theorem forwardSplit_step
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8)
    (interface : ForwardSplitInterface ops findnext iter.str iter.splitter delimiter suffix observe)
    (keep : iter.keepempty = true) (i k n : Index)
    (low : 1 ≤ i.val) (high : i.val ≤ (ops.ncodeunits iter.str).val + 1)
    (hik : i.val ≤ k.val) (hk : k.val ≤ (ops.ncodeunits iter.str).val + 2) :
    (∃ out finalK, iterateSplit ops findnext iter (some (i,k,n)) =
        .ok (some (out, (ops.ncodeunits iter.str + int 2, finalK, n + int 1))) ∧
      observe out = suffix i) ∨
    (∃ out after nextK, iterateSplit ops findnext iter (some (i,k,n)) =
        .ok (some (out, (after, nextK, n + int 1))) ∧
      1 ≤ after.val ∧ after.val ≤ (ops.ncodeunits iter.str).val + 1 ∧
      after.val ≤ nextK.val ∧ nextK.val ≤ (ops.ncodeunits iter.str).val + 2 ∧
      suffix i = observe out ++ delimiter ++ suffix after) := by
  have hone : (int 1).val = 1 := by decide
  have hsub : (i - int 1).val = i.val - 1 := by
    change JuliaLean.wrapInt .i64 (i.val - (int 1).val) = _
    rw [hone]
    have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
    have hmax := i.property.2
    exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
  have guard : ¬ (i - int 1).val > (ops.ncodeunits iter.str).val := by omega
  obtain ⟨range, hf, hlaw⟩ := interface.2 i k low high hik hk
  have tailAt : ∀ k0, ∃ out, splitTail ops iter i k0 n =
      .ok (some (out, (ops.ncodeunits iter.str + int 2, k0, n + int 1))) ∧ observe out = suffix i := by
    intro k0
    obtain ⟨out, hs, ho⟩ := interface.1 i low high
    exact ⟨out, by simp [splitTail, keep, hs, bind, Except.bind, pure, Except.pure], ho⟩
  cases range with
  | none =>
    obtain ⟨out, ht, ho⟩ := tailAt k
    exact Or.inl ⟨out, k, by simpa [iterateSplit, guard, hf, iterateSplit.loop, bind, Except.bind] using ht, ho⟩
  | some pair =>
    obtain ⟨a,b⟩ := pair
    by_cases hlimit : n.val = (iter.limit - int 1).val ∨ a.val > (ops.ncodeunits iter.str).val
    · obtain ⟨out, ht, ho⟩ := tailAt k
      exact Or.inl ⟨out, k, by simpa [iterateSplit, guard, hf, iterateSplit.loop, hlimit,
        bind, Except.bind] using ht, ho⟩
    · have haLe : a.val ≤ (ops.ncodeunits iter.str).val := by omega
      rcases hlaw a b rfl haLe with
        ⟨after, nextK, before, out, hia, hafter, hanext, hnextHi, hn, hnextK, hp, hs, hb⟩ |
        ⟨after, k_, range2, hafterI, hafterA, hn, hk_, hf2, hlaw2⟩
      · refine Or.inr ⟨out, after, nextK, ?_, by omega, hafter, hanext, hnextHi, hb⟩
        by_cases hleA : after.val ≤ a.val
        · simp only [hleA, ↓reduceIte] at hnextK
          simp [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hleA, hnextK, hp, hs,
            hia, keep, bind, Except.bind, pure, Except.pure]
        · simp only [hleA, ↓reduceIte] at hnextK
          subst nextK
          simp [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hleA, hp, hs,
            hia, keep, bind, Except.bind, pure, Except.pure]
      · have hnotLt : ¬ i.val < after.val := by omega
        cases range2 with
        | none =>
          obtain ⟨out, ht, ho⟩ := tailAt k_
          exact Or.inl ⟨out, k_, by
            simpa [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hafterA, hk_,
              hnotLt, hf2, bind, Except.bind, pure, Except.pure] using ht, ho⟩
        | some pair2 =>
          obtain ⟨a2,b2⟩ := pair2
          by_cases hlimit2 : n.val = (iter.limit - int 1).val ∨ a2.val > (ops.ncodeunits iter.str).val
          · obtain ⟨out, ht, ho⟩ := tailAt k_
            exact Or.inl ⟨out, k_, by
              simpa [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hafterA, hk_,
                hnotLt, hf2, hlimit2, bind, Except.bind, pure, Except.pure] using ht, ho⟩
          · have ha2Le : a2.val ≤ (ops.ncodeunits iter.str).val := by omega
            obtain ⟨after2, nextK2, before2, out2, hia2, hafter2, hanext2, hnextHi2, hn2, hnextK2, hp2, hs2, hb2⟩ :=
              hlaw2 a2 b2 rfl ha2Le
            refine Or.inr ⟨out2, after2, nextK2, ?_, by omega, hafter2, hanext2, hnextHi2, hb2⟩
            by_cases hleA2 : after2.val ≤ a2.val
            · simp only [hleA2, ↓reduceIte] at hnextK2
              simp [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hafterA, hk_,
                hnotLt, hf2, hlimit2, hn2, hleA2, hnextK2, hp2, hs2, hia2, keep,
                bind, Except.bind, pure, Except.pure]
            · simp only [hleA2, ↓reduceIte] at hnextK2
              subst nextK2
              simp [iterateSplit, guard, hf, iterateSplit.loop, hlimit, hn, hafterA, hk_,
                hnotLt, hf2, hlimit2, hn2, hleA2, hp2, hs2, hia2, keep,
                bind, Except.bind, pure, Except.pure]

private theorem forwardSplitTrace_join
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8)
    (interface : ForwardSplitInterface ops findnext iter.str iter.splitter delimiter suffix observe)
    (keep : iter.keepempty = true)
    (size : (ops.ncodeunits iter.str).val < JuliaLean.IntTy.i64.max) :
    ∀ (pieces : List R) (i k n : Index),
    1 ≤ i.val → i.val ≤ (ops.ncodeunits iter.str).val + 1 →
    i.val ≤ k.val → k.val ≤ (ops.ncodeunits iter.str).val + 2 →
    CollectedTrace (fun state => iterateSplit ops findnext iter state) (some (i,k,n)) pieces →
    pieces ≠ [] ∧ joinBytePieces delimiter (pieces.map observe) = suffix i := by
  intro pieces
  induction pieces with
  | nil =>
    intro i k n low high hik hk trace
    cases trace with
    | nil stop =>
      rcases forwardSplit_step ops findnext iter delimiter suffix observe interface keep i k n low high hik hk with
        ⟨out, finalK, step, _⟩ | ⟨out, after, nextK, step, _⟩
      all_goals rw [stop] at step; cases step
  | cons piece rest ih =>
    intro i k n low high hik hk trace
    cases trace with
    | @cons _ _ next _ step trace =>
      rcases forwardSplit_step ops findnext iter delimiter suffix observe interface keep i k n low high hik hk with
        ⟨out, finalK, expected, ho⟩ | ⟨out, after, nextK, expected, hlo, hhi, hanext, hnextHi, hb⟩
      · rw [step] at expected
        cases expected
        have stop : iterateSplit ops findnext iter
            (some (ops.ncodeunits iter.str + int 2, finalK, n + int 1)) = .ok none := by
          simp [iterateSplit, indexSentinel_stops _ size, pure, Except.pure]
        have empty := collectedTrace_stopped stop trace
        subst rest
        exact ⟨by simp, by simpa [joinBytePieces] using ho⟩
      · rw [step] at expected
        cases expected
        obtain ⟨nonempty, joined⟩ := ih after nextK (n + int 1) hlo hhi hanext hnextHi trace
        cases rest with
        | nil => exact False.elim (nonempty rfl)
        | cons r rs =>
          refine ⟨by simp, ?_⟩
          change observe piece ++ delimiter ++ joinBytePieces delimiter ((r :: rs).map observe) = suffix i
          rw [joined]
          exact hb.symm

def SplitIterationJoin : Prop :=
  ∀ {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (s : S) (splitter : F) (limit : Index) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8) (pieces : List R),
    ops.firstindex s = int 1 →
    0 ≤ (ops.ncodeunits s).val →
    (ops.ncodeunits s).val < JuliaLean.IntTy.i64.max →
    ForwardSplitInterface ops findnext s splitter delimiter suffix observe →
    CollectedTrace (fun state => iterateSplit ops findnext ⟨s,splitter,limit,true⟩ state) none pieces →
    joinBytePieces delimiter (pieces.map observe) = suffix (ops.firstindex s)

theorem splitIterationJoin_proven : SplitIterationJoin := by
  intro S R F E ops findnext s splitter limit delimiter suffix observe pieces first nonneg size interface trace
  have run : iterateSplit ops findnext ⟨s,splitter,limit,true⟩ none =
      iterateSplit ops findnext ⟨s,splitter,limit,true⟩ (some (int 1,int 1,int 0)) := by
    simp [iterateSplit, first]
  have mapped : CollectedTrace (fun state => iterateSplit ops findnext ⟨s,splitter,limit,true⟩ state)
      (some (int 1,int 1,int 0)) pieces := by
    cases trace with
    | nil stop => exact .nil (run ▸ stop)
    | cons step tail => exact .cons (run ▸ step) tail
  have hone : (int 1).val = 1 := by decide
  have high : (int 1).val ≤ (ops.ncodeunits s).val + 1 := by rw [hone]; omega
  have high2 : (int 1).val ≤ (ops.ncodeunits s).val + 2 := by rw [hone]; omega
  have result := forwardSplitTrace_join ops findnext ⟨s,splitter,limit,true⟩ delimiter suffix observe
    interface rfl size pieces (int 1) (int 1) (int 0) (by decide) high (by decide) high2 mapped
  simpa [first] using result.2

def SplitJoin : Prop :=
  ∀ {S R F : Type} (ops : SplitStringOps S R JuliaLean.JlError)
    (findnext : F → S → Index → Except JuliaLean.JlError (Option (Index × Index)))
    (collect : SplitIteratorModel S F → Except JuliaLean.JlError (List R))
    (methodError : String → JuliaLean.JlError),
    (∀ iter pieces, collect iter = .ok pieces →
      CollectedTrace (fun state => iterateSplit ops findnext iter state) none pieces) →
    ∀ (s : S) (splitter : F) (limit : Index) (delimiter : List UInt8)
    (suffix : Index → List UInt8) (observe : R → List UInt8) (pieces : List R),
    ops.firstindex s = int 1 → 0 ≤ (ops.ncodeunits s).val →
    (ops.ncodeunits s).val < JuliaLean.IntTy.i64.max →
    ForwardSplitInterface ops findnext s splitter delimiter suffix observe →
    splitGeneric (fun _ : Index => true) (JuliaLean.base.int.convert .i64)
      methodError collect s splitter limit true = .ok pieces →
    joinBytePieces delimiter (pieces.map observe) = suffix (ops.firstindex s)

theorem splitJoin_proven : SplitJoin := by
  intro S R F ops findnext collect methodError collectLaw s splitter limit delimiter
    suffix observe pieces hfirst hzero hsize interface run
  have converted : JuliaLean.base.int.convert .i64 limit = .ok limit := by
    simp [JuliaLean.base.int.convert, JuliaLean.JInt.convert, limit.property]
  have collected : collect ⟨s,splitter,limit,true⟩ = .ok pieces := by
    simpa [splitGeneric, eachsplitGeneric, converted, bind, Except.bind, pure, Except.pure] using run
  exact splitIterationJoin_proven ops findnext s splitter limit delimiter suffix observe pieces
    hfirst hzero hsize interface (collectLaw _ _ collected)
def joinReversePieces (delimiter : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [piece] => piece
  | piece :: next :: rest => joinReversePieces delimiter (next :: rest) ++ delimiter ++ piece

private theorem joinBytePieces_append (delimiter : List UInt8) :
    ∀ (pieces : List (List UInt8)) piece, pieces ≠ [] →
      joinBytePieces delimiter (pieces ++ [piece]) =
        joinBytePieces delimiter pieces ++ delimiter ++ piece := by
  intro pieces
  induction pieces with
  | nil => simp
  | cons first rest ih =>
    intro piece nonempty
    cases rest with
    | nil => simp [joinBytePieces]
    | cons second rest =>
      simpa [joinBytePieces, List.append_assoc] using
        congrArg (fun bytes => first ++ delimiter ++ bytes) (ih piece (by simp))

private theorem joinReversePieces_eq (delimiter : List UInt8) (pieces : List (List UInt8)) :
    joinReversePieces delimiter pieces = joinBytePieces delimiter pieces.reverse := by
  induction pieces with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      simp only [joinReversePieces, List.reverse_cons]
      rw [joinBytePieces_append delimiter _ first (by simp)]
      simpa only [List.reverse_cons] using congrArg (fun bytes => bytes ++ delimiter ++ first) ih

def ReverseSplitInterface {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (s : S) (splitter : F) (delimiter : List UInt8)
    (prefixBytes : Index → List UInt8) (observe : R → List UInt8) : Prop :=
  (∀ to, 0 ≤ to.val → to.val ≤ (ops.lastindex s).val →
    ∃ out, ops.substringChecked s (int 1) to = .ok out ∧ observe out = prefixBytes to) ∧
  (∀ to, 0 ≤ to.val → to.val ≤ (ops.lastindex s).val →
    ∃ range, findprev splitter s to = .ok range ∧
      ∀ a b, range = some (a,b) →
        if b.val < a.val ∧ to.val < 2 then
          ∃ fromIndex out,
            ops.nextind s b = .ok fromIndex ∧
            ops.substringChecked s fromIndex to = .ok out ∧
            observe out = prefixBytes to
        else
          ∃ fromIndex nextTo out,
            0 ≤ nextTo.val ∧ nextTo.val ≤ (ops.lastindex s).val ∧
            ops.nextind s b = .ok fromIndex ∧ ops.prevind s a = .ok nextTo ∧
            ops.substringChecked s fromIndex to = .ok out ∧
            prefixBytes to = prefixBytes nextTo ++ delimiter ++ observe out)

private theorem reverseSplit_step
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (delimiter : List UInt8)
    (prefixBytes : Index → List UInt8) (observe : R → List UInt8)
    (interface : ReverseSplitInterface ops findprev iter.str iter.splitter delimiter prefixBytes observe)
    (keep : iter.keepempty = true) (to n : Index)
    (low : 0 ≤ to.val) (high : to.val ≤ (ops.lastindex iter.str).val) :
    (∃ out, iterateRSplit ops findprev iter (some (to,n)) =
        .ok (some (out, (int (-1), n - int 1))) ∧ observe out = prefixBytes to) ∨
    (∃ out nextTo, iterateRSplit ops findprev iter (some (to,n)) =
        .ok (some (out, (nextTo, n - int 1))) ∧
      0 ≤ nextTo.val ∧ nextTo.val ≤ (ops.lastindex iter.str).val ∧
      prefixBytes to = prefixBytes nextTo ++ delimiter ++ observe out) := by
  have guard : ¬to.val < 0 := by omega
  obtain ⟨whole, hw, hb⟩ := interface.1 to low high
  by_cases hz : n.val = 0
  · exact Or.inl ⟨whole, by simp [iterateRSplit, iterateRSplit.loop, guard, hz, keep, hw,
      bind, Except.bind, pure, Except.pure], hb⟩
  · obtain ⟨range, hf, law⟩ := interface.2 to low high
    cases range with
    | none =>
      exact Or.inl ⟨whole, by simp [iterateRSplit, iterateRSplit.loop, guard, hz, hf, keep, hw,
        bind, Except.bind, pure, Except.pure], hb⟩
    | some pair =>
      obtain ⟨a,b⟩ := pair
      have hlaw := law a b rfl
      by_cases hemptyStop : b.val < a.val ∧ to.val < 2
      · simp only [hemptyStop, ↓reduceIte] at hlaw
        obtain ⟨fromIndex, out, hn, hs, hd⟩ := hlaw
        have hcond : (decide (b.val < a.val) && decide (to.val < 2)) = true := by
          simp [hemptyStop.1, hemptyStop.2]
        exact Or.inl ⟨out, by simp [iterateRSplit, iterateRSplit.loop, guard, hz, hf, keep,
          hn, hs, hemptyStop.1, hemptyStop.2, bind, Except.bind, pure, Except.pure], hd⟩
      · simp only [hemptyStop, ↓reduceIte] at hlaw
        obtain ⟨fromIndex, nextTo, out, hlo, hhi, hn, hp, hs, hd⟩ := hlaw
        refine Or.inr ⟨out, nextTo, ?_, hlo, hhi, hd⟩
        simp [iterateRSplit, iterateRSplit.loop, guard, hz, hf, keep, hn, hp, hs,
          hemptyStop, bind, Except.bind, pure, Except.pure]
private theorem reverseSplitTrace_join
    {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (delimiter : List UInt8)
    (prefixBytes : Index → List UInt8) (observe : R → List UInt8)
    (interface : ReverseSplitInterface ops findprev iter.str iter.splitter delimiter prefixBytes observe)
    (keep : iter.keepempty = true) :
    ∀ (pieces : List R) (to n : Index),
    0 ≤ to.val → to.val ≤ (ops.lastindex iter.str).val →
    CollectedTrace (fun state => iterateRSplit ops findprev iter state) (some (to,n)) pieces →
    pieces ≠ [] ∧ joinReversePieces delimiter (pieces.map observe) = prefixBytes to := by
  intro pieces
  induction pieces with
  | nil =>
    intro to n low high trace
    cases trace with
    | nil stop =>
      rcases reverseSplit_step ops findprev iter delimiter prefixBytes observe interface keep to n low high with
        ⟨out, step, _⟩ | ⟨out, after, step, _⟩
      all_goals rw [stop] at step; cases step
  | cons piece rest ih =>
    intro to n low high trace
    cases trace with
    | @cons _ _ next _ step trace =>
      rcases reverseSplit_step ops findprev iter delimiter prefixBytes observe interface keep to n low high with
        ⟨out, expected, ho⟩ | ⟨out, after, expected, hlo, hhi, hb⟩
      · rw [step] at expected
        cases expected
        have stop : iterateRSplit ops findprev iter (some (int (-1), n - int 1)) = .ok none := by
          simp [iterateRSplit, show (int (-1)).val < 0 by decide, pure, Except.pure]
        have empty := collectedTrace_stopped stop trace
        subst rest
        exact ⟨by simp, by simpa [joinReversePieces] using ho⟩
      · rw [step] at expected
        cases expected
        obtain ⟨nonempty, joined⟩ := ih after (n - int 1) hlo hhi trace
        cases rest with
        | nil => exact False.elim (nonempty rfl)
        | cons r rs =>
          refine ⟨by simp, ?_⟩
          change joinReversePieces delimiter ((r :: rs).map observe) ++ delimiter ++ observe piece = prefixBytes to
          rw [joined]
          exact hb.symm

def RsplitJoin : Prop :=
  ∀ {S R F : Type} (ops : SplitStringOps S R JuliaLean.JlError)
    (findprev : F → S → Index → Except JuliaLean.JlError (Option (Index × Index)))
    (collect : RSplitIteratorModel S F → Except JuliaLean.JlError (List R))
    (methodError : String → JuliaLean.JlError),
    (∀ iter pieces, collect iter = .ok pieces →
      CollectedTrace (fun state => iterateRSplit ops findprev iter state) none pieces) →
    ∀ (s : S) (splitter : F) (limit : Index) (delimiter : List UInt8)
    (prefixBytes : Index → List UInt8) (observe : R → List UInt8) (pieces : List R),
    0 ≤ (ops.lastindex s).val →
    ReverseSplitInterface ops findprev s splitter delimiter prefixBytes observe →
    rsplitGeneric (fun _ : Index => true) (JuliaLean.base.int.convert .i64)
      methodError collect List.reverse s splitter limit true = .ok pieces →
    joinBytePieces delimiter (pieces.map observe) = prefixBytes (ops.lastindex s)

theorem rsplitJoin_proven : RsplitJoin := by
  intro S R F ops findprev collect methodError collectLaw s splitter limit delimiter
    prefixBytes observe pieces hzero interface run
  have converted : JuliaLean.base.int.convert .i64 limit = .ok limit := by
    simp [JuliaLean.base.int.convert, JuliaLean.JInt.convert, limit.property]
  cases hc : collect ⟨s,splitter,limit,true⟩ with
  | error e => simp [rsplitGeneric, eachrsplitGeneric, converted, hc, bind, Except.bind, pure, Except.pure] at run
  | ok collected =>
    have heq : collected.reverse = pieces := by
      simpa [rsplitGeneric, eachrsplitGeneric, converted, hc, bind, Except.bind,
        pure, Except.pure] using run
    subst pieces
    have trace := collectLaw ⟨s,splitter,limit,true⟩ collected hc
    have initial : iterateRSplit ops findprev ⟨s,splitter,limit,true⟩ none =
        iterateRSplit ops findprev ⟨s,splitter,limit,true⟩
          (some (ops.lastindex s,limit - int 1)) := by simp [iterateRSplit]
    have mapped : CollectedTrace
        (fun state => iterateRSplit ops findprev ⟨s,splitter,limit,true⟩ state)
        (some (ops.lastindex s,limit - int 1)) collected := by
      cases trace with
      | nil stop => exact .nil (initial ▸ stop)
      | cons step tail => exact .cons (initial ▸ step) tail
    have result := reverseSplitTrace_join ops findprev ⟨s,splitter,limit,true⟩ delimiter prefixBytes observe
      interface rfl collected (ops.lastindex s) (limit - int 1) hzero (by exact Int.le_refl _) mapped
    simpa [joinReversePieces_eq, List.map_reverse] using result.2

private theorem literalReplaceOnce_count
    {S P Q R IO E : Type} (ops : ReplaceOnceOps S P Q R IO E)
    (write : IO → R → Except E (IO × Index)) (measure : IO → Nat)
    (copyLaw : ∀ io str i len out, ops.unsafeWrite io str i len = .ok out → measure out = measure io)
    (writeLaw : ∀ io repl out bytes, write io repl = .ok (out,bytes) → measure out ≤ measure io + 1)
    (io : IO) (str : S) (start e1 : Index) (patterns : List Q) (replaces : List R)
    (ranges : List ReplaceRange) (count n i : Index) (step : ReplaceStep IO)
    (run : replaceOnce (P := P) {ops with replace := replaceLiteral write}
      io str start e1 patterns replaces ranges count n i = .ok step) :
    measure step.io ≤ measure io + 1 := by
  simp only [replaceOnce, replaceLiteral, bind, Except.bind, pure, Except.pure] at run
  repeat' split at run
  all_goals try simp_all only [Except.ok.injEq]
  all_goals grind

private theorem replacementLoop_count
    {S P Q R IO E : Type} (ops : ReplaceFinishOps S P R IO E)
    (onceOps : ReplaceOnceOps S P Q R IO E)
    (write : IO → R → Except E (IO × Index)) (measure : IO → Nat)
    (copyLaw : ∀ io str i len out, onceOps.unsafeWrite io str i len = .ok out → measure out = measure io)
    (writeLaw : ∀ io repl out bytes, write io repl = .ok (out,bytes) → measure out ≤ measure io + 1)
    (str : S) (count e1 : Index) (patterns : List Q) (replaces : List R) (start : Index)
    (countHigh : count.val < JuliaLean.IntTy.i64.max) :
    ∀ fuel io ranges n i out, 1 ≤ n.val → n.val ≤ count.val + 1 →
    replaceFinish.loop ops (replaceOnce (P := P) {onceOps with replace := replaceLiteral write})
      str count e1 patterns replaces start fuel io ranges n i = .ok out →
    Int.ofNat (measure out.1) ≤ Int.ofNat (measure io) + count.val - n.val + 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro io ranges n i out low high run
    simp only [replaceFinish.loop, Except.ok.injEq] at run
    cases run
    dsimp only
    omega
  | succ fuel ih =>
    intro io ranges n i out low high run
    simp only [replaceFinish.loop] at run
    split at run
    · cases run
      dsimp only
      omega
    · rename_i within
      simp only [bind, Except.bind] at run
      split at run
      · cases run
      · rename_i step stepRun
        have stepBound := literalReplaceOnce_count onceOps write measure copyLaw writeLaw
          io str start e1 patterns replaces ranges count n i step stepRun
        have stepInt : Int.ofNat (measure step.io) ≤ Int.ofNat (measure io) + 1 := by
          have bound := Int.ofNat_le.mpr stepBound
          simpa using bound
        split at run
        · cases run
          dsimp only
          omega
        · have hone : (int 1).val = 1 := by decide
          have increment : (n + int 1).val = n.val + 1 := by
            change JuliaLean.wrapInt .i64 (n.val + (int 1).val) = _
            rw [hone]
            have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
            exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
          have bound := ih step.io step.ranges (n + int 1) step.nextIndex out
            (by rw [increment]; omega) (by rw [increment]; omega) run
          rw [increment] at bound
          omega

private theorem replaceFinish_count
    {S P Q R IO E : Type} (ops : ReplaceFinishOps S P R IO E)
    (onceOps : ReplaceOnceOps S P Q R IO E)
    (write : IO → R → Except E (IO × Index)) (measure : IO → Nat)
    (finite : ∀ io, Int.ofNat (measure io) ≤ JuliaLean.IntTy.i64.max)
    (copyLaw : ∀ io str i len out, onceOps.unsafeWrite io str i len = .ok out → measure out = measure io)
    (writeLaw : ∀ io repl out bytes, write io repl = .ok (out,bytes) → measure out ≤ measure io + 1)
    (restLaw : ∀ io str i out, ops.writeRest io str i = .ok out → measure out = measure io)
    (io : IO) (str : S) (count e1 : Index) (patterns : List Q) (replaces : List R)
    (ranges : List ReplaceRange) (out : IO) (nonneg : 0 ≤ count.val)
    (run : replaceFinish ops (replaceOnce (P := P) {onceOps with replace := replaceLiteral write})
      io str count e1 patterns replaces ranges = .ok out) :
    Int.ofNat (measure out) ≤ Int.ofNat (measure io) + count.val := by
  by_cases hmax : count.val = JuliaLean.IntTy.i64.max
  · have hb := finite out
    have positive : 0 ≤ Int.ofNat (measure io) := Int.natCast_nonneg _
    omega
  · have high : count.val < JuliaLean.IntTy.i64.max := by have := count.property.2; omega
    cases hl : replaceFinish.loop ops (replaceOnce (P := P) {onceOps with replace := replaceLiteral write})
        str count e1 patterns replaces (ops.firstindex str) (ops.iterationBound count + 1)
        io ranges (int 1) (ops.firstindex str) with
    | error e => simp [replaceFinish, hl, bind, Except.bind] at run
    | ok value =>
      obtain ⟨nextIO, nextRanges, nextIndex⟩ := value
      have hone : (int 1).val = 1 := by decide
      have limitLow : (int 1).val ≤ count.val + 1 := by rw [hone]; omega
      have bound := replacementLoop_count ops onceOps write measure copyLaw writeLaw
        str count e1 patterns replaces (ops.firstindex str) high (ops.iterationBound count + 1)
        io ranges (int 1) (ops.firstindex str) (nextIO,nextRanges,nextIndex)
        (by decide) limitLow hl
      have rest : ops.writeRest nextIO str nextIndex = .ok out := by
        simp only [replaceFinish, hl, bind, Except.bind] at run
        split at run
        · cases run
        · simpa [bind, Except.bind, pure, Except.pure] using run
      rw [restLaw _ _ _ _ rest]
      rw [hone] at bound
      dsimp only at bound
      omega

def ReplaceCountMin : Prop :=
  ∀ {S P Q R IO E : Type} (ops : ReplaceEngineOps S P Q R IO IO E)
    (write : IO → R → Except E (IO × Index)) (measure : IO → Nat),
    (∀ io, Int.ofNat (measure io) ≤ JuliaLean.IntTy.i64.max) →
    (∀ io str i len out, ops.onceOps.unsafeWrite io str i len = .ok out → measure out = measure io) →
    (∀ io repl out bytes, write io repl = .ok (out,bytes) → measure out ≤ measure io + 1) →
    (∀ io str i out, ops.finishOps.writeRest io str i = .ok out → measure out = measure io) →
    (∀ io str out, ops.writeString io str = .ok out → measure out = measure io) →
    (∀ (io : IO) (str : S) (count e1 : Index) patterns replaces ranges out, 0 ≤ count.val →
      replaceFinish ops.finishOps (replaceOnce (P := P) {ops.onceOps with replace := replaceLiteral write})
        io str count e1 patterns replaces ranges = .ok out →
      Int.ofNat (measure out) ≤ Int.ofNat (measure io) + count.val) ∧
    (∀ (io : IO) (str : S) (pairs : List (ReplacePair P R)) (count : Index) (out : IO),
      replaceIOEngine {ops with onceOps := {ops.onceOps with replace := replaceLiteral write}}
        io str pairs count = .ok out →
      Int.ofNat (measure out) ≤ Int.ofNat (measure io) + count.val)

theorem replaceCountMin_proven : ReplaceCountMin := by
  intro S P Q R IO E ops write measure finite copyLaw writeLaw restLaw stringLaw
  refine ⟨fun io str count e1 patterns replaces ranges out nonneg run =>
    replaceFinish_count ops.finishOps ops.onceOps write measure finite copyLaw writeLaw restLaw
      io str count e1 patterns replaces ranges out nonneg run, ?_⟩
  intro io str pairs count out run
  by_cases hzero : count.val = 0
  · have hw : ops.writeString io str = .ok out := by
      simpa [replaceIOEngine, hzero, bind, Except.bind, pure, Except.pure] using run
    rw [stringLaw _ _ _ hw, hzero]
    omega
  · by_cases hneg : count.val < 0
    · simp [replaceIOEngine, hzero, replaceInit, hneg, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at run
    · have nonneg : 0 ≤ count.val := by omega
      cases hi : replaceInit ops.initOps str pairs count with
      | error e => simp [replaceIOEngine, hzero, hi, bind, Except.bind] at run
      | ok initVal =>
        obtain ⟨e1, patterns, replaces, ranges, notfound⟩ := initVal
        cases notfound with
        | false =>
          have hf : replaceFinish ops.finishOps
              (replaceOnce (P := P) {ops.onceOps with replace := replaceLiteral write})
              io str count e1 patterns replaces ranges = .ok out := by
            simpa [replaceIOEngine, hzero, hi, bind, Except.bind] using run
          exact replaceFinish_count ops.finishOps ops.onceOps write measure
            finite copyLaw writeLaw restLaw io str count e1 patterns replaces ranges out nonneg hf
        | true =>
          simp only [replaceIOEngine, hzero, hi, ↓reduceIte, bind, Except.bind] at run
          split at run
          · cases run
          · have hw : ops.writeString io str = .ok out := by
              simpa [bind, Except.bind, pure, Except.pure] using run
            rw [stringLaw _ _ _ hw]
            omega

def ReplaceCountEdge : Prop :=
  (∀ {S P Q R IO O E : Type} (ops : ReplaceEngineOps S P Q R IO O E)
    (str : S) (pairs : List (ReplacePair P R)) (count : Index),
    (count.val = 0 →
      replaceStringEngine ops str pairs count = ops.toString str) ∧
    (count.val < 0 →
      replaceStringEngine ops str pairs count = .error (ops.initOps.domainError count))) ∧
  (∀ {S P Q R IO O E : Type} (ops : ReplaceEngineOps S P Q R IO O E)
    (write : IO → R → Except E (IO × Index)) (measure : IO → Nat) (outMeasure : O → Nat),
    (∀ io, Int.ofNat (measure io) ≤ JuliaLean.IntTy.i64.max) →
    (∀ io str i len out, ops.onceOps.unsafeWrite io str i len = .ok out → measure out = measure io) →
    (∀ io repl out bytes, write io repl = .ok (out, bytes) → measure out ≤ measure io + 1) →
    (∀ io str i out, ops.finishOps.writeRest io str i = .ok out → measure out = measure io) →
    (∀ s out, ops.toString s = .ok out → outMeasure out = 0) →
    (∀ s io, ops.newBuffer s = .ok io → measure io = 0) →
    (∀ io out, ops.takeString io = .ok out → outMeasure out = measure io) →
    ∀ (str : S) (pairs : List (ReplacePair P R)) (count : Index) (out : O),
      replaceStringEngine {ops with onceOps := {ops.onceOps with replace := replaceLiteral write}}
        str pairs count = .ok out →
      Int.ofNat (outMeasure out) ≤ count.val)

theorem replaceCountEdge_proven : ReplaceCountEdge := by
  refine ⟨?_, ?_⟩
  · intro S P Q R IO O E ops str pairs count
    constructor
    · intro h
      simp [replaceStringEngine, h]
    · intro h
      have hzero : count.val ≠ 0 := by omega
      simp [replaceStringEngine, replaceInit, hzero, h, Bind.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]
  · intro S P Q R IO O E ops write measure outMeasure finite copyLaw writeLaw restLaw
      toStringLaw newBufferLaw takeStringLaw str pairs count out run
    by_cases hzero : count.val = 0
    · have hs : ops.toString str = .ok out := by
        simpa [replaceStringEngine, hzero] using run
      rw [toStringLaw str out hs, hzero]
      decide
    · by_cases hneg : count.val < 0
      · simp [replaceStringEngine, hzero, replaceInit, hneg, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at run
      · have nonneg : 0 ≤ count.val := by omega
        cases hi : replaceInit ops.initOps str pairs count with
        | error e => simp [replaceStringEngine, hzero, hi, bind, Except.bind] at run
        | ok initVal =>
          obtain ⟨e1, patterns, replaces, ranges, notfound⟩ := initVal
          cases notfound with
          | true =>
            simp only [replaceStringEngine, hzero, hi, ↓reduceIte, bind, Except.bind] at run
            split at run
            · cases run
            · have hs : ops.toString str = .ok out := by
                simpa [bind, Except.bind, pure, Except.pure] using run
              rw [toStringLaw str out hs]
              exact nonneg
          | false =>
            dsimp only [replaceStringEngine, bind, Except.bind] at run
            rw [ite_eq_right_iff.mpr (fun h => False.elim (hzero h))] at run
            rw [hi] at run
            dsimp only at run
            cases hb : ops.newBuffer str with
            | error e => simp [hb] at run
            | ok initIO =>
              rw [hb] at run
              dsimp only at run
              cases hf : replaceFinish ops.finishOps
                  (replaceOnce (P := P) {ops.onceOps with replace := replaceLiteral write})
                  initIO str count e1 patterns replaces ranges with
              | error e => simp [hf] at run
              | ok finishedIO =>
                rw [hf] at run
                dsimp only at run
                have hcount := replaceFinish_count ops.finishOps ops.onceOps write measure
                  finite copyLaw writeLaw restLaw initIO str count e1 patterns replaces ranges
                  finishedIO nonneg hf
                rw [takeStringLaw finishedIO out run]
                rw [newBufferLaw str initIO hb] at hcount
                simpa using hcount

private theorem mapM_loop_const {α β E : Type} (f : α → Except E β) (v : β) :
    ∀ (xs : List α) (acc : List β),
      (∀ x ∈ xs, f x = .ok v) →
      List.mapM.loop f xs acc = .ok (acc.reverse ++ List.replicate xs.length v) := by
  intro xs
  induction xs with
  | nil =>
    intro acc _
    simp [List.mapM.loop, pure, Except.pure]
  | cons x rest ih =>
    intro acc hall
    have hx := hall x (by simp)
    have hrest := ih (v :: acc) (fun y hy => hall y (by simp [hy]))
    simpa [List.mapM.loop, hx, List.replicate_succ, List.append_assoc,
      bind, Except.bind] using hrest

private theorem mapM_const {α β E : Type} (f : α → Except E β) (v : β) (xs : List α)
    (hall : ∀ x ∈ xs, f x = .ok v) :
    xs.mapM f = .ok (List.replicate xs.length v) := by
  simpa [List.mapM] using mapM_loop_const f v xs [] hall

private theorem replicate_sentinel_all_gt (e1 : Index)
    (hmax : e1.val < JuliaLean.IntTy.i64.max) :
    ∀ n : Nat,
      (List.replicate n (replaceSentinel e1)).all (fun range => decide (range.first.val > e1.val)) = true
  | 0 => rfl
  | n + 1 => by
    have hone : (int 1).val = 1 := by decide
    have hadd : (e1 + int 1).val = e1.val + 1 := by
      change JuliaLean.wrapInt .i64 (e1.val + (int 1).val) = _
      rw [hone]
      have hmin := e1.property.1
      exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
    have hgt : (replaceSentinel e1).first.val > e1.val := by
      change (e1 + int 1).val > e1.val
      omega
    simp [List.replicate_succ, hgt, replicate_sentinel_all_gt e1 hmax n]

def ReplacementInitContract : Prop :=
  ∀ {S P Q R IO O E : Type} (ops : ReplaceEngineOps S P Q R IO O E)
    (str : S) (pairs : List (ReplacePair P R)) (count : Index),
    (count.val < 0 →
      replaceInit ops.initOps str pairs count = .error (ops.initOps.domainError count) ∧
      replaceStringEngine ops str pairs count = .error (ops.initOps.domainError count)) ∧
    (∀ e1 : Index,
      0 ≤ count.val →
      ops.initOps.nextind str (ops.initOps.lastindex str) = .ok e1 →
      e1.val < JuliaLean.IntTy.i64.max →
      (∀ pair ∈ pairs,
        ops.initOps.findnext (ops.initOps.patternReplacer pair.pattern) str
          (ops.initOps.firstindex str) = .ok none) →
      replaceInit ops.initOps str pairs count =
        .ok (e1,
          pairs.map (fun pair => ops.initOps.patternReplacer pair.pattern),
          pairs.map (·.replacement),
          List.replicate pairs.length (replaceSentinel e1),
          true) ∧
      replaceStringEngine ops str pairs count = ops.toString str)

theorem replacementInitContract_proven : ReplacementInitContract := by
  intro S P Q R IO O E ops str pairs count
  refine ⟨?_, ?_⟩
  · intro hneg
    have hzero : count.val ≠ 0 := by omega
    exact ⟨by simp [replaceInit, hneg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind],
      by simp [replaceStringEngine, replaceInit, hzero, hneg, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind]⟩
  · intro e1 _hnonneg hnext hmax hnone
    have hnotNeg : ¬ count.val < 0 := by omega
    have hall := replicate_sentinel_all_gt e1 hmax pairs.length
    have hinit : replaceInit ops.initOps str pairs count =
        .ok (e1,
          pairs.map (fun pair => ops.initOps.patternReplacer pair.pattern),
          pairs.map (·.replacement),
          List.replicate pairs.length (replaceSentinel e1),
          true) := by
      have hbind : ∀ {α β : Type} (x : Except E α) (v : α) (f : α → Except E β),
          x = .ok v → bind x f = f v := by
        intro _ _ _ _ _ hx; subst hx; rfl
      have hstep : ∀ (x : Except E (List ReplaceRange))
          (f : List ReplaceRange → Except E (Index × List Q × List R × List ReplaceRange × Bool)),
          x = .ok (List.replicate pairs.length (replaceSentinel e1)) →
          bind x f = f (List.replicate pairs.length (replaceSentinel e1)) := by
        intro _ _ hx; rw [hx]; rfl
      unfold replaceInit
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnotNeg h))]
      rw [hbind _ e1 _ hnext]
      dsimp only
      rw [hstep]
      · dsimp only [pure, Except.pure]
        rw [hall]
      · rw [← List.length_map (f := fun pair => ops.initOps.patternReplacer pair.pattern)]
        refine mapM_const _ (replaceSentinel e1)
          (pairs.map fun pair => ops.initOps.patternReplacer pair.pattern) ?_
        intro pattern hp
        obtain ⟨pair, hmem, rfl⟩ := List.mem_map.mp hp
        simp [hnone pair hmem, bind, Except.bind, pure, Except.pure]
    refine ⟨hinit, ?_⟩
    by_cases hzero : count.val = 0
    · simp [replaceStringEngine, hzero]
    · have hfree := mapM_const
        (fun pattern : Q => (Except.ok (freePatReplacer pattern) : Except E Unit))
        ()
        (pairs.map fun pair => ops.initOps.patternReplacer pair.pattern)
        (fun _ _ => rfl)
      unfold replaceStringEngine
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hzero h))]
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [hinit]
      dsimp only [↓reduceIte]
      rw [hfree]
      rfl

def charListWidth {S V R C E : Type} (ops : TruncateOps S V R C E) (chars : List C) : Int :=
  (chars.map (fun c => (ops.textwidthChar c).val)).sum

private theorem charListWidth_nonneg
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2) :
    ∀ chars : List C, 0 ≤ charListWidth ops chars
  | [] => by simp [charListWidth]
  | c :: rest => by
    have hc := (charBounds c).1
    have hrest := charListWidth_nonneg ops charBounds rest
    simp only [charListWidth, List.map_cons, List.sum_cons] at hrest ⊢
    omega

private theorem add_charWidth_val
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2)
    (maxwidth width : Index) (c : C)
    (widthHigh : maxwidth.val + 2 ≤ JuliaLean.IntTy.i64.max)
    (_hnonneg : 0 ≤ width.val) (hle : width.val ≤ maxwidth.val) :
    (width + ops.textwidthChar c).val = width.val + (ops.textwidthChar c).val := by
  have hc := charBounds c
  change JuliaLean.wrapInt .i64 (width.val + (ops.textwidthChar c).val) = _
  have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
  exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩

private theorem add_charWidth_of_total_bound
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2)
    (total : Index) (c : C) (rest : List C)
    (_hnonneg : 0 ≤ total.val)
    (hbound : total.val + charListWidth ops (c :: rest) ≤ JuliaLean.IntTy.i64.max) :
    (total + ops.textwidthChar c).val = total.val + (ops.textwidthChar c).val := by
  have hc := charBounds c
  have hrest := charListWidth_nonneg ops charBounds rest
  have hcons : charListWidth ops (c :: rest) = (ops.textwidthChar c).val + charListWidth ops rest := rfl
  change JuliaLean.wrapInt .i64 (total.val + (ops.textwidthChar c).val) = _
  have hmin : JuliaLean.IntTy.i64.min ≤ 0 := by decide
  exact JuliaLean.wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩

private theorem checkWidthLoop_sum
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2)
    (width : Index) :
    ∀ {steps : IterSteps C Index E} {chars : List C},
      IterStepTrace steps chars →
      ∀ (total : Index),
      0 ≤ total.val → total.val ≤ width.val →
      total.val + charListWidth ops chars ≤ JuliaLean.IntTy.i64.max →
      checkTextwidthLoop ops.textwidthChar width steps total = .ok true →
      total.val + charListWidth ops chars ≤ width.val := by
  intro steps chars htrace
  induction htrace with
  | done =>
    intro total _ hle _ _
    simpa [charListWidth] using hle
  | @yield c state next rest _ ih =>
    intro total hnonneg hle hbound hloop
    have hc := charBounds c
    have hadd := add_charWidth_of_total_bound ops charBounds total c rest hnonneg hbound
    by_cases hgt : (total + ops.textwidthChar c).val > width.val
    · simp [checkTextwidthLoop, hgt] at hloop
    · have hnextLe : (total + ops.textwidthChar c).val ≤ width.val := by omega
      have hnextNonneg : 0 ≤ (total + ops.textwidthChar c).val := by omega
      have htail : checkTextwidthLoop ops.textwidthChar width (next state) (total + ops.textwidthChar c) = .ok true := by
        simpa [checkTextwidthLoop, hgt] using hloop
      have hnextBound : (total + ops.textwidthChar c).val + charListWidth ops rest ≤ JuliaLean.IntTy.i64.max := by
        simp only [charListWidth, List.map_cons, List.sum_cons] at hbound ⊢
        omega
      have hrec := ih (total + ops.textwidthChar c) hnextNonneg hnextLe hnextBound htail
      simp only [charListWidth, List.map_cons, List.sum_cons] at hrec ⊢
      omega

private theorem checkWidthLoop_false_lt
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2)
    (width : Index) :
    ∀ {steps : IterSteps C Index E} {chars : List C},
      IterStepTrace steps chars →
      ∀ (total : Index),
      0 ≤ total.val →
      total.val + charListWidth ops chars ≤ JuliaLean.IntTy.i64.max →
      checkTextwidthLoop ops.textwidthChar width steps total = .ok false →
      width.val < total.val + charListWidth ops chars := by
  intro steps chars htrace
  induction htrace with
  | done =>
    intro total _ _ hloop
    simp [checkTextwidthLoop] at hloop
  | @yield c state next rest _ ih =>
    intro total hnonneg hbound hloop
    have hc := charBounds c
    have hrest := charListWidth_nonneg ops charBounds rest
    have hadd := add_charWidth_of_total_bound ops charBounds total c rest hnonneg hbound
    have hcons : charListWidth ops (c :: rest) = (ops.textwidthChar c).val + charListWidth ops rest := rfl
    by_cases hgt : (total + ops.textwidthChar c).val > width.val
    · omega
    · have hnextNonneg : 0 ≤ (total + ops.textwidthChar c).val := by omega
      have hnextBound : (total + ops.textwidthChar c).val + charListWidth ops rest ≤ JuliaLean.IntTy.i64.max := by
        simp only [charListWidth, List.map_cons, List.sum_cons] at hbound ⊢
        omega
      have htail : checkTextwidthLoop ops.textwidthChar width (next state) (total + ops.textwidthChar c) = .ok false := by
        simpa [checkTextwidthLoop, hgt] using hloop
      have hrec := ih (total + ops.textwidthChar c) hnextNonneg hnextBound htail
      simp only [charListWidth, List.map_cons, List.sum_cons] at hrec ⊢
      omega

private theorem checkWidthLoop_true_of_le
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (charBounds : ∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2)
    (width : Index) :
    ∀ {steps : IterSteps C Index E} {chars : List C},
      IterStepTrace steps chars →
      ∀ (total : Index),
      0 ≤ total.val →
      total.val + charListWidth ops chars ≤ width.val →
      checkTextwidthLoop ops.textwidthChar width steps total = .ok true := by
  intro steps chars htrace
  induction htrace with
  | done =>
    intro total _ _
    rfl
  | @yield c state next rest _ ih =>
    intro total hnonneg hle
    have hc := charBounds c
    have hrest := charListWidth_nonneg ops charBounds rest
    have hmax := width.property.2
    have hbound : total.val + charListWidth ops (c :: rest) ≤ JuliaLean.IntTy.i64.max := by omega
    have hadd := add_charWidth_of_total_bound ops charBounds total c rest hnonneg hbound
    have hcons : charListWidth ops (c :: rest) = (ops.textwidthChar c).val + charListWidth ops rest := rfl
    have hnotGt : ¬ (total + ops.textwidthChar c).val > width.val := by
      omega
    have hnextLe : (total + ops.textwidthChar c).val + charListWidth ops rest ≤ width.val := by
      simp only [charListWidth, List.map_cons, List.sum_cons] at hle ⊢
      omega
    have htail := ih (total + ops.textwidthChar c) (by omega) hnextLe
    simpa [checkTextwidthLoop, hnotGt] using htail

def TruncateInterface {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (replacement : R) (strChars : List C) (prefixWidth suffixWidth : Index → Int) : Prop :=
  (∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2) ∧
  IterStepTrace (ops.iterate str) strChars ∧
  charListWidth ops strChars + 2 ≤ JuliaLean.IntTy.i64.max ∧
  prefixWidth (ops.firstindex str) = 0 ∧
  suffixWidth (ops.lastindex str) = 0 ∧
  (∀ left c nextLeft,
    ops.getindex str left = .ok c →
    ops.nextind str left = .ok nextLeft →
    prefixWidth nextLeft = prefixWidth left + (ops.textwidthChar c).val) ∧
  (∀ right c prevRight,
    ops.getindex str right = .ok c →
    ops.prevind str right = .ok prevRight →
    suffixWidth prevRight = suffixWidth right + (ops.textwidthChar c).val) ∧
  (∀ out chars,
    ops.stringify str = .ok out →
    IterStepTrace (ops.iterate out) chars →
    chars = strChars) ∧
  (∀ rw left0 left view replStr out chars,
    ops.textwidthReplacement replacement = .ok rw →
    ops.prevind str left0 = .ok left →
    ops.substring str (ops.firstindex str) left = .ok view →
    ops.stringifyReplacement replacement = .ok replStr →
    ops.concat [.view view, .string replStr] = .ok out →
    IterStepTrace (ops.iterate out) chars →
    charListWidth ops chars = prefixWidth left0 + rw.val) ∧
  (∀ rw right0 right view replStr out chars,
    ops.textwidthReplacement replacement = .ok rw →
    ops.nextind str right0 = .ok right →
    ops.substring str right (ops.lastindex str) = .ok view →
    ops.stringifyReplacement replacement = .ok replStr →
    ops.concat [.string replStr, .view view] = .ok out →
    IterStepTrace (ops.iterate out) chars →
    charListWidth ops chars = rw.val + suffixWidth right0) ∧
  (∀ rw left0 right0 left right viewL viewR replStr out chars,
    ops.textwidthReplacement replacement = .ok rw →
    ops.prevind str left0 = .ok left →
    ops.nextind str right0 = .ok right →
    ops.substring str (ops.firstindex str) left = .ok viewL →
    ops.substring str right (ops.lastindex str) = .ok viewR →
    ops.stringifyReplacement replacement = .ok replStr →
    ops.concat [.view viewL, .string replStr, .view viewR] = .ok out →
    IterStepTrace (ops.iterate out) chars →
    charListWidth ops chars = prefixWidth left0 + rw.val + suffixWidth right0)

private theorem truncateLoop_width_bound
    {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (replacement : R) (strChars : List C) (maxwidth : Index) (mode : TruncMode) (preferLeft : Bool)
    (prefixWidth suffixWidth : Index → Int) (rwVal : Int)
    (interface : TruncateInterface ops str replacement strChars prefixWidth suffixWidth)
    (hRwNonneg : 0 ≤ rwVal)
    (widthHigh : maxwidth.val + 2 ≤ JuliaLean.IntTy.i64.max) :
    ∀ (fuel : Nat) (left right width removedLeft removedRight : Index) (forceOther : Bool)
      (finalLeft finalRight : Index),
      0 ≤ prefixWidth left →
      0 ≤ suffixWidth right →
      width.val = rwVal + prefixWidth left + suffixWidth right →
      width.val ≤ maxwidth.val →
      truncateLoop ops str maxwidth mode preferLeft fuel left right width
        removedLeft removedRight forceOther = .ok (finalLeft, finalRight) →
      0 ≤ prefixWidth finalLeft ∧
        0 ≤ suffixWidth finalRight ∧
        rwVal + prefixWidth finalLeft + suffixWidth finalRight ≤ maxwidth.val := by
  rcases interface with ⟨charBounds, _, _, _, _, nextLaw, prevLaw, _, _, _, _⟩
  intro fuel
  induction fuel with
  | zero =>
    intro left right width removedLeft removedRight forceOther finalLeft finalRight
      hL hR hW hLe hrun
    simp only [truncateLoop, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨hL, hR, by omega⟩
  | succ fuel ih =>
    intro left right width removedLeft removedRight forceOther finalLeft finalRight
      hL hR hW hLe hrun
    have hSecond :
        ∀ (right1 width1 removedRight1 : Index) (forceOther1 : Bool),
          0 ≤ suffixWidth right1 →
          width1.val = rwVal + prefixWidth left + suffixWidth right1 →
          width1.val ≤ maxwidth.val →
          (if mode == .right || mode == .center then do
            let removed ← textwidthAt ops str left
            if mode == .left || removedLeft.val ≤ removedRight1.val || forceOther1 then
              if (width1 + removed).val ≤ maxwidth.val then do
                let left ← ops.nextind str left
                return ← truncateLoop ops str maxwidth mode preferLeft fuel left right1 (width1 + removed)
                  (removedLeft + removed) removedRight1 false
              else return (left, right1)
            else
              return ← truncateLoop ops str maxwidth mode preferLeft fuel left right1 width1
                removedLeft removedRight1 true
          else
            truncateLoop ops str maxwidth mode preferLeft fuel left right1 width1
              removedLeft removedRight1 forceOther1) = .ok (finalLeft, finalRight) →
          0 ≤ prefixWidth finalLeft ∧
            0 ≤ suffixWidth finalRight ∧
            rwVal + prefixWidth finalLeft + suffixWidth finalRight ≤ maxwidth.val := by
      intro right1 width1 removedRight1 forceOther1 hR1 hW1 hLe1 hstep2
      split at hstep2
      · cases hg : ops.getindex str left with
        | error e => simp [textwidthAt, hg, bind, Except.bind] at hstep2
        | ok cL =>
          have hcL := charBounds cL
          have haddL := add_charWidth_val ops charBounds maxwidth width1 cL widthHigh (by omega) hLe1
          simp only [textwidthAt, hg, bind, Except.bind, pure, Except.pure] at hstep2
          split at hstep2
          · split at hstep2
            · rename_i hfitL
              cases hn : ops.nextind str left with
              | error e => simp [hn] at hstep2
              | ok nextLeft =>
                have hnextW := nextLaw left cL nextLeft hg hn
                simp only [hn] at hstep2
                exact ih nextLeft right1 (width1 + ops.textwidthChar cL)
                  (removedLeft + ops.textwidthChar cL) removedRight1 false finalLeft finalRight
                  (by omega) hR1 (by omega) hfitL hstep2
            · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep2
              rcases hstep2 with ⟨rfl, rfl⟩
              exact ⟨hL, hR1, by omega⟩
          · exact ih left right1 width1 removedLeft removedRight1 true finalLeft finalRight
              hL hR1 hW1 hLe1 hstep2
      · exact ih left right1 width1 removedLeft removedRight1 forceOther1 finalLeft finalRight
          hL hR1 hW1 hLe1 hstep2
    unfold truncateLoop at hrun
    by_cases hremR : (mode == .left || (mode == .center && (!preferLeft || decide (left.val > (ops.firstindex str).val)))) = true
    · simp only [hremR, ↓reduceIte] at hrun
      cases hgR : ops.getindex str right with
      | error e => simp [textwidthAt, hgR, bind, Except.bind] at hrun
      | ok cR =>
        have hcR := charBounds cR
        have haddR := add_charWidth_val ops charBounds maxwidth width cR widthHigh (by omega) hLe
        simp only [textwidthAt, hgR, bind, Except.bind, pure, Except.pure] at hrun
        by_cases hcondR : (mode == .left || decide (removedRight.val ≤ removedLeft.val) || forceOther) = true
        · simp only [hcondR, ↓reduceIte] at hrun
          by_cases hfitR : (width + ops.textwidthChar cR).val ≤ maxwidth.val
          · simp only [hfitR, ↓reduceIte] at hrun
            cases hpR : ops.prevind str right with
            | error e => simp [hpR] at hrun
            | ok prevRight =>
              have hprevW := prevLaw right cR prevRight hgR hpR
              simp only [hpR] at hrun
              exact hSecond prevRight (width + ops.textwidthChar cR)
                (removedRight + ops.textwidthChar cR) false (by omega) (by omega) hfitR hrun
          · simp only [hfitR, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrun
            rcases hrun with ⟨rfl, rfl⟩
            exact ⟨hL, hR, by omega⟩
        · simp only [hcondR, Bool.false_eq_true, ↓reduceIte] at hrun
          exact hSecond right width removedRight true hR hW hLe hrun
    · simp only [hremR, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hrun
      exact hSecond right width removedRight forceOther hR hW hLe hrun

def TruncateWidthBound : Prop :=
  ∀ {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (replacement : R) (strChars : List C) (width rw : Index) (preferLeft : Bool)
    (prefixWidth suffixWidth : Index → Int),
    TruncateInterface ops str replacement strChars prefixWidth suffixWidth →
    (width.val < 0 →
      stringTruncateBoundaries ops str width replacement .right true =
        .error (ops.argumentError ("maxwidth " ++ toString width.val ++ " should be non-negative")) ∧
      rtruncate ops str width replacement =
        .error (ops.argumentError ("maxwidth " ++ toString width.val ++ " should be non-negative")) ∧
      ltruncate ops str width replacement =
        .error (ops.argumentError ("maxwidth " ++ toString width.val ++ " should be non-negative")) ∧
      ctruncate ops str width replacement preferLeft =
        .error (ops.argumentError ("maxwidth " ++ toString width.val ++ " should be non-negative"))) ∧
    (ops.textwidthReplacement replacement = .ok rw →
      0 ≤ rw.val →
      rw.val ≤ width.val →
      (checkTextwidth ops str width = .ok (decide (charListWidth ops strChars ≤ width.val))) ∧
      (∀ out chars, rtruncate ops str width replacement = .ok out →
        IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val) ∧
      (∀ out chars, ltruncate ops str width replacement = .ok out →
        IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val) ∧
      (∀ out chars, ctruncate ops str width replacement preferLeft = .ok out →
        IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val))

theorem truncateWidthBound_proven : TruncateWidthBound := by
  intro S V R C E ops str replacement strChars width rw preferLeft prefixWidth suffixWidth
    interface
  refine ⟨?_, ?_⟩
  · intro hneg
    simp [rtruncate, ltruncate, ctruncate, stringTruncateBoundaries, hneg,
      bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro hrw hrwNonneg hrwLe
    have hwidthNonneg : 0 ≤ width.val := by omega
    have hnotNeg : ¬ width.val < 0 := by omega
    have hstrTrace := interface.2.1
    have hstrMax := interface.2.2.1
    have hzeroVal : (int 0).val = 0 := by decide
    have hstrBound : (int 0).val + charListWidth ops strChars ≤ JuliaLean.IntTy.i64.max := by
      rw [hzeroVal]; omega
    have hCheckDecide :
        checkTextwidth ops str width = .ok (decide (charListWidth ops strChars ≤ width.val)) := by
      by_cases hfit : charListWidth ops strChars ≤ width.val
      · have htrue := checkWidthLoop_true_of_le ops interface.1 width hstrTrace (int 0)
          (by rw [hzeroVal]; omega) (by rw [hzeroVal]; simpa using hfit)
        simpa [checkTextwidth, hfit] using htrue
      · cases hchk : checkTextwidthLoop ops.textwidthChar width (ops.iterate str) (int 0) with
        | error e =>
          exfalso
          have hsumOrFalse :
              ∀ {steps : IterSteps C Index E} {chars : List C},
                IterStepTrace steps chars →
                ∀ total, ∃ b, checkTextwidthLoop ops.textwidthChar width steps total = .ok b := by
            intro steps chars htr
            induction htr with
            | done => intro total; exact ⟨true, rfl⟩
            | @yield c state next rest _ ih =>
              intro total
              by_cases hgt : (total + ops.textwidthChar c).val > width.val
              · exact ⟨false, by simp [checkTextwidthLoop, hgt]⟩
              · obtain ⟨b, hb⟩ := ih (total + ops.textwidthChar c)
                exact ⟨b, by simpa [checkTextwidthLoop, hgt] using hb⟩
          obtain ⟨b, hb⟩ := hsumOrFalse hstrTrace (int 0)
          rw [hchk] at hb
          cases hb
        | ok b =>
          cases b with
          | false =>
            simpa [checkTextwidth, hfit] using hchk
          | true =>
            have hsum := checkWidthLoop_sum ops interface.1 width hstrTrace (int 0)
              (by rw [hzeroVal]; omega) (by rw [hzeroVal]; exact hwidthNonneg) hstrBound hchk
            rw [hzeroVal, Int.zero_add] at hsum
            exact False.elim (hfit hsum)
    have hCheckTrue :
        ∀ out chars,
          checkTextwidth ops str width = .ok true →
          ops.stringify str = .ok out →
          IterStepTrace (ops.iterate out) chars →
          charListWidth ops chars ≤ width.val := by
      intro out chars hcheck hstr hchars
      have heq := interface.2.2.2.2.2.2.2.1 out chars hstr hchars
      subst chars
      have hsum := checkWidthLoop_sum ops interface.1 width hstrTrace (int 0)
        (by rw [hzeroVal]; omega) (by rw [hzeroVal]; exact hwidthNonneg) hstrBound
        (by simpa [checkTextwidth] using hcheck)
      omega
    have hBoundariesNone :
        ∀ mode pref,
          stringTruncateBoundaries ops str width replacement mode pref = .ok none →
          checkTextwidth ops str width = .ok true := by
      intro mode pref hbound
      simp only [stringTruncateBoundaries, hnotNeg, ↓reduceIte, bind, Except.bind] at hbound
      cases hchk : checkTextwidth ops str width with
      | error e => simp [hchk] at hbound
      | ok b =>
        cases b with
        | true => rfl
        | false =>
          simp only [hchk, Bool.false_eq_true, ↓reduceIte, hrw] at hbound
          cases hloop : truncateLoop ops str width mode pref (ops.iterationBound str * 2 + 4)
              (ops.firstindex str) (ops.lastindex str) rw (int 0) (int 0) false with
          | error e => simp [hloop] at hbound
          | ok pair =>
            obtain ⟨left0, right0⟩ := pair
            simp only [hloop] at hbound
            cases hp : ops.prevind str left0 with
            | error e => simp [hp] at hbound
            | ok prevL =>
              simp only [hp] at hbound
              cases hn : ops.nextind str right0 with
              | error e => simp [hn] at hbound
              | ok nextR => simp [hn, pure, Except.pure] at hbound
    have hBoundaries :
        ∀ mode pref left right,
          stringTruncateBoundaries ops str width replacement mode pref = .ok (some (left, right)) →
          ∃ left0 right0,
            ops.prevind str left0 = .ok left ∧
            ops.nextind str right0 = .ok right ∧
            0 ≤ prefixWidth left0 ∧
            0 ≤ suffixWidth right0 ∧
            rw.val + prefixWidth left0 + suffixWidth right0 ≤ width.val := by
      intro mode pref left right hbound
      simp only [stringTruncateBoundaries, hnotNeg, ↓reduceIte, bind, Except.bind] at hbound
      cases hchk : checkTextwidth ops str width with
      | error e => simp [hchk] at hbound
      | ok b =>
        cases b with
        | true => simp [hchk, pure, Except.pure] at hbound
        | false =>
          have hlt := checkWidthLoop_false_lt ops interface.1 width hstrTrace (int 0)
            (by rw [hzeroVal]; omega) hstrBound (by simpa [checkTextwidth] using hchk)
          have widthHigh : width.val + 2 ≤ JuliaLean.IntTy.i64.max := by
            rw [hzeroVal] at hlt
            omega
          simp only [hchk, Bool.false_eq_true, ↓reduceIte, hrw] at hbound
          cases hloop : truncateLoop ops str width mode pref (ops.iterationBound str * 2 + 4)
              (ops.firstindex str) (ops.lastindex str) rw (int 0) (int 0) false with
          | error e => simp [hloop] at hbound
          | ok pair =>
            obtain ⟨left0, right0⟩ := pair
            simp only [hloop] at hbound
            cases hp : ops.prevind str left0 with
            | error e => simp [hp] at hbound
            | ok prevL =>
              simp only [hp] at hbound
              cases hn : ops.nextind str right0 with
              | error e => simp [hn] at hbound
              | ok nextR =>
                simp only [hn, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hbound
                rcases hbound with ⟨rfl, rfl⟩
                have hfirstW := interface.2.2.2.1
                have hlastW := interface.2.2.2.2.1
                have hinv := truncateLoop_width_bound ops str replacement strChars width mode pref
                  prefixWidth suffixWidth rw.val interface hrwNonneg widthHigh
                  (ops.iterationBound str * 2 + 4) (ops.firstindex str) (ops.lastindex str)
                  rw (int 0) (int 0) false left0 right0
                  (by omega) (by omega) (by omega) hrwLe hloop
                exact ⟨left0, right0, hp, hn, hinv.1, hinv.2.1, hinv.2.2⟩
    refine ⟨hCheckDecide, ?_, ?_, ?_⟩
    · intro out chars hrun hchars
      simp only [rtruncate, bind, Except.bind] at hrun
      cases hb : stringTruncateBoundaries ops str width replacement .right true with
      | error e => simp [hb] at hrun
      | ok opt =>
        cases opt with
        | none =>
          simp only [hb] at hrun
          exact hCheckTrue out chars (hBoundariesNone .right true hb) hrun hchars
        | some pair =>
          obtain ⟨left, right⟩ := pair
          simp only [hb] at hrun
          obtain ⟨left0, right0, hp, _, _, hR0, hsum⟩ := hBoundaries .right true left right hb
          cases hs : ops.substring str (ops.firstindex str) left with
          | error e => simp [hs] at hrun
          | ok view =>
            simp only [hs] at hrun
            cases hsr : ops.stringifyReplacement replacement with
            | error e => simp [hsr] at hrun
            | ok replStr =>
              simp only [hsr] at hrun
              have hcw := interface.2.2.2.2.2.2.2.2.1 rw left0 left view replStr out chars
                hrw hp hs hsr hrun hchars
              omega
    · intro out chars hrun hchars
      simp only [ltruncate, bind, Except.bind] at hrun
      cases hb : stringTruncateBoundaries ops str width replacement .left true with
      | error e => simp [hb] at hrun
      | ok opt =>
        cases opt with
        | none =>
          simp only [hb] at hrun
          exact hCheckTrue out chars (hBoundariesNone .left true hb) hrun hchars
        | some pair =>
          obtain ⟨left, right⟩ := pair
          simp only [hb] at hrun
          obtain ⟨left0, right0, _, hn, hL0, _, hsum⟩ := hBoundaries .left true left right hb
          cases hs : ops.substring str right (ops.lastindex str) with
          | error e => simp [hs] at hrun
          | ok view =>
            simp only [hs] at hrun
            cases hsr : ops.stringifyReplacement replacement with
            | error e => simp [hsr] at hrun
            | ok replStr =>
              simp only [hsr] at hrun
              have hcw := interface.2.2.2.2.2.2.2.2.2.1 rw right0 right view replStr out chars
                hrw hn hs hsr hrun hchars
              omega
    · intro out chars hrun hchars
      simp only [ctruncate, bind, Except.bind] at hrun
      cases hb : stringTruncateBoundaries ops str width replacement .center preferLeft with
      | error e => simp [hb] at hrun
      | ok opt =>
        cases opt with
        | none =>
          simp only [hb] at hrun
          exact hCheckTrue out chars (hBoundariesNone .center preferLeft hb) hrun hchars
        | some pair =>
          obtain ⟨left, right⟩ := pair
          simp only [hb] at hrun
          obtain ⟨left0, right0, hp, hn, _, _, hsum⟩ := hBoundaries .center preferLeft left right hb
          cases hsL : ops.substring str (ops.firstindex str) left with
          | error e => simp [hsL] at hrun
          | ok viewL =>
            simp only [hsL] at hrun
            cases hsR : ops.substring str right (ops.lastindex str) with
            | error e => simp [hsR] at hrun
            | ok viewR =>
              simp only [hsR] at hrun
              cases hsr : ops.stringifyReplacement replacement with
              | error e => simp [hsr] at hrun
              | ok replStr =>
                simp only [hsr] at hrun
                have hcw := interface.2.2.2.2.2.2.2.2.2.2 rw left0 right0 left right viewL viewR replStr out chars
                  hrw hp hn hsL hsR hsr hrun hchars
                omega
def SplitLimitInteger : Prop :=
  ∀ {S F : Type} (methodError : String → JuliaLean.JlError) (str : S) (splitter : F)
    (t : JuliaLean.IntTy) (limit : JuliaLean.JInt t) (keepempty : Bool),
    -(2 ^ 63 : Int) ≤ limit.val → limit.val < 2 ^ 63 →
    eachsplitGeneric (fun _ : JuliaLean.JInt t => decide (t = .i64))
      (JuliaLean.base.int.convert .i64) methodError str splitter limit keepempty =
    eachsplitGeneric (fun _ : Index => true) (JuliaLean.base.int.convert .i64)
      methodError str splitter (int limit.val) keepempty

theorem splitLimitInteger_refuted : ¬ SplitLimitInteger := by
  intro h
  have hbad := h JuliaLean.JlError.methodError () () .u64 (JuliaLean.JInt.lit .u64 2)
    true (by decide) (by decide)
  have hactual :
      eachsplitGeneric (fun _ : Index => true) (JuliaLean.base.int.convert .i64)
        JuliaLean.JlError.methodError () () (int 2) true =
        .ok (⟨(), (), int 2, true⟩ : SplitIteratorModel Unit Unit) := by rfl
  change Except.error (JuliaLean.JlError.methodError "SplitIterator") = _ at hbad
  have hv : (JuliaLean.JInt.lit .u64 2).val = 2 := by decide
  rw [hv, hactual] at hbad
  cases hbad

def TruncateWidth : Prop :=
  ∀ {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (replacement : R) (strChars : List C) (width rw : Index) (preferLeft : Bool)
    (prefixWidth suffixWidth : Index → Int),
    TruncateInterface ops str replacement strChars prefixWidth suffixWidth →
    ops.textwidthReplacement replacement = .ok rw →
    0 ≤ rw.val → rw.val ≤ width.val → 0 ≤ width.val →
    (∀ out chars, rtruncate ops str width replacement = .ok out →
      IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val) ∧
    (∀ out chars, ltruncate ops str width replacement = .ok out →
      IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val) ∧
    (∀ out chars, ctruncate ops str width replacement preferLeft = .ok out →
      IterStepTrace (ops.iterate out) chars → charListWidth ops chars ≤ width.val)

/-- The docstring's width promise holds whenever the replacement itself fits within the
requested maximum width; the three-mode specialization of the general bound. -/
theorem truncateWidth_proven : TruncateWidth := by
  intro S V R C E ops str replacement strChars width rw preferLeft prefixWidth suffixWidth
    interface hrw hrwNonneg hrwLe _hwidthNonneg
  have hbound := truncateWidthBound_proven ops str replacement strChars width rw preferLeft
    prefixWidth suffixWidth interface
  have hsecond := hbound.2 hrw hrwNonneg hrwLe
  exact ⟨hsecond.2.1, hsecond.2.2.1, hsecond.2.2.2⟩

/-! ## Overflow in generic index arithmetic -/

def dataLastindex (s : StringData) : Index :=
  s.starts.foldl (fun _ i => i) (int 0)

def dataSubstring (s : StringData) (i j : Index) :
    Except JuliaLean.JlError StringData :=
  if j.val < i.val then .ok StringData.empty
  else if i.val < 1 ∨ Int.ofNat s.bytes.length < j.val then .error .boundsError
  else .ok (stringDataSlice s i j)

def ChopTooMany : Prop :=
  ∀ (s : StringData) (head tail : Index),
    0 ≤ head.val → 0 ≤ tail.val → Int.ofNat s.chars.length ≤ head.val + tail.val →
    ∃ out,
      chop (isemptyString stringDataOps) (fun s => .ok s)
        (fun _ => int 1) dataLastindex
        (nextindInt stringDataOps (fun _ => ""))
        (previndInt stringDataOps (fun _ => "")) dataSubstring s head tail = .ok out ∧
      out.bytes = []

set_option maxRecDepth 10000 in
theorem chopTooMany_refuted : ¬ ChopTooMany := by
  intro h
  let s : StringData := ⟨[0x61, 0x62], [int 1, int 2], [0x61, 0x62]⟩
  let maxInt := int ((2 : Int) ^ 63 - 1)
  obtain ⟨out, hbad, _⟩ := h s maxInt (int 0) (by decide) (by decide) (by decide)
  have hactual :
      chop (isemptyString stringDataOps) (fun s => .ok s)
        (fun _ => int 1) dataLastindex
        (nextindInt stringDataOps (fun _ => ""))
        (previndInt stringDataOps (fun _ => "")) dataSubstring s maxInt (int 0) =
        .error .boundsError := by
    dsimp only [s, maxInt]
    decide +kernel
  rw [hactual] at hbad
  cases hbad

def dataPartitionOps : PartitionOps StringData StringData JuliaLean.JlError where
  ncodeunits s := int s.bytes.length
  firstindex _ := int 1
  lastindex := dataLastindex
  nextindN := nextindInt stringDataOps (fun _ => "")
  nextind := nextindOne stringDataOps
  substring := dataSubstring

def PartitionWhole : Prop :=
  ∀ (s : StringData) (n : Index),
    1 ≤ s.bytes.length → Int.ofNat s.chars.length ≤ n.val →
    ∃ out next,
      iteratePartition dataPartitionOps ⟨s, n⟩ = .ok (some (out, next)) ∧
      out.bytes = s.bytes

set_option maxRecDepth 10000 in
theorem partitionWhole_refuted : ¬ PartitionWhole := by
  intro h
  let s : StringData :=
    ⟨[0xc3, 0xa9, 0xe2, 0x82, 0xac], [int 1, int 3], [0xe9, 0x20ac]⟩
  let maxInt := int ((2 : Int) ^ 63 - 1)
  obtain ⟨out, next, hbad, _⟩ := h s maxInt (by decide) (by decide)
  have hactual : iteratePartition dataPartitionOps ⟨s, maxInt⟩ =
      .error .boundsError := by
    dsimp only [s, maxInt]
    decide +kernel
  rw [hactual] at hbad
  cases hbad

/-! ## Replacement output versus the external match sequence -/

def byteReplacementOps
    (findnext : Unit → List UInt8 → Index → Except String (Option ReplaceRange)) :
    ReplaceEngineOps (List UInt8) Unit Unit (List UInt8) (List UInt8) (List UInt8) String where
  initOps :=
    { patternReplacer := patReplacer
      firstindex := fun _ => int 1
      lastindex := fun s => int s.length
      nextind := fun _ i => .ok (i + int 1)
      findnext := findnext
      domainError := fun _ => "DomainError" }
  finishOps :=
    { firstindex := fun _ => int 1
      first := ReplaceRange.first
      writeRest := fun io s i => .ok (io ++ s.drop (i.val - 1).toNat)
      iterationBound := fun count => count.val.toNat }
  onceOps :=
    { argmin := fun xs =>
        let values := xs.map (fun i => i.val)
        int ((values.idxOf (values.foldl min (values.headD 0))) + 1)
      selectRange := fun xs i => match xs[i.val.toNat - 1]? with
        | some r => .ok r
        | none => .error "BoundsError"
      selectPattern := fun xs i => match xs[i.val.toNat - 1]? with
        | some p => .ok p
        | none => .error "BoundsError"
      selectReplacement := fun xs i => match xs[i.val.toNat - 1]? with
        | some r => .ok r
        | none => .error "BoundsError"
      first := ReplaceRange.first
      last := ReplaceRange.last
      unsafeWrite := fun io s i n => .ok (io ++ (s.drop (i.val - 1).toNat).take n.val.toNat)
      replace := replaceLiteral (fun io repl => .ok (io ++ repl, int repl.length))
      nextind := fun _ i => .ok (i + int 1)
      findnext := findnext }
  writeString := fun io s => .ok (io ++ s)
  newBuffer := fun _ => .ok []
  takeString := fun io => .ok io
  toString := fun s => .ok s

/-! `MatchTrace` is the documented non-overlapping match-iterator interface:
advance past a nonempty match, and advance one character after an empty one. -/
inductive MatchTrace
    (finder : Unit → List UInt8 → Index → Except String (Option ReplaceRange))
    (s : List UInt8) : Index → List ReplaceRange → Prop where
  | nil {i : Index} (finished : finder () s i = .ok none) : MatchTrace finder s i []
  | cons {i : Index} {r : ReplaceRange} {rest : List ReplaceRange}
      (found : finder () s i = .ok (some r))
      (tail : MatchTrace finder s
        (if r.last.val < r.first.val then r.first + int 1 else r.last + int 1) rest) :
      MatchTrace finder s i (r :: rest)

def assembleMatches (s replacement : List UInt8) : Index → List ReplaceRange → List UInt8
  | previous, [] => s.drop (previous.val - 1).toNat
  | previous, r :: rest =>
    (s.drop (previous.val - 1).toNat).take (r.first.val - previous.val).toNat ++ replacement ++
      assembleMatches s replacement
        (if r.last.val < r.first.val then r.first else r.last + int 1) rest

def ReplaceAssemblesEachmatch : Prop :=
  ∀ (finder : Unit → List UInt8 → Index → Except String (Option ReplaceRange))
    (s replacement : List UInt8) (ms : List ReplaceRange) (count : Index),
    (∀ c ∈ s, c.toNat < 128) →
    MatchTrace finder s (int 1) ms →
    Int.ofNat ms.length ≤ count.val →
    replaceStringEngine (byteReplacementOps finder) s [⟨(), replacement⟩] count =
      .ok (assembleMatches s replacement (int 1) ms)

/-- The ASCII `x*` finder, including its empty matches at ordinary and final positions. -/
def xStarFinder (_ : Unit) (s : List UInt8) (i : Index) :
    Except String (Option ReplaceRange) :=
  if i.val < 1 ∨ Int.ofNat s.length + 1 < i.val then .ok none
  else
    let run := ((s.drop (i.val - 1).toNat).takeWhile (· == 0x78)).length
    .ok (some ⟨i, i + int run - int 1⟩)

set_option maxRecDepth 10000 in
theorem replaceAssemblesEachmatch_refuted : ¬ ReplaceAssemblesEachmatch := by
  intro h
  let s : List UInt8 := [0x61, 0x62, 0x78, 0x64]
  let ms : List ReplaceRange :=
    [⟨int 1, int 0⟩, ⟨int 2, int 1⟩, ⟨int 3, int 3⟩, ⟨int 4, int 3⟩, ⟨int 5, int 4⟩]
  have trace : MatchTrace xStarFinder s (int 1) ms := by
    apply MatchTrace.cons (by decide +kernel)
    apply MatchTrace.cons (by decide +kernel)
    apply MatchTrace.cons (by decide +kernel)
    apply MatchTrace.cons (by decide +kernel)
    apply MatchTrace.cons (by decide +kernel)
    apply MatchTrace.nil (by decide +kernel)
  have hbad := h xStarFinder s [0x2d] ms (int 10)
    (by simp [s]) trace (by decide)
  have hactual :
      replaceStringEngine (byteReplacementOps xStarFinder) s [⟨(), [0x2d]⟩] (int 10) =
      .ok [0x2d, 0x61, 0x2d, 0x62, 0x2d, 0x64, 0x2d] := by
    dsimp only [s]
    decide +kernel
  rw [hactual] at hbad
  have hnot : ([0x2d, 0x61, 0x2d, 0x62, 0x2d, 0x64, 0x2d] : List UInt8) ≠
      assembleMatches s [0x2d] (int 1) ms := by decide +kernel
  exact hnot (Except.ok.inj hbad)

/-! ## Malformed UTF-8 concatenation

These primitive callbacks group the bytes of a Julia character, including incomplete byte
sequences. Utility methods still execute their source definitions; no padding result is supplied.
-/

def byteCharacters : List UInt8 → List (List UInt8)
  | [] => []
  | c :: rest =>
    let count := if 0xc0 ≤ c && c < 0xe0 then 1
      else if 0xe0 ≤ c && c < 0xf0 then 2
      else if 0xf0 ≤ c && c < 0xf8 then 3 else 0
    let continuation := (rest.take count).takeWhile (fun b => b &&& 0xc0 == 0x80)
    (c :: continuation) :: byteCharacters (rest.drop continuation.length)
termination_by bytes => bytes.length
decreasing_by
  simp_wf
  omega

def byteCharacterPairs : Index → List (List UInt8) → List (Index × List UInt8)
  | _, [] => []
  | i, c :: rest => (i, c) :: byteCharacterPairs (i + int c.length) rest

def byteTextwidth (cw : List UInt8 → Int) (s : List UInt8) : Int :=
  ((byteCharacters s).map cw).sum

def bytePadBytes : PadInput (List UInt8) (List UInt8) → List UInt8
  | .string s => s
  | .character c => c

def bytePadOps (cw : List UInt8 → Int) :
    PadValueOps (List UInt8) (List UInt8) (List UInt8) (List UInt8) Index String where
  toInt n := .ok n
  signed n := n
  textwidth
    | .string s => .ok (int (byteTextwidth cw s))
    | .character c => .ok (int (cw c))
  isAnnotated _ := false
  repr p := toString (bytePadBytes p)
  ncodeunits p := (bytePadBytes p).length
  isString
    | .string _ => true
    | .character _ => false
  codeunitIsUInt8 _ := true
  argumentError message := message
  divrem m n := if n.val = 0 then .error "DivideError"
    else .ok (int (m.val / n.val), int (m.val % n.val))
  repeatPad p n := if n.val < 0 then .error "ArgumentError"
    else .ok (.string ((List.replicate n.val.toNat (bytePadBytes p)).flatten))
  assemble _ parts := .ok (parts.flatMap (fun p => match p with
    | .value p => bytePadBytes p
    | .view v => v))

def bytePadRemainderOps (cw : List UInt8 → Int) :
    PadRemainderOps (List UInt8) (List UInt8) (List UInt8)
      (List (Index × List UInt8)) String where
  textwidthChar c := .ok (int (cw c))
  pairsFirst s := .ok (match byteCharacterPairs (int 1) (byteCharacters s) with
    | [] => none
    | p :: rest => some (p, rest))
  pairsNext _ rest := .ok (match rest with
    | [] => none
    | p :: tail => some (p, tail))
  pairsBound s := (byteCharacters s).length
  viewPrefix s i :=
    let c := ((byteCharacterPairs (int 1) (byteCharacters s)).find?
      (fun p => p.1.val == i.val)).map Prod.snd
    .ok (s.take ((i.val - 1).toNat + (c.getD []).length))
  whole s := .ok s

def byteDenseOps : DenseStringOps (List UInt8) String where
  ncodeunits s := int s.length
  sizeof s := int s.length
  memcmp a b n := .ok (if a.take n.val.toNat = b.take n.val.toNat then 0 else 1)
  memcmpFrom a i b n :=
    .ok (if (a.drop (i.val - 1).toNat).take n.val.toNat = b.take n.val.toNat then 0 else 1)
  nextind s i :=
    let starts := (byteCharacterPairs (int 1) (byteCharacters s)).map Prod.fst
    .ok ((starts.find? (fun start => i.val < start.val)).getD (int (s.length + 1)))
  thisind s i :=
    let starts := (byteCharacterPairs (int 1) (byteCharacters s)).map Prod.fst
    .ok ((starts.filter (fun start => start.val ≤ i.val)).getLastD (int 0))

def LpadWidthSuffix : Prop :=
  ∀ (cw : List UInt8 → Int),
    (∀ c, 0 ≤ cw c ∧ cw c ≤ 2) →
    ∀ (s p : List UInt8) (n : Index) (out : List UInt8),
    0 < byteTextwidth cw p →
    lpad (bytePadOps cw) (bytePadRemainderOps cw) (.string s) (.string p) n = .ok out →
    n.val ≤ byteTextwidth cw out ∧ endswithDense byteDenseOps out s = .ok true

set_option maxRecDepth 10000 in
theorem lpadWidthSuffix_refuted : ¬ LpadWidthSuffix := by
  intro h
  have hactual :
      lpad (bytePadOps (fun _ => 1)) (bytePadRemainderOps (fun _ => 1))
        (.string [0x80]) (.string [0xe0]) (int 3) = .ok [0xe0, 0xe0, 0x80] := by
    decide +kernel
  have hbad := (h (fun _ => 1) (by intro _; constructor <;> decide)
    [0x80] [0xe0] (int 3) [0xe0, 0xe0, 0x80] (by decide +kernel) hactual).1
  exact (by decide +kernel : ¬ (int 3).val ≤ byteTextwidth (fun _ => 1) [0xe0, 0xe0, 0x80]) hbad

private theorem asciiLoop_correct {S E : Type} (ops : AsciiOps S E)
    (throwInvalid : S → Index → E) (s : S) (indices : List Nat) :
    asciiString.loop ops throwInvalid s indices = .ok s ↔
      ∀ k ∈ indices, (ops.codeunit s (int (Int.ofNat k + 1))).toNat < 128 := by
  induction indices with
  | nil => simp [asciiString.loop]
  | cons k rest ih =>
    by_cases h : (ops.codeunit s (int (Int.ofNat k + 1))).toNat < 128
    · simp_all [asciiString.loop]
    · simp_all [asciiString.loop]
      split
      · omega
      · simp_all
        omega

private theorem asciiLoop_firstInvalid {S E : Type} (ops : AsciiOps S E)
    (throwInvalid : S → Index → E) (s : S) :
    ∀ (indices : List Nat) (k : Nat) (before after : List Nat),
      indices = before ++ k :: after →
      (∀ j ∈ before, (ops.codeunit s (int (Int.ofNat j + 1))).toNat < 128) →
      128 ≤ (ops.codeunit s (int (Int.ofNat k + 1))).toNat →
      asciiString.loop ops throwInvalid s indices = .error (throwInvalid s (int (Int.ofNat k + 1))) := by
  intro indices k before after hsplit hbefore hk
  subst indices
  induction before with
  | nil =>
    have hnot : ¬ (ops.codeunit s (int (Int.ofNat k + 1))).toNat < 128 := by omega
    change (if (ops.codeunit s (int (Int.ofNat k + 1))).toNat < 128 then
      asciiString.loop ops throwInvalid s after
    else .error (throwInvalid s (int (Int.ofNat k + 1)))) =
      .error (throwInvalid s (int (Int.ofNat k + 1)))
    exact ite_eq_right_iff.mpr (fun h => False.elim (hnot h))
  | cons j rest ih =>
    have hj : (ops.codeunit s (int (Int.ofNat j + 1))).toNat < 128 :=
      hbefore j (by simp)
    change (if (ops.codeunit s (int (Int.ofNat j + 1))).toNat < 128 then
      asciiString.loop ops throwInvalid s (rest ++ k :: after)
    else .error (throwInvalid s (int (Int.ofNat j + 1)))) =
      .error (throwInvalid s (int (Int.ofNat k + 1)))
    rw [ite_eq_left_iff.mpr (fun h => False.elim (h hj))]
    exact ih (fun m hm => hbefore m (by simp [hm]))

def AsciiAllBytes : Prop :=
  ∀ {S E : Type} (ops : AsciiOps S E) (s : S),
    (asciiString ops (__throw_invalid_ascii ops) s = .ok s ↔
      ∀ k : Nat, k < (ops.sizeof s).val.toNat →
        (ops.codeunit s (int (Int.ofNat k + 1))).toNat < 128) ∧
    (∀ k : Nat, k < (ops.sizeof s).val.toNat →
      128 ≤ (ops.codeunit s (int (Int.ofNat k + 1))).toNat →
      (∀ j : Nat, j < k → (ops.codeunit s (int (Int.ofNat j + 1))).toNat < 128) →
      asciiString ops (__throw_invalid_ascii ops) s =
        .error (ops.argumentError ("invalid ASCII at index " ++ toString (int (Int.ofNat k + 1)).val ++ " in " ++ ops.repr s)))

theorem asciiAllBytes_proven : AsciiAllBytes := by
  intro S E ops s
  refine ⟨?_, ?_⟩
  · simpa [asciiString, List.mem_range] using
      asciiLoop_correct ops (__throw_invalid_ascii ops) s (List.range (ops.sizeof s).val.toNat)
  · intro k hklt hbad hprev
    let n := (ops.sizeof s).val.toNat
    have hlen : k < (List.range n).length := by simp [n, hklt]
    have hsplit : List.range n = (List.range n).take k ++ k :: (List.range n).drop (k + 1) := by
      have hd := List.drop_eq_getElem_cons hlen
      have ht := (List.take_append_drop k (List.range n)).symm
      simpa [List.getElem_range] using ht.trans (congrArg _ hd)
    have hbefore : ∀ j ∈ (List.range n).take k,
        (ops.codeunit s (int (Int.ofNat j + 1))).toNat < 128 := by
      intro j hj
      rw [List.mem_take_iff_getElem] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      simp only [List.getElem_range]
      exact hprev i (by omega)
    simpa [asciiString, __throw_invalid_ascii, n] using
      asciiLoop_firstInvalid ops (__throw_invalid_ascii ops) s (List.range n) k
        ((List.range n).take k) ((List.range n).drop (k + 1)) hsplit hbefore hbad
/-! ## Remaining-character collection -/

private theorem restLoop_correct
    {S Iter State C IO O E : Type} (ops : RestOps S Iter State C IO O E)
    (bufferChars : IO → List C) (resultChars : O → List C) (iter : Iter)
    (hprint : ∀ io c, ∃ next, ops.print io c = .ok next ∧
      bufferChars next = bufferChars io ++ [c])
    (htake : ∀ io, ∃ out, ops.takeString io = .ok out ∧ resultChars out = bufferChars io) :
    ∀ chars fuel io current,
      CharacterTrace (ops.iterateNext iter) current chars →
      chars.length < fuel →
      ∃ out, restGeneric.loop ops iter fuel io current = .ok out ∧
        resultChars out = bufferChars io ++ chars := by
  intro chars
  induction chars with
  | nil =>
    intro fuel io current ht hf
    cases ht
    cases fuel with
    | zero => omega
    | succ n =>
      obtain ⟨out, ho, hv⟩ := htake io
      exact ⟨out, by simpa [restGeneric.loop] using ho, by simpa using hv⟩
  | cons c chars ih =>
    intro fuel io current ht hf
    cases ht with
    | cons hstep htail =>
      cases fuel with
      | zero => omega
      | succ n =>
        obtain ⟨next, hn, hv⟩ := hprint io c
        obtain ⟨out, ho, hout⟩ := ih n next _ htail (by simp at hf; omega)
        refine ⟨out, ?_, ?_⟩
        · simpa [restGeneric.loop, hn, hstep, bind, Except.bind] using ho
        · simpa [hv, List.append_assoc] using hout

def RestCharacters : Prop :=
  ∀ {S Iter State C IO O E : Type} (ops : RestOps S Iter State C IO O E)
    (bufferChars : IO → List C) (resultChars : O → List C),
    (∀ io c, ∃ next, ops.print io c = .ok next ∧ bufferChars next = bufferChars io ++ [c]) →
    (∀ io, ∃ out, ops.takeString io = .ok out ∧ resultChars out = bufferChars io) →
    ∀ (s : S) (states : List State) (iter : Iter) (first : Option (C × State))
      (chars : List C) (emptyBuffer : IO),
    ops.newIOBuffer = .ok emptyBuffer → bufferChars emptyBuffer = [] →
    ops.restIterator s states = .ok iter → ops.iterateFirst iter = .ok first →
    CharacterTrace (ops.iterateNext iter) first chars →
    chars.length ≤ ops.iterationBound iter →
    ∃ out, restGeneric ops s states = .ok out ∧ resultChars out = chars

theorem restCharacters_proven : RestCharacters := by
  intro S Iter State C IO O E ops bufferChars resultChars hprint htake
    s states iter first chars emptyBuffer hbuffer hempty hiter hfirst ht hf
  obtain ⟨out, ho, hv⟩ := restLoop_correct ops bufferChars resultChars iter hprint htake
    chars (ops.iterationBound iter + 1) emptyBuffer first ht (by omega)
  refine ⟨out, ?_, ?_⟩
  · simpa [restGeneric, hbuffer, hiter, hfirst, bind, Except.bind] using ho
  · simpa [hempty] using hv

/-! ## Identity behavior before allocation -/

def WrappedPaddingIdentity : Prop :=
  (∀ {S C R O N E FS : Type} (ops : PadValueOps S C R O N E)
    (remOps : PadRemainderOps S C R FS E) (represent : PadInput S C → O)
    (failRepeat : PadInput S C → Index → Except E (PadInput S C)),
    (∀ annotated s, ops.assemble annotated [.value s] = .ok (represent s)) →
    ∀ (s p : PadInput S C) (n : N) (converted width : Index),
    ops.toInt n = .ok converted →
    ops.textwidth s = .ok width →
    ((ops.signed converted - width).val ≤ 0 →
      lpad {ops with repeatPad := failRepeat} remOps s p n = .ok (represent s) ∧
        rpad {ops with repeatPad := failRepeat} remOps s p n = .ok (represent s)) ∧
    (0 < (ops.signed converted - width).val →
      ops.textwidth p = .ok (int 0) →
      lpad {ops with repeatPad := failRepeat} remOps s p n =
        .error (ops.argumentError (lpadZeroWidthMessage ops s p)) ∧
      rpad {ops with repeatPad := failRepeat} remOps s p n =
        .error (ops.argumentError (rpadZeroWidthMessage ops s p)))) ∧
  PaddingPieces

theorem wrappedPaddingIdentity_proven : WrappedPaddingIdentity := by
  refine ⟨?_, paddingPieces_proven⟩
  intro S C R O N E FS ops remOps represent failRepeat hassemble s p n converted width hn hw
  refine ⟨?_, ?_⟩
  · intro hm
    constructor <;>
      simp [lpad, rpad, hn, hw, hm, hassemble, bind, Except.bind]
  · intro hm hp0
    have hnotLe : ¬ (ops.signed converted - width).val ≤ 0 := by omega
    have hz : (int 0).val = 0 := by decide
    constructor <;>
      simp [lpad, rpad, lpadZeroWidthMessage, rpadZeroWidthMessage,
        hn, hw, hnotLe, hp0, hz, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

def TruncationFitsIdentity : Prop :=
  (∀ {S V R C E : Type} (ops : TruncateOps S V R C E),
    (∀ c, 0 ≤ (ops.textwidthChar c).val ∧ (ops.textwidthChar c).val ≤ 2) →
    (∀ s, ops.stringify s = .ok s) →
    ∀ (str : S) (chars : List C) (replacement : R) (width : Index) (preferLeft : Bool),
    IterStepTrace (ops.iterate str) chars →
    0 ≤ width.val →
    charListWidth ops chars ≤ width.val →
    checkTextwidth ops str width = .ok true ∧
      stringTruncateBoundaries ops str width replacement .right true = .ok none ∧
      stringTruncateBoundaries ops str width replacement .left true = .ok none ∧
      stringTruncateBoundaries ops str width replacement .center preferLeft = .ok none ∧
      rtruncate ops str width replacement = .ok str ∧
      ltruncate ops str width replacement = .ok str ∧
      ctruncate ops str width replacement preferLeft = .ok str) ∧
  TruncateWidthBound

theorem truncationFitsIdentity_proven : TruncationFitsIdentity := by
  refine ⟨?_, truncateWidthBound_proven⟩
  intro S V R C E ops charBounds hstring str chars replacement width preferLeft htrace hn hfit
  have hnegative : ¬ width.val < 0 := by omega
  have hzeroVal : (int 0).val = 0 := by decide
  have hcheck : checkTextwidth ops str width = .ok true := by
    simpa [checkTextwidth] using
      checkWidthLoop_true_of_le ops charBounds width htrace (int 0)
        (by rw [hzeroVal]; omega) (by rw [hzeroVal]; simpa using hfit)
  simp [rtruncate, ltruncate, ctruncate, stringTruncateBoundaries, hnegative, hcheck,
    hstring, bind, pure, Except.bind, Except.pure]
/-! Nothing to promise:
startswith@83: forwards to the dense UTF-8 method without changing either argument.
startswith@105: materializes String and forwards to the UTF-8 stream method.
endswith@120: forwards to the dense UTF-8 method without changing either argument.
contains@152: swaps the arguments into occursin, whose search contract belongs to search.jl.
endswith@175: packages the suffix in Fix2.
startswith@198: packages the prefix in Fix2.
contains@209: packages the needle in Fix2.
lstrip@423: supplies the whitespace predicate to lstrip.
lstrip@424: supplies character membership to lstrip.
rstrip@457: supplies the whitespace predicate to rstrip.
rstrip@458: supplies character membership to rstrip.
strip@486: composes the whitespace rstrip and lstrip methods.
strip@487: composes the character-membership rstrip and lstrip methods.
strip@489: composes the predicate rstrip and lstrip methods.
lpad@511: stringifies source and padding, then forwards to lpad.
_pad_remainder@524: the character specialization returns its argument unchanged.
rpad@564: stringifies source and padding, then forwards to rpad.
eachsplit@772: empty generic function declaration.
eltype@783: type trait selecting SubString of the source type.
eltype@784: type trait preserving the SubString parent type.
IteratorSize@786: type trait declaring unknown iterator size.
eltype@810: type trait selecting the partition's SubString type.
eltype@812: type trait preserving an existing SubString type.
eachsplit@823: constructs a membership predicate, then forwards keywords unchanged.
eachsplit@827: constructs character equality, then forwards keywords unchanged.
eachsplit@831: supplies the whitespace predicate and forwards keywords unchanged.
eachrsplit@870: empty generic function declaration.
eltype@879: type trait selecting SubString of the source type.
eltype@880: type trait preserving the SubString parent type.
IteratorSize@882: type trait declaring unknown iterator size.
eachrsplit@884: forwards the source, splitter, limit and keepempty flag to the typed reverse-split iterator constructor.
eachrsplit@887: constructs a membership predicate, then forwards keywords unchanged.
eachrsplit@891: constructs character equality, then forwards keywords unchanged.
eachrsplit@895: supplies the whitespace predicate and forwards keywords unchanged.
split@958: collects the forward split iterator.
split@964: supplies whitespace to the collecting split wrapper.
rsplit@1001: collects the reverse iterator and restores source order.
rsplit@1007: supplies whitespace to the collecting reverse-split wrapper.
_replace@1011: forwards the literal replacement to write.
_replace@1023: applies the user replacement function to a SubString, then dispatches _replace.
_replace@1025: applies the user replacement function to a character, then dispatches _replace.
_pat_replacer@1028: generic identity pattern preparation.
_free_pat_replacer@1029: generic no-op cleanup.
_pat_replacer@1031: packages character equality.
_pat_replacer@1032: packages collection membership.
replace@1183: converts the source and count, then forwards to the stream engine.
replace@1186: converts the source and count, then forwards to the String engine.
hex2bytes@1235: empty generic function declaration.
hex2bytes@1237: allocates the destination and dispatches hex2bytes!.
number_from_hex@1276: converts AbstractChar to Char, then dispatches the Char method.
number_from_hex@1277: converts Char to UInt8, then dispatches the byte method.
bytes2hex@1314: empty generic function declaration.
__throw_invalid_ascii@1343: constructs the index-specific ArgumentError used by ascii.
ascii@1364: materializes String and forwards to ascii(String).
Base.rest@1366: forwards the starting state to SubString.
-/

/-- Registry entries of the string utility model. -/
def entries : List Entry := [
  { id := "strings-lpad-typemin"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad(::Union{AbstractChar,AbstractString}, ::Integer, ::Union{AbstractChar,AbstractString})@526-544",
      "rpad(::Union{AbstractChar,AbstractString}, ::Integer, ::Union{AbstractChar,AbstractString})@566-584"]
    statement := "lpad and rpad return the original string when the requested width is no greater than its textwidth."
    source := "lpad and rpad docstrings, base/strings/util.jl:494-510,547-563"
    status := .refuted, prop := ``LpadNoPadding, thm := some ``lpadNoPadding_refuted
    notes := "At typemin(Int), signed(width) - textwidth(source) wraps positive, so both methods try to repeat the padding and raise OutOfMemoryError."
    issue := "none found (queries: lpad typemin, lpad negative OutOfMemoryError, lpad overflow, rpad typemin, lpad)" },
  { id := "stringutil-replace-count-edge"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace_@1122-1131", "_replace_init@1035", "_replace_finish@1053", "_replace_once@1068"]
    statement := "A zero replacement count returns the original string, a negative count throws DomainError, and any nonnegative count applies at most count replacement writes."
    source := "replace docstring, base/strings/util.jl:1133-1180"
    status := .proven, prop := ``ReplaceCountEdge, thm := some ``replaceCountEdge_proven },
  { id := "stringutil-prefix-sequence", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::AbstractString,::AbstractString)@31"]
    statement := "startswith succeeds exactly when the prefix's complete character sequence is a prefix of the source's sequence, for lawful finite character iterators."
    source := "startswith docstring, base/strings/util.jl:16-39"
    status := .proven, prop := ``PrefixSequence, thm := some ``prefixSequence_proven },
  { id := "stringscova-util-endswith-abstract-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["endswith(::AbstractString,::AbstractString)@57"]
    statement := "endswith succeeds exactly when the reversed suffix character sequence is a prefix of the reversed source sequence."
    source := "endswith docstring, base/strings/util.jl:42-66"
    status := .proven, prop := ``SuffixSequence, thm := some ``suffixSequence_proven },
  { id := "stringutil-startswith-io-peek", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO,::UTF8String)@99"]
    statement := "With the documented mark/read/reset interface, stream startswith compares the requested unread bytes and restores the original stream position."
    source := "base/strings/util.jl:87-104; mark, read, reset interfaces"
    status := .proven, prop := ``StartswithIoPeek, thm := some ``startswithIoPeek_proven },
  { id := "stringutil-startswith-io-mark", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO,::UTF8String)@99", "startswith(::IO,::Chars)@93"]
    statement := "Under the documented mark/read/reset stream interface, stream startswith returns exactly the comparison of the unread bytes against a string prefix and of the next character against a character set, with the stream returned in the reset state."
    source := "base/strings/util.jl:87-104, startswith refers to peek"
    status := .proven, prop := ``StartswithIoChecks, thm := some ``startswithIoChecks_proven
    notes := "The startswith(io, prefix) docstring promises prefix checking without preserving a caller's earlier mark." },
  { id := "stringutil-startswith-io-eof", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO,::Chars)@93"]
    statement := "At end of stream, a character-set prefix check returns false."
    source := "base/strings/util.jl:87-98, stream prefix-check contract"
    status := .refuted, prop := ``StartswithIoEof, thm := some ``startswithIoEof_refuted
    notes := "The character read throws EOFError before reset executes."
    issue := "none found; related #40616 (queries: issues: startswith IO, issues: startswith IOBuffer, issues: startswith EOFError, prs: startswith EOFError)" },
  { id := "strings-chop-head-overflow", juliaFile := "base/strings/util.jl"
    juliaFns := ["chop(::AbstractString)@236"]
    statement := "Removing at least the source's character count with nonnegative head and tail counts returns an empty string."
    source := "chop docstring, base/strings/util.jl:214-241"
    status := .refuted, prop := ``ChopTooMany, thm := some ``chopTooMany_refuted
    notes := "The source basic.nextindInt operation wraps for head=typemax(Int), so the substring constructor raises BoundsError."
    issue := "none found (queries: chop head overflow, chop typemax, chop)" },
  { id := "strings-partition-overflow", juliaFile := "base/strings/util.jl"
    juliaFns := ["iterate(::PartitionIterator{<:AbstractString})@814"]
    statement := "A chunk size covering the nonempty source's character count yields the whole string as the first partition."
    source := "Iterators.partition docstring; base/strings/util.jl:814-818"
    status := .refuted, prop := ``PartitionWhole, thm := some ``partitionWhole_refuted
    notes := "For the multibyte string é€, nextind wraps with chunk size typemax(Int)."
    issue := "none found (queries: partition string typemax)" },
  { id := "regexunicode-replace-empty-after-match", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace_init@1035", "_replace_once@1068", "_replace_finish@1053", "_replace_@1122"]
    statement := "Replacing each non-overlapping occurrence agrees with assembling the output from the match iterator's complete sequence, including empty matches."
    source := "replace docstring, base/strings/util.jl:1136; non-overlapping match-iterator interface"
    status := .refuted, prop := ``ReplaceAssemblesEachmatch, thm := some ``replaceAssemblesEachmatch_refuted
    notes := "For abxd and x*, the source replacement engine produces -a-b-d- while the match sequence assembles -a-b--d-."
    issue := "none found (queries: replace regex empty match; replace empty matches; eachmatch empty; findall regex empty)" },
  { id := "stringutil-hex2bytes-nonascii", juliaFile := "base/strings/util.jl"
    juliaFns := ["hex2bytes@1237", "hex2bytes!@1260", "number_from_hex@1276", "number_from_hex@1277"]
    statement := "Hexadecimal decoding of an iterator of ASCII character codes, of Int-representable length, returns bytes or throws ArgumentError."
    source := "hex2bytes docstring, base/strings/util.jl:1195-1201"
    status := .proven, prop := ``Hex2bytesAsciiArgError, thm := some ``hex2bytesAsciiArgError_proven
    notes := "Non-ASCII input lies outside the documented ASCII-hexadecimal domain; the U+0100 iterator counterexample raises InexactError rather than silently returning bytes." },
  { id := "stringutil-split-limit-type", juliaFile := "base/strings/util.jl"
    juliaFns := ["eachsplit(::AbstractString,splitter)@820"]
    statement := "An Integer limit whose value fits in Int behaves identically to its conversion to Int."
    source := "eachsplit and split signatures and docstrings; base/strings/util.jl:738,820,958"
    status := .refuted, prop := ``SplitLimitInteger, thm := some ``splitLimitInteger_refuted
    notes := "A UInt64 limit of two triggers the SplitIterator constructor's MethodError."
    issue := "none found (queries: issues: split limit UInt; prs: split limit UInt; issues: split limit Integer MethodError; issues: SplitIterator limit)" },
  { id := "stringutil-truncate-width", juliaFile := "base/strings/util.jl"
    juliaFns := ["rtruncate@609", "ltruncate@642", "ctruncate@676", "string_truncate_boundaries@697"]
    statement := "When the replacement's own display width fits within a nonnegative maximum width, all three truncation modes return text no wider than that width."
    source := "rtruncate docstring, base/strings/util.jl:589-590"
    status := .proven, prop := ``TruncateWidth, thm := some ``truncateWidth_proven
    notes := "The replacement's own display width must fit within maxwidth for the stated output-width bound." },
  { id := "stringscova-util-hex2bytes-bang-iterator-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["hex2bytes!(dest,itr)@1260", "number_from_hex(::UInt8)@1278"]
    statement := "The iterator decoder rejects odd input lengths and mismatched destination lengths, and decodes every pair of lowercase hexadecimal digits in order into the destination array."
    source := "hex2bytes! docstring and input validation, base/strings/util.jl:1251-1274"
    status := .proven, prop := ``HexDecodeLengths, thm := some ``hexDecodeLengths_proven },
  { id := "stringscova-util-review-1278", juliaFile := "base/strings/util.jl"
    juliaFns := ["number_from_hex(::UInt8)@1278"]
    statement := "Decimal digits decode to zero through nine, and both uppercase and lowercase ASCII letters A through F decode to ten through fifteen."
    source := "hex2bytes docstring; base/strings/util.jl:1278-1283"
    status := .proven, prop := ``HexadecimalDigits, thm := some ``hexadecimalDigits_proven },
  { id := "stringutil-lstrip-maximal-run", juliaFile := "base/strings/util.jl"
    juliaFns := ["lstrip(f,::AbstractString)@416"]
    statement := "lstrip returns the suffix starting at the first character that fails the predicate, or the empty suffix when all characters satisfy it."
    source := "lstrip docstring, base/strings/util.jl:392-422"
    status := .proven, prop := ``LstripMaximalRun, thm := some ``lstripMaximalRun_proven },
  { id := "stringutil-rstrip-maximal-run", juliaFile := "base/strings/util.jl"
    juliaFns := ["rstrip(f,::AbstractString)@451"]
    statement := "rstrip returns the prefix ending at the first predicate failure in reverse character order, or the empty prefix when all characters satisfy it."
    source := "rstrip docstring, base/strings/util.jl:427-456"
    status := .proven, prop := ``RstripMaximalRun, thm := some ``rstripMaximalRun_proven },
  { id := "stringscova-util-review-526", juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad@526", "_pad_remainder(::AbstractString,::Int)@516"]
    statement := "When the wrapped padding difference is nonpositive, lpad returns the source without invoking repeatPad; when padding width is zero it throws ArgumentError; otherwise it decomposes the missing width into whole copies and a minimal character-prefix remainder."
    source := "lpad docstring and nonpositive-padding invariant, base/strings/util.jl:526-544"
    status := .proven, prop := ``WrappedPaddingIdentity, thm := some ``wrappedPaddingIdentity_proven },
  { id := "stringscova-util-review-566", juliaFile := "base/strings/util.jl"
    juliaFns := ["rpad@566", "_pad_remainder(::AbstractString,::Int)@516"]
    statement := "When the wrapped padding difference is nonpositive, rpad returns the source without invoking repeatPad; when padding width is zero it throws ArgumentError; otherwise it decomposes the missing width into whole copies and a minimal character-prefix remainder."
    source := "rpad docstring and nonpositive-padding invariant, base/strings/util.jl:566-584"
    status := .proven, prop := ``WrappedPaddingIdentity, thm := some ``wrappedPaddingIdentity_proven },
  { id := "stringscova-util-review-676", juliaFile := "base/strings/util.jl"
    juliaFns := ["rtruncate@609", "ltruncate@642", "ctruncate@676", "check_textwidth@687", "string_truncate_boundaries@697"]
    statement := "When the total character width is at most a nonnegative maxwidth, check_textwidth returns true and all three truncation modes preserve the source; otherwise all three modes truncate to display width at most maxwidth."
    source := "truncation docstrings, base/strings/util.jl:587-684"
    status := .proven, prop := ``TruncationFitsIdentity, thm := some ``truncationFitsIdentity_proven },
  { id := "stringscova-util-review-1035", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace_init@1035", "_replace_@1122"]
    statement := "Replacement initialization rejects negative counts with DomainError, and for nonnegative counts maps unmatched patterns to sentinel ranges above e1 and sets notfound=true so _replace_ returns the original string without allocating a buffer."
    source := "replacement count and sentinel initialization invariant, base/strings/util.jl:1035-1050,1122-1131"
    status := .proven, prop := ``ReplacementInitContract, thm := some ``replacementInitContract_proven },
  { id := "stringutil-pad-malformed", juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad@526", "_pad_remainder@516", "endswith(::DenseUTF8String,::DenseUTF8String)@107"]
    statement := "With character widths from zero through two and positive-width padding, successful lpad returns text at least as wide as requested and ending in the original source."
    source := "lpad docstring, base/strings/util.jl:494-498"
    status := .refuted, prop := ``LpadWidthSuffix, thm := some ``lpadWidthSuffix_refuted
    notes := "For source byte 0x80, pad byte 0xe0, and width three, the source lpad returns e0 e0 80, which has two Julia characters."
    issue := "none found; related #25016 (queries: issues: lpad invalid UTF-8, issues: lpad textwidth, issues: rpad textwidth, issues: lpad malformed)" },
  { id := "stringscova-util-ascii-string-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["ascii(::String)@1337", "__throw_invalid_ascii(::String,::Int)@1343"]
    statement := "ascii returns its identical source String iff every code unit is below 0x80, and otherwise throws the ArgumentError constructed by __throw_invalid_ascii at the first invalid 1-based byte index."
    source := "ascii docstring, base/strings/util.jl:1337-1362"
    status := .proven, prop := ``AsciiAllBytes, thm := some ``asciiAllBytes_proven },
  { id := "stringscova-util-startswith-dense-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::DenseUTF8String,::DenseUTF8String)@69"]
    statement := "Dense startswith accepts precisely the equal prefix bytes ending at a character boundary, under the byte-comparison and string-index interfaces."
    source := "startswith docstring and UTF-8 boundary invariant, base/strings/util.jl:69-78"
    status := .proven, prop := ``DensePrefixBytes, thm := some ``densePrefixBytes_proven },
  { id := "stringscova-util-startswith-fast-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::Union{String,SubString{String}},::Union{String,SubString{String}})@83"]
    statement := "The specialized startswith accepts precisely an equal byte prefix ending at a character boundary."
    source := "startswith docstring and specialization, base/strings/util.jl:69-85"
    status := .proven, prop := ``DensePrefixBytes, thm := some ``densePrefixBytes_proven },
  { id := "stringscova-util-endswith-dense-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["endswith(::DenseUTF8String,::DenseUTF8String)@107"]
    statement := "Dense endswith accepts precisely an equal final byte sequence beginning at a character boundary, under the byte-comparison and string-index interfaces."
    source := "endswith docstring and UTF-8 boundary invariant, base/strings/util.jl:107-116"
    status := .proven, prop := ``DenseSuffixBytes, thm := some ``denseSuffixBytes_proven },
  { id := "stringscova-util-chopprefix-abstract-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopprefix(::AbstractString,::AbstractString)@268"]
    statement := "chopprefix removes the complete matching prefix character sequence and otherwise preserves the source character sequence."
    source := "chopprefix docstring, base/strings/util.jl:246-279"
    status := .proven, prop := ``ChopPrefixSequence, thm := some ``chopPrefixSequence_proven },
  { id := "stringscova-util-chopsuffix-abstract-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopsuffix(::AbstractString,::AbstractString)@320"]
    statement := "chopsuffix removes the complete matching suffix character sequence and otherwise preserves the source character sequence."
    source := "chopsuffix docstring, base/strings/util.jl:300-332"
    status := .proven, prop := ``ChopSuffixSequence, thm := some ``chopSuffixSequence_proven },
  { id := "stringscova-util-review-290", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopprefix(::AbstractString,::AbstractChar)@290"]
    statement := "The character chopprefix overload removes the first character exactly when it matches, and preserves the original characters for an empty source or mismatch."
    source := "chopprefix docstring and character overload, base/strings/util.jl:290-296"
    status := .proven, prop := ``ChopPrefixCharacter, thm := some ``chopPrefixCharacter_proven },
  { id := "stringutil-chopsuffix-character", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopsuffix(::AbstractString,::AbstractChar)@344"]
    statement := "The character chopsuffix overload removes the last character exactly when it matches, and preserves the original characters for an empty source or mismatch."
    source := "chopsuffix docstring and character overload, base/strings/util.jl:344-350"
    status := .proven, prop := ``ChopSuffixCharacter, thm := some ``chopSuffixCharacter_proven },
  { id := "stringutil-lstrip-chars", juliaFile := "base/strings/util.jl"
    juliaFns := ["lstrip(f,::AbstractString)@416", "lstrip(::AbstractString,::Chars)@424", "lstrip(::AbstractString,::AbstractString)@425"]
    statement := "lstrip removes the maximal leading character run satisfying a predicate or character set, and rejects a string second argument with ArgumentError."
    source := "lstrip docstring, base/strings/util.jl:392-425; pair iteration and SubString interfaces"
    status := .proven, prop := ``LstripChars, thm := some ``lstripChars_proven },
  { id := "stringutil-rstrip-chars", juliaFile := "base/strings/util.jl"
    juliaFns := ["rstrip(f,::AbstractString)@451", "rstrip(::AbstractString,::Chars)@458", "rstrip(::AbstractString,::AbstractString)@459"]
    statement := "rstrip removes the maximal trailing character run satisfying a predicate or character set, and rejects a string second argument with ArgumentError."
    source := "rstrip docstring, base/strings/util.jl:427-459; reverse pair iteration and SubString interfaces"
    status := .proven, prop := ``RstripChars, thm := some ``rstripChars_proven },
  { id := "stringutil-strip-chars", juliaFile := "base/strings/util.jl"
    juliaFns := ["strip(f,::AbstractString)@489", "strip(::AbstractString,::Chars)@487", "strip(::AbstractString,::AbstractString)@488", "rstrip(f,::AbstractString)@451", "lstrip(f,::AbstractString)@416"]
    statement := "strip removes the maximal leading and trailing runs satisfying a predicate or character set while preserving intervening characters in order, and rejects a string second argument with ArgumentError."
    source := "strip docstring, base/strings/util.jl:461-489; pair iteration and SubString interfaces"
    status := .proven, prop := ``StripChars, thm := some ``stripChars_proven },
  { id := "stringscova-util-chopprefix-fast-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopprefix(::Union{String,SubString{String}},::Union{String,SubString{String}})@281"]
    statement := "Fast chopprefix removes precisely an equal initial byte sequence ending at a character boundary and otherwise preserves the entire source."
    source := "chopprefix docstring, base/strings/util.jl:244-288; memcmp, indexing and SubString interfaces"
    status := .proven, prop := ``ChopPrefixFastBytes, thm := some ``chopPrefixFastBytes_proven },
  { id := "stringutil-chopsuffix-fast-bytes", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopsuffix(::Union{String,SubString{String}},::Union{String,SubString{String}})@334"]
    statement := "Fast chopsuffix removes an equal final byte sequence starting at a character boundary, preserves the source on mismatch, and preserves it for an empty suffix."
    source := "chopsuffix docstring, base/strings/util.jl:299-342; memcmp, prevind and SubString interfaces"
    status := .proven, prop := ``ChopSuffixFastBytes, thm := some ``chopSuffixFastBytes_proven },
  { id := "stringscova-util-chopsuffix-faithful", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopsuffix(::AbstractString,::AbstractString)@320", "chopsuffix(::Union{String,SubString{String}},::Union{String,SubString{String}})@334", "chopsuffix(::AbstractString,::AbstractChar)@344"]
    statement := "Every chopsuffix specialization removes a matching suffix, preserves the source on mismatch, and preserves the character or byte sequence before the removed suffix."
    source := "chopsuffix docstring, base/strings/util.jl:299-350"
    status := .proven, prop := ``ChopSuffixFaithful, thm := some ``chopSuffixFaithful_proven },
  { id := "stringscova-util-chop-affixes", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopprefix(::AbstractString,::AbstractString)@268", "chopprefix(::Union{String,SubString{String}},::Union{String,SubString{String}})@281", "chopprefix(::AbstractString,::AbstractChar)@290", "chopsuffix(::AbstractString,::AbstractString)@320", "chopsuffix(::Union{String,SubString{String}},::Union{String,SubString{String}})@334", "chopsuffix(::AbstractString,::AbstractChar)@344"]
    statement := "Prefix and suffix removal preserve the untouched sequence in order for abstract, dense and single-character arguments, and preserve the entire source on mismatch."
    source := "chopprefix and chopsuffix docstrings, base/strings/util.jl:244-350"
    status := .proven, prop := ``ChopAffixes, thm := some ``chopAffixes_proven },
  { id := "stringscova-util-rest-generic-rebuilt", juliaFile := "base/strings/util.jl"
    juliaFns := ["rest(::AbstractString,st...)@1367"]
    statement := "Generic rest collects every remaining character exactly once and in iterator order."
    source := "rest iterator contract, base/strings/util.jl:1367-1373; buffer and character-printing interfaces"
    status := .proven, prop := ``RestCharacters, thm := some ``restCharacters_proven },
  { id := "stringutil-chomp-characters", juliaFile := "base/strings/util.jl"
    juliaFns := ["chomp(::AbstractString)@371"]
    statement := "Generic chomp removes exactly one final line feed and its immediately preceding carriage return, preserving every other character in order."
    source := "chomp docstring, base/strings/util.jl:353-378; reverse character indexing and SubString interfaces"
    status := .proven, prop := ``ChompCharacters, thm := some ``chompCharacters_proven },
  { id := "stringutil-bytes2hex-io-characters", juliaFile := "base/strings/util.jl"
    juliaFns := ["bytes2hex(::IO,itr)@1329"]
    statement := "Stream hexadecimal conversion appends exactly the two lowercase hexadecimal digits of every input byte, in iterator order, while preserving the preceding stream contents."
    source := "bytes2hex docstring, base/strings/util.jl:1287-1334; hexadecimal table, iteration and print interfaces"
    status := .proven, prop := ``Bytes2hexIOCharacters, thm := some ``bytes2hexIOCharacters_proven },
  { id := "stringutil-textwidth-prefix-check", juliaFile := "base/strings/util.jl"
    juliaFns := ["check_textwidth(::AbstractString,::Integer)@687"]
    statement := "The text-width check succeeds exactly when every nonempty character prefix has accumulated machine-integer text width at most the requested width."
    source := "check_textwidth invariant, base/strings/util.jl:687-695"
    status := .proven, prop := ``TextwidthPrefixCheck, thm := some ``textwidthPrefixCheck_proven },
  { id := "stringutil-stream-replace-count-edge", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace_(::IO,str,pat_repl::NTuple{N,Pair},count::Int)@1107"]
    statement := "A zero replacement count appends the original bytes unchanged to the output stream, and a negative count throws DomainError before writing."
    source := "replace count contract, base/strings/util.jl:1107-1120; stream write interface"
    status := .proven, prop := ``StreamReplaceCountEdge, thm := some ``streamReplaceCountEdge_proven },
  { id := "stringutil-replacement-shown-byte-count", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace(io,repl,str,r,pattern)@1013"]
    statement := "On a stream supporting position, a displayed replacement returns the updated stream and the exact nonnegative byte count printed."
    source := "_replace byte-count invariant, base/strings/util.jl:1013-1022; position and print interfaces"
    status := .proven, prop := ``ReplacementShownByteCount, thm := some ``replacementShownByteCount_proven },
  { id := "stringutil-pad-remainder-minimal", juliaFile := "base/strings/util.jl"
    juliaFns := ["_pad_remainder(::AbstractString,::Int)@516"]
    statement := "The padding remainder preserves a prefix of the padding's characters and selects the shortest nonempty prefix reaching the requested accumulated width; it returns the whole padding when no earlier prefix reaches that width."
    source := "_pad_remainder minimal-prefix invariant, base/strings/util.jl:516-523; character widths, pair iteration and view interfaces"
    status := .proven, prop := ``PadRemainderMinimal, thm := some ``padRemainderMinimal_proven },
  { id := "stringutil-startswith-character-set", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::AbstractString,::Chars)@40"]
    statement := "Character-set startswith succeeds exactly when the source has a first character belonging to the supplied character set."
    source := "startswith docstring, base/strings/util.jl:16-40; emptiness, first and membership interfaces"
    status := .proven, prop := ``StartswithCharacterSet, thm := some ``startswithCharacterSet_proven },
  { id := "stringutil-endswith-character-set", juliaFile := "base/strings/util.jl"
    juliaFns := ["endswith(::AbstractString,::Chars)@67"]
    statement := "Character-set endswith succeeds exactly when the source has a last character belonging to the supplied character set."
    source := "endswith docstring, base/strings/util.jl:42-67; emptiness, last and membership interfaces"
    status := .proven, prop := ``EndswithCharacterSet, thm := some ``endswithCharacterSet_proven },
  { id := "stringutil-chomp-fast-characters", juliaFile := "base/strings/util.jl"
    juliaFns := ["chomp(::Union{String,SubString{String}})@379"]
    statement := "Fast chomp removes a final LF or CRLF byte sequence exactly once and otherwise preserves all source bytes."
    source := "chomp docstring, base/strings/util.jl:353-391; raw substring interface"
    status := .proven, prop := ``ChompFastCharacters, thm := some ``chompFastCharacters_proven },
  { id := "stringutil-chomp-generic", juliaFile := "base/strings/util.jl"
    juliaFns := ["chomp(::AbstractString)@371", "chomp(::Union{String,SubString{String}})@379"]
    statement := "Generic and fast chomp return exactly the same view, including its parent, offset and length, under the byte/character indexing and substring interfaces."
    source := "chomp docstring, base/strings/util.jl:353-391; ASCII newline encoding, prevind and SubString interfaces"
    status := .proven, prop := ``ChompGeneric, thm := some ``chompGeneric_proven },
  { id := "stringutil-split-limit", juliaFile := "base/strings/util.jl"
    juliaFns := ["split(::AbstractString,splitter;limit,keepempty)@958", "iterate(::SplitIterator)@791"]
    statement := "For every splitter and keepempty setting, a successful split with a positive Int limit returns at most that many pieces, under the complete-collection interface."
    source := "split docstring, base/strings/util.jl:930-956; SplitIterator emission counter and complete collection"
    status := .proven, prop := ``SplitLimit, thm := some ``splitLimit_proven },
  { id := "stringutil-split-sentinel-overflow", juliaFile := "base/strings/util.jl"
    juliaFns := ["iterate(::SplitIterator)@791", "eachsplit(::AbstractString,splitter)@820"]
    statement := "After emitting a piece with limit=1, a split iterator terminates on the next iteration."
    source := "eachsplit and split limit contract, base/strings/util.jl:739-770,930-956"
    status := .refuted, prop := ``SplitIteratorLimitOne, thm := some ``splitIteratorLimitOne_refuted
    notes := "A valid virtual ASCII AbstractString with typemax(Int) code units wraps the end sentinel to typemin(Int)+1. Subsequent iterations emit invalid views with ncodeunits=-1 instead of stopping."
    issue := "none found (queries: eachsplit overflow; SplitIterator iterate; eachsplit typemax; split ncodeunits overflow)" },
  { id := "stringutil-hex-decoder-roundtrip", juliaFile := "base/strings/util.jl"
    juliaFns := ["hex2bytes!(::AbstractArray{UInt8},itr)@1260", "number_from_hex(::UInt8)@1278"]
    statement := "Decoding a finite iterator of the lowercase hexadecimal digit pairs for any byte sequence restores exactly those bytes, in order, under tuple assertion, iteration and indexed-array update interfaces."
    source := "hex2bytes docstring, base/strings/util.jl:1189-1274"
    status := .proven, prop := ``HexDecodeRoundtrip, thm := some ``hexDecodeRoundtrip_proven },
  { id := "stringutil-hex-string-decoder", juliaFile := "base/strings/util.jl"
    juliaFns := ["hex2bytes!(::AbstractArray{UInt8},::String)@1240"]
    statement := "String decoding rejects a codeunit-count/character-count mismatch and restores every input byte encoded as two lowercase hexadecimal digits under the transcoding and indexed-array interfaces."
    source := "hex2bytes String validation and decode contract, base/strings/util.jl:1240-1244"
    status := .proven, prop := ``HexStringDecode, thm := some ``hexStringDecode_proven },
  { id := "stringutil-bytes2hex-encoding", juliaFile := "base/strings/util.jl"
    juliaFns := ["bytes2hex(itr)@1316"]
    statement := "Allocating bytes2hex writes exactly each byte's high and low lowercase hexadecimal digit in input order into the allocated output string."
    source := "bytes2hex docstring, base/strings/util.jl:1287-1327; allocation, enumeration, digit-table and indexed-store interfaces"
    status := .proven, prop := ``Bytes2hexEncoding, thm := some ``bytes2hexEncoding_proven },
  { id := "stringutil-bytes2hex-lowercase", juliaFile := "base/strings/util.jl"
    juliaFns := ["bytes2hex(itr)@1316"]
    statement := "The encoded output has twice the input byte count, and every output byte is an ASCII digit in 0-9 or a-f."
    source := "bytes2hex docstring, base/strings/util.jl:1287-1327"
    status := .proven, prop := ``Bytes2hexLowercase, thm := some ``bytes2hexLowercase_proven },
  { id := "stringutil-hex-roundtrip", juliaFile := "base/strings/util.jl"
    juliaFns := ["bytes2hex(itr)@1316", "hex2bytes(s)@1237", "hex2bytes!(::AbstractArray{UInt8},::String)@1240", "hex2bytes!(::AbstractArray{UInt8},itr)@1260"]
    statement := "Encoding any byte sequence as lowercase hexadecimal and decoding the resulting String restores exactly the original bytes, under the allocation, indexed-store, transcoding and iterator interfaces."
    source := "hex2bytes/bytes2hex roundtrip examples, base/strings/util.jl:1189-1327"
    status := .proven, prop := ``HexRoundtrip, thm := some ``hexRoundtrip_proven },
  { id := "stringutil-lpad-pieces", juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad@526", "rpad@566", "_pad_remainder(::AbstractString,::Int)@516"]
    statement := "For any target width convertible to Int, padding returns the source when the signed width difference is nonpositive and otherwise decomposes that difference into whole padding copies and the shortest character-prefix remainder reaching the remainder width."
    source := "lpad and rpad docstrings, base/strings/util.jl:494-584; division, repetition, concatenation, pair iteration and SubString interfaces"
    status := .proven, prop := ``PaddingPieces, thm := some ``paddingPieces_proven },
  { id := "stringutil-rpad-pieces", juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad@526", "rpad@566", "_pad_remainder(::AbstractString,::Int)@516"]
    statement := "For any target width convertible to Int, left and right padding return the source when the signed width difference is nonpositive and otherwise adjoin whole padding copies and a minimal character-prefix remainder with exact piecewise width bounds."
    source := "lpad and rpad docstrings, base/strings/util.jl:494-584; division, repetition, concatenation, pair iteration and SubString interfaces"
    status := .proven, prop := ``PaddingPieces, thm := some ``paddingPieces_proven },
  { id := "stringutil-rsplit-emission-limit", juliaFile := "base/strings/util.jl"
    juliaFns := ["Base.iterate(::RSplitIterator)@898"]
    statement := "A complete reverse-split iteration with a positive limit emits at most that many pieces, for every delimiter and keepempty setting."
    source := "rsplit limit keyword contract, base/strings/util.jl:973-1004"
    status := .proven, prop := ``ReverseSplitLimit, thm := some ``reverseSplitLimit_proven },
  { id := "stringutil-split-join", juliaFile := "base/strings/util.jl"
    juliaFns := ["split@958", "iterate(::SplitIterator)@791"]
    statement := "Joining successfully collected forward-split pieces with the delimiter restores every source byte when keepempty=true, for both empty and nonempty delimiters under the finder, SubString and complete-collection interfaces."
    source := "split inverse invariant, base/strings/util.jl:930-961; representable end sentinel"
    status := .proven, prop := ``SplitJoin, thm := some ``splitJoin_proven },
  { id := "stringutil-rsplit-join", juliaFile := "base/strings/util.jl"
    juliaFns := ["rsplit@1001", "Base.iterate(::RSplitIterator)@898"]
    statement := "Joining successfully collected reverse-split pieces in their returned source order with the delimiter restores every source byte when keepempty=true, for both empty and nonempty delimiters under the finder, SubString and complete-collection interfaces."
    source := "rsplit inverse invariant, base/strings/util.jl:973-1004"
    status := .proven, prop := ``RsplitJoin, thm := some ``rsplitJoin_proven },
  { id := "stringutil-replace-count-min", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace_finish@1053", "_replace_once@1068", "_replace@1011", "_replace_(::IO,str,pat_repl::NTuple{N,Pair},count::Int)@1107"]
    statement := "For any non-negative count, the replacement loop and stream replacement engine apply at most count literal replacement writes across the scan."
    source := "replace count docstring contract, base/strings/util.jl:1137 (replace at most count occurrences)"
    status := .proven, prop := ``ReplaceCountMin, thm := some ``replaceCountMin_proven },
  { id := "stringutil-truncate-width-bound", juliaFile := "base/strings/util.jl"
    juliaFns := ["rtruncate@609", "ltruncate@642", "ctruncate@676", "check_textwidth@687", "string_truncate_boundaries@697"]
    statement := "Negative maximum widths throw ArgumentError, and for any non-negative maximum width at least the replacement's display width, check_textwidth decides whether the string fits and rtruncate, ltruncate and ctruncate produce output of display width at most maxwidth."
    source := "rtruncate, ltruncate and ctruncate docstrings, base/strings/util.jl:589-735"
    status := .proven, prop := ``TruncateWidthBound, thm := some ``truncateWidthBound_proven }
]

/-! ## Method to property table

Each row names the available source-model properties or the forwarding explanation.

| Julia method | Registry property or forwarding explanation |
|---|---|
| `startswith(a::AbstractString, b::AbstractString)@31` | stringutil-prefix-sequence |
| `startswith(str::AbstractString, chars::Chars)@40` | stringutil-startswith-character-set |
| `endswith(a::AbstractString, b::AbstractString)@57` | stringscova-util-endswith-abstract-rebuilt |
| `endswith(str::AbstractString, chars::Chars)@67` | stringutil-endswith-character-set |
| `startswith(a::DenseUTF8String, b::DenseUTF8String)@69` | stringscova-util-startswith-dense-rebuilt |
| `startswith(a::Union{String,SubString{String}}, b::Union{String,SubString{String}})@83` | stringscova-util-startswith-fast-rebuilt |
| `startswith(io::IO, prefix::Base.Chars)@93` | stringutil-startswith-io-eof; stringutil-startswith-io-mark |
| `startswith(io::IO, prefix::UTF8String)@99` | stringutil-startswith-io-peek; stringutil-startswith-io-mark |
| `startswith(io::IO, prefix::AbstractString)@105` | Nothing to promise (see block above) |
| `endswith(a::DenseUTF8String, b::DenseUTF8String)@107` | stringscova-util-endswith-dense-rebuilt |
| `endswith(a::Union{String,SubString{String}}, b::Union{String,SubString{String}})@120` | Nothing to promise (see block above) |
| `contains(haystack::AbstractString, needle)@152` | Nothing to promise (see block above) |
| `endswith(s)@175` | Nothing to promise (see block above) |
| `startswith(s)@198` | Nothing to promise (see block above) |
| `contains(needle)@209` | Nothing to promise (see block above) |
| `chop(s::AbstractString; head::Integer = 0, tail::Integer = 1)@236` | strings-chop-head-overflow |
| `chopprefix(s::AbstractString, prefix::AbstractString)@268` | stringscova-util-chopprefix-abstract-rebuilt |
| `chopprefix(s::Union{String, SubString{String}}, prefix::Union{String, SubString{String}})@281` | stringscova-util-chopprefix-fast-rebuilt |
| `chopprefix(s::AbstractString, prefix::AbstractChar)@290` | stringscova-util-review-290 |
| `chopsuffix(s::AbstractString, suffix::AbstractString)@320` | stringscova-util-chopsuffix-abstract-rebuilt |
| `chopsuffix(s::Union{String, SubString{String}}, suffix::Union{String, SubString{String}})@334` | stringutil-chopsuffix-fast-bytes |
| `chopsuffix(s::AbstractString, suffix::AbstractChar)@344` | stringutil-chopsuffix-character |
| `chomp(s::AbstractString)@371` | stringutil-chomp-characters; stringutil-chomp-generic |
| `chomp(s::Union{String, SubString{String}})@379` | stringutil-chomp-fast-characters; stringutil-chomp-generic |
| `lstrip(f, s::AbstractString)@416` | stringutil-lstrip-chars; stringutil-lstrip-maximal-run |
| `lstrip(s::AbstractString)@423` | Nothing to promise (see block above) |
| `lstrip(s::AbstractString, chars::Chars)@424` | stringutil-lstrip-chars |
| `lstrip(::AbstractString, ::AbstractString)@425` | stringutil-lstrip-chars |
| `rstrip(f, s::AbstractString)@451` | stringutil-rstrip-chars; stringutil-rstrip-maximal-run |
| `rstrip(s::AbstractString)@457` | Nothing to promise (see block above) |
| `rstrip(s::AbstractString, chars::Chars)@458` | stringutil-rstrip-chars |
| `rstrip(::AbstractString, ::AbstractString)@459` | stringutil-rstrip-chars |
| `strip(s::AbstractString)@486` | Nothing to promise (see block above) |
| `strip(s::AbstractString, chars::Chars)@487` | stringutil-strip-chars |
| `strip(::AbstractString, ::AbstractString)@488` | stringutil-strip-chars |
| `strip(f, s::AbstractString)@489` | stringutil-strip-chars |
| `lpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ')@511` | Nothing to promise (see block above) |
| `_pad_remainder(p::AbstractString, r::Int)@516` | stringutil-pad-remainder-minimal; stringutil-lpad-pieces; stringutil-rpad-pieces |
| `_pad_remainder(p::AbstractChar, r::Int)@524` | Nothing to promise (see block above) |
| `lpad( s::Union{AbstractChar,AbstractString}, n::Integer, p::Union{AbstractChar,AbstractString}=' ', )@526` | stringutil-lpad-pieces; strings-lpad-typemin; stringutil-pad-malformed; stringscova-util-review-526 |
| `rpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ')@564` | Nothing to promise (see block above) |
| `rpad( s::Union{AbstractChar,AbstractString}, n::Integer, p::Union{AbstractChar,AbstractString}=' ', )@566` | stringutil-rpad-pieces; stringscova-util-review-566 |
| `rtruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…')@609` | stringutil-truncate-width-bound; stringutil-truncate-width; stringscova-util-review-676 |
| `ltruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…')@642` | stringutil-truncate-width-bound; stringscova-util-review-676 |
| `ctruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…'; prefer_left::Bool = true)@676` | stringutil-truncate-width-bound; stringscova-util-review-676 |
| `check_textwidth(str::AbstractString, maxwidth::Integer)@687` | stringutil-textwidth-prefix-check; stringutil-truncate-width-bound; stringscova-util-review-676 |
| `string_truncate_boundaries( str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar}, ::Val{mode}, prefer_left::Bool = true) where {mode}@697` | stringutil-truncate-width-bound; stringscova-util-review-676 |
| `eachsplit@772` | Nothing to promise (see block above) |
| `eltype(::Type{<:SplitIterator{T}}) where T@783` | Nothing to promise (see block above) |
| `eltype(::Type{<:SplitIterator{<:SubString{T}}}) where T@784` | Nothing to promise (see block above) |
| `IteratorSize(::Type{<:SplitIterator})@786` | Nothing to promise (see block above) |
| `iterate(iter::SplitIterator, (i, k, n)=(firstindex(iter.str), firstindex(iter.str), 0))@791` | stringutil-split-join; stringutil-split-limit; stringutil-split-sentinel-overflow |
| `eltype(::Type{PartitionIterator{T}}) where {T<:AbstractString}@810` | Nothing to promise (see block above) |
| `eltype(::Type{PartitionIterator{T}}) where {T<:SubString}@812` | Nothing to promise (see block above) |
| `iterate(itr::PartitionIterator{<:AbstractString}, state = firstindex(itr.c))@814` | strings-partition-overflow |
| `eachsplit(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}@820` | stringutil-split-limit-type |
| `eachsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}}; limit::Integer=0, keepempty=true) where {T<:AbstractString}@823` | Nothing to promise (see block above) |
| `eachsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString}@827` | Nothing to promise (see block above) |
| `eachsplit(str::AbstractString; limit::Integer=0, keepempty=false)@831` | Nothing to promise (see block above) |
| `eachrsplit@870` | Nothing to promise (see block above) |
| `eltype(::Type{<:RSplitIterator{T}}) where T@879` | Nothing to promise (see block above) |
| `eltype(::Type{<:RSplitIterator{<:SubString{T}}}) where T@880` | Nothing to promise (see block above) |
| `IteratorSize(::Type{<:RSplitIterator})@882` | Nothing to promise (see block above) |
| `eachrsplit(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}@884` | Nothing to promise (see block above) |
| `eachrsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}}; limit::Integer=0, keepempty=true) where {T<:AbstractString}@887` | Nothing to promise (see block above) |
| `eachrsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString}@891` | Nothing to promise (see block above) |
| `eachrsplit(str::AbstractString; limit::Integer=0, keepempty=false)@895` | Nothing to promise (see block above) |
| `Base.iterate(it::RSplitIterator, (to, remaining_splits)=(lastindex(it.str), it.limit-1))@898` | stringutil-rsplit-join; stringutil-rsplit-emission-limit |
| `split(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}@958` | stringutil-split-join; stringutil-split-limit |
| `split(str::AbstractString; limit::Integer=0, keepempty::Bool=false)@964` | Nothing to promise (see block above) |
| `rsplit(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}@1001` | stringutil-rsplit-join |
| `rsplit(str::AbstractString; limit::Integer=0, keepempty::Bool=false)@1007` | Nothing to promise (see block above) |
| `_replace(io, repl::Union{<:AbstractString, <:AbstractChar}, str, r, pattern)@1011` | Nothing to promise (see block above) |
| `_replace(io, repl, str, r, pattern)@1013` | stringutil-replacement-shown-byte-count |
| `_replace(io, repl::Function, str, r, pattern)@1023` | Nothing to promise (see block above) |
| `_replace(io, repl::Function, str, r, pattern::Function)@1025` | Nothing to promise (see block above) |
| `_pat_replacer(x)@1028` | Nothing to promise (see block above) |
| `_free_pat_replacer(x)@1029` | Nothing to promise (see block above) |
| `_pat_replacer(x::AbstractChar)@1031` | Nothing to promise (see block above) |
| `_pat_replacer(x::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}})@1032` | Nothing to promise (see block above) |
| `_replace_init(str, pat_repl::NTuple{N, Pair}, count::Int) where N@1035` | stringscova-util-review-1035; regexunicode-replace-empty-after-match |
| `_replace_finish(io::IO, str, count::Int, e1::Int, patterns::Tuple, replaces::Tuple, rs::Tuple)@1053` | stringutil-replace-count-min; regexunicode-replace-empty-after-match |
| `_replace_once(io::IO, str, start::Int, e1::Int, patterns::Tuple, replaces::Tuple, rs::Tuple, count::Int, n::Int, i::Int)@1068` | stringutil-replace-count-min; regexunicode-replace-empty-after-match |
| `_replace_(io::IO, str, pat_repl::NTuple{N, Pair}, count::Int) where N@1107` | stringutil-replace-count-min; stringutil-stream-replace-count-edge |
| `_replace_(str, pat_repl::NTuple{N, Pair}, count::Int) where N@1122` | stringutil-replace-count-edge; regexunicode-replace-empty-after-match |
| `replace(io::IO, s::AbstractString, pat_f::Pair...; count=typemax(Int))@1183` | Nothing to promise (see block above) |
| `replace(s::AbstractString, pat_f::Pair...; count=typemax(Int))@1186` | Nothing to promise (see block above) |
| `hex2bytes@1235` | Nothing to promise (see block above) |
| `hex2bytes(s)@1237` | stringutil-hex-roundtrip |
| `hex2bytes!(dest::AbstractArray{UInt8}, s::String)@1240` | stringutil-hex-string-decoder; stringutil-hex-roundtrip |
| `hex2bytes!(dest::AbstractArray{UInt8}, itr)@1260` | stringutil-hex-decoder-roundtrip; stringscova-util-hex2bytes-bang-iterator-rebuilt; stringutil-hex2bytes-nonascii |
| `number_from_hex(c::AbstractChar)@1276` | Nothing to promise (see block above) |
| `number_from_hex(c::Char)@1277` | Nothing to promise (see block above) |
| `number_from_hex(c::UInt8)@1278` | stringscova-util-review-1278 |
| `bytes2hex@1314` | Nothing to promise (see block above) |
| `bytes2hex(itr)@1316` | stringutil-bytes2hex-encoding; stringutil-bytes2hex-lowercase; stringutil-hex-roundtrip |
| `bytes2hex(io::IO, itr)@1329` | stringutil-bytes2hex-io-characters |
| `ascii(s::String)@1337` | stringscova-util-ascii-string-rebuilt |
| `__throw_invalid_ascii(s::String, i::Int)@1343` | stringscova-util-ascii-string-rebuilt |
| `ascii(x::AbstractString)@1364` | Nothing to promise (see block above) |
| `Base.rest(s::Union{String,SubString{String}}, i=1)@1366` | Nothing to promise (see block above) |
| `Base.rest(s::AbstractString, st...)@1367` | stringscova-util-rest-generic-rebuilt |
-/

end JuliaLean.Proofs.base.strings.util
