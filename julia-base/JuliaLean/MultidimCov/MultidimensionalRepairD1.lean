import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairD1

open JuliaLean.Registry

inductive Error where
  | bounds
  | dimensionMismatch
  | argument
  | source (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def tupleCartesianGetindex (getindex : T → I → Result O) (tuple : T) (coordinates : List I) : Result O :=
  match coordinates with
  | [index] => getindex tuple index
  | _ => .error .dimensionMismatch

def cartesianProduct : List (List I) → List (List I)
  | [] => [[]]
  | axis :: rest => axis.flatMap fun value => (cartesianProduct rest).map fun tail => value :: tail

structure Dense (A : Type) where
  values : List A
  shape : List Nat
  deriving Repr, DecidableEq

def gatherValues (getindex : A → List I → Result V) (source : A) :
    List (List I) → Result (List V)
  | [] => .ok []
  | index :: rest => match getindex source index with
    | .error error => .error error
    | .ok value => match gatherValues getindex source rest with
      | .error error => .error error
      | .ok tail => .ok (value :: tail)

theorem gatherValues_length (getindex : A → List I → Result V) (source : A) :
    ∀ indices values, gatherValues getindex source indices = .ok values →
      values.length = indices.length := by
  intro indices
  induction indices with
  | nil => intro values h; simpa [gatherValues] using congrArg List.length (Except.ok.inj h).symm
  | cons index rest ih =>
      intro values h
      cases hg : getindex source index with
      | error error => simp [gatherValues, hg] at h
      | ok value =>
          cases ht : gatherValues getindex source rest with
          | error error => simp [gatherValues, hg, ht] at h
          | ok tail =>
              simp [gatherValues, hg, ht] at h
              subst values
              simp [ih tail ht]

def unsafeGetindex (indexShape : List (List I) → List Nat)
    (similar : A → List Nat → Result (Dense V))
    (getindex : A → List I → Result V) (source : A) (selectors : List (List I)) : Result (Dense V) :=
  let shape := indexShape selectors
  match similar source shape with
  | .error error => .error error
  | .ok destination =>
      if destination.shape ≠ shape then .error .dimensionMismatch
      else match gatherValues getindex source (cartesianProduct selectors) with
        | .error error => .error error
        | .ok values => .ok { destination with values }

def generatedGetindexBody (rank : Nat) (destinationIndices : List Nat)
    (selectors : List (List I)) (getindex : List I → Result V) : Result (List (Nat × V)) :=
  if selectors.length ≠ rank then .error .dimensionMismatch
  else
    let sourceIndices := cartesianProduct selectors
    if destinationIndices.length ≠ sourceIndices.length then .error .dimensionMismatch
    else gatherPairs destinationIndices sourceIndices
where
  gatherPairs : List Nat → List (List I) → Result (List (Nat × V))
    | [], [] => .ok []
    | destination :: destinations, source :: sources => match getindex source with
      | .error error => .error error
      | .ok value => match gatherPairs destinations sources with
        | .error error => .error error
        | .ok tail => .ok ((destination, value) :: tail)
    | _, _ => .error .dimensionMismatch

theorem gatherPairs_length (getindex : List I → Result V) :
    ∀ destinations sources output,
      generatedGetindexBody.gatherPairs getindex destinations sources = .ok output →
      output.length = destinations.length := by
  intro destinations
  induction destinations with
  | nil =>
      intro sources output h
      cases sources with
      | nil =>
          simp [generatedGetindexBody.gatherPairs] at h
          exact congrArg List.length h
      | cons source sources => simp [generatedGetindexBody.gatherPairs] at h
  | cons destination destinations ih =>
      intro sources output h
      cases sources with
      | nil => simp [generatedGetindexBody.gatherPairs] at h
      | cons source sources =>
          cases hg : getindex source with
          | error error => simp [generatedGetindexBody.gatherPairs, hg] at h
          | ok value =>
              cases ht : generatedGetindexBody.gatherPairs getindex destinations sources with
              | error error => simp [generatedGetindexBody.gatherPairs, hg, ht] at h
              | ok tail =>
                  simp [generatedGetindexBody.gatherPairs, hg, ht] at h
                  subst output
                  simp [ih sources tail ht]

def maybeReshapedSetindex (checkbounds : A → List I → Result Unit)
    (maybeReshape : A → List I → Result A) (unsafeSetindex : A → X → List I → Result A)
    (array : A) (value : X) (indices : List I) : Result A :=
  match checkbounds array indices with
  | .error error => .error error
  | .ok _ => match maybeReshape array indices with
    | .error error => .error error
    | .ok reshaped => match unsafeSetindex reshaped value indices with
      | .error error => .error error
      | .ok _ => .ok array

def generatedSetindexBody (rank : Nat) (unaliasValue : X → Result (List V))
    (unaliasSelector : List I → Result (List I))
    (shapeCheck : List V → List Nat → Result Unit)
    (setindex : V → List I → Result Unit) (value : X) (selectors : List (List I)) : Result Unit :=
  if selectors.length ≠ rank then .error .dimensionMismatch
  else match unaliasValue value with
    | .error error => .error error
    | .ok values => match selectors.mapM unaliasSelector with
      | .error error => .error error
      | .ok unaliased =>
          let shape := unaliased.map List.length
          match shapeCheck values shape with
          | .error error => .error error
          | .ok _ => setLoop values (cartesianProduct unaliased)
where
  setLoop : List V → List (List I) → Result Unit
    | [], [] => .ok ()
    | value :: values, index :: indices => match setindex value index with
      | .error error => .error error
      | .ok _ => setLoop values indices
    | _, _ => .error .dimensionMismatch

def diffArray (requireOneBased : A → Result Unit) (axes : A → Result (List (Int × Int)))
    (view : A → List (Int × Int) → Result V) (subtract : V → V → Result O)
    (array : A) (dimension rank : Int) : Result O :=
  match requireOneBased array with
  | .error error => .error error
  | .ok _ => if dimension < 1 ∨ dimension > rank then .error .argument else
    match axes array with
    | .error error => .error error
    | .ok ranges =>
        let lower := ranges.zipIdx 1 |>.map fun pair =>
          if pair.2 = dimension.toNat then (1, pair.1.2 - 1) else pair.1
        let upper := ranges.zipIdx 1 |>.map fun pair =>
          if pair.2 = dimension.toNat then (2, pair.1.2) else pair.1
        match view array upper with
        | .error error => .error error
        | .ok high => match view array lower with
          | .error error => .error error
          | .ok low => subtract high low

structure AliasFacts where
  leftParentBits : Bool
  rightParentBits : Bool
  parentsMatch : Bool
  parentIdsOverlap : Bool
  leftParentWithRightIndices : Bool
  rightParentWithLeftIndices : Bool
  indicesOverlap : Bool
  deriving Repr, DecidableEq

def mightAlias (facts : AliasFacts) : Bool :=
  if facts.leftParentBits || facts.rightParentBits then false
  else if facts.parentsMatch then facts.indicesOverlap
  else facts.parentIdsOverlap || facts.leftParentWithRightIndices || facts.rightParentWithLeftIndices

def rangesMightOverlap (intersect : R → R → Result R) (isempty : R → Result Bool)
    (tailOverlap : Result Bool) (left right : R) : Result Bool :=
  match intersect left right with
  | .error error => .error error
  | .ok overlap => match isempty overlap with
    | .error error => .error error
    | .ok true => .ok false
    | .ok false => tailOverlap

def unitRangesMightOverlap (first last : R → Result Int) (tailOverlap : Result Bool)
    (left right : R) : Result Bool :=
  match first left with
  | .error e => .error e
  | .ok leftFirst => match first right with
    | .error e => .error e
    | .ok rightFirst => match last left with
      | .error e => .error e
      | .ok leftLast => match last right with
        | .error e => .error e
        | .ok rightLast =>
          if max leftFirst rightFirst ≤ min leftLast rightLast then tailOverlap else .ok false

structure Region (I : Type) where
  indices : List (List I)
  deriving Repr, DecidableEq

def copyRegion (isempty : Region I → Result Bool) (size : Region I → Result (List Nat))
    (first last : Region I → Result (List I)) (checkbounds : A → List I → Result Unit)
    (unalias : A → A → Result A) (read : A → List I → Result V)
    (write : A → List I → V → Result A) (destination : A) (destinationRegion : Region I)
    (source : A) (sourceRegion : Region I) : Result A :=
  match isempty destinationRegion with
  | .error error => .error error
  | .ok true => .ok destination
  | .ok false => match size destinationRegion, size sourceRegion with
    | .ok destinationSize, .ok sourceSize => if destinationSize ≠ sourceSize then .error .argument else
      match first destinationRegion, last destinationRegion, first sourceRegion, last sourceRegion with
      | .ok destinationFirst, .ok destinationLast, .ok sourceFirst, .ok sourceLast =>
          match checkbounds destination destinationFirst with
          | .error e => .error e
          | .ok _ => match checkbounds destination destinationLast with
            | .error e => .error e
            | .ok _ => match checkbounds source sourceFirst with
              | .error e => .error e
              | .ok _ => match checkbounds source sourceLast with
                | .error e => .error e
                | .ok _ => match unalias destination source with
                  | .error e => .error e
                  | .ok safeSource => copyLoop destination safeSource
                      (cartesianProduct sourceRegion.indices)
                      (cartesianProduct destinationRegion.indices)
      | _, _, _, _ => .error (.source 4)
    | _, _ => .error (.source 2)
where
  copyLoop : A → A → List (List I) → List (List I) → Result A
    | output, _, [], [] => .ok output
    | output, safeSource, sourceIndex :: sourceRest, destinationIndex :: destinationRest =>
        match read safeSource sourceIndex with
        | .error e => .error e
        | .ok value => match write output destinationIndex value with
          | .error e => .error e
          | .ok next => copyLoop next safeSource sourceRest destinationRest
    | _, _, _, _ => .error .dimensionMismatch

def Contract : Prop :=
  (∀ {T I O : Type} getindex tuple index output,
    tupleCartesianGetindex (T := T) (I := I) (O := O) getindex tuple [index] = .ok output →
      getindex tuple index = .ok output) ∧
  (∀ {A I V : Type} indexShape similar getindex source selectors output,
    unsafeGetindex (A := A) (I := I) (V := V) indexShape similar getindex source selectors = .ok output →
      output.shape = indexShape selectors ∧ output.values.length = (cartesianProduct selectors).length) ∧
  (∀ {I V : Type} rank destinationIndices selectors getindex output,
    generatedGetindexBody (I := I) (V := V) rank destinationIndices selectors getindex = .ok output →
      output.length = destinationIndices.length) ∧
  (∀ {X V I : Type} rank unaliasValue unaliasSelector shapeCheck setindex value selectors,
    generatedSetindexBody (X := X) (V := V) (I := I) rank unaliasValue unaliasSelector
      shapeCheck setindex value selectors = .ok () →
      selectors.length = rank ∧ ∃ values unaliased,
        unaliasValue value = .ok values ∧ selectors.mapM unaliasSelector = .ok unaliased ∧
        shapeCheck values (unaliased.map List.length) = .ok ()) ∧
  (∀ {A I X : Type} checkbounds reshape unsafeSet array value indices output,
    maybeReshapedSetindex (A := A) (I := I) (X := X) checkbounds reshape unsafeSet array value indices = .ok output →
      output = array) ∧
  (∀ {A V O : Type} requireOneBased axes view subtract array dimension rank output,
    diffArray (A := A) (V := V) (O := O) requireOneBased axes view subtract
      array dimension rank = .ok output →
      requireOneBased array = .ok () ∧ 1 ≤ dimension ∧ dimension ≤ rank) ∧
  (∀ facts, mightAlias facts =
    if facts.leftParentBits || facts.rightParentBits then false else if facts.parentsMatch then facts.indicesOverlap
    else facts.parentIdsOverlap || facts.leftParentWithRightIndices || facts.rightParentWithLeftIndices) ∧
  (∀ {R : Type} intersect isempty tail left right,
    rangesMightOverlap (R := R) intersect isempty tail left right = .ok true →
      ∃ overlap, intersect left right = .ok overlap ∧ isempty overlap = .ok false ∧ tail = .ok true) ∧
  (∀ {R : Type} first last tail left right,
    unitRangesMightOverlap (R := R) first last tail left right = .ok true → tail = .ok true) ∧
  (∀ {A I V : Type} isempty size first last checkbounds unalias read write destination destinationRegion source sourceRegion output,
    copyRegion (A := A) (I := I) (V := V) isempty size first last checkbounds unalias read write
      destination destinationRegion source sourceRegion = .ok output →
      (isempty destinationRegion = .ok true ∧ output = destination) ∨
      (isempty destinationRegion = .ok false ∧ ∃ destinationSize sourceSize,
        size destinationRegion = .ok destinationSize ∧ size sourceRegion = .ok sourceSize ∧
        destinationSize = sourceSize))

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    simpa [tupleCartesianGetindex] using ‹_›
  · intro A I V indexShape similar getindex source selectors output h
    cases hs : similar source (indexShape selectors) with
    | error error => simp [unsafeGetindex, hs] at h
    | ok destination =>
        by_cases hshape : destination.shape = indexShape selectors
        · cases hg : gatherValues getindex source (cartesianProduct selectors) with
          | error error => simp [unsafeGetindex, hs, hshape, hg] at h
          | ok values =>
              simp [unsafeGetindex, hs, hshape, hg] at h
              subst output
              constructor
              · rfl
              · exact gatherValues_length getindex source (cartesianProduct selectors) values hg
        · simp [unsafeGetindex, hs, hshape] at h
  · intro I V rank destinationIndices selectors getindex output h
    by_cases hr : selectors.length = rank
    · by_cases hl : destinationIndices.length = (cartesianProduct selectors).length
      · apply gatherPairs_length getindex destinationIndices (cartesianProduct selectors) output
        simpa [generatedGetindexBody, hr, hl] using h
      · simp [generatedGetindexBody, hr, hl] at h
    · simp [generatedGetindexBody, hr] at h
  · intro X V I rank unaliasValue unaliasSelector shapeCheck setindex value selectors h
    by_cases hr : selectors.length = rank
    · cases hv : unaliasValue value with
      | error error => simp [generatedSetindexBody, hr, hv] at h
      | ok values =>
          cases hi : selectors.mapM unaliasSelector with
          | error error => simp [generatedSetindexBody, hr, hv, hi] at h
          | ok unaliased =>
              cases hs : shapeCheck values (unaliased.map List.length) with
              | error error => simp [generatedSetindexBody, hr, hv, hi, hs] at h
              | ok checked => exact ⟨hr, values, unaliased, rfl, rfl, hs⟩
    · simp [generatedSetindexBody, hr] at h
  · intro A I X checkbounds reshape unsafeSet array value indices output h
    cases hb : checkbounds array indices with
    | error error => simp [maybeReshapedSetindex, hb] at h
    | ok checked =>
        cases hr : reshape array indices with
        | error error => simp [maybeReshapedSetindex, hb, hr] at h
        | ok reshaped =>
            cases hs : unsafeSet reshaped value indices with
            | error error => simp [maybeReshapedSetindex, hb, hr, hs] at h
            | ok changed =>
                simp [maybeReshapedSetindex, hb, hr, hs] at h
                exact h.symm
  · intro A V O requireOneBased axes view subtract array dimension rank output h
    cases hb : requireOneBased array with
    | error error => simp [diffArray, hb] at h
    | ok checked =>
        by_cases hd : dimension < 1 ∨ dimension > rank
        · simp [diffArray, hb, hd] at h
        · exact ⟨rfl, by omega, by omega⟩
  · intros
    rfl
  · intro R intersect isempty tail left right h
    cases hi : intersect left right with
    | error error => simp [rangesMightOverlap, hi] at h
    | ok overlap =>
        cases he : isempty overlap with
        | error error => simp [rangesMightOverlap, hi, he] at h
        | ok empty =>
            cases empty
            · have ht := h
              simp [rangesMightOverlap, hi, he] at ht
              exact ⟨overlap, rfl, he, ht⟩
            · simp [rangesMightOverlap, hi, he] at h
  · intro R first last tail left right h
    cases hfl : first left with
    | error error => simp [unitRangesMightOverlap, hfl] at h
    | ok leftFirst =>
        cases hfr : first right with
        | error error => simp [unitRangesMightOverlap, hfl, hfr] at h
        | ok rightFirst =>
            cases hll : last left with
            | error error => simp [unitRangesMightOverlap, hfl, hfr, hll] at h
            | ok leftLast =>
                cases hlr : last right with
                | error error => simp [unitRangesMightOverlap, hfl, hfr, hll, hlr] at h
                | ok rightLast =>
                    by_cases hover : max leftFirst rightFirst ≤ min leftLast rightLast
                    · simpa [unitRangesMightOverlap, hfl, hfr, hll, hlr, hover] using h
                    · simp [unitRangesMightOverlap, hfl, hfr, hll, hlr, hover] at h
  · intro A I V isempty size first last checkbounds unalias read write destination destinationRegion source sourceRegion output h
    cases he : isempty destinationRegion with
    | error error => simp [copyRegion, he] at h
    | ok empty =>
        cases empty
        · cases hd : size destinationRegion with
          | error error => simp [copyRegion, he, hd] at h
          | ok destinationSize =>
              cases hs : size sourceRegion with
              | error error => simp [copyRegion, he, hd, hs] at h
              | ok sourceSize =>
                  by_cases hsize : destinationSize = sourceSize
                  · exact Or.inr ⟨rfl, destinationSize, sourceSize, rfl, rfl, hsize⟩
                  · simp [copyRegion, he, hd, hs, hsize] at h
        · simp [copyRegion, he] at h
          exact Or.inl ⟨rfl, h.symm⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairD1
