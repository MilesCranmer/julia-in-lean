import JuliaLean.AbstractArraySpecs.IndexOrdinary

namespace JuliaLean.AbstractArraySpecs

/-! Generic Cartesian zero-index fallback. Axis starts retain their integer type
until the second call to `getindex`/`setindex!` converts them through `to_index`.
The canonical methods are supplied by the concrete array type. -/

inductive ScalarIndex where
  | machineInt (value : I64)
  | integer (value : Int)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

def ScalarIndex.value : ScalarIndex → Int
  | .machineInt i => i.val
  | .integer i => i
  | .boolean b => if b then 1 else 0

inductive AxisIndexing where
  | unitRange
  | identityRange
  deriving DecidableEq, Repr

structure GenericAxis where
  first : ScalarIndex
  last : ScalarIndex
  indexing : AxisIndexing
  length : Nat
  deriving DecidableEq, Repr

/-- Integer `to_index` on a non-Array, including the Bool specialization
(base/indices.jl:243, 258-259). -/
def scalarToIndex (i : ScalarIndex) : R Int :=
  match i with
  | .machineInt value => .ok value.val
  | .boolean _ => .error .argumentError
  | .integer value =>
      if tmin ≤ value ∧ value ≤ tmax then .ok value else .error .inexactError

def convertScalarIndices : List ScalarIndex → R (List Int)
  | [] => .ok []
  | i :: is => do
      let j ← scalarToIndex i
      let js ← convertScalarIndices is
      .ok (j :: js)

def genericStarts (axes : List GenericAxis) : List ScalarIndex :=
  axisStarts GenericAxis.first axes

def genericInBounds : List GenericAxis → List Int → Prop
  | [], [] => True
  | axis :: axes, i :: indices =>
      axis.first.value ≤ i ∧ i < axis.first.value + axis.length ∧
        genericInBounds axes indices
  | _, _ => False

structure GenericCartesianArray (α σ : Type) where
  axes : List GenericAxis
  /-- Abstract element function, independent of the concrete getter. -/
  element : List Int → α
  canonicalGet : List Int → R α
  canonicalSet : Option (α → List Int → R σ)
  updated : α → List Int → σ

/-- The concrete array's canonical methods agree with its elements at every valid
full-dimensional Int index. Mutable arrays provide a setter; read-only arrays do
not. This law makes no assertion about indices produced by the fallback. -/
def GenericCartesianArray.Lawful {α σ : Type} (A : GenericCartesianArray α σ) : Prop :=
  (∀ I, genericInBounds A.axes I → A.canonicalGet I = .ok (A.element I)) ∧
  (∀ set, A.canonicalSet = some set → ∀ v I, genericInBounds A.axes I →
    set v I = .ok (A.updated v I))

def singletonAxes (axes : List GenericAxis) : Bool :=
  axes.all (fun axis => axis.length == 1)

/-- Cartesian `_getindex` zero-index path (abstractarray.jl:1404-1416). -/
def genericZeroGet {α σ : Type} (A : GenericCartesianArray α σ) : R α :=
  if A.axes.isEmpty then A.canonicalGet []
  else if singletonAxes A.axes then do
    let I ← convertScalarIndices (genericStarts A.axes)
    A.canonicalGet I
  else .error .boundsError

/-- Cartesian `_setindex!` zero-index path (abstractarray.jl:1495-1503).
A missing canonical setter is Julia's CanonicalIndexError. -/
def genericZeroSet {α σ : Type} (A : GenericCartesianArray α σ) (v : α) : R σ :=
  let call := fun I => match A.canonicalSet with
    | some set => set v I
    | none => .error .canonicalIndexError
  if A.axes.isEmpty then call []
  else if singletonAxes A.axes then do
    let I ← convertScalarIndices (genericStarts A.axes)
    call I
  else .error .boundsError

def genericZeroDefault {α σ : Type} (A : GenericCartesianArray α σ) (d : α) : R α :=
  if singletonAxes A.axes then genericZeroGet A else .ok d

/-- Conversion preserves the mathematical value of every accepted index. -/
theorem scalarToIndex_value (i : ScalarIndex) (j : Int)
    (h : scalarToIndex i = .ok j) : j = i.value := by
  cases i with
  | machineInt value => simpa [scalarToIndex, ScalarIndex.value] using h.symm
  | boolean value => simp [scalarToIndex] at h
  | integer value =>
    simp only [scalarToIndex] at h
    split at h <;> simp_all [ScalarIndex.value]

theorem convertScalarIndices_values (is : List ScalarIndex) (js : List Int)
    (h : convertScalarIndices is = .ok js) : js = is.map ScalarIndex.value := by
  induction is generalizing js with
  | nil => simp [convertScalarIndices] at h; simp [← h]
  | cons i is ih =>
    simp only [convertScalarIndices] at h
    cases hi : scalarToIndex i with
    | error e => simp [hi, bind_err] at h
    | ok j =>
      cases hs : convertScalarIndices is with
      | error e => simp [hi, hs, bind_ok, bind_err] at h
      | ok rest =>
        simp only [hi, hs, bind_ok, Except.ok.injEq] at h
        subst js
        simp [scalarToIndex_value i j hi, ih rest hs]

theorem starts_inBounds (axes : List GenericAxis)
    (h : singletonAxes axes = true) :
    genericInBounds axes ((genericStarts axes).map ScalarIndex.value) := by
  induction axes with
  | nil => trivial
  | cons a axes ih =>
    simp only [singletonAxes, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [genericStarts, axisStarts, List.map_cons, genericInBounds]
    have ht := ih h.2
    simp only [genericStarts, axisStarts] at ht
    exact ⟨by omega, by rw [h.1]; omega, ht⟩

/-- A converted set of first indices is in bounds whenever every dimension is
singleton. Conversion errors are not suppressed. -/
theorem convertedStarts_inBounds (axes : List GenericAxis) (I : List Int)
    (hs : singletonAxes axes = true)
    (hc : convertScalarIndices (genericStarts axes) = .ok I) :
    genericInBounds axes I := by
  rw [convertScalarIndices_values _ _ hc]
  exact starts_inBounds axes hs

/-- Independent zero-index promise: empty or non-singleton arrays reject the
read and return the default; singleton arrays select their sole element, except
when converting an axis start fails. The setter promise applies only when the
array supplies its canonical setter. -/
def GenericZeroContract : Prop :=
  ∀ {α σ : Type} (A : GenericCartesianArray α σ), A.Lawful →
    (∀ I, singletonAxes A.axes = true →
      convertScalarIndices (genericStarts A.axes) = .ok I →
      genericZeroGet A = .ok (A.element ((genericStarts A.axes).map ScalarIndex.value)) ∧
      (∀ d, genericZeroDefault A d = .ok (A.element ((genericStarts A.axes).map ScalarIndex.value))) ∧
      (∀ set, A.canonicalSet = some set → ∀ v,
        genericZeroSet A v = .ok (A.updated v ((genericStarts A.axes).map ScalarIndex.value))) ∧
      (A.canonicalSet = none → ∀ v, genericZeroSet A v = .error .canonicalIndexError)) ∧
    (singletonAxes A.axes = false →
      genericZeroGet A = .error .boundsError ∧
      (∀ d, genericZeroDefault A d = .ok d) ∧
      (∀ v, genericZeroSet A v = .error .boundsError)) ∧
    (∀ e, singletonAxes A.axes = true →
      convertScalarIndices (genericStarts A.axes) = .error e →
      genericZeroGet A = .error e ∧
      (∀ d, genericZeroDefault A d = .error e) ∧
      (∀ v, genericZeroSet A v = .error e))
theorem genericZeroContract_proven : GenericZeroContract := by
  intro α σ A lawful
  obtain ⟨getLaw, setLaw⟩ := lawful
  constructor
  · intro I hs hc
    have hvalues := convertScalarIndices_values _ _ hc
    rw [← hvalues]
    have hin := convertedStarts_inBounds A.axes I hs hc
    have hg := getLaw I hin
    have hset : ∀ set, A.canonicalSet = some set → ∀ v,
        set v I = .ok (A.updated v I) := by
      intro set h v
      exact setLaw set h v I hin
    have hget : genericZeroGet A = .ok (A.element I) := by
      cases ha : A.axes with
      | nil =>
        simp [genericStarts, axisStarts, convertScalarIndices, ha] at hc
        subst I
        simpa [genericZeroGet, genericStarts, axisStarts, ha] using hg
      | cons a axes =>
        rw [ha] at hs hc
        simp [genericZeroGet, ha, hs, hc, bind_ok, hg]
    refine ⟨hget, ?_, ?_, ?_⟩
    · intro d
      simp [genericZeroDefault, hs, hget]
    · intro set h v
      cases ha : A.axes with
      | nil =>
        simp [genericStarts, axisStarts, convertScalarIndices, ha] at hc
        subst I
        simpa [genericZeroSet, genericStarts, axisStarts, ha, h] using hset set h v
      | cons a axes =>
        rw [ha] at hs hc
        simp [genericZeroSet, ha, hs, hc, bind_ok, h, hset set h v]
    · intro h v
      cases ha : A.axes with
      | nil =>
        simp [genericStarts, axisStarts, convertScalarIndices, ha] at hc
        subst I
        simp [genericZeroSet, ha, h]
      | cons a axes =>
        rw [ha] at hs hc
        simp [genericZeroSet, ha, hs, hc, bind_ok, h]
  · constructor
    · intro hs
      have hn : A.axes.isEmpty = false := by
        cases h : A.axes with
        | nil => simp [singletonAxes, h] at hs
        | cons a axes => simp [h]
      simp [genericZeroGet, genericZeroSet, genericZeroDefault, hn, hs]
    · intro e hs hc
      have hn : A.axes.isEmpty = false := by
        cases h : A.axes with
        | nil => simp [genericStarts, axisStarts, convertScalarIndices, h] at hc
        | cons a axes => simp [h]
      simp [genericZeroGet, genericZeroSet, genericZeroDefault, hn, hs, hc, bind_err]


def axisLengthProduct : List GenericAxis → Nat
  | [] => 1
  | axis :: axes => axis.length * axisLengthProduct axes

/-- Each axis of `LinearIndices(A)` is converted to an Int range, including
both endpoints, before `first` examines the range's own indexing axes.
UnitRange is indexed from 1; IdentityUnitRange is indexed from its first value
(base/indices.jl:482-487, 525-527). -/
def convertRangeEndpoint (i : ScalarIndex) : R Int :=
  if tmin ≤ i.value ∧ i.value ≤ tmax then .ok i.value else .error .inexactError

def convertLinearAxes : List GenericAxis → R (List (AxisIndexing × Int))
  | [] => .ok []
  | axis :: axes => do
      let first ← convertRangeEndpoint axis.first
      let _ ← convertRangeEndpoint axis.last
      let rest ← convertLinearAxes axes
      .ok ((axis.indexing, first) :: rest)

def genericLinearStart (axes : List GenericAxis) : R Int := do
  let converted ← convertLinearAxes axes
  match converted with
  | [(.identityRange, first)] => .ok first
  | _ => .ok 1

/-- Independent linear index of the only element of a singleton array. -/
def genericReferenceLinearStart : List GenericAxis → Int
  | [axis] => axis.first.value
  | _ => 1

def genericLinearInBounds (axes : List GenericAxis) (i : Int) : Prop :=
  match axes with
  | [axis] => axis.first.value ≤ i ∧ i < axis.first.value + axis.length
  | _ => 1 ≤ i ∧ i ≤ axisLengthProduct axes

structure GenericLinearArray (α σ : Type) where
  axes : List GenericAxis
  element : Int → α
  canonicalGet : Int → R α
  canonicalSet : Option (α → Int → R σ)
  updated : α → Int → σ

/-- The canonical linear method agrees with the array's elements at all valid
linear indices; a setter is required only when one is supplied. -/
def GenericLinearArray.Lawful {α σ : Type} (A : GenericLinearArray α σ) : Prop :=
  (∀ i, genericLinearInBounds A.axes i → A.canonicalGet i = .ok (A.element i)) ∧
  (∀ set, A.canonicalSet = some set → ∀ v i, genericLinearInBounds A.axes i →
    set v i = .ok (A.updated v i))

def genericLinearZeroGet {α σ : Type} (A : GenericLinearArray α σ) : R α :=
  if singletonAxes A.axes then do
    let i ← genericLinearStart A.axes
    A.canonicalGet i
  else .error .boundsError

def genericLinearZeroSet {α σ : Type} (A : GenericLinearArray α σ) (v : α) : R σ :=
  if singletonAxes A.axes then do
    let i ← genericLinearStart A.axes
    match A.canonicalSet with
    | some set => set v i
    | none => .error .canonicalIndexError
  else .error .boundsError

def genericLinearZeroDefault {α σ : Type} (A : GenericLinearArray α σ) (d : α) : R α :=
  if singletonAxes A.axes then genericLinearZeroGet A else .ok d


/-- The documented zero-index promise for lawful linear arrays. -/
def GenericLinearZeroPromise : Prop :=
  ∀ {α σ : Type} (A : GenericLinearArray α σ), A.Lawful →
    singletonAxes A.axes = true →
    genericLinearZeroGet A = .ok (A.element (genericReferenceLinearStart A.axes)) ∧
    (∀ d, genericLinearZeroDefault A d = .ok (A.element (genericReferenceLinearStart A.axes))) ∧
    (∀ set, A.canonicalSet = some set → ∀ v,
      genericLinearZeroSet A v = .ok (A.updated v (genericReferenceLinearStart A.axes)))

def unitAxisExample : GenericAxis :=
  ⟨.machineInt (i64 3), .machineInt (i64 3), .unitRange, 1⟩

def unitAxisLinearExample : GenericLinearArray Int Int where
  axes := [unitAxisExample]
  element := fun _ => 7
  canonicalGet := fun i => if i = 3 then .ok 7 else .error .boundsError
  canonicalSet := some (fun v i => if i = 3 then .ok v else .error .boundsError)
  updated := fun v _ => v

theorem unitAxisLinearExample_lawful : unitAxisLinearExample.Lawful := by
  have h3 : (i64 3).val = 3 := by decide
  constructor
  · intro i hi
    simp only [unitAxisLinearExample, genericLinearInBounds, unitAxisExample,
      ScalarIndex.value, h3] at hi
    have : i = 3 := by omega
    simp [unitAxisLinearExample, this]
  · intro set hs v i hi
    simp only [unitAxisLinearExample, Option.some.injEq] at hs
    subst set
    simp only [unitAxisLinearExample, genericLinearInBounds, unitAxisExample,
      ScalarIndex.value, h3] at hi
    have : i = 3 := by omega
    simp [unitAxisLinearExample, this]

theorem genericLinearZeroPromise_refuted : ¬ GenericLinearZeroPromise := by
  intro h
  have hp := h unitAxisLinearExample unitAxisLinearExample_lawful (by decide)
  have hb : genericLinearZeroGet unitAxisLinearExample = .error .boundsError := by decide
  rw [hb] at hp
  cases hp.1

/-- Ordinary singleton axes are represented by Int ranges containing 1. -/
def OrdinarySingletonAxes (axes : List GenericAxis) : Prop :=
  ∀ axis ∈ axes, axis.first = .machineInt (i64 1) ∧
    axis.last = .machineInt (i64 1) ∧ axis.length = 1

theorem ordinarySingletonAxes_check (axes : List GenericAxis)
    (h : OrdinarySingletonAxes axes) : singletonAxes axes = true := by
  induction axes with
  | nil => rfl
  | cons a axes ih =>
    have ha := h a (by simp)
    have ht : OrdinarySingletonAxes axes := fun x hx => h x (by simp [hx])
    simp only [singletonAxes, List.all_cons, ha.2.2, beq_self_eq_true, Bool.true_and]
    exact ih ht

theorem ordinarySingletonAxes_convert (axes : List GenericAxis)
    (h : OrdinarySingletonAxes axes) :
    convertLinearAxes axes = .ok (axes.map (fun axis => (axis.indexing, 1))) := by
  induction axes with
  | nil => rfl
  | cons a axes ih =>
    have ha := h a (by simp)
    have ht : OrdinarySingletonAxes axes := fun x hx => h x (by simp [hx])
    have hc : convertRangeEndpoint (.machineInt (i64 1)) = .ok 1 := by decide
    simp only [convertLinearAxes, ha.1, ha.2.1, hc, ih ht, bind_ok, List.map_cons]

theorem ordinarySingletonAxes_linearStart (axes : List GenericAxis)
    (h : OrdinarySingletonAxes axes) : genericLinearStart axes = .ok 1 := by
  have hc := ordinarySingletonAxes_convert axes h
  unfold genericLinearStart
  rw [hc, bind_ok]
  cases axes with
  | nil => rfl
  | cons a axes =>
    cases axes with
    | nil => cases hidx : a.indexing <;> simp [hidx]
    | cons b rest => simp

theorem ordinarySingletonAxes_inBounds (axes : List GenericAxis)
    (h : OrdinarySingletonAxes axes) : genericLinearInBounds axes 1 := by
  have hp : axisLengthProduct axes = 1 := by
    induction axes with
    | nil => rfl
    | cons a axes ih =>
      have ha := h a (by simp)
      have ht : OrdinarySingletonAxes axes := fun x hx => h x (by simp [hx])
      simp [axisLengthProduct, ha.2.2, ih ht]
  cases axes with
  | nil => simp [genericLinearInBounds, axisLengthProduct]
  | cons a axes =>
    cases axes with
    | nil =>
      have ha := h a (by simp)
      simp [genericLinearInBounds, ha.1, ha.2.2, ScalarIndex.value, one_val]
    | cons b rest =>
      simp only [genericLinearInBounds]
      rw [hp]
      decide

def GenericLinearOrdinaryZero : Prop :=
  ∀ {α σ : Type} (A : GenericLinearArray α σ), A.Lawful →
    OrdinarySingletonAxes A.axes →
    genericLinearZeroGet A = .ok (A.element 1) ∧
    (∀ d, genericLinearZeroDefault A d = .ok (A.element 1)) ∧
    (∀ set, A.canonicalSet = some set → ∀ v, genericLinearZeroSet A v = .ok (A.updated v 1)) ∧
    (A.canonicalSet = none → ∀ v, genericLinearZeroSet A v = .error .canonicalIndexError)

theorem genericLinearOrdinaryZero_proven : GenericLinearOrdinaryZero := by
  intro α σ A lawful ho
  obtain ⟨hg, hw⟩ := lawful
  have hs := ordinarySingletonAxes_check A.axes ho
  have hc := ordinarySingletonAxes_linearStart A.axes ho
  have hi := ordinarySingletonAxes_inBounds A.axes ho
  simp only [genericLinearZeroGet, genericLinearZeroSet, genericLinearZeroDefault,
    hs, if_true, hc, bind_ok]
  refine ⟨hg 1 hi, fun _ => hg 1 hi, ?_, ?_⟩
  · intro set h v
    simp only [h]
    exact hw set h v 1 hi
  · intro h v
    simp [h]

end JuliaLean.AbstractArraySpecs
