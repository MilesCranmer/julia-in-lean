import JuliaLean.base.subarray
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

/-!
# Properties of `base/subarray.jl`

Specifications describe view-axis, indexing, constructor, stride, and aliasing behaviour promised
by Base and the array manual. Parent access and operations supplied by other Base files remain
explicit interfaces in the model.
-/

/-! Nothing to promise:
similar@72: Forwards allocation to the parent with the requested type and dimensions.
similar@73: Forwards allocation to the parent type.
parentindices@107: Forward declaration; it installs no method body.
_maybe_reshape_parent@165: Forwards the one-dimensional reshape request to reshape.
_maybe_reshape_parent@166: Forwards the vector reshape request to reshape.
_maybe_reshape_parent@168: Forwards the requested rank to reshape.
view@230: Forwards immutable range selection to getindex.
view@234: Forwards immutable range selection to getindex.
view@238: Forwards immutable range selection to getindex.
view@242: Forwards immutable range selection to getindex.
view@246: Forwards immutable range selection to getindex.
view@252: Forwards Colon selection of an immutable range to getindex.
unsafe_view@257: Forwards construction to SubArray; it has no separate selection algorithm.
_maybe_reindex@273: Dispatch plumbing: resumes the scan after a CartesianIndex{1} array.
_maybe_reindex@275: Dispatch plumbing: resumes the scan after the current index.
getindex@383: Converts Colon to parent indices and forwards to getindex.
setindex!@412: Converts Colon to parent indices and forwards to setindex!.
elsize@458: Forwards element storage size to the parent type.
iscontiguous@460: Forwards contiguity classification to the view type.
has_offset_axes@543: Forwards offset-axis detection to the stored index tuple.
replace_in_print_matrix@545: Reindexes coordinates and delegates formatting to the parent.
replace_in_print_matrix@548: Reindexes the row and delegates formatting to the parent.
unsafe_wrap@553: Delegates wrapping of the view pointer and dimensions to unsafe_wrap.
-/

/-! Method-to-property table. A qualified scope below is partial coverage;
`uncovered` identifies a method with no registered behavioural specification.

| Method | Registry property |
| --- | --- |
| SubArray{T,N,P,I,L}@19 | subarray-constructor-retains-parent-indices; subarray-constructor-rejects-rank |
| SubArray@26 | multidimcov-subarray-v2-construct-linear; multidimcov-subarray-v2-view-of-view |
| SubArray@30 | multidimcov-subarray-v2-construct-cartesian |
| SubArray@34 | multidimcov-subarray-v2-construct-linear |
| _compute_linear_layout@40 | multidimcov-subarray-v2-construct-linear; multidimcov-subarray-v2-offset1 |
| check_parent_index_match@46 | subarray-constructor-rejects-rank |
| check_parent_index_match@47 | subarray-constructor-retains-parent-indices |
| check_parent_index_match@48 | multidimcov-subarray-v2-check-mismatch |
| viewindexing@52 | subarray-linear-index-classification |
| viewindexing@54 | multidimcov-subarray-v2-viewindexing-scalar |
| viewindexing@56 | subarray-linear-index-classification |
| viewindexing@58 | subarray-linear-index-classification |
| viewindexing@59 | subarray-linear-index-classification |
| viewindexing@63 | subarray-linear-index-classification |
| viewindexing@65 | multidimcov-subarray-v2-maybe-reindex-cartesian |
| viewindexing@67 | subarray-linear-index-classification |
| size@70 | subarray-size-index-axes |
| similar@72 | Nothing to promise (see above) |
| similar@73 | Nothing to promise (see above) |
| sizeof@75 | subarray-sizeof-machine-bytes |
| sizeof@76 | subarray-sizeof-machine-bytes |
| Base.copy@78 | subarray-copy-nonscalar-selection (non-scalar branch) |
| parent@86 | subarray-constructor-retains-parent-indices |
| parentindices@87 | subarray-constructor-retains-parent-indices |
| parentindices@107 | Nothing to promise (see above) |
| parentindices@109 | subarray-default-parentindices-coordinate-domain |
| dataids@112 | subarray-dataids-membership |
| _splatmap@113 | multidimcov-subarray-v2-splatmap |
| _splatmap@114 | multidimcov-subarray-v2-splatmap |
| unaliascopy@115 | subarray-unaliascopy-keeps-layout |
| unaliascopy@119 | uncovered |
| _trimmedshape@133 | uncovered |
| _trimmedshape@134 | uncovered |
| _trimmedshape@135 | uncovered |
| _trimmedshape@136 | uncovered |
| _trimmedshape@137 | uncovered |
| _trimmedshape@138 | uncovered |
| _trimmedshape@139 | uncovered |
| _trimmedpind@141 | uncovered |
| _trimmedpind@142 | uncovered |
| _trimmedpind@143 | uncovered |
| _trimmedpind@144 | uncovered |
| _trimmedpind@145 | uncovered |
| _trimmedvind@146 | uncovered |
| _trimmedvind@147 | uncovered |
| _trimmedvind@148 | uncovered |
| _trimmedindex@150 | uncovered |
| _trimmedindex@151 | uncovered |
| _trimmedindex@152 | uncovered |
| _trimmedindex@153 | uncovered |
| _trimmedindex@154 | uncovered |
| _trimmedindex@155 | uncovered |
| _maybe_reshape_parent@165 | Nothing to promise (see above) |
| _maybe_reshape_parent@166 | Nothing to promise (see above) |
| _maybe_reshape_parent@167 | multidimcov-subarray-v2-reshape-parent-same |
| _maybe_reshape_parent@168 | Nothing to promise (see above) |
| rm_singleton_indices@170 | uncovered |
| rm_singleton_indices@171 | uncovered |
| rm_singleton_indices@172 | uncovered |
| view@221 | uncovered |
| view@230 | Nothing to promise (see above) |
| view@234 | Nothing to promise (see above) |
| view@238 | Nothing to promise (see above) |
| view@242 | Nothing to promise (see above) |
| view@246 | Nothing to promise (see above) |
| view@252 | Nothing to promise (see above) |
| unsafe_view@257 | Nothing to promise (see above) |
| unsafe_view@267 | multidimcov-subarray-v2-view-of-view |
| _maybe_reindex@269 | multidimcov-subarray-v2-maybe-reindex |
| _maybe_reindex@270 | multidimcov-subarray-v2-maybe-reindex-cartesian |
| _maybe_reindex@273 | Nothing to promise (see above) |
| _maybe_reindex@275 | Nothing to promise (see above) |
| _maybe_reindex@276 | multidimcov-subarray-v2-maybe-reindex |
| reindex@292 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| reindex@295 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| reindex@299 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| reindex@303 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| reindex@307 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| reindex@311 | multidimcov-subarray-v2-reindex; broadcastviews-nested-view-compose |
| getindex@316 | multidimcov-subarray-v2-construct-cartesian; multidimcov-subarray-v2-maybe-reindex-cartesian |
| _reindexlinear@327 | reinterpretarrays-view-linear-index (first-dimension range case) |
| _reindexlinear@328 | uncovered |
| getindex@330 | multidimcov-subarray-v2-getindex-fast; subarray-fast-bounds-errors; subarray-fast-write-readback |
| getindex@339 | multidimcov-subarray-v2-getindex-fast-vector; subarray-fast-bounds-errors; subarray-fast-vector-write-readback |
| _reindexlinear@351 | uncovered |
| _reindexlinear@352 | uncovered |
| getindex@376 | uncovered |
| getindex@383 | Nothing to promise (see above) |
| setindex!@386 | subarray-cartesian-selected-write |
| setindex!@392 | subarray-fast-bounds-errors; subarray-fast-write-readback |
| setindex!@398 | multidimcov-subarray-v2-setindex-fast-vector; subarray-fast-bounds-errors; subarray-fast-vector-write-readback |
| setindex!@405 | uncovered |
| setindex!@412 | Nothing to promise (see above) |
| isassigned@414 | subarray-cartesian-selected-isassigned |
| isassigned@420 | subarray-isassigned-outside-view (bounds branch) |
| isassigned@426 | multidimcov-subarray-v2-isassigned-fast-vector |
| IndexStyle@433 | uncovered |
| strides@437 | broadcastviews-stride-zero-dim |
| substrides@439 | broadcastviews-stride-zero-dim |
| substrides@440 | uncovered |
| substrides@441 | uncovered |
| substrides@442 | uncovered |
| substrides@443 | uncovered |
| stride@446 | broadcastviews-stride-zero-dim |
| compute_stride1@448 | reinterpretarrays-view-linear-index (first-dimension range case) |
| compute_stride1@450 | uncovered |
| compute_stride1@451 | uncovered |
| compute_stride1@452 | uncovered |
| compute_stride1@454 | reinterpretarrays-view-linear-index |
| compute_stride1@455 | reinterpretarrays-nested-slice-offset (identity-range colon case) |
| compute_stride1@456 | uncovered |
| elsize@458 | Nothing to promise (see above) |
| iscontiguous@460 | Nothing to promise (see above) |
| iscontiguous@461 | uncovered |
| iscontiguous@462 | uncovered |
| first_index@464 | uncovered |
| first_index@465 | uncovered |
| compute_offset1@471 | multidimcov-subarray-v2-offset1 |
| compute_offset1@478 | multidimcov-subarray-v2-offset1 |
| compute_offset1@480 | multidimcov-subarray-v2-offset1 |
| compute_offset1@482 | multidimcov-subarray-v2-offset1 |
| compute_offset1@484 | multidimcov-subarray-v2-offset1 |
| compute_linindex@486 | multidimcov-subarray-v2-linindex |
| compute_linindex@491 | multidimcov-subarray-v2-linindex-step |
| compute_linindex@496 | multidimcov-subarray-v2-linindex-last |
| compute_linindex@501 | multidimcov-subarray-v2-linindex |
| find_extended_dims@503 | subarray-extended-coordinate-order |
| find_extended_dims@504 | subarray-extended-coordinate-order |
| find_extended_dims@505 | subarray-extended-coordinate-order |
| find_extended_inds@506 | subarray-extended-coordinate-order |
| find_extended_inds@507 | subarray-extended-coordinate-order |
| find_extended_inds@508 | subarray-extended-coordinate-order |
| pointer@510 | multidimcov-subarray-v2-pointer-fast |
| pointer@511 | multidimcov-subarray-v2-pointer-contiguous |
| pointer@513 | uncovered |
| axes@525 | multidimcov-subarray-v2-axes |
| _indices_sub@526 | multidimcov-subarray-v2-axes |
| _indices_sub@527 | multidimcov-subarray-v2-axes |
| _indices_sub@528 | multidimcov-subarray-v2-axes |
| axes1@533 | multidimcov-subarray-v2-axes1 |
| axes1@534 | multidimcov-subarray-v2-axes1 |
| _axes1_sub@535 | multidimcov-subarray-v2-axes1 |
| _axes1_sub@536 | multidimcov-subarray-v2-axes1 |
| _axes1_sub@537 | multidimcov-subarray-v2-axes1 |
| _axes1_sub@538 | multidimcov-subarray-v2-axes1 |
| has_offset_axes@543 | Nothing to promise (see above) |
| replace_in_print_matrix@545 | Nothing to promise (see above) |
| replace_in_print_matrix@548 | Nothing to promise (see above) |
| unsafe_wrap@553 | Nothing to promise (see above) |
-/

namespace JuliaLean.Proofs.base.subarray

open JuliaLean JuliaLean.base.subarray JuliaLean.Registry

@[simp] theorem iadd_lit (a b : Int) : iadd (int64 a) (int64 b) = int64 (a + b) := by
  apply Subtype.ext
  change (JuliaLean.base.int.add (int64 a) (int64 b)).val = _
  rw [JuliaLean.Proofs.base.int.addWraps_proven]
  simp only [int64, JuliaLean.Proofs.base.int.lit_val,
    JuliaLean.Proofs.base.int.wrapInt_add_left, JuliaLean.Proofs.base.int.wrapInt_add_right]

@[simp] theorem isub_lit (a b : Int) : isub (int64 a) (int64 b) = int64 (a - b) := by
  apply Subtype.ext
  change (JuliaLean.base.int.sub (int64 a) (int64 b)).val = _
  rw [JuliaLean.Proofs.base.int.subWraps_proven]
  simp only [int64, JuliaLean.Proofs.base.int.lit_val,
    JuliaLean.Proofs.base.int.wrapInt_sub_left, JuliaLean.Proofs.base.int.wrapInt_sub_right]

@[simp] theorem imul_lit (a b : Int) : imul (int64 a) (int64 b) = int64 (a * b) := by
  apply Subtype.ext
  change (JuliaLean.base.int.mul (int64 a) (int64 b)).val = _
  rw [JuliaLean.Proofs.base.int.mulWraps_proven]
  simp only [int64, JuliaLean.Proofs.base.int.lit_val,
    JuliaLean.Proofs.base.int.wrapInt_mul_left, JuliaLean.Proofs.base.int.wrapInt_mul_right]


private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/subarray.jl", juliaFns, statement, source,
    status := .proven, prop, thm := some thm }

private def refuted (id : String) (juliaFns : List String) (statement source : String)
    (prop thm : Lean.Name) (issue notes : String) : Entry :=
  { id, juliaFile := "base/subarray.jl", juliaFns, statement, source,
    status := .refuted, prop, thm := some thm, issue, notes }

/-- A leading scalar leaves the classification of the remaining indices unchanged. -/
def LeadingScalarIndexStyle : Prop :=
  ∀ (value : I64) (rest : List Index), viewIndexing (.scalar value :: rest) = viewIndexing rest

theorem leadingScalarIndexStyle_proven : LeadingScalarIndexStyle := by
  intro value rest
  simp [viewIndexing]

/-- `_splatmap` concatenates the mapped tuple elements in order and propagates its first error. -/
def SplatMapOrder : Prop :=
  ∀ {α β : Type} (f : α → Jl (List β)) (indices : List α),
    splatmap f indices = (indices.mapM f).map List.flatten

theorem splatMapOrder_proven : SplatMapOrder := by
  intro α β f indices
  induction indices with
  | nil => rfl
  | cons x xs ih =>
      cases hx : f x with
      | error e =>
          have hMap : List.mapM f (x :: xs) = .error e := by
            rw [List.mapM_cons, hx]
            rfl
          rw [hMap, splatmap, hx]
          rfl
      | ok first =>
          cases htail : List.mapM f xs with
          | error e =>
              have hMap : List.mapM f (x :: xs) = .error e := by
                rw [List.mapM_cons, hx, htail]
                rfl
              rw [hMap, splatmap, hx, ih, htail]
              rfl
          | ok tail =>
              have hMap : List.mapM f (x :: xs) = .ok (first :: tail) := by
                rw [List.mapM_cons, hx, htail]
                rfl
              rw [hMap, splatmap, hx, ih, htail]
              rfl

/-- A same-rank reshape request returns the parent array unchanged. -/
def ReshapeParentSameRank : Prop :=
  ∀ {A : Type} (parent : A) (dimensions : List Bool) (parentRank : Nat),
    parentRank = dimensions.length → maybeReshapeParentSameRank parent dimensions = .ok parent

theorem reshapeParentSameRank_proven : ReshapeParentSameRank := by
  intro A parent dimensions parentRank _
  rfl

/-- A rank mismatch reports the parent rank and the number of consumed indices. -/
def ParentIndexMismatchMessage : Prop :=
  ∀ {P : Type} (parent : P) (dimensions : List Bool) (ndims : P → Jl Nat) (rank : Nat),
    ndims parent = .ok rank →
    checkParentIndexMatchMismatch parent dimensions ndims =
      .error (.argumentError s!"number of indices ({dimensions.length}) must match the parent dimensionality ({rank})")

theorem parentIndexMismatchMessage_proven : ParentIndexMismatchMessage := by
  intro P parent dimensions ndims rank hndims
  unfold checkParentIndexMatchMismatch
  rw [hndims]
  rfl

def ParentIndexMismatchContract : Prop :=
  ParentIndexMismatchMessage ∧
  ∀ {P : Type} (parent : P) (dimensions : List Bool) (ndims : P → Jl Nat) (error : JlError),
    ndims parent = .error error →
    checkParentIndexMatchMismatch parent dimensions ndims = .error error

theorem parentIndexMismatchContract_proven : ParentIndexMismatchContract := by
  refine ⟨parentIndexMismatchMessage_proven, ?_⟩
  intro P parent dimensions ndims error failure
  simp [checkParentIndexMatchMismatch, failure, Bind.bind, Except.bind]


/-- The axes of a view are the axes of its stored indices, in their original order. -/
def viewAxesManual (indices : List Index) : List Axis := indices.flatMap Index.indexAxes

def StoredIndex : Index → Prop
  | .colon | .other | .cartesian _ => False
  | _ => True

def StoredIndices : List Index → Prop
  | [] => True
  | index :: rest => StoredIndex index ∧ StoredIndices rest

def SubArrayAxesContract : Prop :=
  ∀ {P T : Type} (view : SubArray P T),
    axesSubArrayModel view = viewAxesManual view.indices

theorem indicesSubDispatch_spec : ∀ indices,
    indicesSubDispatch indices = viewAxesManual indices
  | [] => by simp [indicesSubDispatch, indicesSubEmpty, viewAxesManual]
  | index :: rest => by
      cases index <;>
        simp [indicesSubDispatch, indicesSubEmpty, viewAxesManual, Index.indexAxes,
          indicesSubDispatch_spec rest]

theorem subArrayAxesContract_proven : SubArrayAxesContract := by
  intro P T view
  exact indicesSubDispatch_spec view.indices



/-- Axis access selects the first axis of the non-scalar stored indices. -/
def firstOrDefaultAxis (axes : List Axis) : Axis := axes.headD axes1ZeroDimSubArray

def Axes1Contract {P T : Type} (view : SubArray P T) : Prop :=
  StoredIndices view.indices →
    view.dimensions.length = (viewAxesManual view.indices).length →
    axes1SubArrayModel view = some (firstOrDefaultAxis (viewAxesManual view.indices))

theorem axes1SubDispatch_spec : ∀ indices, StoredIndices indices →
    axes1SubDispatch indices = (viewAxesManual indices).head?
  | [], _ => by simp [axes1SubDispatch, axes1SubEmpty, viewAxesManual]
  | index :: rest, h => by
      have hr := h.2
      cases index with
      | scalar value =>
          simp [axes1SubDispatch, viewAxesManual, Index.indexAxes, axes1SubDispatch_spec rest hr]
      | colon => cases h.1
      | slice axis => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | unitRange axis => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | oneTo length => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | identity axis => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | stepRange first step count => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | stepRangeLen first step count => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | ordinalRange first step count => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | linRange first last count => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | values axes items =>
          cases axes with
          | nil => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes, axes1SubDispatch_spec rest hr]
          | cons axis axes => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | cartesianValues axes elementRank items =>
          cases axes with
          | nil => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes, axes1SubDispatch_spec rest hr]
          | cons axis axes => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | mask values => simp [axes1SubDispatch, viewAxesManual, Index.indexAxes]
      | other => cases h.1
      | cartesian coordinates => cases h.1

theorem axes1Contract_proven {P T : Type} (view : SubArray P T) : Axes1Contract view := by
  intro valid hRank
  unfold axes1SubArrayModel axes1SubArray firstOrDefaultAxis
  by_cases hZero : view.dimensions.length = 0
  · have hAxes : viewAxesManual view.indices = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← hRank, hZero]
    simp [hZero, hAxes, axes1ZeroDimSubArray]
  · have hSpec := axes1SubDispatch_spec view.indices valid
    simp only [if_neg hZero, hSpec]
    cases hAxes : viewAxesManual view.indices with
    | nil =>
        have hLen : view.dimensions.length = 0 := by simpa [hAxes] using hRank
        exact (hZero hLen).elim
    | cons axis rest => simp [hAxes, axes1ZeroDimSubArray]

def Axes1ContractAll : Prop :=
  ∀ {P T : Type} (view : SubArray P T), Axes1Contract view

theorem axes1ContractAll_proven : Axes1ContractAll := by
  intro P T view
  exact axes1Contract_proven view


def CartesianArrayFallbackNests : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P)
    (view : SubArray P T) (axes : List Axis) (elementRank : Nat)
    (items : List (List I64)) (rest : List Index),
  elementRank ≠ 1 →
  (ops.indexNdims (ops.ensureIndexable
    (.cartesianValues axes elementRank items :: rest))).length = view.dimensions.length →
  ∀ (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index)),
    ∃ nested : SubArray (SubArray P T) T,
      unsafeViewSubArrayConfigured ops firstLinearIndex
        getVector getMatrix getArray toIndices view
        (.cartesianValues axes elementRank items :: rest) = .ok (.nested nested) ∧
      nested.parent = view ∧
      nested.indices = ops.ensureIndexable (.cartesianValues axes elementRank items :: rest) ∧
      nested.linear = false ∧ nested.offset1 = int64 0 ∧ nested.stride1 = int64 0

theorem cartesianArrayFallbackNests_proven : CartesianArrayFallbackNests := by
  intro P T ops view axes elementRank items rest hNonVector hConsumed
    firstLinearIndex getVector getMatrix getArray toIndices
  let indices : List Index := .cartesianValues axes elementRank items :: rest
  let nested : SubArray (SubArray P T) T :=
    ⟨view, ops.ensureIndexable indices, int64 0, int64 0, false,
      ops.indexDimsum indices⟩
  have hRank : view.dimensions.length =
      (ops.indexNdims (ops.ensureIndexable indices)).length := hConsumed.symm
  refine ⟨nested, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp [unsafeViewSubArrayConfigured, unsafeViewSubArray, maybeReindexConfigured,
    maybeReindex, maybeReindexDispatch, maybeReindexCartesianArray,
    constructSubArrayConfigured, subarrayOuter, constructSubArrayByStyle,
    subarrayCartesian, subarrayInner, checkParentIndexMatchWithOps,
    checkParentIndexMatch, parentArrayOpsSubArray, viewIndexing, Index.isRange,
    Index.isArray, Index.indexAxes, viewIndexingArray, indexStyleCombine,
    checkParentIndexMatchArray, hNonVector, hRank, indices, nested,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

def SupportedStrideIndex (index : Index) : Prop :=
  index.isScalar = true ∨ index.isRange = true

def SupportedStrideIndices : List Index → Prop
  | [] => True
  | index :: rest => SupportedStrideIndex index ∧ SupportedStrideIndices rest

def getListI64OneBased (values : List I64) (index : I64) : Jl I64 :=
  if 1 ≤ index.val ∧ index.val ≤ values.length then
    match values[index.val.toNat - 1]? with
    | some value => .ok value
    | none => .error .boundsError
  else .error .boundsError

def lastListI64 : List I64 → Jl I64
  | [] => .error .boundsError
  | [value] => .ok value
  | _ :: next :: rest => lastListI64 (next :: rest)
termination_by values => values.length
decreasing_by all_goals simp_wf

def strideSubArrayConfigured {P T : Type} (ops : ParentArrayOps P)
    (view : SubArray P T) (dimension : I64) : Jl I64 :=
  strideSubArray view dimension id (fun view => view.dimensions.length)
    (fun _ => stridesSubArray view ops.strides
      (substridesDispatch ops.indexStep ops.indexTypeName))
    (fun _ => .ok (sizeSubArray view axesSubArrayModel ops.axisLength))
    getListI64OneBased lastListI64

def SubArrayStrideTotal : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (view : SubArray P T) (dimension : I64),
    SupportedStrideIndices view.indices →
    view.dimensions.length = (axesSubArrayModel view).length →
    (∃ strides,
      stridesSubArray view ops.strides
        (substridesDispatch ops.indexStep ops.indexTypeName) = .ok strides ∧
      strides.length = view.dimensions.length) →
    1 ≤ dimension.val →
    ∃ stride, strideSubArrayConfigured ops view dimension = .ok stride

def strideCounterexampleOps : ParentArrayOps (List Axis) where
  parentStyle := fun _ => .linear
  isArrayRank := fun axes rank => decide (axes.length = rank)
  ndims := fun axes => .ok axes.length
  indexNdims := fun indices => indices.flatMap fun index =>
    match index with
    | .cartesian coordinates => List.replicate coordinates.length true
    | .cartesianValues _ rank _ => List.replicate rank true
    | _ => [true]
  indexDimsum := fun indices => (indices.flatMap Index.indexAxes).map (fun _ => true)
  ensureIndexable := id
  axes := id
  strides := fun _ => .ok [int64 1, int64 4]
  fillToLength := fun axes default count =>
    .ok (axes.take count ++ List.replicate (count - axes.length) default)
  firstLinearIndex := fun _ => .ok (int64 1)
  axisFirst := Axis.first
  axisLength := fun axis => iadd (isub axis.last axis.first) (int64 1)
  indexFirst := fun index =>
    match index with
    | .scalar value => .ok value
    | .slice axis | .identity axis | .unitRange axis => .ok axis.first
    | .oneTo _ => .ok (int64 1)
    | .stepRange first _ _ | .stepRangeLen first _ _ | .ordinalRange first _ _ => .ok first
    | .linRange first _ _ => .ok first
    | _ => .error (.methodError "first")
  indexStep := fun index =>
    match index with
    | .stepRange _ step _ | .stepRangeLen _ step _ | .ordinalRange _ step _ => step
    | _ => int64 1
  indexTypeName := fun index =>
    match index with
    | .scalar _ => "ScalarIndex"
    | .slice _ => "Slice"
    | .unitRange _ => "UnitRange"
    | .oneTo _ => "OneTo"
    | .identity _ => "IdentityUnitRange"
    | .stepRange _ _ _ => "StepRange"
    | .stepRangeLen _ _ _ => "StepRangeLen"
    | .ordinalRange _ _ _ => "OrdinalRange"
    | .linRange _ _ _ => "LinRange"
    | .values _ _ => "Array"
    | .cartesianValues _ _ _ => "Array"
    | .mask _ => "Array"
    | .colon => "Colon"
    | .other => "Index"
    | .cartesian _ => "CartesianIndex"
  axes1First := fun index =>
    match index.indexAxes with
    | axis :: _ => .ok axis.first
    | [] => .error .boundsError
  isVector := fun axes => decide (axes.length = 1)

theorem subArrayStrideTotal_refuted : ¬ SubArrayStrideTotal := by
  intro h
  let view : SubArray (List Axis) Unit :=
    { parent := [{ first := int64 1, last := int64 4 },
        { first := int64 1, last := int64 5 }]
      indices := [.scalar (int64 1), .scalar (int64 2)]
      offset1 := int64 0
      stride1 := int64 0
      linear := false
      dimensions := [] }
  have hSupported : SupportedStrideIndices view.indices := by
    simp [view, SupportedStrideIndices, SupportedStrideIndex, Index.isScalar]
  have hAxes : view.dimensions.length = (axesSubArrayModel view).length := by
    simp [view, axesSubArrayModel, axesSubArray, indicesSubDispatch, indicesSubEmpty]
  have hStrides : stridesSubArray view strideCounterexampleOps.strides
      (substridesDispatch strideCounterexampleOps.indexStep strideCounterexampleOps.indexTypeName) =
        .ok [] := by
    simp [stridesSubArray, view, strideCounterexampleOps, substridesDispatch,
      substridesEmpty, List.drop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hTotal := h strideCounterexampleOps view (int64 1)
    hSupported hAxes ⟨[], hStrides, by simp [view]⟩ (by decide)
  obtain ⟨stride, hStride⟩ := hTotal
  have hError : strideSubArrayConfigured strideCounterexampleOps view (int64 1) =
      .error .boundsError := by
    simp [strideSubArrayConfigured, strideSubArray, view, hStrides,
      getListI64OneBased, lastListI64, Bind.bind, Except.bind, Pure.pure,
      Except.pure, Functor.map, Except.map]
  rw [hError] at hStride
  cases hStride

def FastSubArrayWriteReadback : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) (value : R) (index manualIndex : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (setParent : P → I64 → R → Jl P) (getParent : P → I64 → Jl R)
    (parent' : P),
    view.linear = true →
    checkBounds view index = .ok () →
    reindexLinearDispatch view index = manualIndex →
    setParent view.parent (reindexLinearDispatch view index) value = .ok parent' →
    checkBounds {view with parent := parent'} index = .ok () →
    getParent parent' manualIndex = .ok value →
    (∀ other, other ≠ manualIndex →
      getParent parent' other = getParent view.parent other) →
    ∃ updated : SubArray P T,
      setindexFastSubArray view value index checkBounds setParent = .ok updated ∧
      updated.parent = parent' ∧ updated.indices = view.indices ∧
      (∀ other, other ≠ manualIndex →
        getParent updated.parent other = getParent view.parent other) ∧
      getindexFastSubArray updated index checkBounds getParent = .ok value

theorem fastSubArrayWriteReadback_proven : FastSubArrayWriteReadback := by
  intro P T R view value index manualIndex checkBounds setParent getParent parent'
    hLinear hBounds hIndex hSet hBoundsAfter hGet hOther
  refine ⟨{view with parent := parent'}, ?_, rfl, rfl, hOther, ?_⟩
  · simp [setindexFastSubArray, hBounds, hSet,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
  · have address : reindexLinearDispatch (T := T) {view with parent := parent'} index =
        reindexLinearDispatch view index := rfl
    simp [getindexFastSubArray, hBoundsAfter, address, hIndex, hGet,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

def FastVectorSubArrayWriteReadback : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) (value : R) (index manualIndex : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (setParent : P → I64 → R → Jl P) (getParent : P → I64 → Jl R)
    (parent' : P),
    view.linear = true →
    view.dimensions.length = 1 →
    checkBounds view index = .ok () →
    reindexLinearDispatch view index = manualIndex →
    setParent view.parent (reindexLinearDispatch view index) value = .ok parent' →
    checkBounds {view with parent := parent'} index = .ok () →
    getParent parent' manualIndex = .ok value →
    (∀ other, other ≠ manualIndex →
      getParent parent' other = getParent view.parent other) →
    ∃ updated : SubArray P T,
      setindexFastVectorSubArray view value index checkBounds setParent = .ok updated ∧
      updated.parent = parent' ∧ updated.indices = view.indices ∧
      (∀ other, other ≠ manualIndex →
        getParent updated.parent other = getParent view.parent other) ∧
      getindexFastVectorSubArray updated index checkBounds getParent = .ok value

theorem fastVectorSubArrayWriteReadback_proven : FastVectorSubArrayWriteReadback := by
  intro P T R view value index manualIndex checkBounds setParent getParent parent'
    hLinear hRank hBounds hIndex hSet hBoundsAfter hGet hOther
  refine ⟨{view with parent := parent'}, ?_, rfl, rfl, hOther, ?_⟩
  · simp [setindexFastVectorSubArray, hBounds, hSet,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
  · have address : reindexLinearDispatch (T := T) {view with parent := parent'} index =
        reindexLinearDispatch view index := rfl
    simp [getindexFastVectorSubArray, hBoundsAfter, address, hIndex, hGet,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

def SubArraySizeMatchesIndexAxes : Prop :=
  ∀ {P T : Type} (view : SubArray P T) (length : Axis → I64),
    sizeSubArray view axesSubArrayModel length =
      (viewAxesManual view.indices).map length

theorem subArraySizeMatchesIndexAxes_proven : SubArraySizeMatchesIndexAxes := by
  intro P T view length
  unfold sizeSubArray axesSubArrayModel axesSubArray
  rw [indicesSubDispatch_spec]

def FastViewBoundsErrors : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) (value : R) (index : I64)
    (checkBounds : SubArray P T → I64 → Jl Unit)
    (getParent : P → I64 → Jl R) (setParent : P → I64 → R → Jl P)
    (error : JlError),
    checkBounds view index = .error error →
    getindexFastSubArray view index checkBounds getParent = .error error ∧
    getindexFastVectorSubArray view index checkBounds getParent = .error error ∧
    setindexFastSubArray view value index checkBounds setParent = .error error ∧
    setindexFastVectorSubArray view value index checkBounds setParent = .error error

theorem fastViewBoundsErrors_proven : FastViewBoundsErrors := by
  intro P T R view value index checkBounds getParent setParent error hBounds
  simp [getindexFastSubArray, getindexFastVectorSubArray, setindexFastSubArray,
    setindexFastVectorSubArray, hBounds, Bind.bind, Except.bind, Pure.pure,
    Except.pure, Functor.map, Except.map]

def UnaliascopyKeepsCachedLayout : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P)
    (view : SubArray P T) (unaliasParent : P → Jl P)
    (unaliasIndex : Index → Jl Index),
  ∀ parent' indices',
    unaliasParent view.parent = .ok parent' →
    view.indices.mapM unaliasIndex = .ok indices' →
    checkParentIndexMatchWithOps ops parent' indices' = .ok () →
    unaliascopySubArray view unaliasParent unaliasIndex (subarrayInnerConfigured ops) =
      .ok {view with parent := parent', indices := indices'}

theorem unaliascopyKeepsCachedLayout_proven : UnaliascopyKeepsCachedLayout := by
  intro P T ops view unaliasParent unaliasIndex parent' indices' hParent hIndices hCheck
  simp [unaliascopySubArray, subarrayInnerConfigured, subarrayInner,
    hParent, hIndices, hCheck, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Functor.map, Except.map]

def nestedIdentityGetVector : Index → Index → Jl Index
  | .identity _, .slice axis => .ok (.slice axis)
  | .identity _, .scalar value => .ok (.scalar value)
  | _, _ => .error (.methodError "getindex")

def nestedSliceGetMatrix (_ : Index) (_ _ : Index) : Jl Index :=
  .error (.methodError "getindex")

def nestedSliceGetArray (_ : Index) (_ : List Index) : Jl Index :=
  .error (.methodError "getindex")

def nestedSliceToIndices (_ : List Axis) (indices : List Index) : Jl (List Index) :=
  .ok indices

def nestedSliceFirstLinearIndex (_ : SubArray (List Axis) Unit) : Jl I64 :=
  .ok (int64 1)

/-- Colon selection preserves the parent coordinates of an identity-indexed matrix slice. -/
def NestedColonViewCorrect : Prop :=
  ∀ (s1 s2 lo hi c i : I64),
    1 ≤ s1.val → 1 ≤ s2.val → 1 ≤ lo.val → lo.val ≤ hi.val →
    hi.val ≤ s1.val → 1 ≤ c.val → c.val ≤ s2.val →
    lo.val ≤ i.val → i.val ≤ hi.val →
    ∀ (firstLinearIndexView : SubArray (List Axis) Unit → Jl I64)
      (getVector : Index → Index → Jl Index)
      (getMatrix : Index → Index → Index → Jl Index)
      (getArray : Index → List Index → Jl Index)
      (toIndices : List Axis → List Index → Jl (List Index)),
      getVector (.identity { first := lo, last := hi }) (.slice { first := lo, last := hi }) =
        .ok (.slice { first := lo, last := hi }) →
      toIndices [{ first := int64 1, last := s1 }, { first := int64 1, last := s2 }]
        [.slice { first := lo, last := hi }, .scalar c] =
        .ok [.slice { first := lo, last := hi }, .scalar c] →
      ∃ view nested,
        constructSubArrayConfigured strideCounterexampleOps
          [{ first := int64 1, last := s1 }, { first := int64 1, last := s2 }]
          [.identity { first := lo, last := hi }, .scalar c] = .ok view ∧
        unsafeViewSubArrayConfigured strideCounterexampleOps firstLinearIndexView
          getVector getMatrix getArray toIndices view [.slice { first := lo, last := hi}] =
          .ok (.flattened nested) ∧
        reindexLinearDispatch nested i = iadd i (imul s1 (isub c (int64 1)))

theorem int64_self (x : I64) : int64 x.val = x :=
  Subtype.ext (JuliaLean.Proofs.base.int.wrapInt_val x)

private theorem iadd_zero (x : I64) : iadd x (int64 0) = x := by
  rw [← int64_self x, iadd_lit, Int.add_zero]

private theorem imul_zero (x : I64) : imul x (int64 0) = int64 0 := by
  rw [← int64_self x, imul_lit, Int.mul_zero]

private theorem imul_comm (x y : I64) : imul x y = imul y x := by
  rw [← int64_self x, ← int64_self y, imul_lit, imul_lit, Int.mul_comm]

private theorem index_accumulator (f s x a n r : I64) :
    iadd (iadd f (imul (isub x a) s)) (imul (imul s n) r) =
      iadd f (imul s (iadd (isub x a) (imul n r))) := by
  rw [← int64_self f, ← int64_self s, ← int64_self x, ← int64_self a,
    ← int64_self n, ← int64_self r]
  simp only [iadd_lit, imul_lit, isub_lit]
  congr 1
  simp only [Int.mul_add, Int.mul_assoc, Int.add_assoc, Int.mul_comm (x.val - a.val) s.val]

/-- Column-major addressing: each coordinate is weighted by the sizes of earlier axes.
The arithmetic is Julia's machine-Int arithmetic, including wrapping. -/
def columnMajorOffset (first length : Axis → I64) : List Axis → List I64 → I64
  | axis :: axes, coordinate :: coordinates =>
      iadd (isub coordinate (first axis))
        (imul (length axis) (columnMajorOffset first length axes coordinates))
  | _, _ => int64 0

theorem linindexDispatch_spec (first : Index → Jl I64) (axisFirst length : Axis → I64)
    (indices : List Index) :
    ∀ (axes : List Axis) (f stride : I64), axes.length = indices.length →
      computeLinindexDispatch first axisFirst length f stride axes indices =
        (indices.mapM first).map (fun coordinates =>
          iadd f (imul stride (columnMajorOffset axisFirst length axes coordinates))) := by
  induction indices with
  | nil =>
      intro axes f stride _
      simp [computeLinindexDispatch, computeLinindexEmpty, columnMajorOffset,
        imul_zero, iadd_zero, Pure.pure, Except.pure, Functor.map, Except.map]
  | cons index rest ih =>
      intro axes f stride rank
      cases axes with
      | nil => simp at rank
      | cons axis axes =>
          have rankTail : axes.length = rest.length := by simpa using rank
          cases rest with
          | nil =>
              have axesEmpty : axes = [] := List.eq_nil_of_length_eq_zero rankTail
              subst axes
              cases hfirst : first index with
              | error error =>
                  simp [computeLinindexDispatch, computeLinindexLast, List.mapM_cons,
                    hfirst, Bind.bind, Except.bind, Functor.map, Except.map]
              | ok coordinate =>
                  simp [computeLinindexDispatch, computeLinindexLast, List.mapM_cons,
                    hfirst, columnMajorOffset, imul_zero, iadd_zero, imul_comm,
                    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
          | cons next rest =>
              cases hfirst : first index with
              | error error =>
                  simp [computeLinindexDispatch, List.mapM_cons, hfirst,
                    Bind.bind, Except.bind, Functor.map, Except.map]
              | ok coordinate =>
                  simp only [computeLinindexDispatch, hfirst, Bind.bind, Except.bind]
                  rw [ih axes _ _ rankTail]
                  cases hrest : (next :: rest).mapM first with
                  | error error =>
                      simp [List.mapM_cons, hfirst, hrest, Bind.bind, Except.bind,
                        Functor.map, Except.map]
                  | ok coordinates =>
                      simp only [List.mapM_cons, hfirst, hrest, Bind.bind, Except.bind,
                        Pure.pure, Except.pure, Functor.map, Except.map, columnMajorOffset]
                      rw [index_accumulator]

def LinindexContract : Prop :=
  ∀ {P : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index)
    (filled : List Axis) (firstLinear : I64),
    ops.fillToLength (ops.axes parent) {first := int64 1, last := int64 1}
      indices.length = .ok filled →
    filled.length = indices.length →
    ops.firstLinearIndex parent = .ok firstLinear →
    computeLinindexWithOps ops parent indices =
      (indices.mapM ops.indexFirst).map (fun coordinates =>
        iadd firstLinear (imul (int64 1)
          (columnMajorOffset ops.axisFirst ops.axisLength filled coordinates)))

theorem linindexContract_proven : LinindexContract := by
  intro P ops parent indices filled firstLinear padded rank first
  simp only [computeLinindexWithOps, computeLinindex, padded, first,
    Bind.bind, Except.bind]
  exact linindexDispatch_spec ops.indexFirst ops.axisFirst ops.axisLength indices
    filled firstLinear (int64 1) rank

def LinindexStepContract : Prop :=
  ∀ (f stride : I64) (axis : Axis) (axes : List Axis) (index next : Index)
    (rest : List Index) (first : Index → Jl I64) (axisFirst length : Axis → I64),
    axes.length = (next :: rest).length →
    computeLinindexMany (A := Unit) f stride (axis :: axes) index (next :: rest)
      first axisFirst length (computeLinindexDispatch first axisFirst length) =
      ((index :: next :: rest).mapM first).map (fun coordinates =>
        iadd f (imul stride (columnMajorOffset axisFirst length (axis :: axes) coordinates)))

theorem linindexStepContract_proven : LinindexStepContract := by
  intro f stride axis axes index next rest first axisFirst length rank
  have result := linindexDispatch_spec first axisFirst length (index :: next :: rest)
    (axis :: axes) f stride (by simpa using rank)
  simpa only [computeLinindexDispatch, computeLinindexMany, List.drop, Bind.bind, Except.bind] using result

def LinindexLastContract : Prop :=
  ∀ (f stride : I64) (axis : Axis) (index : Index) (first : Index → Jl I64)
    (axisFirst : Axis → I64),
    computeLinindexLast f stride axis index first axisFirst =
      (first index).map (fun coordinate => iadd f (imul stride (isub coordinate (axisFirst axis))))

theorem linindexLastContract_proven : LinindexLastContract := by
  intro f stride axis index first axisFirst
  cases result : first index <;>
    simp [computeLinindexLast, result, imul_comm,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

private def bugParent : List Axis :=
  [{ first := int64 1, last := int64 4 }, { first := int64 1, last := int64 5 }]

private def bugAxis : Axis := { first := int64 2, last := int64 3 }

private def bugInitial : SubArray (List Axis) Unit :=
  ⟨bugParent, [.identity bugAxis, .scalar (int64 2)], int64 4, int64 1, true, [true]⟩

private def bugFlattened : SubArray (List Axis) Unit :=
  ⟨bugParent, [.slice bugAxis, .scalar (int64 2)], int64 5, int64 1, true, [true]⟩

private theorem bug_initial_stride :
    computeStride1WithOps strideCounterexampleOps bugParent
      [.identity bugAxis, .scalar (int64 2)] = .ok (int64 1) := by
  simp [computeStride1WithOps, computeStride1, computeStride1Dispatch, computeStride1Range,
    strideCounterexampleOps, Index.isRange, bugParent, Bind.bind, Except.bind]

private theorem bug_flattened_stride :
    computeStride1WithOps strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] = .ok (int64 1) := by
  simp [computeStride1WithOps, computeStride1, computeStride1Dispatch, computeStride1Slice,
    strideCounterexampleOps, bugParent, Bind.bind, Except.bind]

private theorem bug_linindex (head : Index)
    (first : strideCounterexampleOps.indexFirst head = .ok (int64 2)) :
    computeLinindexWithOps strideCounterexampleOps bugParent
      [head, .scalar (int64 2)] = .ok (int64 6) := by
  simp only [computeLinindexWithOps, computeLinindex]
  change (do
    let filled ← (pure bugParent : Jl (List Axis))
    let initial ← (pure (int64 1) : Jl I64)
    computeLinindexDispatch strideCounterexampleOps.indexFirst
      strideCounterexampleOps.axisFirst strideCounterexampleOps.axisLength
      initial (int64 1) filled [head, .scalar (int64 2)]) = .ok (int64 6)
  simp only [Pure.pure, Except.pure, Bind.bind, Except.bind, bugParent,
    computeLinindexDispatch, first]
  simp [computeLinindexLast, strideCounterexampleOps, bugParent,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem offset_identity_matrix {P : Type} (ops : ParentArrayOps P) (parent : P)
    (axis : Axis) (column stride linear first : I64)
    (notVector : ops.isVector parent = false)
    (lin : computeLinindexWithOps ops parent [.identity axis, .scalar column] = .ok linear)
    (axisFirst : ops.axes1First (.identity axis) = .ok first) :
    computeOffset1WithOps ops parent stride [.identity axis, .scalar column] =
      .ok (isub linear (imul stride first)) := by
  simp [computeOffset1WithOps, computeOffset1, findExtendedDimsDispatch,
    findExtendedIndicesDispatch, computeOffset1Dispatch, notVector, Index.isRange,
    computeOffset1Range, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem offset_slice_matrix {P : Type} (ops : ParentArrayOps P) (parent : P)
    (axis : Axis) (column stride linear first : I64)
    (notVector : ops.isVector parent = false)
    (lin : computeLinindexWithOps ops parent [.slice axis, .scalar column] = .ok linear)
    (axisFirst : axisFirstAt (ops.axes parent) (int64 1) = .ok first) :
    computeOffset1WithOps ops parent stride [.slice axis, .scalar column] =
      .ok (isub linear (imul stride first)) := by
  simp [computeOffset1WithOps, computeOffset1, findExtendedDimsDispatch,
    findExtendedIndicesDispatch, computeOffset1Dispatch, notVector,
    computeOffset1Slice, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem bug_initial_offset :
    computeOffset1WithOps strideCounterexampleOps bugParent (int64 1)
      [.identity bugAxis, .scalar (int64 2)] = .ok (int64 4) := by
  have result := offset_identity_matrix strideCounterexampleOps bugParent bugAxis
    (int64 2) (int64 1) (int64 6) (int64 2) rfl
    (bug_linindex (.identity bugAxis) rfl) rfl
  simpa only [imul_lit, isub_lit, Int.reduceMul, Int.reduceSub] using result

private theorem bug_flattened_offset :
    computeOffset1WithOps strideCounterexampleOps bugParent (int64 1)
      [.slice bugAxis, .scalar (int64 2)] = .ok (int64 5) := by
  have one : (int64 1).val = 1 := by decide
  have first : axisFirstAt (strideCounterexampleOps.axes bugParent) (int64 1) =
      .ok (int64 1) := by simp [axisFirstAt, strideCounterexampleOps, bugParent, one]
  have result := offset_slice_matrix strideCounterexampleOps bugParent bugAxis
    (int64 2) (int64 1) (int64 6) (int64 1) rfl
    (bug_linindex (.slice bugAxis) rfl) first
  simpa only [imul_lit, isub_lit, Int.reduceMul, Int.reduceSub] using result

private theorem bug_initial_layout :
    computeLinearLayoutWithOps strideCounterexampleOps bugParent
      [.identity bugAxis, .scalar (int64 2)] = .ok (int64 4, int64 1) := by
  simp only [computeLinearLayoutWithOps, computeLinearLayout, bug_initial_stride,
    Bind.bind, Except.bind, bug_initial_offset, Pure.pure, Except.pure]

private theorem bug_flattened_layout :
    computeLinearLayoutWithOps strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] = .ok (int64 5, int64 1) := by
  simp only [computeLinearLayoutWithOps, computeLinearLayout, bug_flattened_stride,
    Bind.bind, Except.bind, bug_flattened_offset, Pure.pure, Except.pure]

private theorem bug_initial_construct :
    constructSubArrayConfigured strideCounterexampleOps bugParent
      [.identity bugAxis, .scalar (int64 2)] = .ok bugInitial := by
  simp only [constructSubArrayConfigured, subarrayOuter, viewIndexing, Index.isRange,
    Index.allScalar, Index.isScalar, List.all_cons, List.all_nil, Bool.true_and,
    ite_true, viewIndexingScalarRange, indexStyleCombine, constructSubArrayByStyle,
    subarrayLinear]
  simp only [show strideCounterexampleOps.parentStyle bugParent = .linear from rfl,
    show strideCounterexampleOps.ensureIndexable = id from rfl, id_eq]
  rw [bug_initial_layout]
  simp [subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
    checkParentIndexMatchArray, strideCounterexampleOps, Index.indexAxes,
    bugParent, bugAxis, bugInitial, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem bug_flattened_construct :
    constructSubArrayConfigured strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] = .ok bugFlattened := by
  simp only [constructSubArrayConfigured, subarrayOuter, viewIndexing, Index.allScalar,
    Index.isScalar, List.all_cons, List.all_nil, Bool.true_and, ite_true,
    indexStyleCombine, constructSubArrayByStyle, subarrayLinear]
  simp only [show strideCounterexampleOps.parentStyle bugParent = .linear from rfl,
    show strideCounterexampleOps.ensureIndexable = id from rfl, id_eq]
  rw [bug_flattened_layout]
  simp [subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
    checkParentIndexMatchArray, strideCounterexampleOps, Index.indexAxes,
    bugParent, bugAxis, bugFlattened, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem bug_reindexed :
    unsafeViewSubArrayConfigured strideCounterexampleOps
      nestedSliceFirstLinearIndex nestedIdentityGetVector nestedSliceGetMatrix
      nestedSliceGetArray nestedSliceToIndices bugInitial [.slice bugAxis] =
        .ok (.flattened bugFlattened) := by
  have reindexed : reindexDispatch nestedIdentityGetVector nestedSliceGetMatrix
      nestedSliceGetArray [.identity bugAxis, .scalar (int64 2)] [.slice bugAxis] =
      .ok [.slice bugAxis, .scalar (int64 2)] := by
    simp [reindexDispatch, nestedIdentityGetVector, Index.indexAxes, reindexEmpty,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [unsafeViewSubArrayConfigured, unsafeViewSubArray, maybeReindexConfigured,
    maybeReindex, maybeReindexDispatch, maybeReindexEmpty, bugInitial,
    reindexed, nestedSliceToIndices, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [bug_flattened_construct]

theorem nestedColonViewCorrect_refuted : ¬ NestedColonViewCorrect := by
  intro h
  obtain ⟨view, nested, hView, hNested, hIndex⟩ :=
    h (int64 4) (int64 5) (int64 2) (int64 3) (int64 2) (int64 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      nestedSliceFirstLinearIndex nestedIdentityGetVector nestedSliceGetMatrix
      nestedSliceGetArray nestedSliceToIndices rfl rfl
  have viewEq : bugInitial = view := Except.ok.inj (bug_initial_construct.symm.trans hView)
  subst view
  have nestedEq : bugFlattened = nested :=
    ReindexedView.flattened.inj (Except.ok.inj (bug_reindexed.symm.trans hNested))
  subst nested
  have bad : int64 7 = int64 6 := by
    simpa [reindexLinearDispatch, reindexLinearContiguous, Index.isUnitRange, bugFlattened] using hIndex
  exact (by decide : (int64 7 : I64) ≠ int64 6) bad

def DataidsContainsParentAndIndices : Prop :=
  ∀ {P T D : Type} (view : SubArray P T) (parentIds : P → Jl (List D))
    (indexIds : Index → Jl (List D)) (parentData : List D) (indexData : List (List D)),
    parentIds view.parent = .ok parentData →
    view.indices.mapM indexIds = .ok indexData →
    ∃ ids, dataidsSubArray view parentIds splatmap indexIds = .ok ids ∧
      ∀ id, id ∈ ids ↔ id ∈ parentData ∨ ∃ data ∈ indexData, id ∈ data

theorem dataidsContainsParentAndIndices_proven : DataidsContainsParentAndIndices := by
  intro P T D view parentIds indexIds parentData indexData hp hi
  refine ⟨parentData ++ indexData.flatten, ?_, ?_⟩
  · have hs := splatMapOrder_proven indexIds view.indices
    rw [hi] at hs
    simp [dataidsSubArray, hp, hs, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Functor.map, Except.map]
  · intro id
    simp only [List.mem_append, List.mem_flatten]

def SizeofMachineBytes : Prop :=
  ∀ {P T : Type} (view : SubArray P T) (length : SubArray P T → I64)
    (elementSize : Type → I64) (parentElementSize : P → I64),
    (sizeofSubArray view length elementSize).val =
      wrapInt .i64 ((length view).val * (elementSize T).val) ∧
    (sizeofArraySubArray view length parentElementSize).val =
      wrapInt .i64 ((length view).val * (parentElementSize view.parent).val)

theorem sizeofMachineBytes_proven : SizeofMachineBytes := by
  intro P T view length elementSize parentElementSize
  constructor <;> exact JuliaLean.Proofs.base.int.mulWraps_proven .i64 _ _

def ConstructorRetainsParentAndIndices : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index)
    (offset stride : I64) (linear : Bool) (dimensions : List Bool),
    ops.isArrayRank parent (ops.indexNdims indices).length = true →
    ∃ view : SubArray P T,
      subarrayInnerConfigured ops parent indices offset stride linear dimensions = .ok view ∧
      parentSubArray view = parent ∧ parentindicesSubArray view = indices ∧
      axesSubArrayModel view = viewAxesManual indices ∧
      view.offset1 = offset ∧ view.stride1 = stride ∧
      view.linear = linear ∧ view.dimensions = dimensions

theorem constructorRetainsParentAndIndices_proven : ConstructorRetainsParentAndIndices := by
  intro P T ops parent indices offset stride linear dimensions rank
  refine ⟨⟨parent, indices, offset, stride, linear, dimensions⟩, ?_,
    rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · simp [subarrayInnerConfigured, subarrayInner, checkParentIndexMatchWithOps,
      checkParentIndexMatch, checkParentIndexMatchArray, rank, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
  · exact indicesSubDispatch_spec indices

def ConstructorRejectsWrongRank : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index)
    (offset stride : I64) (linear : Bool) (dimensions : List Bool) (rank : Nat),
    ops.isArrayRank parent (ops.indexNdims indices).length = false →
    ops.ndims parent = .ok rank →
    (subarrayInnerConfigured ops parent indices offset stride linear dimensions : Jl (SubArray P T)) =
      .error (.argumentError
        s!"number of indices ({(ops.indexNdims indices).length}) must match the parent dimensionality ({rank})")

theorem constructorRejectsWrongRank_proven : ConstructorRejectsWrongRank := by
  intro P T ops parent indices offset stride linear dimensions rank mismatch ndims
  simp [subarrayInnerConfigured, subarrayInner, checkParentIndexMatchWithOps,
    checkParentIndexMatch, checkParentIndexMatchMismatch, mismatch, ndims,
    Bind.bind, Except.bind]

def CopyNonScalarSelection : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) (getParent : P → List Index → Jl R)
    (ndims : SubArray P T → Nat) (similar : SubArray P T → Jl R)
    (setEmpty : R → R → Jl Unit),
    ndims view ≠ 0 → copySubArray view getParent ndims similar setEmpty =
      getParent view.parent view.indices

theorem copyNonScalarSelection_proven : CopyNonScalarSelection := by
  intro P T R view getParent ndims similar setEmpty nonzero
  cases result : getParent view.parent view.indices <;>
    simp [copySubArray, result, nonzero, Bind.bind, Except.bind, Pure.pure, Except.pure]

def IsassignedOutsideView : Prop :=
  ∀ {P T : Type} (view : SubArray P T) (coordinates : List I64) (index : I64)
    (checkCartesian : SubArray P T → List I64 → Bool)
    (checkLinear : SubArray P T → I64 → Bool)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (assignedCartesian : P → List Index → Jl Bool) (assignedLinear : P → I64 → Jl Bool),
    checkCartesian view coordinates = false → checkLinear view index = false →
    isassignedSubArray view coordinates checkCartesian
      (reindexDispatch getVector getMatrix getArray) assignedCartesian = .ok false ∧
    isassignedFastSubArray view index checkLinear assignedLinear = .ok false ∧
    isassignedFastVectorSubArray view index checkLinear assignedLinear = .ok false

theorem isassignedOutsideView_proven : IsassignedOutsideView := by
  intro P T view coordinates index checkCartesian checkLinear getVector getMatrix getArray
    assignedCartesian assignedLinear cartesian linear
  simp [isassignedSubArray, isassignedFastSubArray, isassignedFastVectorSubArray,
    cartesian, linear, Pure.pure, Except.pure]

private theorem imul_one_left (x : I64) : imul (int64 1) x = x := by
  rw [← int64_self x, imul_lit, Int.one_mul]

private theorem range_origin (start block : I64) :
    iadd (int64 1) (iadd (isub start (int64 1)) block) = iadd start block := by
  rw [← int64_self start, ← int64_self block]
  simp only [iadd_lit, isub_lit]
  congr 1
  omega

private theorem range_address (start block step index : I64) :
    iadd (isub (iadd start block) step) (imul step index) =
      iadd (iadd start (imul (isub index (int64 1)) step)) block := by
  rw [← int64_self start, ← int64_self block, ← int64_self step, ← int64_self index]
  simp only [iadd_lit, isub_lit, imul_lit]
  congr 1
  rw [Int.sub_mul, Int.one_mul, Int.mul_comm index.val step.val]
  omega

private theorem scalar_indices (coordinates : List I64) :
    findExtendedIndicesDispatch (coordinates.map Index.scalar) = [] := by
  induction coordinates with
  | nil => rfl
  | cons x xs ih => simpa [findExtendedIndicesDispatch] using ih

private theorem scalar_dims (coordinates : List I64) :
    ∀ dimension, findExtendedDimsDispatch dimension (coordinates.map Index.scalar) = [] := by
  induction coordinates with
  | nil => intro dimension; rfl
  | cons x xs ih =>
      intro dimension
      simpa [findExtendedDimsDispatch] using ih (iadd dimension (int64 1))

/-- Addressing a range in the first dimension and fixing the remaining coordinates.
The hypotheses describe the external array and index interfaces, rather than any layout code. -/
def RangeViewAddress : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P)
    (axis : Axis) (axes : List Axis) (columns : List I64)
    (start step count index : I64),
    axes.length = columns.length →
    ops.fillToLength (ops.axes parent) {first := int64 1, last := int64 1}
      (Index.stepRange start step count :: columns.map Index.scalar).length = .ok (axis :: axes) →
    ops.firstLinearIndex parent = .ok (int64 1) →
    ops.axisFirst axis = int64 1 →
    (Index.stepRange start step count :: columns.map Index.scalar).mapM ops.indexFirst =
      .ok (start :: columns) →
    ops.indexStep (.stepRange start step count) = step →
    ops.axes1First (.stepRange start step count) = .ok (int64 1) →
    ops.indexFirst (.stepRange start step count) = .ok start →
    ops.isVector parent = decide (columns = []) →
    ops.isArrayRank parent
      (ops.indexNdims (.stepRange start step count :: columns.map Index.scalar)).length = true →
    ∃ view : SubArray P T,
      subarrayLinear parent (.stepRange start step count :: columns.map Index.scalar) [true]
        (checkParentIndexMatchWithOps ops) (computeLinearLayoutWithOps ops) = .ok view ∧
      reindexLinearDispatch view index =
        iadd (iadd start (imul (isub index (int64 1)) step))
          (imul (ops.axisLength axis)
            (columnMajorOffset ops.axisFirst ops.axisLength axes columns))

theorem rangeViewAddress_proven : RangeViewAddress := by
  intro P T ops parent axis axes columns start step count index rank fill first axisOrigin
    firstCoordinates stepValue rangeAxisFirst rangeFirst vector matched
  let indices := Index.stepRange start step count :: columns.map Index.scalar
  let block := imul (ops.axisLength axis)
    (columnMajorOffset ops.axisFirst ops.axisLength axes columns)
  let origin := iadd start block
  have lin : computeLinindexWithOps ops parent indices = .ok origin := by
    have result := linindexContract_proven ops parent indices (axis :: axes) (int64 1)
      fill (by simpa [indices] using rank) first
    rw [firstCoordinates] at result
    simpa [columnMajorOffset, axisOrigin, imul_one_left, range_origin,
      origin, block, Functor.map, Except.map] using result
  have stride : computeStride1WithOps ops parent indices = .ok step := by
    simp only [computeStride1WithOps, computeStride1]
    rw [fill]
    simp [indices, computeStride1Dispatch, Index.isRange, computeStride1Range,
      stepValue, imul_one_left, Bind.bind, Except.bind]
  have offset : computeOffset1WithOps ops parent step indices = .ok (isub origin step) := by
    simp only [computeOffset1WithOps, computeOffset1, indices, findExtendedDimsDispatch,
      findExtendedIndicesDispatch, scalar_dims, scalar_indices]
    cases columns with
    | nil =>
        have isVector : ops.isVector parent = true := by simpa using vector
        simp [computeOffset1Dispatch, isVector, Index.isRange, computeOffset1VectorRange,
          rangeFirst, rangeAxisFirst, origin, block, columnMajorOffset, imul_zero,
          iadd_zero, imul_comm step (int64 1), imul_one_left,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
    | cons column columns =>
        have notVector : ops.isVector parent = false := by simpa using vector
        simp only [indices, List.map_cons] at lin
        simp [computeOffset1Dispatch, notVector, Index.isRange, computeOffset1Range,
          rangeAxisFirst, lin, imul_comm step (int64 1), imul_one_left,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
  let view : SubArray P T :=
    ⟨parent, indices, isub origin step, step, true, [true]⟩
  refine ⟨view, ?_, ?_⟩
  · simp [subarrayLinear, computeLinearLayoutWithOps, computeLinearLayout, stride, offset,
      subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
      checkParentIndexMatchArray, matched, view, indices,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa only [reindexLinearDispatch, view, indices, Index.isUnitRange, Index.allScalar,
      List.all_cons, Index.isScalar, Bool.false_and, Bool.or_self, Bool.false_eq_true,
      ite_false, reindexLinear] using range_address start block step index

/-- Membership and addressing in the array manual's column-major coordinate system. -/
def coordinatesInAxes : List Axis → List I64 → Prop
  | [], [] => True
  | axis :: axes, coordinate :: coordinates =>
      axis.first.val ≤ coordinate.val ∧ coordinate.val ≤ axis.last.val ∧
        coordinatesInAxes axes coordinates
  | _, _ => False

def axisLengthSpec (axis : Axis) : I64 :=
  int64 (max 0 (axis.last.val - axis.first.val + 1))

def densePosition (axes : List Axis) (coordinates : List I64) : I64 :=
  iadd (int64 1) (columnMajorOffset Axis.first axisLengthSpec axes coordinates)

def linearPosition (axes : List Axis) (coordinates : List I64) : I64 :=
  match axes, coordinates with
  | [_], [coordinate] => coordinate
  | _, _ => densePosition axes coordinates

/-- Each index selects its stored values, independently of SubArray's cached layout. -/
inductive IndexSelection : Index → List I64 → List I64 → Prop
  | scalar (value : I64) : IndexSelection (.scalar value) [] [value]
  | cartesian (coordinates : List I64) : IndexSelection (.cartesian coordinates) [] coordinates
  | slice (axis : Axis) (coordinate : I64) :
      coordinatesInAxes [axis] [coordinate] →
      IndexSelection (.slice axis) [coordinate] [coordinate]
  | identity (axis : Axis) (coordinate : I64) :
      coordinatesInAxes [axis] [coordinate] →
      IndexSelection (.identity axis) [coordinate] [coordinate]
  | unitRange (axis : Axis) (coordinate : I64) :
      coordinatesInAxes (Index.indexAxes (.unitRange axis)) [coordinate] →
      IndexSelection (.unitRange axis) [coordinate]
        [iadd axis.first (isub coordinate (int64 1))]
  | oneTo (length coordinate : I64) :
      1 ≤ coordinate.val → coordinate.val ≤ length.val →
      IndexSelection (.oneTo length) [coordinate] [coordinate]
  | stepRange (first step count coordinate : I64) :
      1 ≤ coordinate.val → coordinate.val ≤ count.val →
      IndexSelection (.stepRange first step count) [coordinate]
        [iadd first (imul (isub coordinate (int64 1)) step)]
  | stepRangeLen (first step count coordinate : I64) :
      1 ≤ coordinate.val → coordinate.val ≤ count.val →
      IndexSelection (.stepRangeLen first step count) [coordinate]
        [iadd first (imul (isub coordinate (int64 1)) step)]
  | ordinalRange (first step count coordinate : I64) :
      1 ≤ coordinate.val → coordinate.val ≤ count.val →
      IndexSelection (.ordinalRange first step count) [coordinate]
        [iadd first (imul (isub coordinate (int64 1)) step)]
  | values (axes : List Axis) (items : List I64) (coordinates : List I64) (value : I64) :
      coordinatesInAxes axes coordinates →
      items[(densePosition axes coordinates).val.toNat - 1]? = some value →
      IndexSelection (.values axes items) coordinates [value]
  | cartesianValues (axes : List Axis) (rank : Nat) (items : List (List I64))
      (coordinates selected : List I64) :
      coordinatesInAxes axes coordinates →
      items[(densePosition axes coordinates).val.toNat - 1]? = some selected →
      selected.length = rank →
      IndexSelection (.cartesianValues axes rank items) coordinates selected
  | mask (bits : List Bool) (coordinate value : I64) :
      1 ≤ coordinate.val →
      ((bits.zipIdx.filter (fun item => item.1)).map
        (fun item => int64 (item.2 + 1)))[coordinate.val.toNat - 1]? = some value →
      IndexSelection (.mask bits) [coordinate] [value]

inductive TupleSelection : List Index → List I64 → List I64 → Prop
  | nil : TupleSelection [] [] []
  | cons {index : Index} {indices : List Index} {coordinates rest selected remaining : List I64} :
      IndexSelection index coordinates selected → TupleSelection indices rest remaining →
      TupleSelection (index :: indices) (coordinates ++ rest) (selected ++ remaining)

def firstIndexSpec : Index → Option I64
  | .scalar value => some value
  | .slice axis | .identity axis | .unitRange axis => some axis.first
  | .oneTo _ => some (int64 1)
  | .stepRange first _ _ | .stepRangeLen first _ _ | .ordinalRange first _ _ => some first
  | .linRange first _ _ => some first
  | _ => none

def indexStepSpec : Index → I64
  | .stepRange _ step _ | .stepRangeLen _ step _ | .ordinalRange _ step _ => step
  | _ => int64 1

/-- The interfaces supplied by other Base files for an IndexLinear parent and normalized indices.
No hypothesis asserts the correctness of SubArray's own layout or reindexing functions. -/
structure FastViewInputs {P : Type} (ops : ParentArrayOps P) (parent : P)
    (indices : List Index) : Prop where
  rank : (ops.axes parent).length = indices.length
  parentLinear : ops.parentStyle parent = .linear
  indexLinear : viewIndexing indices = .linear
  normalized : ops.ensureIndexable indices = indices
  dimensions : ops.indexDimsum indices = List.replicate (viewAxesManual indices).length true
  matched : ops.isArrayRank parent (ops.indexNdims indices).length = true
  filled : ops.fillToLength (ops.axes parent) {first := int64 1, last := int64 1}
    indices.length = .ok (ops.axes parent)
  firstLinear : ops.firstLinearIndex parent =
    .ok (match ops.axes parent with | [axis] => axis.first | _ => int64 1)
  vector : ops.isVector parent = decide ((ops.axes parent).length = 1)
  axisFirst : ∀ axis, ops.axisFirst axis = axis.first
  axisLength : ∀ axis, ops.axisLength axis = iadd (isub axis.last axis.first) (int64 1)
  indexFirst : ∀ index value, firstIndexSpec index = some value → ops.indexFirst index = .ok value
  indexStep : ∀ index, ops.indexStep index = indexStepSpec index
  indexAxis : ∀ index axis, index.indexAxes.head? = some axis →
    ops.axes1First index = .ok axis.first

def ViewAddressCorrect {P T : Type} (ops : ParentArrayOps P) (parent : P)
    (indices : List Index) (view : SubArray P T) : Prop :=
  ∀ coordinates selected,
    TupleSelection indices coordinates selected →
    coordinatesInAxes (viewAxesManual indices) coordinates →
    coordinatesInAxes (ops.axes parent) selected →
    reindexLinearDispatch view (linearPosition (viewAxesManual indices) coordinates) =
      linearPosition (ops.axes parent) selected

def GeneralLinearConstruction : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices →
    ∃ view : SubArray P T,
      subarrayLinear parent indices (List.replicate (viewAxesManual indices).length true)
        (checkParentIndexMatchWithOps ops) (computeLinearLayoutWithOps ops) = .ok view ∧
      view.parent = parent ∧ view.indices = indices ∧ view.linear = true ∧
      view.dimensions = List.replicate (viewAxesManual indices).length true ∧
      ViewAddressCorrect ops parent indices view

private theorem bug_fast_inputs :
    FastViewInputs strideCounterexampleOps bugParent [.slice bugAxis, .scalar (int64 2)] := by
  constructor
  · rfl
  · rfl
  · simp [viewIndexing, Index.allScalar, Index.isScalar]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro axis; rfl
  · intro axis; rfl
  · intro index value first
    cases index <;> simp [firstIndexSpec] at first <;>
      subst value <;> rfl
  · intro index
    cases index <;> rfl
  · intro index axis first
    change (match index.indexAxes with
      | a :: _ => Except.ok a.first
      | [] => Except.error JlError.boundsError) = .ok axis.first
    cases axes : index.indexAxes with
    | nil => simp [axes] at first
    | cons a rest =>
        have eq : a = axis := by simpa [axes] using first
        subst a
        rfl

private theorem bug_selected :
    TupleSelection [.slice bugAxis, .scalar (int64 2)] [int64 2] [int64 2, int64 2] := by
  exact TupleSelection.cons (IndexSelection.slice bugAxis (int64 2)
      (by simp only [coordinatesInAxes, bugAxis]; decide))
    (TupleSelection.cons (IndexSelection.scalar (int64 2)) TupleSelection.nil)

private theorem bug_addresses_disagree : ¬ ViewAddressCorrect strideCounterexampleOps
    bugParent [.slice bugAxis, .scalar (int64 2)] bugFlattened := by
  intro correct
  have bad := correct [int64 2] [int64 2, int64 2] bug_selected
    (by simp only [viewAxesManual, List.flatMap_cons, List.flatMap_nil, Index.indexAxes,
          List.nil_append, List.append_nil, coordinatesInAxes, bugAxis]; decide)
    (by simp only [strideCounterexampleOps, bugParent, id_eq, coordinatesInAxes]; decide)
  have axisLength : axisLengthSpec {first := int64 1, last := int64 4} = int64 4 := by
    apply Subtype.ext
    decide
  have six : linearPosition (strideCounterexampleOps.axes bugParent)
      [int64 2, int64 2] = int64 6 := by
    simp [linearPosition, densePosition, columnMajorOffset, strideCounterexampleOps,
      bugParent, axisLengthSpec] <;> decide
  have seven : reindexLinearDispatch bugFlattened
      (linearPosition (viewAxesManual [.slice bugAxis, .scalar (int64 2)]) [int64 2]) =
      int64 7 := by
    simp [reindexLinearDispatch, reindexLinearContiguous, Index.isUnitRange,
      linearPosition, viewAxesManual, Index.indexAxes, bugFlattened]
  rw [seven, six] at bad
  exact (by decide : (int64 7 : I64) ≠ int64 6) bad

private theorem bug_sublinear :
    subarrayLinear bugParent [.slice bugAxis, .scalar (int64 2)] [true]
      (checkParentIndexMatchWithOps strideCounterexampleOps)
      (computeLinearLayoutWithOps strideCounterexampleOps) = .ok bugFlattened := by
  unfold subarrayLinear
  rw [bug_flattened_layout]
  simp [subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
    checkParentIndexMatchArray, strideCounterexampleOps, bugParent, bugFlattened,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem generalLinearConstruction_refuted : ¬ GeneralLinearConstruction := by
  intro correct
  obtain ⟨view, constructed, _, _, _, _, addresses⟩ :=
    correct strideCounterexampleOps bugParent [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs
  have eq : bugFlattened = view := Except.ok.inj (bug_sublinear.symm.trans constructed)
  subst view
  exact bug_addresses_disagree addresses

private theorem bug_view_position :
    linearPosition (viewAxesManual [.slice bugAxis, .scalar (int64 2)]) [int64 2] =
      int64 2 := rfl

private theorem bug_parent_position :
    linearPosition (strideCounterexampleOps.axes bugParent) [int64 2, int64 2] =
      int64 6 := by
  simp [linearPosition, densePosition, columnMajorOffset, strideCounterexampleOps,
    bugParent, axisLengthSpec] <;> decide

private theorem bug_view_bounds :
    coordinatesInAxes (viewAxesManual [.slice bugAxis, .scalar (int64 2)]) [int64 2] := by
  simp only [viewAxesManual, List.flatMap_cons, List.flatMap_nil, Index.indexAxes,
    List.append_nil, coordinatesInAxes, bugAxis]
  decide

private theorem bug_parent_bounds :
    coordinatesInAxes (strideCounterexampleOps.axes bugParent) [int64 2, int64 2] := by
  simp only [strideCounterexampleOps, bugParent, id_eq, coordinatesInAxes]
  decide

private def readAddressOracle (_ : List Axis) (index : I64) : Jl I64 := .ok index
private def checkedPositionOracle (_ : SubArray (List Axis) Unit) (_ : I64) : Jl Unit := .ok ()

def FastReadContract
    (read : {P T R : Type} → SubArray P T → I64 →
      (SubArray P T → I64 → Jl Unit) → (P → I64 → Jl R) → Jl R)
    (vectorOnly : Bool) : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices →
    (vectorOnly = true → (viewAxesManual indices).length = 1) →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      view.linear = true ∧ view.dimensions.length = (viewAxesManual indices).length ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ (check : SubArray P T → I64 → Jl Unit) (get : P → I64 → Jl R),
          check view (linearPosition (viewAxesManual indices) coordinates) = .ok () →
          read view (linearPosition (viewAxesManual indices) coordinates) check get =
            get parent (linearPosition (ops.axes parent) selected)

def GeneralFastRead : Prop := FastReadContract (@getindexFastSubArray) false ∧ FastViewBoundsErrors
def GeneralFastVectorRead : Prop := FastReadContract (@getindexFastVectorSubArray) true ∧ FastViewBoundsErrors

theorem generalFastRead_refuted : ¬ GeneralFastRead := by
  intro correct
  obtain ⟨view, constructed, _, _, reads⟩ :=
    correct.1 (R := I64) strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs (by intro impossible; cases impossible)
  have eq : bugFlattened = view := Except.ok.inj (bug_flattened_construct.symm.trans constructed)
  subst view
  have bad := reads [int64 2] [int64 2, int64 2] bug_selected bug_view_bounds bug_parent_bounds
    checkedPositionOracle readAddressOracle rfl
  rw [bug_view_position, bug_parent_position] at bad
  have impossible : (int64 7 : I64) = int64 6 := by
    apply (Except.ok.inj (ε := JlError))
    simpa [getindexFastSubArray, checkedPositionOracle, readAddressOracle, reindexLinearDispatch,
      reindexLinearContiguous, bugFlattened, Index.isUnitRange,
      Bind.bind, Except.bind] using bad
  exact (by decide : (int64 7 : I64) ≠ int64 6) impossible

theorem generalFastVectorRead_refuted : ¬ GeneralFastVectorRead := by
  intro correct
  obtain ⟨view, constructed, _, _, reads⟩ :=
    correct.1 (R := I64) strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs (by intro _; rfl)
  have eq : bugFlattened = view := Except.ok.inj (bug_flattened_construct.symm.trans constructed)
  subst view
  have bad := reads [int64 2] [int64 2, int64 2] bug_selected bug_view_bounds bug_parent_bounds
    checkedPositionOracle readAddressOracle rfl
  rw [bug_view_position, bug_parent_position] at bad
  have impossible : (int64 7 : I64) = int64 6 := by
    apply (Except.ok.inj (ε := JlError))
    simpa [getindexFastVectorSubArray, checkedPositionOracle, readAddressOracle, reindexLinearDispatch,
      reindexLinearContiguous, bugFlattened, Index.isUnitRange,
      Bind.bind, Except.bind] using bad
  exact (by decide : (int64 7 : I64) ≠ int64 6) impossible

def GeneralFastVectorAssignedInBounds : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices → (viewAxesManual indices).length = 1 →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ (check : SubArray P T → I64 → Bool) (assigned : P → I64 → Jl Bool),
          check view (linearPosition (viewAxesManual indices) coordinates) = true →
          isassignedFastVectorSubArray view (linearPosition (viewAxesManual indices) coordinates)
            check assigned = assigned parent (linearPosition (ops.axes parent) selected)

def GeneralFastVectorAssigned : Prop := GeneralFastVectorAssignedInBounds ∧ IsassignedOutsideView

private def assignedAddressOracle (_ : List Axis) (index : I64) : Jl Bool :=
  .ok (decide (index.val = 7))

theorem generalFastVectorAssigned_refuted : ¬ GeneralFastVectorAssigned := by
  intro correct
  obtain ⟨view, constructed, assigned⟩ :=
    correct.1 strideCounterexampleOps bugParent [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs rfl
  have eq : bugFlattened = view := Except.ok.inj (bug_flattened_construct.symm.trans constructed)
  subst view
  have bad := assigned [int64 2] [int64 2, int64 2] bug_selected bug_view_bounds bug_parent_bounds
    (fun _ _ => true) assignedAddressOracle rfl
  rw [bug_view_position, bug_parent_position] at bad
  have address : reindexLinearDispatch bugFlattened (int64 2) = int64 7 := by
    simp [reindexLinearDispatch, reindexLinearContiguous, bugFlattened, Index.isUnitRange]
  have values : assignedAddressOracle bugParent (int64 7) = .ok true ∧
      assignedAddressOracle bugParent (int64 6) = .ok false := by
    constructor <;> simp [assignedAddressOracle] <;> decide
  simp only [isassignedFastVectorSubArray, Bool.not_true, Bool.false_eq_true, ite_false,
    address, values.1, values.2] at bad
  cases bad

def GeneralOffsetCorrect : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices →
    ∃ stride offset,
      computeStride1WithOps ops parent indices = .ok stride ∧
      computeOffset1WithOps ops parent stride indices = .ok offset ∧
      ViewAddressCorrect ops parent indices
        (⟨parent, indices, offset, stride, true,
          List.replicate (viewAxesManual indices).length true⟩ : SubArray P T)

theorem generalOffsetCorrect_refuted : ¬ GeneralOffsetCorrect := by
  intro correct
  obtain ⟨stride, offset, computedStride, computedOffset, addresses⟩ :=
    correct (T := Unit) strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs
  have strideEq : int64 1 = stride :=
    Except.ok.inj (bug_flattened_stride.symm.trans computedStride)
  subst stride
  have offsetEq : int64 5 = offset :=
    Except.ok.inj (bug_flattened_offset.symm.trans computedOffset)
  subst offset
  exact bug_addresses_disagree addresses

def GeneralContiguousPointer : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices →
    (match indices with | [] => true | index :: _ => index.isUnitRange || Index.allScalar indices) = true →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ pointer : P → I64 → Jl R,
          pointerFastContiguousSubArray view (linearPosition (viewAxesManual indices) coordinates) pointer =
            pointer parent (linearPosition (ops.axes parent) selected)

theorem generalContiguousPointer_refuted : ¬ GeneralContiguousPointer := by
  intro correct
  obtain ⟨view, constructed, pointers⟩ :=
    correct (R := I64) strideCounterexampleOps bugParent
      [.slice bugAxis, .scalar (int64 2)] bug_fast_inputs rfl
  have eq : bugFlattened = view := Except.ok.inj (bug_flattened_construct.symm.trans constructed)
  subst view
  have bad := pointers [int64 2] [int64 2, int64 2] bug_selected
    bug_view_bounds bug_parent_bounds readAddressOracle
  rw [bug_view_position, bug_parent_position] at bad
  have impossible : (int64 7 : I64) = int64 6 := by
    apply (Except.ok.inj (ε := JlError))
    simpa [pointerFastContiguousSubArray, reindexLinearContiguous, bugFlattened,
      readAddressOracle] using bad
  exact (by decide : (int64 7 : I64) ≠ int64 6) impossible

def GeneralFastVectorWriteInBounds : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices → (viewAxesManual indices).length = 1 →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ (value : R) (check : SubArray P T → I64 → Jl Unit) (set : P → I64 → R → Jl P),
          check view (linearPosition (viewAxesManual indices) coordinates) = .ok () →
          setindexFastVectorSubArray view value
            (linearPosition (viewAxesManual indices) coordinates) check set =
            (set parent (linearPosition (ops.axes parent) selected) value).map
              (fun parent' => {view with parent := parent'})

def GeneralFastVectorWrite : Prop := GeneralFastVectorWriteInBounds ∧ FastViewBoundsErrors

private abbrev WriteParent := List Axis × List I64

private def writeProbeParent : WriteParent := (bugParent, List.replicate 20 (int64 0))

private def writeProbeOps : ParentArrayOps WriteParent where
  parentStyle := fun parent => strideCounterexampleOps.parentStyle parent.1
  isArrayRank := fun parent rank => strideCounterexampleOps.isArrayRank parent.1 rank
  ndims := fun parent => strideCounterexampleOps.ndims parent.1
  indexNdims := strideCounterexampleOps.indexNdims
  indexDimsum := strideCounterexampleOps.indexDimsum
  ensureIndexable := strideCounterexampleOps.ensureIndexable
  axes := Prod.fst
  strides := fun parent => strideCounterexampleOps.strides parent.1
  fillToLength := strideCounterexampleOps.fillToLength
  firstLinearIndex := fun parent => strideCounterexampleOps.firstLinearIndex parent.1
  axisFirst := strideCounterexampleOps.axisFirst
  axisLength := strideCounterexampleOps.axisLength
  indexFirst := strideCounterexampleOps.indexFirst
  indexStep := strideCounterexampleOps.indexStep
  indexTypeName := strideCounterexampleOps.indexTypeName
  axes1First := strideCounterexampleOps.axes1First
  isVector := fun parent => strideCounterexampleOps.isVector parent.1

private theorem write_probe_inputs :
    FastViewInputs writeProbeOps writeProbeParent [.slice bugAxis, .scalar (int64 2)] :=
  { rank := bug_fast_inputs.rank
    parentLinear := bug_fast_inputs.parentLinear
    indexLinear := bug_fast_inputs.indexLinear
    normalized := bug_fast_inputs.normalized
    dimensions := bug_fast_inputs.dimensions
    matched := bug_fast_inputs.matched
    filled := bug_fast_inputs.filled
    firstLinear := bug_fast_inputs.firstLinear
    vector := bug_fast_inputs.vector
    axisFirst := bug_fast_inputs.axisFirst
    axisLength := bug_fast_inputs.axisLength
    indexFirst := bug_fast_inputs.indexFirst
    indexStep := bug_fast_inputs.indexStep
    indexAxis := bug_fast_inputs.indexAxis }

private def writeProbeView : SubArray WriteParent Unit :=
  ⟨writeProbeParent, [.slice bugAxis, .scalar (int64 2)], int64 5, int64 1, true, [true]⟩

private theorem write_probe_layout :
    computeLinearLayoutWithOps writeProbeOps writeProbeParent
      [.slice bugAxis, .scalar (int64 2)] = .ok (int64 5, int64 1) := by
  change computeLinearLayoutWithOps strideCounterexampleOps bugParent
    [.slice bugAxis, .scalar (int64 2)] = .ok (int64 5, int64 1)
  exact bug_flattened_layout

private theorem write_probe_constructed :
    constructSubArrayConfigured writeProbeOps writeProbeParent
      [.slice bugAxis, .scalar (int64 2)] = .ok writeProbeView := by
  simp only [constructSubArrayConfigured, subarrayOuter, viewIndexing, Index.allScalar,
    Index.isScalar, List.all_cons, List.all_nil, Bool.true_and, ite_true,
    indexStyleCombine, constructSubArrayByStyle, subarrayLinear]
  simp only [show writeProbeOps.parentStyle writeProbeParent = .linear from rfl,
    show writeProbeOps.ensureIndexable = id from rfl, id_eq]
  rw [write_probe_layout]
  simp [subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
    checkParentIndexMatchArray, writeProbeOps, strideCounterexampleOps, Index.indexAxes,
    writeProbeParent, writeProbeView, bugParent, Bind.bind, Except.bind, Pure.pure, Except.pure]

private def writeParentSet (parent : WriteParent) (index value : I64) : Jl WriteParent :=
  if 1 ≤ index.val ∧ index.val ≤ parent.2.length then
    .ok (parent.1, parent.2.set (index.val.toNat - 1) value)
  else .error .boundsError

theorem generalFastVectorWrite_refuted : ¬ GeneralFastVectorWrite := by
  intro correct
  obtain ⟨view, constructed, writes⟩ :=
    correct.1 (R := I64) writeProbeOps writeProbeParent
      [.slice bugAxis, .scalar (int64 2)] write_probe_inputs rfl
  have eq : writeProbeView = view := Except.ok.inj (write_probe_constructed.symm.trans constructed)
  subst view
  have bad := writes [int64 2] [int64 2, int64 2] bug_selected bug_view_bounds bug_parent_bounds
    (int64 1) (fun _ _ => .ok ()) writeParentSet rfl
  rw [bug_view_position] at bad
  change setindexFastVectorSubArray writeProbeView (int64 1) (int64 2)
      (fun _ _ => .ok ()) writeParentSet =
    (writeParentSet writeProbeParent (int64 6) (int64 1)).map
      (fun parent' => {writeProbeView with parent := parent'}) at bad
  have observed := congrArg
    (Except.map (fun view : SubArray WriteParent Unit => view.parent.2[5]?)) bad
  have six : (int64 6).val = 6 := by decide
  have seven : (int64 7).val = 7 := by decide
  have different : (Except.ok (some (int64 0)) : Jl (Option I64)) ≠ .ok (some (int64 1)) := by
    intro equality
    exact (by decide : (some (int64 0) : Option I64) ≠ some (int64 1)) (Except.ok.inj equality)
  apply different
  simpa [setindexFastVectorSubArray, reindexLinearDispatch, reindexLinearContiguous,
    Index.isUnitRange, writeProbeView, writeProbeParent,
    writeParentSet, six, seven, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Functor.map, Except.map, List.set, List.replicate] using observed

private def bugStridedView : SubArray (List Axis) Unit :=
  ⟨bugParent, [.scalar (int64 1), .slice bugAxis], int64 1, int64 4, true, [true]⟩

private theorem strided_fast_inputs :
    FastViewInputs strideCounterexampleOps bugParent [.scalar (int64 1), .slice bugAxis] := by
  constructor
  · rfl
  · rfl
  · simp [viewIndexing, Index.allScalar, Index.isScalar]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bug_fast_inputs.axisFirst
  · exact bug_fast_inputs.axisLength
  · exact bug_fast_inputs.indexFirst
  · exact bug_fast_inputs.indexStep
  · exact bug_fast_inputs.indexAxis

private theorem strided_stride :
    computeStride1WithOps strideCounterexampleOps bugParent
      [.scalar (int64 1), .slice bugAxis] = .ok (int64 4) := by
  simp [computeStride1WithOps, computeStride1, computeStride1Dispatch, computeStride1Slice,
    strideCounterexampleOps, bugParent, Index.isScalar, Bind.bind, Except.bind]

private theorem strided_linindex :
    computeLinindexWithOps strideCounterexampleOps bugParent
      [.scalar (int64 1), .slice bugAxis] = .ok (int64 5) := by
  have firstCoordinates :
      [.scalar (int64 1), .slice bugAxis].mapM strideCounterexampleOps.indexFirst =
        .ok [int64 1, int64 2] := by
    simp [List.mapM_cons, strideCounterexampleOps, bugAxis,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have result := linindexContract_proven strideCounterexampleOps bugParent
    [.scalar (int64 1), .slice bugAxis] bugParent (int64 1) rfl rfl rfl
  rw [firstCoordinates] at result
  simpa [columnMajorOffset, strideCounterexampleOps, bugParent, Functor.map, Except.map] using result

private theorem offset_second_slice_matrix {P : Type} (ops : ParentArrayOps P) (parent : P)
    (axis : Axis) (fixed stride linear first : I64)
    (notVector : ops.isVector parent = false)
    (lin : computeLinindexWithOps ops parent [.scalar fixed, .slice axis] = .ok linear)
    (axisFirst : axisFirstAt (ops.axes parent) (int64 2) = .ok first) :
    computeOffset1WithOps ops parent stride [.scalar fixed, .slice axis] =
      .ok (isub linear (imul stride first)) := by
  simp [computeOffset1WithOps, computeOffset1, findExtendedDimsDispatch,
    findExtendedIndicesDispatch, computeOffset1Dispatch, notVector,
    computeOffset1Slice, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem strided_offset :
    computeOffset1WithOps strideCounterexampleOps bugParent (int64 4)
      [.scalar (int64 1), .slice bugAxis] = .ok (int64 1) := by
  have two : (int64 2).val = 2 := by decide
  have first : axisFirstAt (strideCounterexampleOps.axes bugParent) (int64 2) =
      .ok (int64 1) := by simp [axisFirstAt, strideCounterexampleOps, bugParent, two]
  have result := offset_second_slice_matrix strideCounterexampleOps bugParent bugAxis
    (int64 1) (int64 4) (int64 5) (int64 1) rfl strided_linindex first
  simpa only [imul_lit, isub_lit, Int.reduceMul, Int.reduceSub] using result

private theorem strided_layout :
    computeLinearLayoutWithOps strideCounterexampleOps bugParent
      [.scalar (int64 1), .slice bugAxis] = .ok (int64 1, int64 4) := by
  simp only [computeLinearLayoutWithOps, computeLinearLayout, strided_stride,
    Bind.bind, Except.bind, strided_offset, Pure.pure, Except.pure]

private theorem strided_constructed :
    constructSubArrayConfigured strideCounterexampleOps bugParent
      [.scalar (int64 1), .slice bugAxis] = .ok bugStridedView := by
  simp only [constructSubArrayConfigured, subarrayOuter, viewIndexing, Index.allScalar,
    Index.isScalar, List.all_cons, List.all_nil, Bool.true_and, ite_true,
    indexStyleCombine, constructSubArrayByStyle, subarrayLinear]
  simp only [show strideCounterexampleOps.parentStyle bugParent = .linear from rfl,
    show strideCounterexampleOps.ensureIndexable = id from rfl, id_eq]
  rw [strided_layout]
  simp [subarrayInner, checkParentIndexMatchWithOps, checkParentIndexMatch,
    checkParentIndexMatchArray, strideCounterexampleOps, Index.indexAxes,
    bugParent, bugStridedView, Bind.bind, Except.bind, Pure.pure, Except.pure]

def GeneralFastPointer : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    FastViewInputs ops parent indices →
    (match indices with | [] => true | index :: _ => index.isUnitRange || Index.allScalar indices) = false →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ pointer : P → I64 → Jl R,
          pointerFastSubArray view (linearPosition (viewAxesManual indices) coordinates) pointer =
            pointer parent (linearPosition (ops.axes parent) selected)

theorem generalFastPointer_refuted : ¬ GeneralFastPointer := by
  intro correct
  obtain ⟨view, constructed, pointers⟩ :=
    correct (R := I64) strideCounterexampleOps bugParent
      [.scalar (int64 1), .slice bugAxis] strided_fast_inputs rfl
  have eq : bugStridedView = view := Except.ok.inj (strided_constructed.symm.trans constructed)
  subst view
  have selected :
      TupleSelection [.scalar (int64 1), .slice bugAxis] [int64 2] [int64 1, int64 2] :=
    TupleSelection.cons (IndexSelection.scalar (int64 1))
      (TupleSelection.cons (IndexSelection.slice bugAxis (int64 2)
        (by simp only [coordinatesInAxes, bugAxis]; decide)) TupleSelection.nil)
  have bounds : coordinatesInAxes
      (viewAxesManual [.scalar (int64 1), .slice bugAxis]) [int64 2] := by
    simpa [viewAxesManual, Index.indexAxes] using bug_view_bounds
  have parentBounds : coordinatesInAxes (strideCounterexampleOps.axes bugParent)
      [int64 1, int64 2] := by
    simp only [strideCounterexampleOps, bugParent, id_eq, coordinatesInAxes]
    decide
  have bad := pointers [int64 2] [int64 1, int64 2] selected bounds parentBounds readAddressOracle
  have parentPosition : linearPosition (strideCounterexampleOps.axes bugParent)
      [int64 1, int64 2] = int64 5 := by
    simp [linearPosition, densePosition, columnMajorOffset, strideCounterexampleOps,
      bugParent, axisLengthSpec] <;> decide
  have viewPosition :
      linearPosition (viewAxesManual [.scalar (int64 1), .slice bugAxis]) [int64 2] =
        int64 2 := rfl
  rw [parentPosition, viewPosition] at bad
  have impossible : (int64 9 : I64) = int64 5 := by
    apply (Except.ok.inj (ε := JlError))
    simpa [pointerFastSubArray, reindexLinear, bugStridedView, readAddressOracle] using bad
  exact (by decide : (int64 9 : I64) ≠ int64 5) impossible

theorem coordinatesInAxes_length {axes : List Axis} {coordinates : List I64}
    (valid : coordinatesInAxes axes coordinates) : coordinates.length = axes.length := by
  induction axes generalizing coordinates with
  | nil => cases coordinates <;> simp_all [coordinatesInAxes]
  | cons axis axes ih =>
      cases coordinates with
      | nil => cases valid
      | cons coordinate coordinates =>
          have rest := ih valid.2.2
          simp [rest]

theorem IndexSelection.axesLength {index : Index} {coordinates selected : List I64}
    (selection : IndexSelection index coordinates selected) :
    coordinates.length = index.indexAxes.length := by
  cases selection <;> simp only [Index.indexAxes, List.length_cons, List.length_nil] <;>
    first | rfl | exact coordinatesInAxes_length (by assumption)

inductive IndexResultCoordinates : Index → List I64 → Prop
  | scalar (value : I64) : IndexResultCoordinates (.scalar value) [value]
  | cartesian (coordinates : List I64) : IndexResultCoordinates (.cartesian coordinates) coordinates

/-- Normalization of integer and CartesianIndex argument tuples in other Base files. -/
structure CoordinateNormalization (normalize : List Index → Jl (List I64)) : Prop where
  empty : normalize [] = .ok []
  scalar : ∀ value, normalize [.scalar value] = .ok [value]
  cartesian : ∀ coordinates, normalize [.cartesian coordinates] = .ok coordinates
  append : ∀ left right, normalize (left ++ right) = do
    let a ← normalize left
    let b ← normalize right
    pure (a ++ b)

/-- Dispatch of an index array's `getindex` at scalar coordinates, supplied by other files. -/
def indexElementRead (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (index : Index) : List I64 → Jl Index
  | [coordinate] => getVector index (.scalar coordinate)
  | [first, second] => getMatrix index (.scalar first) (.scalar second)
  | coordinates => getArray index (coordinates.map Index.scalar)

def IndexElementReadLaw (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) : Prop :=
  ∀ index coordinates selected, IndexSelection index coordinates selected →
    StoredIndex index → index.isScalar = false → (∀ axis, index ≠ .slice axis) →
    ∃ value, indexElementRead getVector getMatrix getArray index coordinates = .ok value ∧
      IndexResultCoordinates value selected

private theorem normalize_result_cons (normalize : List Index → Jl (List I64))
    (laws : CoordinateNormalization normalize) {result : Index} {selected : List I64}
    (head : IndexResultCoordinates result selected) (rest : List Index) (remaining : List I64)
    (tail : normalize rest = .ok remaining) :
    normalize (result :: rest) = .ok (selected ++ remaining) := by
  have appended := laws.append [result] rest
  cases head with
  | scalar value =>
      simpa only [List.singleton_append, laws.scalar, tail,
        Bind.bind, Except.bind, Pure.pure, Except.pure] using appended
  | cartesian coordinates =>
      simpa only [List.singleton_append, laws.cartesian, tail,
        Bind.bind, Except.bind, Pure.pure, Except.pure] using appended

private theorem reindex_array_dispatch (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (index : Index)
    (indices : List Index) (arguments : List Index)
    (notScalar : index.isScalar = false) (notSlice : ∀ axis, index ≠ .slice axis)
    (stored : StoredIndex index) :
    reindexDispatch getVector getMatrix getArray (index :: indices) arguments =
      (match index.indexAxes.length with
      | 1 => match arguments with
        | [] => .error .boundsError
        | argument :: arguments => do
            let value ← getVector index argument
            let rest ← reindexDispatch getVector getMatrix getArray indices arguments
            pure (value :: rest)
      | 2 => match arguments with
        | first :: second :: arguments => do
            let value ← getMatrix index first second
            let rest ← reindexDispatch getVector getMatrix getArray indices arguments
            pure (value :: rest)
        | _ => .error .boundsError
      | rank => do
          let value ← getArray index (arguments.take rank)
          let rest ← reindexDispatch getVector getMatrix getArray indices (arguments.drop rank)
          pure (value :: rest)) := by
  cases index <;> simp_all [reindexDispatch, Index.isScalar, StoredIndex, Index.indexAxes,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] <;> rfl

private theorem reindex_array_block (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (index : Index)
    (indices : List Index) (coordinates : List I64) (arguments : List Index)
    (notScalar : index.isScalar = false) (notSlice : ∀ axis, index ≠ .slice axis)
    (stored : StoredIndex index) (rank : coordinates.length = index.indexAxes.length) :
    reindexDispatch getVector getMatrix getArray (index :: indices)
        (coordinates.map Index.scalar ++ arguments) = (do
      let value ← indexElementRead getVector getMatrix getArray index coordinates
      let rest ← reindexDispatch getVector getMatrix getArray indices arguments
      pure (value :: rest)) := by
  rw [reindex_array_dispatch getVector getMatrix getArray index indices _ notScalar notSlice stored,
    ← rank]
  have taken : (coordinates.map Index.scalar ++ arguments).take coordinates.length =
      coordinates.map Index.scalar := by
    simpa only [List.length_map] using
      (List.take_left (l₁ := coordinates.map Index.scalar) (l₂ := arguments))
  have dropped : (coordinates.map Index.scalar ++ arguments).drop coordinates.length = arguments := by
    simpa only [List.length_map] using
      (List.drop_left (l₁ := coordinates.map Index.scalar) (l₂ := arguments))
  cases coordinates with
  | nil => simp [indexElementRead]
  | cons first rest =>
      cases rest with
      | nil => simp [indexElementRead]
      | cons second rest =>
          cases rest with
          | nil => simp [indexElementRead]
          | cons third rest =>
              simp only [List.length_cons, List.map_cons, List.cons_append,
                indexElementRead] at taken dropped ⊢
              rw [taken, dropped]

private theorem reindex_point_array (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (normalize : List Index → Jl (List I64)) (normalization : CoordinateNormalization normalize)
    (getters : IndexElementReadLaw getVector getMatrix getArray)
    (index : Index) (indices : List Index) (coordinates rest selected remaining : List I64)
    (selection : IndexSelection index coordinates selected)
    (notScalar : index.isScalar = false) (notSlice : ∀ axis, index ≠ .slice axis)
    (stored : StoredIndex index) (arguments : List Index)
    (tail : reindexDispatch getVector getMatrix getArray indices (rest.map Index.scalar) = .ok arguments)
    (normalizedTail : normalize arguments = .ok remaining) :
    ∃ result,
      reindexDispatch getVector getMatrix getArray (index :: indices)
        (coordinates.map Index.scalar ++ rest.map Index.scalar) = .ok result ∧
      normalize result = .ok (selected ++ remaining) := by
  obtain ⟨value, read, decoded⟩ := getters index coordinates selected selection stored notScalar notSlice
  refine ⟨value :: arguments, ?_, normalize_result_cons normalize normalization decoded
    arguments remaining normalizedTail⟩
  rw [reindex_array_block getVector getMatrix getArray index indices coordinates
    (rest.map Index.scalar) notScalar notSlice stored selection.axesLength]
  simp only [read, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem reindexPoint_spec (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (normalize : List Index → Jl (List I64)) (normalization : CoordinateNormalization normalize)
    (getters : IndexElementReadLaw getVector getMatrix getArray)
    {indices : List Index} {coordinates selected : List I64}
    (selection : TupleSelection indices coordinates selected) (stored : StoredIndices indices) :
    ∃ arguments, reindexDispatch getVector getMatrix getArray indices
        (coordinates.map Index.scalar) = .ok arguments ∧ normalize arguments = .ok selected := by
  revert stored
  induction selection with
  | nil => intro _; exact ⟨[], rfl, normalization.empty⟩
  | @cons index indices coordinates rest selected remaining head tail ih =>
      intro stored
      obtain ⟨arguments, indexed, normalized⟩ := ih stored.2
      cases index
      case scalar value =>
        cases head
        refine ⟨.scalar value :: arguments, ?_,
          normalize_result_cons normalize normalization (.scalar value) arguments remaining normalized⟩
        simp [reindexDispatch, indexed, Bind.bind, Except.bind, Pure.pure, Except.pure]
      case slice axis =>
        cases head
        rename_i coordinate valid
        refine ⟨.scalar coordinate :: arguments, ?_,
          normalize_result_cons normalize normalization (.scalar coordinate) arguments remaining normalized⟩
        simp [reindexDispatch, indexed, Bind.bind, Except.bind, Pure.pure, Except.pure]
      case colon => cases head
      case other => cases head
      case cartesian coordinates => exact False.elim stored.1
      case linRange first last count => cases head
      all_goals
        simpa only [List.map_append] using
          (reindex_point_array getVector getMatrix getArray normalize normalization getters
            _ indices coordinates rest selected remaining head rfl
            (by intro axis equality; cases equality) trivial arguments indexed normalized)

def IndicesWithinAxes (axes : List Axis) (indices : List Index) : Prop :=
  ∀ coordinates selected, TupleSelection indices coordinates selected →
    coordinatesInAxes (viewAxesManual indices) coordinates → coordinatesInAxes axes selected

def ReindexPointContract : Prop :=
  reindexEmpty = .ok [] ∧
  ∀ (getVector : Index → Index → Jl Index) (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index),
    (∀ index rest, reindexDispatch getVector getMatrix getArray [] (index :: rest) =
      .error (.methodError "reindex")) ∧
    ∀ (normalize : List Index → Jl (List I64)), CoordinateNormalization normalize →
      IndexElementReadLaw getVector getMatrix getArray →
      ∀ axes indices coordinates selected,
        StoredIndices indices → IndicesWithinAxes axes indices → TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        ∃ arguments, reindexDispatch getVector getMatrix getArray indices
            (coordinates.map Index.scalar) = .ok arguments ∧
          normalize arguments = .ok selected ∧ coordinatesInAxes axes selected

theorem reindexPointContract_proven : ReindexPointContract := by
  refine ⟨rfl, ?_⟩
  intro getVector getMatrix getArray
  refine ⟨fun _ _ => rfl, ?_⟩
  intro normalize normalization getters axes indices coordinates selected stored bounds selection valid
  obtain ⟨arguments, indexed, normalized⟩ :=
    reindexPoint_spec getVector getMatrix getArray normalize normalization getters selection stored
  exact ⟨arguments, indexed, normalized, bounds coordinates selected selection valid⟩

def CartesianBoundsLaw {P T : Type} (bounds : ViewBounds P T) : Prop :=
  ∀ view coordinates, view.dimensions.length = (axesSubArrayModel view).length →
    coordinatesInAxes (axesSubArrayModel view) coordinates →
    bounds.cartesian view coordinates = .ok ()

def ParentCoordinateNormalization {P R : Type} (parent : P)
    (get : P → List Index → Jl R) (normalize : List Index → Jl (List I64)) : Prop :=
  ∀ arguments coordinates, normalize arguments = .ok coordinates →
    get parent arguments = get parent (coordinates.map Index.scalar)

def CartesianConstructorContract : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index)
    (dimensions : List Bool),
    (ops.isArrayRank parent (ops.indexNdims indices).length = true →
      subarrayCartesian parent indices dimensions (checkParentIndexMatchWithOps ops) =
        .ok (⟨parent, indices, int64 0, int64 0, false, dimensions⟩ : SubArray P T)) ∧
    (∀ rank, ops.isArrayRank parent (ops.indexNdims indices).length = false →
      ops.ndims parent = .ok rank →
      (subarrayCartesian parent indices dimensions (checkParentIndexMatchWithOps ops) : Jl (SubArray P T)) =
        .error (.argumentError
          s!"number of indices ({(ops.indexNdims indices).length}) must match the parent dimensionality ({rank})")) ∧
    (StoredIndices indices → ops.isArrayRank parent (ops.indexNdims indices).length = true →
      dimensions.length = (viewAxesManual indices).length →
      IndicesWithinAxes (ops.axes parent) indices →
      ∀ (reads : ViewReadOps P T R) (normalize : List Index → Jl (List I64)),
        CartesianBoundsLaw reads.toViewBounds → CoordinateNormalization normalize →
        IndexElementReadLaw reads.getVector reads.getMatrix reads.getArray →
        ParentCoordinateNormalization parent reads.getParentCartesian normalize →
        ∀ coordinates selected, TupleSelection indices coordinates selected →
          coordinatesInAxes (viewAxesManual indices) coordinates →
          getindexSubArrayConfigured
            ⟨parent, indices, int64 0, int64 0, false, dimensions⟩ coordinates reads =
            reads.getParentCartesian parent (selected.map Index.scalar))

theorem cartesianConstructorContract_proven : CartesianConstructorContract := by
  intro P T R ops parent indices dimensions
  refine ⟨?_, ?_, ?_⟩
  · intro matched
    simp [subarrayCartesian, subarrayInner, checkParentIndexMatchWithOps,
      checkParentIndexMatch, checkParentIndexMatchArray, matched,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro rank unmatched ndims
    exact constructorRejectsWrongRank_proven ops parent indices (int64 0) (int64 0)
      false dimensions rank unmatched ndims
  · intro stored matched rank parentBounds reads normalize checkBounds normalization getters
      parentNormalization coordinates selected selection valid
    let view : SubArray P T :=
      ⟨parent, indices, int64 0, int64 0, false, dimensions⟩
    have axes : axesSubArrayModel view = viewAxesManual indices :=
      subArrayAxesContract_proven view
    have checked : reads.cartesian view coordinates = .ok () :=
      checkBounds view coordinates (by simpa [view, axes] using rank)
        (by simpa [axes] using valid)
    obtain ⟨arguments, indexed, normalized⟩ :=
      reindexPoint_spec reads.getVector reads.getMatrix reads.getArray normalize normalization getters
        selection stored
    have parentRead := parentNormalization arguments selected normalized
    simpa only [getindexSubArrayConfigured, getindexSubArray, Bool.false_eq_true, ite_false,
      view, checked, indexed, Bind.bind, Except.bind] using parentRead

theorem normalize_scalar_coordinates (normalize : List Index → Jl (List I64))
    (laws : CoordinateNormalization normalize) (coordinates : List I64) :
    normalize (coordinates.map Index.scalar) = .ok coordinates := by
  induction coordinates with
  | nil => exact laws.empty
  | cons value coordinates ih =>
      exact normalize_result_cons normalize laws (.scalar value)
        (coordinates.map Index.scalar) coordinates ih

theorem view_parent_coordinate_normalization {P T R : Type} (view : SubArray P T)
    (reads : ViewReadOps P T R) (bounds : ViewBounds (SubArray P T) T)
    (normalize : List Index → Jl (List I64)) (laws : CoordinateNormalization normalize) :
    ParentCoordinateNormalization view
      (viewParentReadOps reads bounds normalize).getParentCartesian normalize := by
  intro arguments coordinates normalized
  simp [viewParentReadOps, getindexSubArrayArguments, normalized,
    normalize_scalar_coordinates normalize laws coordinates, Bind.bind, Except.bind]

def HasArrayIndex (indices : List Index) : Prop := ∃ index ∈ indices, index.isArray = true

private theorem hasArray_tail {head : Index} {rest : List Index}
    (notArray : head.isArray = false) (has : HasArrayIndex (head :: rest)) : HasArrayIndex rest := by
  obtain ⟨index, member, array⟩ := has
  rcases List.mem_cons.mp member with equality | member
  · subst index
    rw [notArray] at array
    cases array
  · exact ⟨index, member, array⟩

private theorem array_not_allScalar (indices : List Index) (has : HasArrayIndex indices) :
    Index.allScalar indices = false := by
  cases scalar : Index.allScalar indices with
  | false => rfl
  | true =>
      obtain ⟨index, member, array⟩ := has
      have isScalar : index.isScalar = true :=
        (List.all_eq_true.mp scalar) index member
      cases index <;> simp_all [Index.isScalar, Index.isArray]

theorem viewIndexing_hasArray (indices : List Index) :
    HasArrayIndex indices → viewIndexing indices = .cartesian := by
  induction indices with
  | nil => intro has; simpa [HasArrayIndex] using has
  | cons head rest ih =>
      intro has
      cases head
      case scalar value =>
        simpa only [viewIndexing] using ih (hasArray_tail rfl has)
      case slice axis =>
        have hasRest := hasArray_tail (by rfl) has
        have notScalar := array_not_allScalar rest hasRest
        cases rest with
        | nil => simpa [HasArrayIndex] using hasRest
        | cons second tail =>
            cases second
            case slice secondAxis =>
              have hasTail := hasArray_tail (by rfl) hasRest
              simp [viewIndexing, array_not_allScalar tail hasTail, ih hasRest]
            case unitRange range =>
              have hasTail := hasArray_tail (by rfl) hasRest
              simp [viewIndexing, array_not_allScalar tail hasTail, viewIndexingFallback]
            case oneTo length =>
              have hasTail := hasArray_tail (by rfl) hasRest
              simp [viewIndexing, array_not_allScalar tail hasTail, viewIndexingFallback]
            case identity range =>
              have hasTail := hasArray_tail (by rfl) hasRest
              simp [viewIndexing, array_not_allScalar tail hasTail, viewIndexingFallback]
            all_goals simp [viewIndexing, notScalar]
      all_goals
        first
        | solve | simp [viewIndexing, Index.isRange, Index.isArray, viewIndexingArray, viewIndexingFallback]
        | have hasRest := hasArray_tail (by rfl) has
          simp [viewIndexing, array_not_allScalar rest hasRest, Index.isRange,
            Index.isArray, viewIndexingFallback]

def CartesianArrayFallbackValues : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (view : SubArray P T)
    (indices : List Index) (arrayAxes : List Axis) (elementRank : Nat) (items : List (List I64)),
    elementRank ≠ 1 → Index.cartesianValues arrayAxes elementRank items ∈ indices →
    StoredIndices (ops.ensureIndexable indices) →
    (ops.indexNdims (ops.ensureIndexable indices)).length = view.dimensions.length →
    (ops.indexDimsum indices).length = (viewAxesManual indices).length →
    viewAxesManual (ops.ensureIndexable indices) = viewAxesManual indices →
    (∀ coordinates selected, TupleSelection (ops.ensureIndexable indices) coordinates selected ↔
      TupleSelection indices coordinates selected) →
    IndicesWithinAxes (axesSubArrayModel view) indices →
    ∀ (firstLinearIndex : SubArray P T → Jl I64) (reads : ViewReadOps P T R)
      (bounds : ViewBounds (SubArray P T) T) (normalize : List Index → Jl (List I64)),
      CartesianBoundsLaw bounds → CoordinateNormalization normalize →
      IndexElementReadLaw reads.getVector reads.getMatrix reads.getArray →
      ∃ nested : SubArray (SubArray P T) T,
        maybeReindexCartesianArray view indices
          (constructSubArrayConfigured (parentArrayOpsSubArray ops firstLinearIndex)) =
            .ok (.nested nested) ∧
        nested.parent = view ∧ nested.indices = ops.ensureIndexable indices ∧
        axesSubArrayModel nested = viewAxesManual indices ∧
        ∀ coordinates selected, TupleSelection indices coordinates selected →
          coordinatesInAxes (viewAxesManual indices) coordinates →
          readReindexedView (.nested nested) coordinates reads bounds normalize =
            getindexSubArrayConfigured view selected reads

theorem cartesianArrayFallbackValues_proven : CartesianArrayFallbackValues := by
  intro P T R ops view indices arrayAxes elementRank items notVector member stored consumed
    dimensions axesPreserved selectionPreserved indexBounds firstLinearIndex reads bounds normalize
    checks normalization getters
  have arrayStyle : viewIndexing indices = .cartesian :=
    viewIndexing_hasArray indices ⟨.cartesianValues arrayAxes elementRank items, member, rfl⟩
  let nested : SubArray (SubArray P T) T :=
    ⟨view, ops.ensureIndexable indices, int64 0, int64 0, false, ops.indexDimsum indices⟩
  have constructed : constructSubArrayConfigured (parentArrayOpsSubArray ops firstLinearIndex)
      view indices = .ok nested := by
    simp [constructSubArrayConfigured, subarrayOuter, arrayStyle, indexStyleCombine,
      constructSubArrayByStyle, subarrayCartesian, subarrayInner, checkParentIndexMatchWithOps,
      checkParentIndexMatch, checkParentIndexMatchArray, parentArrayOpsSubArray, consumed,
      nested, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have nestedAxes : axesSubArrayModel nested = viewAxesManual indices :=
    (subArrayAxesContract_proven nested).trans axesPreserved
  refine ⟨nested, ?_, rfl, rfl, nestedAxes, ?_⟩
  · simp [maybeReindexCartesianArray, constructed, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro coordinates selected selection valid
    have ensured := (selectionPreserved coordinates selected).mpr selection
    obtain ⟨arguments, indexed, normalized⟩ :=
      reindexPoint_spec reads.getVector reads.getMatrix reads.getArray normalize normalization getters
        ensured stored
    have checked : bounds.cartesian nested coordinates = .ok () :=
      checks nested coordinates (by simpa [nestedAxes, nested] using dimensions)
        (by simpa [nestedAxes] using valid)
    simpa [readReindexedView, getindexSubArrayConfigured, getindexSubArray,
      viewParentReadOps, getindexSubArrayArguments, nested, checked, indexed, normalized,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using
      (rfl : getindexSubArrayConfigured view selected reads = getindexSubArrayConfigured view selected reads)

def CartesianArrayFallbackContract : Prop := CartesianArrayFallbackNests ∧ CartesianArrayFallbackValues

theorem cartesianArrayFallbackContract_proven : CartesianArrayFallbackContract :=
  ⟨cartesianArrayFallbackNests_proven, cartesianArrayFallbackValues_proven⟩

private def coordinateBlockOracle : Index → Jl (List I64)
  | .scalar value => .ok [value]
  | .cartesian coordinates => .ok coordinates
  | _ => .error (.methodError "to_indices")

private def normalizeCoordinatesOracle (indices : List Index) : Jl (List I64) :=
  splatmap coordinateBlockOracle indices

private theorem splatmap_append {A B : Type} (f : A → Jl (List B))
    (left right : List A) :
    splatmap f (left ++ right) = (do
      let a ← splatmap f left
      let b ← splatmap f right
      pure (a ++ b)) := by
  rw [splatMapOrder_proven f (left ++ right), splatMapOrder_proven f left,
    splatMapOrder_proven f right, List.mapM_append]
  cases left.mapM f <;> cases right.mapM f <;>
    simp [Bind.bind, Except.bind, Functor.map, Except.map, Pure.pure, Except.pure,
      List.flatten_append]

private theorem normalizationOracle_laws : CoordinateNormalization normalizeCoordinatesOracle where
  empty := rfl
  scalar := fun _ => rfl
  cartesian := by
    intro coordinates
    simp [normalizeCoordinatesOracle, splatmap, splatmapEmpty, coordinateBlockOracle,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  append := splatmap_append coordinateBlockOracle

private def indexElementOracle : Index → List I64 → Jl Index
  | .scalar value, [] => .ok (.scalar value)
  | .cartesian selected, [] => .ok (.cartesian selected)
  | .slice _, [coordinate] | .identity _, [coordinate] | .oneTo _, [coordinate] =>
      .ok (.scalar coordinate)
  | .unitRange axis, [coordinate] =>
      .ok (.scalar (iadd axis.first (isub coordinate (int64 1))))
  | .stepRange first step _, [coordinate] | .stepRangeLen first step _, [coordinate]
    | .ordinalRange first step _, [coordinate] =>
      .ok (.scalar (iadd first (imul (isub coordinate (int64 1)) step)))
  | .values axes items, coordinates =>
      match items[(densePosition axes coordinates).val.toNat - 1]? with
      | some value => .ok (.scalar value)
      | none => .error .boundsError
  | .cartesianValues axes _ items, coordinates =>
      match items[(densePosition axes coordinates).val.toNat - 1]? with
      | some selected => .ok (.cartesian selected)
      | none => .error .boundsError
  | .mask bits, [coordinate] =>
      match ((bits.zipIdx.filter (fun item => item.1)).map
        (fun item => int64 (item.2 + 1)))[coordinate.val.toNat - 1]? with
      | some value => .ok (.scalar value)
      | none => .error .boundsError
  | _, _ => .error (.methodError "getindex")

private def getVectorOracle (index argument : Index) : Jl Index :=
  match index, argument with
  | .identity _, .slice axis => .ok (.slice axis)
  | _, .scalar coordinate => indexElementOracle index [coordinate]
  | _, _ => .error (.methodError "getindex")

private def getMatrixOracle (index first second : Index) : Jl Index :=
  match first, second with
  | .scalar first, .scalar second => indexElementOracle index [first, second]
  | _, _ => .error (.methodError "getindex")

private def getArrayOracle (index : Index) (arguments : List Index) : Jl Index := do
  let coordinates ← normalizeCoordinatesOracle arguments
  indexElementOracle index coordinates

private theorem getVectorOracle_point (index : Index) (coordinate : I64) :
    getVectorOracle index (.scalar coordinate) = indexElementOracle index [coordinate] := by
  cases index <;> rfl

private theorem indexElementReadOracle_point (index : Index) (coordinates : List I64) :
    indexElementRead getVectorOracle getMatrixOracle getArrayOracle index coordinates =
      indexElementOracle index coordinates := by
  cases coordinates with
  | nil =>
      simp [indexElementRead, getArrayOracle, normalizationOracle_laws.empty,
        Bind.bind, Except.bind]
  | cons first rest =>
      cases rest with
      | nil => exact getVectorOracle_point index first
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp only [indexElementRead, getArrayOracle,
                normalize_scalar_coordinates _ normalizationOracle_laws, Bind.bind, Except.bind]

private theorem indexElementOracle_selected {index : Index} {coordinates selected : List I64}
    (selection : IndexSelection index coordinates selected) (stored : StoredIndex index)
    (notScalar : index.isScalar = false) (notSlice : ∀ axis, index ≠ .slice axis) :
    ∃ value, indexElementOracle index coordinates = .ok value ∧
      IndexResultCoordinates value selected := by
  cases selection with
  | scalar value => simp [Index.isScalar] at notScalar
  | cartesian coordinates => exact False.elim stored
  | slice axis coordinate valid => exact False.elim (notSlice axis rfl)
  | identity axis coordinate valid => exact ⟨.scalar coordinate, rfl, .scalar coordinate⟩
  | unitRange axis coordinate valid => exact ⟨_, rfl, .scalar _⟩
  | oneTo length coordinate lower upper => exact ⟨.scalar coordinate, rfl, .scalar coordinate⟩
  | stepRange first step count coordinate lower upper => exact ⟨_, rfl, .scalar _⟩
  | stepRangeLen first step count coordinate lower upper => exact ⟨_, rfl, .scalar _⟩
  | ordinalRange first step count coordinate lower upper => exact ⟨_, rfl, .scalar _⟩
  | values axes items coordinates value valid present =>
      exact ⟨.scalar value, by simp [indexElementOracle, present], .scalar value⟩
  | cartesianValues axes rank items coordinates selected valid present length =>
      exact ⟨.cartesian selected, by simp [indexElementOracle, present], .cartesian selected⟩
  | mask bits coordinate value lower present =>
      exact ⟨.scalar value, by simp [indexElementOracle, present], .scalar value⟩

private theorem indexElementOracle_laws :
    IndexElementReadLaw getVectorOracle getMatrixOracle getArrayOracle := by
  intro index coordinates selected selection stored notScalar notSlice
  rw [indexElementReadOracle_point]
  exact indexElementOracle_selected selection stored notScalar notSlice

def indexArrayRead (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (index : Index) : List Index → Jl Index
  | [argument] => getVector index argument
  | [first, second] => getMatrix index first second
  | arguments => getArray index arguments

structure IndexComposition (index : Index) (arguments : List Index) (result : Index) : Prop where
  axes : result.indexAxes = viewAxesManual arguments
  selects : ∀ coordinates selected, IndexSelection result coordinates selected ↔
    ∃ middle, TupleSelection arguments coordinates middle ∧ IndexSelection index middle selected

private theorem tupleSelection_single {index : Index} {coordinates selected : List I64} :
    TupleSelection [index] coordinates selected ↔ IndexSelection index coordinates selected := by
  constructor
  · intro selection
    cases selection with
    | cons head tail =>
        cases tail
        simpa only [List.append_nil] using head
  · intro selection
    simpa only [List.append_nil] using TupleSelection.cons selection TupleSelection.nil

private theorem slice_composition (axis : Axis) (argument : Index)
    (bounds : ∀ coordinates selected, IndexSelection argument coordinates selected →
      coordinatesInAxes [axis] selected) :
    IndexComposition (.slice axis) [argument] argument where
  axes := by simp [viewAxesManual]
  selects := by
    intro coordinates selected
    constructor
    · intro selection
      have valid := bounds coordinates selected selection
      cases selected with
      | nil => cases valid
      | cons coordinate rest =>
          cases rest with
          | nil =>
              exact ⟨[coordinate], tupleSelection_single.mpr selection, .slice axis coordinate valid⟩
          | cons _ _ => simp [coordinatesInAxes] at valid
    · rintro ⟨middle, selectedArguments, selectedSlice⟩
      cases selectedSlice
      exact tupleSelection_single.mp selectedArguments

private theorem scalar_composition (value : I64) :
    IndexComposition (.scalar value) [] (.scalar value) where
  axes := rfl
  selects := by
    intro coordinates selected
    constructor
    · intro selection
      cases selection
      exact ⟨[], .nil, .scalar value⟩
    · rintro ⟨middle, empty, scalar⟩
      cases empty
      exact scalar

/-- Laws for indexing the stored index arrays, whose methods live in other Base files. -/
inductive ReindexRow (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) : Index → List Index → Index → Prop
  | scalar (value : I64) : ReindexRow getVector getMatrix getArray (.scalar value) [] (.scalar value)
  | slice (axis : Axis) (argument : Index)
      (bounds : ∀ coordinates selected, IndexSelection argument coordinates selected →
        coordinatesInAxes [axis] selected) :
      ReindexRow getVector getMatrix getArray (.slice axis) [argument] argument
  | array (index : Index) (arguments : List Index) (result : Index)
      (notScalar : index.isScalar = false) (notSlice : ∀ axis, index ≠ .slice axis)
      (stored : StoredIndex index) (rank : arguments.length = index.indexAxes.length)
      (read : indexArrayRead getVector getMatrix getArray index arguments = .ok result)
      (composition : IndexComposition index arguments result) :
      ReindexRow getVector getMatrix getArray index arguments result

inductive ReindexCompatible (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) : List Index → List Index → List Index → Prop
  | nil : ReindexCompatible getVector getMatrix getArray [] [] []
  | cons {index result : Index} {indices arguments rest results : List Index} :
      ReindexRow getVector getMatrix getArray index arguments result →
      ReindexCompatible getVector getMatrix getArray indices rest results →
      ReindexCompatible getVector getMatrix getArray
        (index :: indices) (arguments ++ rest) (result :: results)

private theorem reindexRow_rank {getVector getMatrix getArray}
    {index arguments result}
    (row : ReindexRow getVector getMatrix getArray index arguments result) :
    arguments.length = index.indexAxes.length := by
  cases row with
  | scalar value => rfl
  | slice axis argument bounds => rfl
  | array index arguments result notScalar notSlice stored rank read composition => exact rank

private theorem reindexRow_composition {getVector getMatrix getArray}
    {index arguments result}
    (row : ReindexRow getVector getMatrix getArray index arguments result) :
    IndexComposition index arguments result := by
  cases row with
  | scalar value => exact scalar_composition value
  | slice axis argument bounds => exact slice_composition axis _ bounds
  | array index arguments result notScalar notSlice stored rank read composition => exact composition

private theorem reindex_raw_block (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (index : Index)
    (indices blockIndices rest : List Index) (notScalar : index.isScalar = false)
    (notSlice : ∀ axis, index ≠ .slice axis) (stored : StoredIndex index)
    (rank : blockIndices.length = index.indexAxes.length) :
    reindexDispatch getVector getMatrix getArray (index :: indices) (blockIndices ++ rest) = (do
      let value ← indexArrayRead getVector getMatrix getArray index blockIndices
      let remaining ← reindexDispatch getVector getMatrix getArray indices rest
      pure (value :: remaining)) := by
  rw [reindex_array_dispatch getVector getMatrix getArray index indices _ notScalar notSlice stored,
    ← rank]
  have taken := List.take_left (l₁ := blockIndices) (l₂ := rest)
  have dropped := List.drop_left (l₁ := blockIndices) (l₂ := rest)
  cases blockIndices with
  | nil => simp [indexArrayRead]
  | cons first blockIndices =>
      cases blockIndices with
      | nil => simp [indexArrayRead]
      | cons second blockIndices =>
          cases blockIndices with
          | nil => simp [indexArrayRead]
          | cons third blockIndices =>
              simp only [List.length_cons, List.cons_append, indexArrayRead] at taken dropped ⊢
              rw [taken, dropped]

private theorem reindexRow_actual {getVector getMatrix getArray}
    {index arguments result}
    (row : ReindexRow getVector getMatrix getArray index arguments result)
    (indices rest : List Index) :
    reindexDispatch getVector getMatrix getArray (index :: indices) (arguments ++ rest) = (do
      let remaining ← reindexDispatch getVector getMatrix getArray indices rest
      pure (result :: remaining)) := by
  cases row with
  | scalar value =>
      simp [reindexDispatch, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | slice axis argument bounds =>
      simp [reindexDispatch, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | array index arguments result notScalar notSlice stored rank read composition =>
      rw [reindex_raw_block getVector getMatrix getArray index indices arguments rest
        notScalar notSlice stored rank, read]
      rfl

theorem reindexCompatible_actual {getVector getMatrix getArray} {indices arguments results}
    (compatible : ReindexCompatible getVector getMatrix getArray indices arguments results) :
    reindexDispatch getVector getMatrix getArray indices arguments = .ok results := by
  induction compatible with
  | nil => rfl
  | cons row tail ih =>
      rw [reindexRow_actual row, ih]
      rfl

private theorem tupleSelection_split (blockIndices rest : List Index)
    {coordinates selected : List I64} (selection : TupleSelection (blockIndices ++ rest) coordinates selected) :
    ∃ firstCoordinates restCoordinates firstSelected restSelected,
      coordinates = firstCoordinates ++ restCoordinates ∧ selected = firstSelected ++ restSelected ∧
      TupleSelection blockIndices firstCoordinates firstSelected ∧ TupleSelection rest restCoordinates restSelected := by
  induction blockIndices generalizing coordinates selected with
  | nil => exact ⟨[], coordinates, [], selected, rfl, rfl, .nil, selection⟩
  | cons index blockIndices ih =>
      cases selection with
      | cons head tail =>
          obtain ⟨a, b, x, y, coordinates, selected, left, right⟩ := ih tail
          refine ⟨_, b, _, y, ?_, ?_, TupleSelection.cons head left, right⟩
          · simp [coordinates, List.append_assoc]
          · simp [selected, List.append_assoc]

def SingleIndexResults (indices : List Index) : Prop :=
  ∀ index ∈ indices, ∀ coordinates selected, IndexSelection index coordinates selected → selected.length = 1

private theorem selected_length {indices : List Index} {coordinates selected : List I64}
    (single : SingleIndexResults indices) (selection : TupleSelection indices coordinates selected) :
    selected.length = indices.length := by
  induction selection with
  | nil => rfl
  | @cons index indices coordinates rest selected remaining head tail ih =>
      rw [List.length_append, single index (by simp) coordinates selected head,
        ih (fun i member => single i (by simp [member]))]
      simp [Nat.add_comm]

private theorem equal_append_parts {A : Type} {a b c d : List A}
    (length : a.length = c.length) (equal : a ++ b = c ++ d) : a = c ∧ b = d := by
  have first := congrArg (fun values => values.take a.length) equal
  rw [List.take_left, length, List.take_left] at first
  have rest := congrArg (fun values => values.drop a.length) equal
  rw [List.drop_left, length, List.drop_left] at rest
  exact ⟨first, rest⟩

private theorem tupleSelection_uncons {index : Index} {indices : List Index}
    {coordinates selected : List I64} (selection : TupleSelection (index :: indices) coordinates selected) :
    ∃ firstCoordinates restCoordinates firstSelected restSelected,
      coordinates = firstCoordinates ++ restCoordinates ∧ selected = firstSelected ++ restSelected ∧
      IndexSelection index firstCoordinates firstSelected ∧ TupleSelection indices restCoordinates restSelected := by
  cases selection with
  | cons head tail => exact ⟨_, _, _, _, rfl, rfl, head, tail⟩

theorem reindexCompatible_selects {getVector getMatrix getArray} {indices arguments results}
    (compatible : ReindexCompatible getVector getMatrix getArray indices arguments results)
    (single : SingleIndexResults arguments) :
    ∀ coordinates middle selected, TupleSelection arguments coordinates middle →
      TupleSelection indices middle selected → TupleSelection results coordinates selected := by
  induction compatible with
  | nil =>
      intro coordinates middle selected outer inner
      cases outer
      exact inner
  | @cons index result indices blockIndices rest results row tail ih =>
      intro coordinates middle selected outer inner
      obtain ⟨firstCoordinates, restCoordinates, firstMiddle, restMiddle,
        coordinatesEqual, middleEqual, firstOuter, restOuter⟩ := tupleSelection_split blockIndices rest outer
      obtain ⟨indexCoordinates, remainingCoordinates, firstSelected, restSelected,
        indexEqual, selectedEqual, firstInner, restInner⟩ := tupleSelection_uncons inner
      have prefixSingle : SingleIndexResults blockIndices :=
        fun i member => single i (List.mem_append_left rest member)
      have restSingle : SingleIndexResults rest :=
        fun i member => single i (List.mem_append_right blockIndices member)
      have length : firstMiddle.length = indexCoordinates.length :=
        (selected_length prefixSingle firstOuter).trans
          ((reindexRow_rank row).trans firstInner.axesLength.symm)
      obtain ⟨firstEqual, restEqual⟩ :=
        equal_append_parts length (middleEqual.symm.trans indexEqual)
      subst indexCoordinates
      subst remainingCoordinates
      have first := (reindexRow_composition row).selects firstCoordinates firstSelected |>.mpr
        ⟨firstMiddle, firstOuter, firstInner⟩
      have remaining := ih restSingle restCoordinates restMiddle restSelected restOuter restInner
      rw [coordinatesEqual, selectedEqual]
      exact TupleSelection.cons first remaining

def ReindexCompositionContract : Prop :=
  ∀ (getVector : Index → Index → Jl Index) (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index) (indices arguments results : List Index),
    ReindexCompatible getVector getMatrix getArray indices arguments results →
    SingleIndexResults arguments →
    reindexDispatch getVector getMatrix getArray indices arguments = .ok results ∧
    (∀ coordinates middle selected, TupleSelection arguments coordinates middle →
        TupleSelection indices middle selected → TupleSelection results coordinates selected) ∧
    ∀ (normalize : List Index → Jl (List I64)), CoordinateNormalization normalize →
      IndexElementReadLaw getVector getMatrix getArray →
      ∀ normalizedResults, StoredIndices normalizedResults →
        (∀ coordinates selected, TupleSelection results coordinates selected →
          TupleSelection normalizedResults coordinates selected) →
        ∀ coordinates middle selected, TupleSelection arguments coordinates middle →
          TupleSelection indices middle selected →
          ∃ parentArguments, reindexDispatch getVector getMatrix getArray normalizedResults
              (coordinates.map Index.scalar) = .ok parentArguments ∧
            normalize parentArguments = .ok selected

theorem reindexCompositionContract_proven : ReindexCompositionContract := by
  intro getVector getMatrix getArray indices arguments results compatible single
  refine ⟨reindexCompatible_actual compatible, reindexCompatible_selects compatible single, ?_⟩
  intro normalize normalization getters normalizedResults stored preserved coordinates middle selected outer inner
  exact reindexPoint_spec getVector getMatrix getArray normalize normalization getters
    (preserved coordinates selected (reindexCompatible_selects compatible single
      coordinates middle selected outer inner)) stored

structure IndexTupleNormalization (arguments normalized : List Index) : Prop where
  stored : StoredIndices normalized
  axes : viewAxesManual arguments = viewAxesManual normalized
  selects : ∀ coordinates selected, TupleSelection arguments coordinates selected ↔
    TupleSelection normalized coordinates selected

private theorem indexTupleNormalization_refl (indices : List Index) (stored : StoredIndices indices) :
    IndexTupleNormalization indices indices :=
  ⟨stored, rfl, fun _ _ => Iff.rfl⟩

/-- Array metadata, index normalization, and primitive arithmetic come from other Base files. -/
structure ViewConstructorInputs {P : Type} (ops : ParentArrayOps P) (parent : P)
    (indices : List Index) : Prop where
  normalized : IndexTupleNormalization indices (ops.ensureIndexable indices)
  dimensions : ops.indexDimsum indices = List.replicate (viewAxesManual indices).length true
  matched : ops.isArrayRank parent (ops.indexNdims (ops.ensureIndexable indices)).length = true
  fast : ops.parentStyle parent = .linear → viewIndexing indices = .linear →
    FastViewInputs ops parent (ops.ensureIndexable indices)

private theorem viewConstructorInputs_of_fast {P : Type} {ops : ParentArrayOps P}
    {parent : P} {indices : List Index} (inputs : FastViewInputs ops parent indices)
    (stored : StoredIndices indices) : ViewConstructorInputs ops parent indices where
  normalized := by
    rw [inputs.normalized]
    exact indexTupleNormalization_refl indices stored
  dimensions := inputs.dimensions
  matched := by simpa only [inputs.normalized] using inputs.matched
  fast := by
    intro _ _
    simpa only [inputs.normalized] using inputs

structure ViewReadInterfaces {P T R : Type} (ops : ParentArrayOps P)
    (reads : ViewReadOps P T R) (normalize : List Index → Jl (List I64)) : Prop where
  normalization : CoordinateNormalization normalize
  elements : IndexElementReadLaw reads.getVector reads.getMatrix reads.getArray
  cartesianBounds : CartesianBoundsLaw reads.toViewBounds
  linearBounds : ∀ view coordinate, view.dimensions.length = 1 →
    coordinatesInAxes (axesSubArrayModel view) [coordinate] →
    reads.linear view coordinate = .ok ()
  parentNormalization : ∀ parent, ParentCoordinateNormalization parent reads.getParentCartesian normalize
  parentLinear : ∀ parent selected, coordinatesInAxes (ops.axes parent) selected →
    reads.getParentLinear parent (linearPosition (ops.axes parent) selected) =
      reads.getParentCartesian parent (selected.map Index.scalar)

/-- Both stages call the source constructors, and both reads call the source SubArray methods. -/
def GeneralNestedRead : Prop :=
  CartesianArrayFallbackValues ∧
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices arguments : List Index),
    ViewConstructorInputs ops parent indices →
    IndicesWithinAxes (ops.axes parent) (ops.ensureIndexable indices) →
    (∀ coordinates, coordinatesInAxes (viewAxesManual (ops.ensureIndexable indices)) coordinates →
      ∃ selected, TupleSelection (ops.ensureIndexable indices) coordinates selected) →
    ∀ (reads : ViewReadOps P T R) (normalize : List Index → Jl (List I64))
      (bounds : ViewBounds (SubArray P T) T)
      (firstLinearIndex : SubArray P T → Jl I64)
      (toIndices : P → List Index → Jl (List Index)),
      ViewReadInterfaces ops reads normalize →
      CartesianBoundsLaw bounds →
      ∀ original : SubArray P T, constructSubArrayConfigured ops parent indices = .ok original →
        StoredIndices arguments → SingleIndexResults arguments →
        IndicesWithinAxes (axesSubArrayModel original) arguments →
        ∀ merged normalized, ReindexCompatible reads.getVector reads.getMatrix reads.getArray
            original.indices arguments merged →
          toIndices parent merged = .ok normalized →
          IndexTupleNormalization merged normalized →
          ViewConstructorInputs ops parent normalized →
          ∀ result, unsafeViewSubArrayConfigured ops firstLinearIndex
              reads.getVector reads.getMatrix reads.getArray toIndices original arguments = .ok result →
            ∀ coordinates middle, TupleSelection arguments coordinates middle →
              coordinatesInAxes (viewAxesManual arguments) coordinates →
              readReindexedView result coordinates reads bounds normalize =
                getindexSubArrayConfigured original middle reads

private def selectionReadOracle : ViewReadOps (List Axis) Unit I64 where
  cartesian := fun _ _ => .ok ()
  linear := fun _ _ => .ok ()
  getVector := getVectorOracle
  getMatrix := getMatrixOracle
  getArray := getArrayOracle
  getParentCartesian := fun parent arguments => do
    let coordinates ← normalizeCoordinatesOracle arguments
    pure (linearPosition parent coordinates)
  getParentLinear := readAddressOracle

private theorem selectionReadOracle_interfaces :
    ViewReadInterfaces strideCounterexampleOps selectionReadOracle normalizeCoordinatesOracle where
  normalization := normalizationOracle_laws
  elements := indexElementOracle_laws
  cartesianBounds := fun _ _ _ _ => rfl
  linearBounds := fun _ _ _ _ => rfl
  parentNormalization := by
    intro parent arguments coordinates normalized
    simp only [selectionReadOracle, normalized, Bind.bind, Except.bind,
      normalize_scalar_coordinates _ normalizationOracle_laws]
  parentLinear := by
    intro parent selected valid
    simp only [selectionReadOracle, strideCounterexampleOps,
      normalize_scalar_coordinates _ normalizationOracle_laws, readAddressOracle,
      Bind.bind, Except.bind, Pure.pure, Except.pure, id_eq]

private theorem identity_slice_composition (axis : Axis) :
    IndexComposition (.identity axis) [.slice axis] (.slice axis) where
  axes := by simp [viewAxesManual]
  selects := by
    intro coordinates selected
    constructor
    · intro selection
      cases selection
      rename_i coordinate valid
      exact ⟨[coordinate], tupleSelection_single.mpr (.slice axis coordinate valid),
        .identity axis coordinate valid⟩
    · rintro ⟨middle, outer, inner⟩
      cases inner with
      | identity coordinate valid => exact tupleSelection_single.mp outer

private theorem bug_reindex_compatible :
    ReindexCompatible getVectorOracle getMatrixOracle getArrayOracle bugInitial.indices
      [.slice bugAxis] [.slice bugAxis, .scalar (int64 2)] := by
  exact ReindexCompatible.cons
    (ReindexRow.array (.identity bugAxis) [.slice bugAxis] (.slice bugAxis)
      rfl (by intro axis equal; cases equal) trivial rfl rfl (identity_slice_composition bugAxis))
    (ReindexCompatible.cons (ReindexRow.scalar (int64 2)) ReindexCompatible.nil)

private theorem bug_initial_indices_total :
    ∀ coordinates, coordinatesInAxes (viewAxesManual bugInitial.indices) coordinates →
      ∃ selected, TupleSelection bugInitial.indices coordinates selected := by
  intro coordinates valid
  change coordinatesInAxes [bugAxis] coordinates at valid
  cases coordinates with
  | nil => cases valid
  | cons coordinate rest =>
      cases rest with
      | nil =>
          exact ⟨[coordinate, int64 2], TupleSelection.cons (.identity bugAxis coordinate valid)
            (TupleSelection.cons (.scalar (int64 2)) .nil)⟩
      | cons _ _ => simp [coordinatesInAxes] at valid

private theorem bug_initial_indices_bounds :
    IndicesWithinAxes bugParent bugInitial.indices := by
  intro coordinates selected selection valid
  change TupleSelection [.identity bugAxis, .scalar (int64 2)] coordinates selected at selection
  cases selection with
  | cons head tail =>
      cases head
      rename_i coordinate bounded
      cases tail with
      | cons scalar empty =>
          cases scalar
          cases empty
          have one : (int64 1).val = 1 := by decide
          have two : (int64 2).val = 2 := by decide
          have three : (int64 3).val = 3 := by decide
          have four : (int64 4).val = 4 := by decide
          have five : (int64 5).val = 5 := by decide
          change (int64 2).val ≤ coordinate.val ∧ coordinate.val ≤ (int64 3).val ∧ True at bounded
          change (int64 1).val ≤ coordinate.val ∧ coordinate.val ≤ (int64 4).val ∧
            (int64 1).val ≤ (int64 2).val ∧ (int64 2).val ≤ (int64 5).val ∧ True
          rw [two, three] at bounded
          rw [one, two, four, five]
          exact ⟨Int.le_trans (by decide) bounded.1, Int.le_trans bounded.2.1 (by decide),
            by decide, by decide, trivial⟩

private theorem bug_outer_indices_bounds :
    IndicesWithinAxes (axesSubArrayModel bugInitial) [.slice bugAxis] := by
  intro coordinates selected selection valid
  have one := tupleSelection_single.mp selection
  cases one
  rename_i coordinate bounded
  rw [subArrayAxesContract_proven bugInitial]
  exact bounded

private theorem bug_initial_fast_inputs :
    FastViewInputs strideCounterexampleOps bugParent bugInitial.indices where
  rank := rfl
  parentLinear := bug_fast_inputs.parentLinear
  indexLinear := by simp [bugInitial, viewIndexing, Index.isRange, Index.allScalar, Index.isScalar,
    viewIndexingScalarRange]
  normalized := rfl
  dimensions := rfl
  matched := rfl
  filled := rfl
  firstLinear := bug_fast_inputs.firstLinear
  vector := bug_fast_inputs.vector
  axisFirst := bug_fast_inputs.axisFirst
  axisLength := bug_fast_inputs.axisLength
  indexFirst := bug_fast_inputs.indexFirst
  indexStep := bug_fast_inputs.indexStep
  indexAxis := bug_fast_inputs.indexAxis

private def nestedBoundsOracle : ViewBounds (SubArray (List Axis) Unit) Unit where
  cartesian := fun _ _ => .ok ()
  linear := fun _ _ => .ok ()

private theorem bug_source_nested_construct :
    unsafeViewSubArrayConfigured strideCounterexampleOps nestedSliceFirstLinearIndex
      getVectorOracle getMatrixOracle getArrayOracle nestedSliceToIndices
      bugInitial [.slice bugAxis] = .ok (.flattened bugFlattened) := by
  have reindexed := reindexCompatible_actual bug_reindex_compatible
  simp only [unsafeViewSubArrayConfigured, unsafeViewSubArray, maybeReindexConfigured,
    maybeReindex, maybeReindexDispatch, maybeReindexEmpty,
    reindexed, nestedSliceToIndices, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [show bugInitial.parent = bugParent from rfl, bug_flattened_construct]

private theorem bug_original_source_read :
    getindexSubArrayConfigured bugInitial [int64 2] selectionReadOracle = .ok (int64 6) := by
  change (Except.ok (iadd (int64 4) (imul (int64 1) (int64 2))) : Jl I64) = .ok (int64 6)
  simp only [imul_lit, iadd_lit, Int.reduceMul, Int.reduceAdd]

private theorem bug_nested_source_read :
    readReindexedView (.flattened bugFlattened) [int64 2] selectionReadOracle
      nestedBoundsOracle normalizeCoordinatesOracle = .ok (int64 7) := by
  change (Except.ok (iadd (int64 5) (imul (int64 1) (int64 2))) : Jl I64) = .ok (int64 7)
  simp only [imul_lit, iadd_lit, Int.reduceMul, Int.reduceAdd]

theorem generalNestedRead_refuted : ¬ GeneralNestedRead := by
  intro promises
  have storedInitial : StoredIndices bugInitial.indices := ⟨trivial, trivial, trivial⟩
  have storedMerged : StoredIndices [.slice bugAxis, .scalar (int64 2)] :=
    ⟨trivial, trivial, trivial⟩
  have single : SingleIndexResults [.slice bugAxis] := by
    intro index member coordinates selected selection
    have equal : index = .slice bugAxis := by simpa using member
    subst index
    cases selection
    rfl
  have point : TupleSelection [.slice bugAxis] [int64 2] [int64 2] :=
    tupleSelection_single.mpr (.slice bugAxis (int64 2)
      (by simp only [coordinatesInAxes, bugAxis]; decide))
  have observed := promises.2 strideCounterexampleOps bugParent bugInitial.indices [.slice bugAxis]
    (viewConstructorInputs_of_fast bug_initial_fast_inputs storedInitial)
    bug_initial_indices_bounds bug_initial_indices_total
    selectionReadOracle normalizeCoordinatesOracle nestedBoundsOracle
    nestedSliceFirstLinearIndex nestedSliceToIndices selectionReadOracle_interfaces
    (fun _ _ _ _ => rfl) bugInitial bug_initial_construct
    (by exact ⟨trivial, trivial⟩) single bug_outer_indices_bounds
    [.slice bugAxis, .scalar (int64 2)] [.slice bugAxis, .scalar (int64 2)]
    bug_reindex_compatible rfl (indexTupleNormalization_refl _ storedMerged)
    (viewConstructorInputs_of_fast bug_fast_inputs storedMerged)
    (.flattened bugFlattened) bug_source_nested_construct [int64 2] [int64 2] point
    (by simp only [viewAxesManual, List.flatMap_cons, List.flatMap_nil, Index.indexAxes,
      List.append_nil, coordinatesInAxes, bugAxis]; decide)
  rw [bug_nested_source_read, bug_original_source_read] at observed
  have impossible : int64 7 = int64 6 := Except.ok.inj observed
  exact (by decide : (int64 7 : I64) ≠ int64 6) impossible

private def indexedNonscalars (indices : List Index) (dimension : I64) : List (I64 × Index) :=
  (indices.zipIdx).filterMap fun (index, position) =>
    if index.isScalar then none else some (iadd dimension (int64 position), index)

private theorem indexedNonscalars_cons (head : Index) (rest : List Index) (dimension : I64) :
    indexedNonscalars (head :: rest) dimension =
      (if head.isScalar then [] else [(dimension, head)]) ++
        indexedNonscalars rest (iadd dimension (int64 1)) := by
  unfold indexedNonscalars
  simp only [List.zipIdx_cons', List.filterMap_cons, List.filterMap_map]
  have shift : ∀ position : Nat,
      iadd dimension (int64 (position + 1)) =
        iadd (iadd dimension (int64 1)) (int64 position) := by
    intro position
    rw [← int64_self dimension]
    simp only [iadd_lit]
    congr 1
    omega
  cases scalar : head.isScalar <;>
    simp [scalar, iadd_zero, Function.comp_def, shift]

private theorem indexedNonscalars_dimensions (indices : List Index) :
    ∀ dimension, findExtendedDimsDispatch dimension indices =
      (indexedNonscalars indices dimension).map Prod.fst := by
  induction indices with
  | nil => intro dimension; rfl
  | cons head rest ih =>
      intro dimension
      rw [indexedNonscalars_cons]
      cases head <;>
        simp [findExtendedDimsDispatch, Index.isScalar, ih]

private theorem indexedNonscalars_indices (indices : List Index) :
    ∀ dimension, findExtendedIndicesDispatch indices =
      (indexedNonscalars indices dimension).map Prod.snd := by
  induction indices with
  | nil => intro dimension; rfl
  | cons head rest ih =>
      intro dimension
      rw [indexedNonscalars_cons]
      cases head <;>
        simp only [findExtendedIndicesDispatch, Index.isScalar, Bool.false_eq_true, ite_false,
          ite_true, List.nil_append, List.singleton_append, List.map_cons] <;>
          first | exact ih _ | exact congrArg (fun xs => _ :: xs) (ih _)

def ExtendedCoordinatesContract : Prop :=
  ∀ indices,
    (findExtendedDimsDispatch (int64 1) indices).zip
        (findExtendedIndicesDispatch indices) =
      (indices.zipIdx).filterMap (fun (index, position) =>
        if index.isScalar then none else some (int64 (position + 1), index))

theorem extendedCoordinatesContract_proven : ExtendedCoordinatesContract := by
  intro indices
  rw [indexedNonscalars_dimensions indices (int64 1), indexedNonscalars_indices indices (int64 1)]
  have zipped : ∀ (items : List (I64 × Index)),
      (items.map Prod.fst).zip (items.map Prod.snd) = items := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [ih]
  rw [zipped]
  have increment : ∀ position : Nat, iadd (int64 1) (int64 position) = int64 (position + 1) := by
    intro position
    rw [iadd_lit]
    congr 1
    omega
  simpa only [indexedNonscalars, increment, List.map_id_fun, List.map_id]

def ParentSetterNormalization {P R : Type} (set : P → List Index → R → Jl P)
    (normalize : List Index → Jl (List I64)) : Prop :=
  ∀ parent arguments coordinates value, normalize arguments = .ok coordinates →
    set parent arguments value = set parent (coordinates.map Index.scalar) value

def CartesianSetContract : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) (coordinates selected : List I64) (value : R)
    (getVector : Index → Index → Jl Index) (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (normalize : List Index → Jl (List I64))
    (checkBounds : SubArray P T → List I64 → Jl Unit)
    (setParent : P → List Index → R → Jl P),
    StoredIndices view.indices → TupleSelection view.indices coordinates selected →
    CoordinateNormalization normalize → IndexElementReadLaw getVector getMatrix getArray →
    ParentSetterNormalization setParent normalize →
    checkBounds view coordinates = .ok () →
    ∀ updatedParent, setParent view.parent (selected.map Index.scalar) value = .ok updatedParent →
      ∃ updated : SubArray P T,
        setindexSubArray view value coordinates checkBounds
          (reindexDispatch getVector getMatrix getArray) setParent = .ok updated ∧
        updated.parent = updatedParent ∧ updated.indices = view.indices ∧
        updated.offset1 = view.offset1 ∧ updated.stride1 = view.stride1 ∧
        updated.linear = view.linear ∧ updated.dimensions = view.dimensions

theorem cartesianSetContract_proven : CartesianSetContract := by
  intro P T R view coordinates selected value getVector getMatrix getArray normalize checkBounds
    setParent stored selection normalization getters parentNormalization checked updatedParent written
  obtain ⟨arguments, indexed, normalized⟩ :=
    reindexPoint_spec getVector getMatrix getArray normalize normalization getters selection stored
  have parentWrite := (parentNormalization view.parent arguments selected value normalized).trans written
  refine ⟨{view with parent := updatedParent}, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [setindexSubArray, checked, indexed, parentWrite, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Functor.map, Except.map]

def CartesianIsassignedContract : Prop :=
  IsassignedOutsideView ∧
  ∀ {P T : Type} (view : SubArray P T) (coordinates selected : List I64)
    (getVector : Index → Index → Jl Index) (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (normalize : List Index → Jl (List I64))
    (checkBounds : SubArray P T → List I64 → Bool)
    (assigned : P → List Index → Jl Bool),
    StoredIndices view.indices → TupleSelection view.indices coordinates selected →
    CoordinateNormalization normalize → IndexElementReadLaw getVector getMatrix getArray →
    ParentCoordinateNormalization view.parent assigned normalize →
    checkBounds view coordinates = true →
    isassignedSubArray view coordinates checkBounds
      (reindexDispatch getVector getMatrix getArray) assigned =
        assigned view.parent (selected.map Index.scalar)

theorem cartesianIsassignedContract_proven : CartesianIsassignedContract := by
  refine ⟨isassignedOutsideView_proven, ?_⟩
  intro P T view coordinates selected getVector getMatrix getArray normalize checkBounds assigned
    stored selection normalization getters parentNormalization checked
  obtain ⟨arguments, indexed, normalized⟩ :=
    reindexPoint_spec getVector getMatrix getArray normalize normalization getters selection stored
  simpa only [isassignedSubArray, checked, Bool.not_true, Bool.false_eq_true, ite_false,
    indexed, Bind.bind, Except.bind] using parentNormalization arguments selected normalized

private theorem scalarPrefix_indexStyle (prefixValues : List I64) (indices : List Index) :
    viewIndexing (prefixValues.map Index.scalar ++ indices) = viewIndexing indices := by
  induction prefixValues with
  | nil => rfl
  | cons value rest ih => simpa only [List.map_cons, List.cons_append, viewIndexing] using ih

private theorem scalarTuple_allScalar (values : List I64) :
    Index.allScalar (values.map Index.scalar) = true := by
  induction values with
  | nil => rfl
  | cons value rest ih => simpa [Index.allScalar, Index.isScalar] using ih

private theorem oneRange_indexStyle (range : Index) (scalars : List I64)
    (isRange : range.isRange = true) :
    viewIndexing (range :: scalars.map Index.scalar) = .linear := by
  have allScalar := scalarTuple_allScalar scalars
  cases range <;> simp_all [Index.isRange, viewIndexing, viewIndexingScalarRange]
  cases scalars with
  | nil => rfl
  | cons value rest =>
      simp [viewIndexing, Index.allScalar, Index.isScalar, scalarTuple_allScalar,
        scalarTuple_allScalar rest] at allScalar ⊢

private theorem unitRangeAfterSlices_indexStyle (slices : List Axis) (range : Index)
    (scalars : List I64) (unitRange : range.isUnitRange = true) :
    viewIndexing (slices.map Index.slice ++ range :: scalars.map Index.scalar) = .linear := by
  have allScalar := scalarTuple_allScalar scalars
  induction slices with
  | nil =>
      exact oneRange_indexStyle range scalars (by cases range <;> simp_all [Index.isUnitRange, Index.isRange])
  | cons axis slices ih =>
      cases slices with
      | nil =>
          cases range <;>
            simp_all [Index.isUnitRange, viewIndexing, Index.allScalar, Index.isScalar,
              viewIndexingSliceUnitRange, viewIndexingScalarRange, List.map]
      | cons second slices =>
          simp only [List.map_cons, List.cons_append, viewIndexing]
          split
          · rfl
          · exact ih

def LinearClassificationContract : Prop :=
  (∀ (prefixValues : List I64) (indices : List Index), viewIndexing (prefixValues.map Index.scalar ++ indices) = viewIndexing indices) ∧
  (∀ (prefixValues : List I64) (range : Index) (scalars : List I64), range.isRange = true →
    viewIndexing (prefixValues.map Index.scalar ++ range :: scalars.map Index.scalar) = .linear) ∧
  (∀ (prefixValues : List I64) (slices : List Axis) (range : Index) (scalars : List I64), range.isUnitRange = true →
    viewIndexing (prefixValues.map Index.scalar ++ slices.map Index.slice ++ range :: scalars.map Index.scalar) =
      .linear) ∧
  (∀ indices, HasArrayIndex indices → viewIndexing indices = .cartesian) ∧
  (∀ (scalars : List I64), viewIndexing (scalars.map Index.scalar) = viewIndexingEmpty) ∧
  (∀ (axis second : Axis) (scalars : List I64), viewIndexingSlices viewIndexing (.slice axis) (.slice second)
      (scalars.map Index.scalar) = viewIndexingSliceSliceScalars (.slice axis) (.slice second)
        (scalars.map Index.scalar)) ∧
  (∀ (axis : Axis) (range : Index) (scalars : List I64), range.isUnitRange = true →
    viewIndexing (.slice axis :: range :: scalars.map Index.scalar) =
      viewIndexingSliceUnitRange (.slice axis) range (scalars.map Index.scalar)) ∧
  (∀ (range : Index) (scalars : List I64), range.isRange = true →
    viewIndexing (range :: scalars.map Index.scalar) =
      viewIndexingScalarRange range (scalars.map Index.scalar))

theorem linearClassificationContract_proven : LinearClassificationContract := by
  refine ⟨scalarPrefix_indexStyle, ?_, ?_, viewIndexing_hasArray, ?_, ?_, ?_, ?_⟩
  · intro prefixValues range scalars isRange
    rw [scalarPrefix_indexStyle]
    exact oneRange_indexStyle range scalars isRange
  · intro prefixValues slices range scalars unitRange
    rw [List.append_assoc, scalarPrefix_indexStyle]
    exact unitRangeAfterSlices_indexStyle slices range scalars unitRange
  · intro scalars
    simpa only [List.append_nil, viewIndexing] using scalarPrefix_indexStyle scalars []
  · intro axis second scalars
    exact oneRange_indexStyle (.slice second) scalars rfl
  · intro axis range scalars unitRange
    exact unitRangeAfterSlices_indexStyle [axis] range scalars unitRange
  · exact oneRange_indexStyle

inductive CoordinatesFitSize : List I64 → List I64 → Prop
  | nil : CoordinatesFitSize [] []
  | cons {coordinate length : I64} {coordinates dimensions : List I64} :
      ((int64 1).val ≤ coordinate.val ∧ coordinate.val ≤ length.val) →
      CoordinatesFitSize coordinates dimensions →
      CoordinatesFitSize (coordinate :: coordinates) (length :: dimensions)

private theorem oneBasedAxes_coordinates (dimensions : List I64) (oneto : I64 → Axis)
    (first : ∀ length, (oneto length).first = int64 1)
    (last : ∀ length, (oneto length).last = length) :
    ∀ coordinates, coordinatesInAxes (dimensions.map oneto) coordinates ↔
      CoordinatesFitSize coordinates dimensions := by
  induction dimensions with
  | nil =>
      intro coordinates
      cases coordinates with
      | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
      | cons value rest =>
          constructor
          · intro invalid; cases invalid
          · intro invalid; cases invalid
  | cons length dimensions ih =>
      intro coordinates
      cases coordinates with
      | nil =>
          constructor
          · intro invalid; cases invalid
          · intro invalid; cases invalid
      | cons coordinate coordinates =>
          change ((oneto length).first.val ≤ coordinate.val ∧
            coordinate.val ≤ (oneto length).last.val ∧
            coordinatesInAxes (dimensions.map oneto) coordinates) ↔ _
          rw [first, last]
          constructor
          · rintro ⟨lower, upper, remaining⟩
            exact .cons ⟨lower, upper⟩ ((ih coordinates).mp remaining)
          · intro selected
            cases selected with
            | cons head tail => exact ⟨head.1, head.2, (ih coordinates).mpr tail⟩

def DefaultParentIndicesContract : Prop :=
  ∀ {P : Type} (parent : P) (size : P → List I64) (oneto : I64 → Axis),
    (∀ length, (oneto length).first = int64 1) →
    (∀ length, (oneto length).last = length) →
    (parentindicesArray parent size oneto).length = (size parent).length ∧
    ∀ coordinates, coordinatesInAxes (parentindicesArray parent size oneto) coordinates ↔
      CoordinatesFitSize coordinates (size parent)

theorem defaultParentIndicesContract_proven : DefaultParentIndicesContract := by
  intro P parent size oneto first last
  exact ⟨List.length_map oneto, oneBasedAxes_coordinates (size parent) oneto first last⟩

def entries : List Entry := [
  entry "subarray-default-parentindices-coordinate-domain"
    ["parentindices(a::AbstractArray)"]
    "Default parentindices has one axis per size dimension and contains exactly the coordinate tuples whose components lie between one and the corresponding dimension size."
    "parentindices documentation; base/subarray.jl:89-109"
    ``DefaultParentIndicesContract ``defaultParentIndicesContract_proven,
  entry "subarray-linear-index-classification"
    ["viewindexing(I::Tuple{})", "viewindexing(I::Tuple{ScalarIndex, Vararg{Any}})",
      "viewindexing(I::Tuple{Slice, Slice, Vararg{Any}})",
      "viewindexing(I::Tuple{Slice, AbstractUnitRange, Vararg{ScalarIndex}})",
      "viewindexing(I::Tuple{Slice, Slice, Vararg{ScalarIndex}})",
      "viewindexing(I::Tuple{AbstractRange{<:ScalarIndex}, Vararg{ScalarIndex}})",
      "viewindexing(I::Tuple{AbstractArray, Vararg{Any}})"]
    "Scalar prefixes preserve indexing style; one varying scalar range and a Slice chain ending in a unit range are linear, whereas every tuple containing an index array is Cartesian."
    "SubArray linear-indexability invariant and comments; base/subarray.jl:52-67"
    ``LinearClassificationContract ``linearClassificationContract_proven,
  entry "subarray-cartesian-selected-write"
    ["setindex!(V::SubArray{T,N}, x, I::Vararg{Int,N})"]
    "A Cartesian view write modifies exactly the independently selected parent coordinates and preserves the view's indices, dimensions, style, offset and stride."
    "view assignment documentation; base/subarray.jl:386-391"
    ``CartesianSetContract ``cartesianSetContract_proven,
  entry "subarray-cartesian-selected-isassigned"
    ["isassigned(V::SubArray{T,N}, I::Vararg{Int,N})"]
    "Assignment state at valid Cartesian view coordinates is the state at the independently selected parent coordinates; an out-of-bounds view coordinate is unassigned."
    "isassigned documentation; base/subarray.jl:414-419"
    ``CartesianIsassignedContract ``cartesianIsassignedContract_proven,
  entry "subarray-extended-coordinate-order"
    ["find_extended_dims(dim, ::ScalarIndex, I...)", "find_extended_dims(dim, i1, I...)",
      "find_extended_dims(dim)", "find_extended_inds(::ScalarIndex, I...)",
      "find_extended_inds(i1, I...)", "find_extended_inds()"]
    "The extended dimensions paired with extended indices are exactly the non-scalar stored indices paired with their original one-based parent dimension numbers, in order, using machine-Int numbering."
    "view dimensions and index-dropping invariant; base/subarray.jl:503-508"
    ``ExtendedCoordinatesContract ``extendedCoordinatesContract_proven,
  refuted "multidimcov-subarray-v2-view-of-view"
    ["unsafe_view(V::SubArray, I::Vararg{ViewIndex})", "_maybe_reindex"]
    "Reading a valid view of a source-constructed view returns the same element as reading the original view at the independently selected coordinates, for arbitrary parent and element types."
    "view documentation; base/subarray.jl:259-280"
    ``GeneralNestedRead ``generalNestedRead_refuted
    "reinterpretarrays-nested-slice-offset" "The source constructs both views; reading coordinate 2 changes from parent element 6 to element 7.",
  refuted "multidimcov-subarray-v2-maybe-reindex"
    ["_maybe_reindex(V, I)", "_maybe_reindex(V, I, ::Tuple{})"]
    "Flattening nested indices preserves every selected element; higher-rank CartesianIndex arrays retain the original view as parent and preserve its reads."
    "view documentation and reindex composition comment; base/subarray.jl:269-288"
    ``GeneralNestedRead ``generalNestedRead_refuted
    "reinterpretarrays-nested-slice-offset" "The IdentityUnitRange-to-Slice flattening preserves axes and indices while shifting the cached parent address.",
  entry "broadcastviews-nested-view-compose"
    ["reindex(idxs::Tuple, subidxs::Tuple)", "reindex(idxs::Tuple{ScalarIndex,Vararg{Any}}, subidxs::Tuple)",
      "reindex(idxs::Tuple{Slice,Vararg{Any}}, subidxs::Tuple)",
      "reindex(idxs::Tuple{AbstractVector,Vararg{Any}}, subidxs::Tuple)",
      "reindex(idxs::Tuple{AbstractMatrix,Vararg{Any}}, subidxs::Tuple)",
      "reindex(idxs::Tuple{AbstractArray,Vararg{Any}}, subidxs::Tuple)"]
    "For scalar, Slice and integer-array subindices, reindexing twice selects the same original coordinates as composing the two selections, including scalar drops and CartesianIndex{1} arrays; parent-index normalization preserves that result."
    "view documentation; reindex composition comment base/subarray.jl:282-312"
    ``ReindexCompositionContract ``reindexCompositionContract_proven,
  entry "multidimcov-subarray-v2-construct-cartesian"
    ["SubArray(::IndexCartesian, parent, indices, dims)", "getindex(V::SubArray{T,N}, I::Vararg{Int,N})"]
    "A Cartesian constructor retains all metadata, rejects a rank mismatch, and reading any valid view coordinate returns precisely the parent element selected by the stored index data."
    "SubArray and view documentation; base/subarray.jl:8-23, 175-183"
    ``CartesianConstructorContract ``cartesianConstructorContract_proven,
  entry "multidimcov-subarray-v2-reindex"
    ["reindex(::Tuple{}, ::Tuple{})", "reindex(::Tuple{ScalarIndex,Vararg{Any}}, ::Tuple)",
      "reindex(::Tuple{Slice,Vararg{Any}}, ::Tuple)", "reindex(::Tuple{AbstractVector,Vararg{Any}}, ::Tuple)",
      "reindex(::Tuple{AbstractMatrix,Vararg{Any}}, ::Tuple)", "reindex(::Tuple{AbstractArray,Vararg{Any}}, ::Tuple)"]
    "Reindexing valid view coordinates returns exactly the independently selected parent coordinates, including expansion of CartesianIndex results; those coordinates remain inside the parent axes."
    "view documentation and reindex comments; base/subarray.jl:282-312"
    ``ReindexPointContract ``reindexPointContract_proven,
  refuted "multidimcov-subarray-v2-pointer-fast"
    ["pointer(V::FastSubArray, i::Int)"]
    "A pointer into a non-contiguous fast view points at the parent element selected by its stored indices."
    "pointer documentation; base/subarray.jl:510"
    ``GeneralFastPointer ``generalFastPointer_refuted
    "reinterpretarrays-nested-slice-offset" "The strided Slice path points at parent element 9 instead of element 5.",
  refuted "multidimcov-subarray-v2-setindex-fast-vector"
    ["setindex!(V::FastSubArray{<:Any,1}, x, i::Int)"]
    "A fast vector write applies the parent's assignment at the independently selected parent coordinate, retaining the view; bounds errors propagate before mutation."
    "view documentation; base/subarray.jl:175-183, 398-403"
    ``GeneralFastVectorWrite ``generalFastVectorWrite_refuted
    "reinterpretarrays-nested-slice-offset" "Writing view coordinate 2 changes parent element 7 instead of element 6.",
  refuted "multidimcov-subarray-v2-construct-linear"
    ["SubArray(::IndexLinear, parent, indices, dims)", "_compute_linear_layout", "_reindexlinear"]
    "A fast linear constructor retains parent, indices, dimensions and index style, and its cached address agrees with the independently selected parent coordinates."
    "SubArray and view documentation; base/subarray.jl:8-23, 175-183"
    ``GeneralLinearConstruction ``generalLinearConstruction_refuted
    "reinterpretarrays-nested-slice-offset" "An in-bounds Slice obtained by flattening an identity-indexed view shifts the cached address.",
  refuted "multidimcov-subarray-v2-getindex-fast"
    ["getindex(V::FastSubArray, i::Int)", "SubArray(parent, indices)"]
    "Every in-bounds fast read returns the parent element selected by the stored indices; failed bounds checks propagate before reading the parent."
    "view documentation; base/subarray.jl:175-183, 330-335"
    ``GeneralFastRead ``generalFastRead_refuted
    "reinterpretarrays-nested-slice-offset" "The generic fast read uses parent index 7 instead of 6.",
  refuted "multidimcov-subarray-v2-getindex-fast-vector"
    ["getindex(V::FastSubArray{<:Any,1}, i::Int)", "SubArray(parent, indices)"]
    "Every in-bounds fast vector read returns the parent element selected by the stored indices; failed bounds checks propagate before reading the parent."
    "view documentation; base/subarray.jl:175-183, 339-344"
    ``GeneralFastVectorRead ``generalFastVectorRead_refuted
    "reinterpretarrays-nested-slice-offset" "The vector specialization uses the same shifted cached address.",
  refuted "multidimcov-subarray-v2-isassigned-fast-vector"
    ["isassigned(V::FastSubArray{<:Any,1}, i::Int)"]
    "An in-bounds fast vector position is assigned exactly when the selected parent position is assigned; positions outside the view are unassigned."
    "isassigned documentation; base/subarray.jl:426-431"
    ``GeneralFastVectorAssigned ``generalFastVectorAssigned_refuted
    "reinterpretarrays-nested-slice-offset" "The shifted parent position can be assigned while the selected position is unassigned.",
  refuted "multidimcov-subarray-v2-offset1"
    ["compute_offset1", "compute_stride1", "_reindexlinear"]
    "The computed cached offset and stride map every valid view coordinate to its independently selected parent coordinate."
    "linear-indexing invariant; base/subarray.jl:17-18, 471-485"
    ``GeneralOffsetCorrect ``generalOffsetCorrect_refuted
    "reinterpretarrays-nested-slice-offset" "The matrix Slice branch subtracts the original parent-axis origin.",
  refuted "multidimcov-subarray-v2-pointer-contiguous"
    ["pointer(V::FastContiguousSubArray, i::Int)"]
    "A pointer into a contiguous fast view points at the parent element selected by its indices."
    "pointer documentation; base/subarray.jl:511"
    ``GeneralContiguousPointer ``generalContiguousPointer_refuted
    "reinterpretarrays-nested-slice-offset" "The contiguous pointer is one element past the selected parent element.",
  entry "reinterpretarrays-view-linear-index"
    ["view(A, r, c...)", "SubArray(::IndexLinear, parent, indices, dims)",
      "compute_stride1", "compute_offset1", "compute_linindex", "_reindexlinear"]
    "For a first-dimension integer range and fixed remaining coordinates, the cached address is the column-major parent address of the selected range element, with machine-Int wrapping."
    "view documentation; base/subarray.jl:175-183"
    ``RangeViewAddress ``rangeViewAddress_proven,
  entry "subarray-dataids-membership" ["dataids(A::SubArray)", "_splatmap"]
    "The data identifiers of a view contain precisely the identifiers of its parent and stored index arrays."
    "aliasing invariant; base/subarray.jl:112-114"
    ``DataidsContainsParentAndIndices ``dataidsContainsParentAndIndices_proven,
  entry "subarray-sizeof-machine-bytes" ["sizeof(V::SubArray)", "sizeof(V::SubArray{<:Any,<:Any,<:Array})"]
    "View byte size is the element count times element storage size, with the machine-Int overflow behavior."
    "sizeof documentation; base/subarray.jl:75-76"
    ``SizeofMachineBytes ``sizeofMachineBytes_proven,
  entry "subarray-constructor-retains-parent-indices"
    ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)", "parent(V::SubArray)", "parentindices(V::SubArray)"]
    "A rank-valid inner constructor retains the parent, exact parent-index tuple, axes, dimensions, index style, and cached layout."
    "SubArray and parentindices documentation; base/subarray.jl:8-23, 86-107"
    ``ConstructorRetainsParentAndIndices ``constructorRetainsParentAndIndices_proven,
  entry "subarray-constructor-rejects-rank"
    ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)", "check_parent_index_match(parent, indices)",
      "check_parent_index_match(parent, ::NTuple{N, Bool})"]
    "A parent/index rank mismatch fails before any SubArray is returned, with the two ranks in the ArgumentError."
    "base/subarray.jl:19-23, 46-49"
    ``ConstructorRejectsWrongRank ``constructorRejectsWrongRank_proven,
  entry "subarray-copy-nonscalar-selection" ["Base.copy(V::SubArray)"]
    "Copying a positive-rank view returns exactly the parent selection, including any parent indexing error."
    "copy documentation; base/subarray.jl:78-84"
    ``CopyNonScalarSelection ``copyNonScalarSelection_proven,
  entry "subarray-isassigned-outside-view"
    ["isassigned(V::SubArray{T,N}, I::Vararg{Int,N})", "isassigned(V::FastSubArray, i::Int)",
      "isassigned(V::FastSubArray{<:Any, 1}, i::Int)"]
    "An index outside the view is unassigned without consulting or reindexing the parent."
    "isassigned documentation; base/subarray.jl:414-431"
    ``IsassignedOutsideView ``isassignedOutsideView_proven,
  entry "multidimcov-subarray-v2-linindex"
    ["compute_linindex(parent, I::NTuple{N,Any}) where N", "compute_linindex(f, s, IP, I)"]
    "The first parent address is the column-major weighted sum of the first stored indices, with machine-Int wrapping; the first index error propagates."
    "base/subarray.jl:486-501; LinearIndices documentation"
    ``LinindexContract ``linindexContract_proven,
  entry "multidimcov-subarray-v2-linindex-step"
    ["compute_linindex(f, s, IP::Tuple, I::Tuple{Any, Any, Vararg{Any}})"]
    "For every accumulator and stride, processing the indices gives the column-major weighted sum of their first coordinates, modulo machine Int arithmetic."
    "base/subarray.jl:491-495; LinearIndices documentation"
    ``LinindexStepContract ``linindexStepContract_proven,
  entry "multidimcov-subarray-v2-linindex-last"
    ["compute_linindex(f, s, IP::Tuple, I::Tuple{Any})"]
    "The final coordinate contributes its distance from the axis origin times the parent stride, and preserves a failed first-index lookup."
    "base/subarray.jl:496-500; LinearIndices documentation"
    ``LinindexLastContract ``linindexLastContract_proven,
  refuted "reinterpretarrays-nested-slice-offset"
    ["view(::SubArray, ::Colon)", "reindex", "compute_offset1", "getindex(V::FastSubArray, i::Int)"]
    "A colon view of an identity-indexed matrix slice retains the parent coordinates of the slice."
    "view docstring base/subarray.jl:175-183; base/subarray.jl:276-280, 480-481"
    ``NestedColonViewCorrect ``nestedColonViewCorrect_refuted
    "reinterpretarrays-nested-slice-offset" "The flattened Slice path shifts the cached linear index by lo - 1.",
  entry "subarray-unaliascopy-keeps-layout"
    ["unaliascopy(A::SubArray)"]
    "unaliascopy preserves the view's cached offsets, index style, dimensions, and transformed parent indices."
    "base/subarray.jl:115-115"
    ``UnaliascopyKeepsCachedLayout ``unaliascopyKeepsCachedLayout_proven,
  entry "subarray-size-index-axes"
    ["size(V::SubArray)", "axes(S::SubArray)", "_indices_sub(::Real, I...)", "_indices_sub()",
      "_indices_sub(i1::AbstractArray, I...)"]
    "A view's dimensions are the lengths of the axes selected by its stored non-scalar indices."
    "view docstring; base/subarray.jl:525-531"
    ``SubArraySizeMatchesIndexAxes ``subArraySizeMatchesIndexAxes_proven,
  entry "subarray-fast-bounds-errors"
    ["getindex(V::FastSubArray, i::Int)", "getindex(V::FastSubArray{<:Any, 1}, i::Int)",
      "setindex!(V::FastSubArray, x, i::Int)", "setindex!(V::FastSubArray{<:Any, 1}, x, i::Int)"]
    "Fast-view reads and writes propagate the bounds error before accessing the parent."
    "base/subarray.jl:330-344, 386-403"
    ``FastViewBoundsErrors ``fastViewBoundsErrors_proven,
  entry "subarray-fast-write-readback"
    ["getindex(V::FastSubArray, i::Int)", "setindex!(V::FastSubArray, x, i::Int)"]
    "After an in-bounds fast-view write, reading that view position returns the assigned value; other parent positions remain unchanged under the parent array's setindex contract."
    "view docstring base/subarray.jl:175-183"
    ``FastSubArrayWriteReadback ``fastSubArrayWriteReadback_proven,
  entry "subarray-fast-vector-write-readback"
    ["getindex(V::FastSubArray{<:Any, 1}, i::Int)", "setindex!(V::FastSubArray{<:Any, 1}, x, i::Int)"]
    "After an in-bounds one-dimensional fast-view write, reading that view position returns the assigned value; other parent positions remain unchanged under the parent array's setindex contract."
    "view docstring base/subarray.jl:175-183"
    ``FastVectorSubArrayWriteReadback ``fastVectorSubArrayWriteReadback_proven,
  refuted "broadcastviews-stride-zero-dim"
    ["stride(::SubArray, ::Integer)", "strides(::SubArray)", "substrides"]
    "stride(V, d) returns a value for every view of an Array with integer, Colon, or integer-range indices and every positive dimension."
    "stride documentation; base/abstractarray.jl:580-582, 597-607"
    ``SubArrayStrideTotal ``subArrayStrideTotal_refuted
    "stride-zero-dim" "A zero-dimensional view has empty strides and size, so the past-end stride branch errors.",
  entry "multidimcov-subarray-v2-maybe-reindex-cartesian"
    ["_maybe_reindex(V, I, ::Tuple{AbstractArray{<:AbstractCartesianIndex}, Vararg{Any}})",
      "getindex(V::SubArray{T,N}, I::Vararg{Int,N})", "viewindexing(I::Tuple{AbstractArray,Vararg{Any}})"]
    "A CartesianIndex array of element rank other than one retains the original view as parent; every selected element of the nested view equals the original view at the independently selected coordinates, including after index normalization."
    "view documentation and reindex comments; base/subarray.jl:259-280"
    ``CartesianArrayFallbackContract ``cartesianArrayFallbackContract_proven,
  entry "multidimcov-subarray-v2-viewindexing-scalar"
    ["viewindexing(I::Tuple{ScalarIndex, Vararg{Any}})"]
    "A leading scalar does not change the IndexStyle assigned to the remaining indices."
    "comments base/subarray.jl:51-66"
    ``LeadingScalarIndexStyle ``leadingScalarIndexStyle_proven,
  entry "multidimcov-subarray-v2-splatmap" ["_splatmap(f, t::Tuple)"]
    "_splatmap(f, t) is the in-order concatenation (f(t[1])..., f(t[2])..., ...); the first exception of f propagates."
    "invariant: dataids(A::SubArray) collects the data ids of every index, base/subarray.jl:112-114"
    ``SplatMapOrder ``splatMapOrder_proven,
  entry "multidimcov-subarray-v2-reshape-parent-same"
    ["_maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N}"]
    "_maybe_reshape_parent returns the parent itself when its rank equals the number of effective indices, as reshape(A, Val(N)) does for an N-dimensional A."
    "reshape docstring base/reshapedarray.jl:86-121; base/reshapedarray.jl:186"
    ``ReshapeParentSameRank ``reshapeParentSameRank_proven,
  entry "multidimcov-subarray-v2-check-mismatch"
    ["check_parent_index_match(parent, ::NTuple{N, Bool}) where {N}"]
    "check_parent_index_match on any other parent throws ArgumentError(\"number of indices (N) must match the parent dimensionality (d)\") with d = ndims(parent), 0 for a number."
    "error message base/subarray.jl:48-49"
    ``ParentIndexMismatchContract ``parentIndexMismatchContract_proven,
  entry "multidimcov-subarray-v2-axes"
    ["axes(S::SubArray)", "_indices_sub(::Real, I...)", "_indices_sub()", "_indices_sub(i1::AbstractArray, I...)"]
    "axes(V) contains the axes of every stored non-scalar index in order."
    "view docstring; base/subarray.jl:525-531"
    ``SubArrayAxesContract ``subArrayAxesContract_proven,
  entry "multidimcov-subarray-v2-axes1"
    ["axes1(S::SubArray)", "axes1(::SubArray{<:Any,0})", "_axes1_sub()",
      "_axes1_sub(::Real, I...)", "_axes1_sub(::AbstractArray{<:Any,0}, I...)",
      "_axes1_sub(i1::AbstractArray, I...)"]
    "axes1(V) is the first axis of axes(V), or OneTo(1) for a zero-dimensional view."
    "axes docstring; base/subarray.jl:533-541"
    ``Axes1ContractAll ``axes1ContractAll_proven,
]

end JuliaLean.Proofs.base.subarray
