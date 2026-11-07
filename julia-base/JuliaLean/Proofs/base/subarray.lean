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
      substridesScalar, substridesScalarSource, JuliaLean.base.subarray.Models1Group17.tupleTail,
      substridesEmpty, List.drop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hTotal := h strideCounterexampleOps view (int64 1)
    hSupported hAxes ⟨[], hStrides, by simp [view]⟩ (by decide)
  obtain ⟨stride, hStride⟩ := hTotal
  have hError : strideSubArrayConfigured strideCounterexampleOps view (int64 1) =
      .error .boundsError := by
    simp [strideSubArrayConfigured, strideSubArray, strideSubArraySource, view, hStrides,
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
    computeStride1RangeSource,
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
    computeOffset1Range, computeOffset1RangeSource, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem offset_slice_matrix {P : Type} (ops : ParentArrayOps P) (parent : P)
    (axis : Axis) (column stride linear first : I64)
    (notVector : ops.isVector parent = false)
    (lin : computeLinindexWithOps ops parent [.slice axis, .scalar column] = .ok linear)
    (axisFirst : axisFirstAt (ops.axes parent) (int64 1) = .ok first) :
    computeOffset1WithOps ops parent stride [.slice axis, .scalar column] =
      .ok (isub linear (imul stride first)) := by
  simp [computeOffset1WithOps, computeOffset1, findExtendedDimsDispatch,
    findExtendedIndicesDispatch, computeOffset1Dispatch, notVector,
    computeOffset1Slice, computeOffset1SliceSource, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

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
      computeStride1RangeSource,
      stepValue, imul_one_left, Bind.bind, Except.bind]
  have offset : computeOffset1WithOps ops parent step indices = .ok (isub origin step) := by
    simp only [computeOffset1WithOps, computeOffset1, indices, findExtendedDimsDispatch,
      findExtendedIndicesDispatch, scalar_dims, scalar_indices]
    cases columns with
    | nil =>
        have isVector : ops.isVector parent = true := by simpa using vector
        simp [computeOffset1Dispatch, isVector, Index.isRange, computeOffset1VectorRange,
          computeOffset1VectorRangeSource,
          rangeFirst, rangeAxisFirst, origin, block, columnMajorOffset, imul_zero,
          iadd_zero, imul_comm step (int64 1), imul_one_left,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
    | cons column columns =>
        have notVector : ops.isVector parent = false := by simpa using vector
        simp only [indices, List.map_cons] at lin
        simp [computeOffset1Dispatch, notVector, Index.isRange, computeOffset1Range,
          computeOffset1RangeSource,
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
    computeOffset1Slice, computeOffset1SliceSource, lin, axisFirst, Bind.bind, Except.bind, Pure.pure, Except.pure]

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
          if arguments.length < rank then return ← .error .boundsError
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
              simp only [List.length_append, List.length_cons, List.length_map]
              split <;> (first | omega | rfl)

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
              simp only [List.length_append, List.length_cons]
              split <;> (first | omega | rfl)

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

def ShapeVolume (shape : List I64) : Int := (shape.map (fun size => size.val)).prod

def TrimmedShapeStorageVolume : Prop :=
  ∀ {A : Type} (index : A) (rest : List A) (tail : List A → List I64)
    (empty : A → Bool) (zero maximum length : A → I64) (rank : Nat),
    ShapeVolume (trimmedShapeScalar index rest tail) = ShapeVolume (tail rest) ∧
    ShapeVolume (trimmedShapeAbstractRange index rest empty zero maximum tail) =
      (if empty index then zero index else maximum index).val * ShapeVolume (tail rest) ∧
    ShapeVolume (trimmedShapeDenseRange index rest length tail) =
      (length index).val * ShapeVolume (tail rest) ∧
    ShapeVolume (trimmedShapeScalarArray index rest length tail) =
      (length index).val * ShapeVolume (tail rest) ∧
    ShapeVolume (trimmedShapeCartesianZero index rest tail) = ShapeVolume (tail rest) ∧
    ShapeVolume (trimmedShapeCartesian rank index rest length tail) =
      (length index).val * ShapeVolume (tail rest)

def SelectorRanks (indices : List Index) : Nat :=
  (indices.map (fun index => if index.isScalar then 0
    else if index = .colon then 1 else index.indexAxes.length)).sum

def TrimmedSelectorRanks : Prop :=
  (∀ {A : Type} (index : A) (rest : List A) (axes : A → List Axis)
      (tail : List A → List Index) colon first,
    SelectorRanks (trimmedParentIndices index rest axes colon tail) =
      (axes index).length + SelectorRanks (tail rest) ∧
    SelectorRanks (trimmedViewIndices index rest axes colon tail) =
      (axes index).length + SelectorRanks (tail rest) ∧
    SelectorRanks (trimmedViewCartesianZero index rest axes first tail) =
      SelectorRanks (tail rest) ∧
    SelectorRanks (trimmedParentDenseRange index rest tail) =
      1 + SelectorRanks (tail rest) ∧
    SelectorRanks (trimmedParentCartesianZero index rest tail) = SelectorRanks (tail rest)) ∧
  (∀ index rest tail,
    SelectorRanks (trimmedParentRange index rest tail) =
      SelectorRanks [index] + SelectorRanks (tail rest))

def DenseRangeTrimExtent : Prop :=
  ∀ index length oftype oneto,
    (∀ count, Index.indexAxes (oneto count) = [{first := int64 1, last := count}]) →
    (∀ original dense, Index.indexAxes (oftype original dense) = Index.indexAxes dense) →
    Index.indexAxes (trimmedIndexDenseRange index length oftype oneto) =
      [{first := int64 1, last := length index}]

def CartesianTrimEachindexFailure : Prop :=
  ∀ {A AxisValue Axes Cartesian Shaped Result : Type} rank (index : A)
    (eachindex : IndexStyle → A → Jl AxisValue)
    (cartesian : AxisValue → List I64 → Jl Cartesian)
    (reshape : Cartesian → Axes → Jl Shaped) (axes : A → Jl Axes)
    (oftype : A → Shaped → Jl Result) error,
    eachindex .linear index = .error error →
      trimmedIndexCartesianSource rank index eachindex cartesian reshape axes oftype = .error error

def ArrayCopyAllocationFailure : Prop :=
  ∀ {P T S : Type} (view : SubArray P T) allocate trimShape trimParent colon
    makeView copyTo (makeSource : SubArray P T → List Index → Jl S)
    trimView trimIndex layout construct error,
    allocate (trimShape view.indices) = .error error →
      unaliascopyArraySubArray view allocate trimShape trimParent colon makeView copyTo
        makeSource trimView trimIndex layout construct = .error error

def ViewBoundsFailure : Prop :=
  ∀ {A R : Type} (array : A) indices unalias toIndices checkBounds ndims remove
    reshape indexNdims (unsafeView : A → List Index → Jl R) error,
    checkBounds array ((toIndices array indices).map (unalias array)) = .error error →
      viewArray array indices unalias toIndices checkBounds ndims remove reshape
        indexNdims unsafeView = .error error

def SubstridesEmptyErrors : Prop :=
  ∀ index rest step recurse,
    substridesScalar [] index rest recurse =
      .error (.argumentError "Cannot call tail on an empty tuple.") ∧
    substridesSlice [] index rest recurse =
      .error (.argumentError "tuple must be non-empty") ∧
    substridesRange [] index rest step recurse =
      .error (.argumentError "tuple must be non-empty")

def StrideComparisonFailure : Prop :=
  ∀ {V D : Type} (view : V) (dimension : D) ndims le strides size get last rank error,
    ndims view = .ok rank → le dimension rank = .error error →
      strideSubArraySource view dimension ndims le strides size get last = .error error

def StrideLastErrorPrecedence : Prop :=
  ∀ {V D : Type} (view : V) (dimension : D) ndims le strides size get last rank values error,
    ndims view = .ok rank → le dimension rank = .ok false →
    strides view = .ok values → last values = .error error →
      strideSubArraySource view dimension ndims le strides size get last = .error error

def ColonNormalizationFailure : Prop :=
  ∀ {V R X : Type} (view : V) (value : X) normalize
    (get : V → List Index → Jl R) (set : V → X → List Index → Jl V) error,
    normalize view [.colon] = .error error →
      getindexFastContiguousColonSource view normalize get = .error error ∧
      setindexFastColonSource view value normalize set = .error error

def ContiguousRangeBoundsFailure : Prop :=
  ∀ {P T I O Q : Type} (view : SubArray P T) (index : I) check reindex
    (get : P → Q → Jl O) error,
    check view index = .error error →
      getindexFastContiguousRange view index check reindex get = .error error

def SetRangeBoundsFailure : Prop :=
  ∀ {P T R Q : Type} (view : SubArray P T) (value : R) (indices : Q) check reindex set error,
    check view indices = .error error →
      setindexFastUnitRange view value indices check reindex set = .error error

def StridesParentFailure : Prop :=
  ∀ {P T : Type} (view : SubArray P T) strides recurse error,
    strides view.parent = .error error → stridesSubArray view strides recurse = .error error

def PrintReindexFailure : Prop :=
  ∀ {P T D : Type} (view : SubArray P T) (i j : D) text reindex normalize matrix vector error,
    (reindex view.indices [i, j] = .error error →
      replaceInPrintMatrixSource view i j text reindex normalize matrix = .error error) ∧
    (reindex view.indices [i] = .error error →
      replaceInPrintVectorSource view i j text reindex normalize vector = .error error)

def UnsafeWrapPointerFailure : Prop :=
  ∀ {V Pointer Result : Type} (view : V) (pointer : V → Jl Pointer) size
    (wrap : Pointer → List I64 → Jl Result) error,
    pointer view = .error error →
      unsafeWrapContiguousSubArraySource view pointer size wrap = .error error

def OffsetFirstError : Prop :=
  (∀ index stride first axes error, first index = .error error →
    computeOffset1VectorRange index stride first axes = .error error) ∧
  (∀ {P : Type} (parent : P) stride dimension index indices linear parentAxis rangeAxis error,
    linear parent indices = .error error →
      computeOffset1Slice parent stride dimension indices linear parentAxis = .error error ∧
      computeOffset1Range parent stride index indices linear rangeAxis = .error error ∧
      computeOffset1Fallback parent stride indices linear = .error error)

def ElsizeIgnoresViewMetadata : Prop :=
  ∀ {P T U : Type} (left : SubArray P T) (right : SubArray P U) elsize,
    elsizeSubArray left elsize = elsizeSubArray right elsize

def HasOffsetIgnoresCachedLayout : Prop :=
  ∀ {P Q T : Type} (view : SubArray P T) (parent : Q) offset stride hasOffset,
    hasOffsetAxesSubArray (T := T)
      ⟨parent, view.indices, offset, stride, view.linear, view.dimensions⟩ hasOffset =
      hasOffsetAxesSubArray view hasOffset
def RangeViewSelectionFailure : Prop :=
  (∀ {A B R : Type} (parent : A) (selector : B) (get : A → B → Jl R) e,
    get parent selector = .error e →
      viewUnitRangeUnitRange parent selector get = .error e ∧
      viewUnitRangeStepRange parent selector get = .error e ∧
      viewStepRangeAbstractRange parent selector get = .error e ∧
      viewStepRangeLenOrdinalRange parent selector get = .error e ∧
      viewLinRangeOrdinalRange parent selector get = .error e) ∧
  (∀ {A R : Type} (parent : A) (get : A → Index → Jl R) e,
    get parent .colon = .error e →
      viewAbstractRangeColon parent .colon get = .error e)

def ReindexArrayMissingCoordinates : Prop :=
  ∀ rank index rest subindices get recurse,
    subindices.length < rank →
      reindexArray rank index rest subindices get recurse = .error .boundsError

def RangeBroadcastFailure : Prop :=
  (∀ {V I M A R : Type} (view : V) (indices : I) offset stride
      (multiply : I64 → I → Jl M) (add : I64 → M → Jl A)
      (materialize : A → Jl R) error,
    multiply (stride view) indices = .error error →
      reindexLinearUnitRangeSource view indices offset stride multiply add materialize =
        .error error) ∧
  (∀ {V I A R : Type} (view : V) (indices : I) offset
      (add : I64 → I → Jl A) (materialize : A → Jl R) error,
    add (offset view) indices = .error error →
      reindexLinearContiguousUnitRangeSource view indices offset add materialize = .error error)

def ParentStridePaddingFailure : Prop :=
  ∀ {P : Type} (parent : P) indices axes fill recurse error,
    fill (axes parent) {first := int64 1, last := int64 1} indices.length = .error error →
      computeStride1 parent indices axes fill recurse = .error error

def CartesianPointerSetupFailure : Prop :=
  ∀ {P T R : Type} (view : SubArray P T) indices first strides get
    (pointer : P → I64 → Jl R) error,
    first view = .error error →
      pointerCartesianSubArray view indices first strides get pointer = .error error

def FirstIndexCalleeFailure : Prop :=
  (∀ {V I Product R : Type} (view : V) offset stride (first : V → Jl I)
      (mul : I64 → I → Jl Product) (add : I64 → Product → Jl R) error,
    first view = .error error →
      firstIndexFastSubArraySource view offset stride first mul add = .error error) ∧
  (∀ {P T : Type} (view : SubArray P T) linear error,
    linear view.parent view.indices = .error error →
      firstIndexSubArray view linear = .error error)

def InvalidStrideExceptionClass : Prop :=
  ∀ stride axes index typeName,
    ∃ message, computeStride1Invalid stride axes index typeName =
      .error (.argumentError message)

def StrideStepConversionFailure : Prop :=
  ∀ {S I Step R : Type} (stride : S) (index : I) (step : I → Jl Step)
    (convert : Step → Jl I64) (mul : S → I64 → Jl R) increment error,
    step index = .ok increment → convert increment = .error error →
      computeStride1RangeSource stride index step convert mul = .error error

theorem trimmedSelectorRanks_proven : TrimmedSelectorRanks := by
  constructor
  · intro A index rest axes tail colon first
    simp [SelectorRanks, trimmedParentIndices, trimmedParentIndicesSource,
      trimmedViewIndices, trimmedViewIndicesSource, trimmedViewCartesianZero,
      trimmedViewCartesianZeroSource, trimmedParentDenseRange, trimmedParentCartesianZero,
      List.map_append, List.map_map, Function.comp_def, Index.isScalar, Index.indexAxes]
    constructor <;> induction axes index <;> simp_all [Nat.add_comm]
  · intros
    simp [SelectorRanks, trimmedParentRange]

private theorem shapeVolume_padding (n : Nat) (tail : List I64) :
    ShapeVolume (List.replicate n (int64 1) ++ tail) = ShapeVolume tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [ShapeVolume, List.replicate_succ, show (int64 1).val = 1 by decide] using ih

theorem trimmedShapeStorageVolume_proven : TrimmedShapeStorageVolume := by
  unfold TrimmedShapeStorageVolume
  intros
  simp [trimmedShapeScalar, trimmedShapeAbstractRange, trimmedShapeDenseRange,
    trimmedShapeScalarArray, trimmedShapeCartesianZero, trimmedShapeCartesian,
    show ∀ x xs, ShapeVolume (x :: xs) = x.val * ShapeVolume xs from fun _ _ => rfl,
    shapeVolume_padding, show (int64 1).val = 1 by decide]

theorem cartesianTrimEachindexFailure_proven : CartesianTrimEachindexFailure := by
  intro A AxisValue Axes Cartesian Shaped Result rank index eachindex cartesian reshape axes oftype error h
  simp [trimmedIndexCartesianSource, h, Bind.bind, Except.bind]

theorem arrayCopyAllocationFailure_proven : ArrayCopyAllocationFailure := by
  unfold ArrayCopyAllocationFailure
  intros
  simp_all [unaliascopyArraySubArray, Bind.bind, Except.bind]

theorem viewBoundsFailure_proven : ViewBoundsFailure := by
  unfold ViewBoundsFailure
  intros
  simp_all [viewArray, Bind.bind, Except.bind]

theorem substridesEmptyErrors_proven : SubstridesEmptyErrors := by
  unfold SubstridesEmptyErrors
  intros
  simp [substridesScalar, substridesScalarSource, substridesSlice, substridesSliceSource,
    substridesRange, substridesRangeSource, Models1Group17.tupleTail,
    Models1Group17.tupleFirst, Bind.bind, Except.bind]

theorem strideComparisonFailure_proven : StrideComparisonFailure := by
  unfold StrideComparisonFailure
  intros
  simp_all [strideSubArraySource, Bind.bind, Except.bind]

theorem strideLastErrorPrecedence_proven : StrideLastErrorPrecedence := by
  unfold StrideLastErrorPrecedence
  intros
  simp_all [strideSubArraySource, Bind.bind, Except.bind]

theorem colonNormalizationFailure_proven : ColonNormalizationFailure := by
  unfold ColonNormalizationFailure
  intros
  simp_all [getindexFastContiguousColonSource, setindexFastColonSource, Bind.bind, Except.bind]

theorem contiguousRangeBoundsFailure_proven : ContiguousRangeBoundsFailure := by
  unfold ContiguousRangeBoundsFailure
  intros
  simp_all [getindexFastContiguousRange, Bind.bind, Except.bind]

theorem setRangeBoundsFailure_proven : SetRangeBoundsFailure := by
  unfold SetRangeBoundsFailure
  intros
  simp_all [setindexFastUnitRange, Bind.bind, Except.bind]

theorem stridesParentFailure_proven : StridesParentFailure := by
  unfold StridesParentFailure
  intros
  simp_all [stridesSubArray, Bind.bind, Except.bind]

theorem printReindexFailure_proven : PrintReindexFailure := by
  unfold PrintReindexFailure
  intros
  constructor <;> intro h <;>
    simp [replaceInPrintMatrixSource, replaceInPrintVectorSource, h, Bind.bind, Except.bind]

theorem unsafeWrapPointerFailure_proven : UnsafeWrapPointerFailure := by
  unfold UnsafeWrapPointerFailure
  intros
  simp_all [unsafeWrapContiguousSubArraySource, Bind.bind, Except.bind]

theorem offsetFirstError_proven : OffsetFirstError := by
  constructor
  · intros
    simp_all [computeOffset1VectorRange, computeOffset1VectorRangeSource, Bind.bind, Except.bind]
  · intros
    simp_all [computeOffset1Slice, computeOffset1SliceSource, computeOffset1Range,
      computeOffset1RangeSource, computeOffset1Fallback, computeOffset1FallbackSource,
      Bind.bind, Except.bind]

theorem elsizeIgnoresViewMetadata_proven : ElsizeIgnoresViewMetadata := by
  unfold ElsizeIgnoresViewMetadata
  intros
  rfl

theorem hasOffsetIgnoresCachedLayout_proven : HasOffsetIgnoresCachedLayout := by
  unfold HasOffsetIgnoresCachedLayout
  intros
  rfl

theorem rangeViewSelectionFailure_proven : RangeViewSelectionFailure := by
  constructor
  · intros
    simp_all [viewUnitRangeUnitRange, viewUnitRangeStepRange, viewStepRangeAbstractRange,
      viewStepRangeLenOrdinalRange, viewLinRangeOrdinalRange]
  · intros
    simp_all [viewAbstractRangeColon]

theorem reindexArrayMissingCoordinates_proven : ReindexArrayMissingCoordinates := by
  unfold ReindexArrayMissingCoordinates
  intros
  simp_all [reindexArray, reindexArraySource]

theorem rangeBroadcastFailure_proven : RangeBroadcastFailure := by
  constructor <;> intros <;>
    simp_all [reindexLinearUnitRangeSource, reindexLinearContiguousUnitRangeSource,
      Bind.bind, Except.bind]

theorem parentStridePaddingFailure_proven : ParentStridePaddingFailure := by
  unfold ParentStridePaddingFailure
  intros
  simp_all [computeStride1, Bind.bind, Except.bind]

theorem cartesianPointerSetupFailure_proven : CartesianPointerSetupFailure := by
  unfold CartesianPointerSetupFailure
  intros
  simp_all [pointerCartesianSubArray, pointerCartesianSubArraySource, Bind.bind, Except.bind]

theorem firstIndexCalleeFailure_proven : FirstIndexCalleeFailure := by
  constructor <;> intros <;>
    simp_all [firstIndexFastSubArraySource, firstIndexSubArray, parentSubArray,
      Bind.bind, Except.bind]

theorem invalidStrideExceptionClass_proven : InvalidStrideExceptionClass := by
  unfold InvalidStrideExceptionClass
  intros
  exact ⟨_, rfl⟩

theorem strideStepConversionFailure_proven : StrideStepConversionFailure := by
  unfold StrideStepConversionFailure
  intros
  simp_all [computeStride1RangeSource, Bind.bind, Except.bind]

def entries : List Entry := [
  { id := "subarray-first-index-callee-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["first_index(::FastSubArray)", "first_index(::SubArray)"]
    statement := "Failure of the first-coordinate or parent linear-address lookup propagates before a first parent address is returned."
    source := "base/subarray.jl:464-465", status := .proven, prop := ``FirstIndexCalleeFailure, thm := some ``firstIndexCalleeFailure_proven },
  { id := "subarray-invalid-compute-stride-exception", juliaFile := "base/subarray.jl"
    juliaFns := ["compute_stride1(s, inds, I::Tuple{Any,Vararg{Any}})"]
    statement := "An unsupported strided selector raises ArgumentError independently of the incoming stride and axis values."
    source := "base/subarray.jl:456", status := .proven, prop := ``InvalidStrideExceptionClass, thm := some ``invalidStrideExceptionClass_proven },
  { id := "subarray-stride-step-conversion-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["compute_stride1(s, inds, I::Tuple{AbstractRange,Vararg{Any}})"]
    statement := "A failed range-step conversion to machine Int propagates before stride multiplication."
    source := "base/subarray.jl:454", status := .proven, prop := ``StrideStepConversionFailure, thm := some ``strideStepConversionFailure_proven },
  { id := "subarray-range-broadcast-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["_reindexlinear(::FastSubArray, ::AbstractUnitRange{Int})",
      "_reindexlinear(::FastContiguousSubArray, ::AbstractUnitRange{Int})"]
    statement := "A failed broadcast-expression construction propagates before materialization of the affine range selection."
    source := "base/subarray.jl:328,352", status := .proven, prop := ``RangeBroadcastFailure, thm := some ``rangeBroadcastFailure_proven },
  { id := "subarray-parent-stride-padding-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["compute_stride1(parent::AbstractArray, I::NTuple{N,Any})"]
    statement := "Failure to extend parent axes stops stride computation before recursive selector processing."
    source := "base/subarray.jl:448-449", status := .proven, prop := ``ParentStridePaddingFailure, thm := some ``parentStridePaddingFailure_proven },
  { id := "subarray-cartesian-pointer-setup-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["pointer(::SubArray, ::AbstractCartesianIndex)"]
    statement := "A failed initial-address computation propagates before stride lookup, coordinate reads and parent pointer access."
    source := "base/subarray.jl:513-520", status := .proven, prop := ``CartesianPointerSetupFailure, thm := some ``cartesianPointerSetupFailure_proven },
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
] ++ [
  { id := "subarray-trimmed-shape-volume", juliaFile := "base/subarray.jl"
    juliaFns := ["_trimmedshape"], statement := "Scalar and zero-rank selectors do not enlarge storage; dense selectors contribute their element count, and Cartesian singleton padding does not enlarge storage."
    source := "base/subarray.jl:133-138", status := .proven, prop := ``TrimmedShapeStorageVolume, thm := some ``trimmedShapeStorageVolume_proven },
  { id := "subarray-trimmed-selector-ranks", juliaFile := "base/subarray.jl"
    juliaFns := ["_trimmedpind", "_trimmedvind"], statement := "Trimmed parent selectors retain one dimension per original axis, while scalar coordinates for Cartesian-zero selectors remove those dimensions from the trimmed view."
    source := "base/subarray.jl:141-147", status := .proven, prop := ``TrimmedSelectorRanks, thm := some ``trimmedSelectorRanks_proven },
  { id := "subarray-dense-range-trim-extent", juliaFile := "base/subarray.jl"
    juliaFns := ["_trimmedindex(::Union{UnitRange,StepRange,OneTo})"], statement := "Dense range trimming has one-based axes with the original range length."
    source := "base/subarray.jl:152", status := .todo, prop := ``DenseRangeTrimExtent },
  { id := "subarray-cartesian-trim-index-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["_trimmedindex(::AbstractArray{<:AbstractCartesianIndex{N}})"], statement := "Failure of linear eachindex propagates before Cartesian-index construction, axes lookup, reshape and conversion."
    source := "base/subarray.jl:155-159", status := .proven, prop := ``CartesianTrimEachindexFailure, thm := some ``cartesianTrimEachindexFailure_proven },
  { id := "subarray-array-copy-allocation-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["unaliascopy(::SubArray)"], statement := "Failure to allocate trimmed parent storage stops unaliascopy before any view, copy, index conversion or layout computation."
    source := "base/subarray.jl:119-131", status := .proven, prop := ``ArrayCopyAllocationFailure, thm := some ``arrayCopyAllocationFailure_proven },
  { id := "subarray-view-bounds-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["view(::AbstractArray, ::Vararg)"], statement := "A failed view bounds check propagates before singleton removal, parent reshaping and unsafe construction."
    source := "base/subarray.jl:221-227", status := .proven, prop := ``ViewBoundsFailure, thm := some ``viewBoundsFailure_proven },
  { id := "subarray-empty-stride-tuple-errors", juliaFile := "base/subarray.jl"
    juliaFns := ["substrides"], statement := "An empty parent stride tuple fails at the source tuple tail or first operation, before later range stepping and recursive calls."
    source := "base/subarray.jl:440-442", status := .proven, prop := ``SubstridesEmptyErrors, thm := some ``substridesEmptyErrors_proven },
  { id := "subarray-stride-comparison-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["stride"], statement := "Dimension comparison errors propagate before reading parent strides or view size."
    source := "base/subarray.jl:446", status := .proven, prop := ``StrideComparisonFailure, thm := some ``strideComparisonFailure_proven },
  { id := "subarray-stride-last-error-precedence", juliaFile := "base/subarray.jl"
    juliaFns := ["stride"], statement := "A failed final-stride lookup in the past-rank branch propagates before the size lookup."
    source := "base/subarray.jl:446", status := .proven, prop := ``StrideLastErrorPrecedence, thm := some ``strideLastErrorPrecedence_proven },
  { id := "subarray-colon-normalization-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["getindex(::FastContiguousSubArray, ::Colon)", "setindex!(::FastSubArray, x, ::Colon)"], statement := "Colon normalization errors propagate before selecting or assigning parent data."
    source := "base/subarray.jl:383,412", status := .proven, prop := ``ColonNormalizationFailure, thm := some ``colonNormalizationFailure_proven },
  { id := "subarray-contiguous-range-bounds-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["getindex(::FastContiguousSubArray, ::_OneBasedRanges)"], statement := "A failed range bounds check stops contiguous selection before reindexing or parent access."
    source := "base/subarray.jl:376-381", status := .proven, prop := ``ContiguousRangeBoundsFailure, thm := some ``contiguousRangeBoundsFailure_proven },
  { id := "subarray-range-assignment-bounds-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["setindex!(::FastSubArray, x, ::AbstractUnitRange{Int})"], statement := "A failed range bounds check prevents parent assignment."
    source := "base/subarray.jl:405-410", status := .proven, prop := ``SetRangeBoundsFailure, thm := some ``setRangeBoundsFailure_proven },
  { id := "subarray-parent-strides-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["strides"], statement := "Failure to obtain parent strides propagates before processing stored selectors."
    source := "base/subarray.jl:437", status := .proven, prop := ``StridesParentFailure, thm := some ``stridesParentFailure_proven },
  { id := "subarray-print-reindex-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["replace_in_print_matrix"], statement := "Printing preserves a failed coordinate reindexing before normalization or parent formatting, without converting the input integers first."
    source := "base/subarray.jl:545-550", status := .proven, prop := ``PrintReindexFailure, thm := some ``printReindexFailure_proven },
  { id := "subarray-wrap-pointer-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["unsafe_wrap"], statement := "Pointer failures propagate before querying dimensions or creating a wrapping array."
    source := "base/subarray.jl:553", status := .proven, prop := ``UnsafeWrapPointerFailure, thm := some ``unsafeWrapPointerFailure_proven },
  { id := "subarray-offset-first-error", juliaFile := "base/subarray.jl"
    juliaFns := ["compute_offset1"], statement := "The initial coordinate or linear-index error propagates before later axis-origin lookups."
    source := "base/subarray.jl:471-485", status := .proven, prop := ``OffsetFirstError, thm := some ``offsetFirstError_proven },
  { id := "subarray-elsize-metadata-independence", juliaFile := "base/subarray.jl"
    juliaFns := ["elsize"], statement := "SubArray element storage size depends on the parent type, independently of stored view values and other type bindings."
    source := "base/subarray.jl:458", status := .proven, prop := ``ElsizeIgnoresViewMetadata, thm := some ``elsizeIgnoresViewMetadata_proven },
  { id := "subarray-offset-axis-layout-independence", juliaFile := "base/subarray.jl"
    juliaFns := ["has_offset_axes"], statement := "Changing the parent, cached offset or cached stride cannot change offset-axis detection when the index tuple is unchanged."
    source := "base/subarray.jl:543", status := .proven, prop := ``HasOffsetIgnoresCachedLayout, thm := some ``hasOffsetIgnoresCachedLayout_proven }
,
  { id := "subarray-range-view-selection-failure", juliaFile := "base/subarray.jl"
    juliaFns := ["view(::AbstractUnitRange, ::AbstractUnitRange)", "view(::AbstractUnitRange, ::StepRange)",
      "view(::StepRange, ::AbstractRange)", "view(::StepRangeLen, ::OrdinalRange)",
      "view(::LinRange, ::OrdinalRange)", "view(::AbstractRange, ::Colon)"]
    statement := "A failed immutable-range selection propagates unchanged through the matching view overload."
    source := "base/subarray.jl:230-255", status := .proven, prop := ``RangeViewSelectionFailure, thm := some ``rangeViewSelectionFailure_proven },
  { id := "subarray-reindex-missing-coordinates", juliaFile := "base/subarray.jl"
    juliaFns := ["reindex(::Tuple{AbstractArray{<:Any,N},Vararg{Any}}, ::Tuple)"]
    statement := "An array selector requiring more coordinates than the subindex tuple contains raises BoundsError before indexing that array."
    source := "base/subarray.jl:311-312; base/tuple.jl tuple range indexing", status := .proven,
    prop := ``ReindexArrayMissingCoordinates, thm := some ``reindexArrayMissingCoordinates_proven }
]

end JuliaLean.Proofs.base.subarray

namespace JuliaLean.Proofs.base.subarray

open JuliaLean JuliaLean.Registry JuliaLean.base.subarray

namespace Models1Group17

/-!
All declarations in this section are unproved specifications, not theorems.
They do not assume callee correctness. The new internal models have complete
input quantification over their explicit representations. Partial models are
not presented as complete coverage of generic Julia methods.
-/

/-- Declarative type/representation domain of the finite public shape models.
Built-in range metadata and concrete one-based Array payloads are admitted;
opaque custom methods are not assumed to agree with stored fields.
Source: base/subarray.jl:70,525-543; base/abstractarray.jl:100-118. -/
def ShapeIndexSupported : Index → Prop
  | .scalar _ | .slice _ | .identity _ | .unitRange _ | .oneTo _ |
    .stepRange _ _ _ | .stepRangeLen _ _ _ | .linRange _ _ _ | .mask _ => True
  | .values axes _ | .cartesianValues axes _ _ =>
      ∀ axis ∈ axes, axis.first = int64 1
  | _ => False

/-- Independent retained rank of an index's type: a scalar removes a dimension,
an array contributes its own rank, and a range/logical index contributes one.
Cartesian element rank is deliberately different from array rank here.
Source: base/subarray.jl:525-541; doc/src/devdocs/subarrays.md:33-40. -/
def retainedRankSpec : Index → Nat
  | .scalar _ => 0
  | .values axes _ | .cartesianValues axes _ _ => axes.length
  | .slice _ | .identity _ | .unitRange _ | .oneTo _ | .stepRange _ _ _ |
    .stepRangeLen _ _ _ | .linRange _ _ _ | .mask _ => 1
  | _ => 0

/-- Axes preserve the total type-derived retained rank and every direct
Slice/Identity origin at its global prefix-rank position. Any non-one-based
output axis must come from one of those origin-preserving selectors. This
specifies rank and placement globally rather than replaying _indices_sub's
recursive tuple concatenation. All valid concrete range values, including
negative unchecked-OneTo stops, are quantified.
Source: base/subarray.jl:525-531; base/indices.jl:343-345,370-372;
doc/src/devdocs/subarrays.md:33-40. -/
def FiniteAxesRankAndOrigins : Prop :=
  ∀ {P T : Type} (input : JuliaLean.base.subarray.Models1Group17.ShapeAxesViewInput P T),
    (∀ index ∈ input.view.indices, ShapeIndexSupported index) →
    ∃ axes : List Axis,
      JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite input = some (.ok axes) ∧
      axes.length = (input.view.indices.map retainedRankSpec).sum ∧
      (∀ (position : Nat) (axis : Axis),
        (input.view.indices[position]? = some (.slice axis) ∨
          input.view.indices[position]? = some (.identity axis)) →
        axes[((input.view.indices.take position).map retainedRankSpec).sum]? = some axis) ∧
      (∀ axis ∈ axes, axis.first.val ≠ 1 →
        Index.slice axis ∈ input.view.indices ∨ Index.identity axis ∈ input.view.indices)

/-- Each finite view size coordinate is the mathematical endpoint interval
width represented modulo Int64, and the number of coordinates is the total
retained type rank. The mathematical difference is independent of the source's
machine-length dispatch and wrapping arithmetic; it preserves negative unchecked-OneTo
stops and full-width wrapped counts instead of adding a no-overflow premise.
The actual axes observation is also required to succeed, not assumed correct.
Source: base/subarray.jl:70,525-531; base/range.jl:503,705-706,794-817. -/
def FiniteSizeCoordinateCardinality : Prop :=
  ∀ {P T : Type} (input : JuliaLean.base.subarray.Models1Group17.ShapeAxesViewInput P T),
    (∀ index ∈ input.view.indices, ShapeIndexSupported index) →
    ∃ (axes : List Axis) (sizes : List I64),
      JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite input = some (.ok axes) ∧
      JuliaLean.base.subarray.Models1Group17.sizeSubArrayFinite input = some (.ok sizes) ∧
      axes.length = (input.view.indices.map retainedRankSpec).sum ∧
      sizes.length = axes.length ∧
      (∀ (position : Nat) (axis : Axis), axes[position]? = some axis →
        ∃ size : I64, sizes[position]? = some size ∧
          size.val = (JInt.wrap .i64 (axis.last.val - axis.first.val + 1)).val)

/-- The first-axis observation agrees with the retained coordinate domain of
the whole view. A nonzero-dimensional view returns the first retained axis or
the actual empty tuple when no axes remain. A zero-dimensional view has the
singleton linear coordinate domain containing one. This compares independent
public observations and mathematical domain properties, and does not assume
an axes or axes1 correctness law.
Source: base/subarray.jl:525-541; base/abstractarray.jl:140-142. -/
def FiniteAxes1CoordinateDomain : Prop :=
  ∀ {P T : Type} (input : JuliaLean.base.subarray.Models1Group17.ShapeAxesViewInput P T),
    (∀ index ∈ input.view.indices, ShapeIndexSupported index) →
    ∃ (axes : List Axis) (firstAxis : Option Axis),
      JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite input = some (.ok axes) ∧
      JuliaLean.base.subarray.Models1Group17.axes1SubArrayFinite input = some (.ok firstAxis) ∧
      axes.length = (input.view.indices.map retainedRankSpec).sum ∧
      if input.view.dimensions.length = 0 then
        ∃ axis : Axis, firstAxis = some axis ∧
          axis.first.val ≤ 1 ∧ 1 ≤ axis.last.val ∧
          axis.last.val - axis.first.val + 1 = 1
      else firstAxis = axes.head?

/-- Offset detection is exactly the presence of a non-one-based coordinate
domain among the returned axes. The specification observes output axes rather
than copying the implementation's short-circuit OR over stored indices.
Source: base/subarray.jl:543; base/abstractarray.jl:114-122. -/
def FiniteOffsetAxisCoherence : Prop :=
  ∀ {P T : Type} (input : JuliaLean.base.subarray.Models1Group17.ShapeAxesViewInput P T),
    (∀ index ∈ input.view.indices, ShapeIndexSupported index) →
    ∃ (axes : List Axis) (offset : Bool),
      JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite input = some (.ok axes) ∧
      JuliaLean.base.subarray.Models1Group17.hasOffsetAxesSubArrayFinite input = some (.ok offset) ∧
      (offset = true ↔ ∃ axis ∈ axes, axis.first.val ≠ 1)

/-- Inserting a scalar selector anywhere in a tuple does not change the view's
shape, axes, first-axis observation, or offset-origin trait when the explicit
N parameter is retained. This whole-input transformation includes unknown
tails and checks that scalar insertion cannot force previously skipped custom
semantics to be read. Both complete inputs carry actual representation proofs;
neither function's result is assumed in the premises.
Source: base/subarray.jl:70,525-543; doc/src/devdocs/subarrays.md:33-40. -/
def ScalarInsertionPreservesShapeObservations : Prop :=
  ∀ {P T : Type}
      (original changed : JuliaLean.base.subarray.Models1Group17.ShapeAxesViewInput P T)
      (before after : List Index) (value : I64),
    original.view.indices = before ++ after →
    changed.view.indices = before ++ (Index.scalar value :: after) →
    original.view.dimensions.length = changed.view.dimensions.length →
    JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite changed =
      JuliaLean.base.subarray.Models1Group17.axesSubArrayFinite original ∧
    JuliaLean.base.subarray.Models1Group17.sizeSubArrayFinite changed =
      JuliaLean.base.subarray.Models1Group17.sizeSubArrayFinite original ∧
    JuliaLean.base.subarray.Models1Group17.axes1SubArrayFinite changed =
      JuliaLean.base.subarray.Models1Group17.axes1SubArrayFinite original ∧
    JuliaLean.base.subarray.Models1Group17.hasOffsetAxesSubArrayFinite changed =
      JuliaLean.base.subarray.Models1Group17.hasOffsetAxesSubArrayFinite original


/-- Mathematical effective parent rank of one represented index.
This independent measure describes the index's type, not the removal algorithm.
Source: base/multidimensional.jl:792-799; base/subarray.jl:163-172. -/
def effectiveRank : Index → Nat
  | .cartesian coordinates => coordinates.length
  | .cartesianValues _ rank _ => rank
  | _ => 1

/-- Extensional retention criterion: a scalar survives precisely while its
original prefix has not already consumed every parent dimension. A nonscalar
always survives. This uses original-position prefix sums, not the recursive
model's shrinking tuple of remaining dimensions.
Source: base/subarray.jl:163-172 and multidimensional.jl:792-799. -/
def retainedByPrefix (dimensions : List Bool) (indices : List Index) : List Index :=
  indices.zipIdx.filterMap fun pair =>
    if pair.1.isScalar = false ∨
        ((indices.take pair.2).map effectiveRank).sum < dimensions.length then
      some pair.1
    else none

/-- Singleton removal preserves exactly the original-position prefix-rank
selection, including zero-dimensional and multi-dimensional Cartesian indices.
No bounds-success or correctness-law premise is needed; this is an invariant
of the helper even on inputs not reached after successful view bounds checks.
Source: base/subarray.jl:170-172; multidimensional.jl:792-799. -/
def SingletonPrefixSelection : Prop :=
  ∀ (dimensions : List Bool) (indices : List Index),
    JuliaLean.base.subarray.Models1Group17.removeSingletonIndices dimensions indices =
      retainedByPrefix dimensions indices

/-- Removing scalar dimensions never invents or reorders surviving indices,
and leaves the complete nonscalar subsequence unchanged.
Source: base/subarray.jl:169-172, obvious index-preservation invariant. -/
def SingletonPreservesNonscalars : Prop :=
  ∀ (dimensions : List Bool) (indices : List Index),
    let result := JuliaLean.base.subarray.Models1Group17.removeSingletonIndices dimensions indices
    result.Sublist indices ∧
      result.filter (fun index => !index.isScalar) =
        indices.filter (fun index => !index.isScalar)

/-- Mathematical cardinality of an endpoint-normalized unit range. This
specification does not use Julia's machine `length`, which can wrap.
Source: base/range.jl:425-441; doc/src/manual/arrays.md:619-621. -/
def unitCountSpec (range : Axis) : Nat :=
  (range.last.val - range.first.val + 1).toNat

/-- Mathematical cardinality of a normalized step range, including the full
machine endpoint span. Division and absolute values here are specification
arithmetic, not replacements for any model operation.
Source: base/range.jl:339-398; doc/src/manual/arrays.md:619-621. -/
def stepCountSpec (range : JuliaLean.base.subarray.Models1Group17.StepRangeFields) : Nat :=
  if (0 < range.step.val ∧ range.start.val ≤ range.stop.val) ∨
      (range.step.val < 0 ∧ range.stop.val ≤ range.start.val) then
    (range.stop.val - range.start.val).natAbs / range.step.val.natAbs + 1
  else 0

/-- Independent mathematical size of either concrete selector sequence.
Unlike a signed Int64 observation index, Nat positions also describe elements
beyond typemax(Int64) in a constructible large range.
Source: base/subarray.jl:230-241; base/range.jl:339-441. -/
def selectorCountSpec : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64 → Nat
  | .unit range => unitCountSpec range.endpoints
  | .step range => stepCountSpec range.val

/-- The value at an original zero-based position in the selector's mathematical
sequence. Its use is restricted by `selectorCountSpec` in the properties below;
all real sequence elements are representable by the input endpoint invariant.
Source: base/range.jl:339-441; doc/src/manual/arrays.md:619-621. -/
def selectorValueSpec
    (selector : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64)
    (position : Nat) : Int :=
  match selector with
  | .unit range => range.endpoints.first.val + Int.ofNat position
  | .step range => range.val.start.val + Int.ofNat position * range.val.step.val

/-- Every selected element lies in the parent's mathematical one-based index
domain. This checks the whole selector, even when its length cannot fit Int64.
Source: base/subarray.jl:177-188; doc/src/manual/arrays.md:619-621. -/
def selectedPositionsValid (parentCount : Nat)
    (selector : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64) : Prop :=
  ∀ position : Nat, position < selectorCountSpec selector →
    1 ≤ selectorValueSpec selector position ∧
      selectorValueSpec selector position ≤ Int.ofNat parentCount

/-- A concrete invalid selected element, expressed without limiting the
selector's position to signed-machine indexing. This is an independent bounds
witness, not a restatement of the source's endpoint-check implementation.
Source: base/subarray.jl:177-188; doc/src/manual/arrays.md:619-621. -/
def badSelectedPosition (parentCount : Nat)
    (selector : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64) : Prop :=
  ∃ position : Nat, position < selectorCountSpec selector ∧
    (selectorValueSpec selector position < 1 ∨
      Int.ofNat parentCount < selectorValueSpec selector position)

/-- Public element-selection contract for the explicit UnitRange{Int64}
specialization. A successful view supports exactly the selector's scalar
positions and mathematical sequence, and each value agrees with the
corresponding scalar parent access.
A BoundsError must have an actual bad selected index as a witness; an
OverflowError must come from an empty selector whose computed starting value
cannot have a representable smaller empty stop. Other exception classes are
not allowed for these concrete machine ranges.

This quantifies the entire constructible two-endpoint input type, including
empty ranges and wrapped lengths, with no no-overflow premise. It compares
independent scalar indexing with range selection; it does not assume success
or copy the range-selection body. A negative or zero wrapped length may expose
a disagreement in the pinned source, so this is deliberately an unproved
promise for review, not an assertion that the implementation is correct.
Source: base/subarray.jl:177-188,230-233; base/range.jl:968-972,1002-1026. -/
def UnitRangeViewElementsAndErrors : Prop :=
  ∀ (parent selector : JuliaLean.base.subarray.Models1Group17.UnitRange64),
    let selection := JuliaLean.base.subarray.Models1Group17.OrdinalSelector64.unit selector
    match JuliaLean.base.subarray.Models1Group17.viewUnitRange64 parent selector with
    | .ok result =>
        (result.first.val ≤ result.last.val ∨
          result.last.val = (JInt.wrap .i64 (result.first.val - 1)).val) ∧
        unitCountSpec result = selectorCountSpec selection ∧
        (∀ position : Nat, position < selectorCountSpec selection →
          result.first.val + Int.ofNat position =
            parent.endpoints.first.val + selectorValueSpec selection position - 1) ∧
        selectedPositionsValid (unitCountSpec parent.endpoints) selection ∧
        (∀ (position : I64),
          JuliaLean.base.subarray.Models1Group17.readUnitRange64 result position =
            match JuliaLean.base.subarray.Models1Group17.readUnitRange64 selector.endpoints position with
            | .ok selected =>
                JuliaLean.base.subarray.Models1Group17.readUnitRange64 parent.endpoints selected
            | .error error => .error error)
    | .error .boundsError =>
        badSelectedPosition (unitCountSpec parent.endpoints) selection
    | .error (.overflowError _) =>
        selectorCountSpec selection = 0 ∧
        (JInt.wrap .i64
          (parent.endpoints.first.val + selector.endpoints.first.val - 1)).val = IntTy.i64.min
    | .error _ => False

/-- Public selection and error contract for the concrete Int64 UnitRange/
StepRange view. Success preserves the entire selector cardinality and ordered
sequence and agrees with independently modelled scalar indexing. A BoundsError
requires a genuinely invalid mathematical selector element; OverflowError is
limited to an empty selector whose affine start has no representable neighboring
stop in the required direction. Every normalized endpoint/step combination is
quantified, including typemin steps and wrapped lengths; no no-overflow or
successful-callee premise is used.
Source: base/subarray.jl:177-188,234-237; base/range.jl:1002-1011,1034-1049;
doc/src/manual/arrays.md:619-621. -/
def UnitStepViewElementsAndErrors : Prop :=
  ∀ (parent : JuliaLean.base.subarray.Models1Group17.UnitRange64)
      (selector : JuliaLean.base.subarray.Models1Group17.StepRange64),
    let selection := JuliaLean.base.subarray.Models1Group17.OrdinalSelector64.step selector
    match JuliaLean.base.subarray.Models1Group17.viewUnitRangeStep64 parent selector with
    | .ok result =>
        JuliaLean.base.subarray.Models1Group17.NormalizedStepRange result ∧
        stepCountSpec result = selectorCountSpec selection ∧
        (∀ position : Nat, position < selectorCountSpec selection →
          result.start.val + Int.ofNat position * result.step.val =
            parent.endpoints.first.val + selectorValueSpec selection position - 1) ∧
        selectedPositionsValid (unitCountSpec parent.endpoints) selection ∧
        (∀ position : I64,
          JuliaLean.base.subarray.Models1Group17.readStepRange64 result position =
            match JuliaLean.base.subarray.Models1Group17.readStepRange64 selector.val position with
            | .ok selected =>
                JuliaLean.base.subarray.Models1Group17.readUnitRange64 parent.endpoints selected
            | .error error => .error error)
    | .error .boundsError =>
        badSelectedPosition (unitCountSpec parent.endpoints) selection
    | .error (.overflowError _) =>
        selectorCountSpec selection = 0 ∧
        let start := (JInt.wrap .i64
          (parent.endpoints.first.val + selector.val.start.val - 1)).val
        if selector.val.step.val > 0 then start = IntTy.i64.min
        else start = IntTy.i64.max
    | .error _ => False

/-- Public selection and error contract for the concrete Int64 StepRange view
with either supported ordinal selector. Success preserves the complete ordered
selector sequence and independent scalar reads, including when composed-step
machine multiplication overflows. BoundsError needs an invalid selected element.
The source's empty-stop OverflowError and zero-composed-step ArgumentError are
classified separately, without excluding their inputs from the property.

The mathematical sequence comparison can expose a sign-changing composed-step
overflow even for a four-element parent. This is deliberately an unproved
documented selection promise, not a claim of correctness or a confirmed bug.
Source: base/subarray.jl:177-188,238-241; base/range.jl:353-387,1002-1011,1051-1073;
doc/src/manual/arrays.md:619-621. -/
def StepRangeViewElementsAndErrors : Prop :=
  ∀ (parent : JuliaLean.base.subarray.Models1Group17.StepRange64)
      (selector : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64),
    match JuliaLean.base.subarray.Models1Group17.viewStepRangeOrdinal64 parent selector with
    | .ok result =>
        JuliaLean.base.subarray.Models1Group17.NormalizedStepRange result ∧
        stepCountSpec result = selectorCountSpec selector ∧
        (∀ position : Nat, position < selectorCountSpec selector →
          result.start.val + Int.ofNat position * result.step.val =
            parent.val.start.val +
              (selectorValueSpec selector position - 1) * parent.val.step.val) ∧
        selectedPositionsValid (stepCountSpec parent.val) selector ∧
        (∀ position : I64,
          JuliaLean.base.subarray.Models1Group17.readStepRange64 result position =
            match JuliaLean.base.subarray.Models1Group17.readSelector64 selector position with
            | .ok selected =>
                JuliaLean.base.subarray.Models1Group17.readStepRange64 parent.val selected
            | .error error => .error error)
    | .error .boundsError =>
        badSelectedPosition (stepCountSpec parent.val) selector
    | .error (.overflowError _) =>
        selectorCountSpec selector = 0 ∧
        let start := (JInt.wrap .i64 (parent.val.start.val +
          (selectorValueSpec selector 0 - 1) * parent.val.step.val)).val
        let step := (JInt.wrap .i64 (parent.val.step.val *
          (JuliaLean.base.subarray.Models1Group17.selectorStep selector).val)).val
        if step > 0 then start = IntTy.i64.min else start = IntTy.i64.max
    | .error (.argumentError _) =>
        selectedPositionsValid (stepCountSpec parent.val) selector ∧
        (JInt.wrap .i64 (parent.val.step.val *
          (JuliaLean.base.subarray.Models1Group17.selectorStep selector).val)).val = 0 ∧
        (selectorCountSpec selector ≠ 0 ∨
          (JInt.wrap .i64 (parent.val.start.val +
            (selectorValueSpec selector 0 - 1) * parent.val.step.val)).val ≠ IntTy.i64.max)
    | .error _ => False

/-- Colon selection of an immutable built-in range succeeds and preserves its
whole mathematical sequence, scalar observations, and actual machine length.
The property observes the result rather than demanding the literal identity
body or assuming a getindex/copy law. Both concrete range input domains include
all constructor-normalized endpoint values and wrapped lengths.
Source: base/subarray.jl:177-188,252-255; base/range.jl:923,1000. -/
def ColonViewPreservesObservations : Prop :=
  ∀ range : JuliaLean.base.subarray.Models1Group17.OrdinalSelector64,
    match JuliaLean.base.subarray.Models1Group17.viewOrdinalColon64 range with
    | .ok result =>
        selectorCountSpec result = selectorCountSpec range ∧
        (∀ position : Nat, position < selectorCountSpec range →
          selectorValueSpec result position = selectorValueSpec range position) ∧
        (∀ position : I64,
          JuliaLean.base.subarray.Models1Group17.readSelector64 result position =
            JuliaLean.base.subarray.Models1Group17.readSelector64 range position) ∧
        JuliaLean.base.subarray.Models1Group17.selectorLength result =
          JuliaLean.base.subarray.Models1Group17.selectorLength range
    | .error _ => False

/-!
Standalone unproved properties for insertion inside
`JuliaLean.Proofs.base.subarray.Models1Group17`.
UNCHECKED: these statements have not been elaborated by Lean.
-/

/-- A tuple consisting entirely of Slice parents substitutes the complete
subindex tuple unchanged whenever the two arities agree. This quantifies
over all represented subindex values and types, including non-scalars and
opaque tags, without any supplied getter or correctness law. It describes
whole-sequence identity rather than the implementation's head/tail recurrence.
The arity condition ensures every tuple access is in bounds, so this invariant
does not depend on whether a caller propagates an inbounds context.
Source: base/subarray.jl:292,299-300; doc/src/devdocs/subarrays.md:109-119,189-192. -/
def ReindexAllSlicesIdentity : Prop :=
  ∀ (parents subindices : JuliaLean.base.subarray.Models1Group17.Input),
    (∀ parent ∈ parents.indices, ∃ axis : Axis, parent = Index.slice axis) →
    parents.indices.length = subindices.indices.length →
    JuliaLean.base.subarray.Models1Group17.reindexPartial parents subindices =
      some (.ok subindices.indices)

/-- If all stored parents are concrete Int64 scalars, reindexing with an
empty subindex tuple preserves the entire parent tuple, including order,
duplicates, typemin/typemax, and the empty tuple. It performs no scalar
arithmetic and consumes no subindices. This is a whole-sequence invariant
over the model's concrete scalar domain, not a claim about unrepresented Real
subtypes. Every accessed tuple is nonempty; the invariant therefore also
survives propagation of an inbounds context.
Source: base/subarray.jl:292,295-296; doc/src/devdocs/subarrays.md:109-119. -/
def ReindexAllScalarsPreserve : Prop :=
  ∀ (parents subindices : JuliaLean.base.subarray.Models1Group17.Input),
    (∀ parent ∈ parents.indices, ∃ value : I64, parent = Index.scalar value) →
    subindices.indices = [] →
    JuliaLean.base.subarray.Models1Group17.reindexPartial parents subindices =
      some (.ok parents.indices)


/-- Type-level contiguity cannot depend on the parent value or cached numeric
layout. Changing these fields without changing the Julia index-type tags or L
flag preserves the trait. This rejects accidental value/stride-based tests.
Source: base/subarray.jl:348-349,460-462. -/
def ContiguityIgnoresValues : Prop :=
  ∀ {P Q T : Type} (view : SubArray P T) (parent : Q) (offset stride : I64),
    let changed : SubArray Q T :=
      ⟨parent, view.indices, offset, stride, view.linear, view.dimensions⟩
    JuliaLean.base.subarray.Models1Group17.iscontiguous changed =
      JuliaLean.base.subarray.Models1Group17.iscontiguous view

/-- Slow views cannot have the fast-contiguous trait; all-scalar fast views do
have it, including zero-dimensional views with an empty index tuple. The
premise in the first clause is a dispatch condition, not a correctness law.
Source: base/subarray.jl:348-349,460-462. -/
def ContiguityDispatchExtremes : Prop :=
  (∀ {P T : Type} (view : SubArray P T), view.linear = false →
    JuliaLean.base.subarray.Models1Group17.iscontiguous view = false) ∧
  (∀ {P T : Type} (view : SubArray P T) (scalars : List I64),
    JuliaLean.base.subarray.Models1Group17.iscontiguous (T := T)
      { view with indices := scalars.map Index.scalar, linear := true } = true)

/-- Every represented leading AbstractUnitRange type selects the fast-contiguous
alias when L is true, regardless of the remaining index tuple. This separately
tests the nonscalar arm of the source type union; scalar-only tests miss it.
Source: base/subarray.jl:348-349,460-462. -/
def ContiguityLeadingUnitRanges : Prop :=
  ∀ {P T : Type} (view : SubArray P T) (axis : Axis) (length : I64)
      (tail : List Index),
    JuliaLean.base.subarray.Models1Group17.iscontiguous (T := T)
      { view with indices := .slice axis :: tail, linear := true } = true ∧
    JuliaLean.base.subarray.Models1Group17.iscontiguous (T := T)
      { view with indices := .identity axis :: tail, linear := true } = true ∧
    JuliaLean.base.subarray.Models1Group17.iscontiguous (T := T)
      { view with indices := .unitRange axis :: tail, linear := true } = true ∧
    JuliaLean.base.subarray.Models1Group17.iscontiguous (T := T)
      { view with indices := .oneTo length :: tail, linear := true } = true

/-- A completely scalar selection drops every parent stride. Its only possible
failures are determined by the two tuple arities: too few strides hits tail(()),
and leftover strides reach an unmatched empty-index method. This describes
the result by arity, rather than replaying the recursion.
Source: base/subarray.jl:439-440; base/essentials.jl:541-542. -/
def ScalarSubstridesArity : Prop :=
  ∀ (strides values : List I64),
    JuliaLean.base.subarray.Models1Group17.substrides strides (values.map Index.scalar) =
      if strides.length = values.length then some (.ok [])
      else if strides.length < values.length then
        some (.error (.argumentError "Cannot call tail on an empty tuple."))
      else some (.error (.methodError "substrides"))

/-- Even if the range's step has no semantics in this partial model,
first(()) throws before evaluating it. The independent expected exception is
the tuple primitive's documented/source error, not the model's result.
Source: base/subarray.jl:441-442; base/tuple.jl:270. -/
def EmptyStrideFirstErrorPrecedence : Prop :=
  ∀ (index : Index) (rest : List Index), index.isRange = true →
    JuliaLean.base.subarray.Models1Group17.substrides [] (index :: rest) =
      some (.error (.argumentError "tuple must be non-empty"))

/-- The all-scalar specialization does not touch parent axes, so it succeeds
even if no axes are supplied, and preserves every possible machine stride.
Source: base/subarray.jl:450-451 (dispatch and cached-layout invariant). -/
def ScalarStrideDoesNotReadAxes : Prop :=
  ∀ (stride : I64) (axes : List Axis) (values : List I64),
    JuliaLean.base.subarray.Models1Group17.computeStride1Rec stride axes
      (values.map Index.scalar) = some (.ok stride)

/-- Independent column-major coordinate displacement: the coordinate at original
position k is weighted by the product of all preceding axis cardinalities.
This global dot product does not use a recursive model intermediate.
Source: doc/src/manual/arrays.md (column-major indexing);
base/subarray.jl:486-501. Unbounded Int here is mathematical specification. -/
def denseOffsetSpec (axes : List Axis) (coordinates : List I64) : Int :=
  ((axes.zip coordinates).zipIdx.map fun pair =>
    (pair.1.2.val - pair.1.1.first.val) *
      ((axes.take pair.2).map (fun axis => axis.last.val - axis.first.val + 1)).prod).sum

/-- Scalar-coordinate linearization equals the independent column-major dot
product modulo the Int64 modulus. The only premises are actual array-shape
constructibility and matching coordinate arity. Coordinates need not be in
bounds because this internal helper has no bounds check.
Source: base/subarray.jl:491-501; doc/src/manual/arrays.md (column-major order).
The property quantifies all machine offsets/strides and all coordinates, and
therefore includes wrapping arithmetic without assuming no overflow. -/
def ScalarLinearizationCongruence : Prop :=
  ∀ (first stride : I64) (axes : List Axis) (coordinates : List I64),
    JuliaLean.base.subarray.Models1Group17.ArrayPayloadValid axes
      (JuliaLean.base.subarray.Models1Group17.shapeCardinality axes) →
    axes.length = coordinates.length →
    ∃ result : I64,
      JuliaLean.base.subarray.Models1Group17.computeLinindexRec first stride axes
        (coordinates.map Index.scalar) = some (.ok result) ∧
      (result.val - (first.val + stride.val * denseOffsetSpec axes coordinates)) %
        (2 ^ 64 : Int) = 0

/-- Terminal tuple helpers introduce no dimensions, selectors or strides.
Source: base/subarray.jl:139,145,148,172,439,505. -/
def EmptyLeafObservations : Prop :=
  trimmedShapeEmpty.length = 0 ∧
  trimmedParentEmpty.length = 0 ∧
  trimmedViewEmpty.length = 0 ∧
  (removeSingletonIndicesEmpty (A := Index)).length = 0 ∧
  (∀ dimension : I64, (findExtendedDimsEmpty dimension).length = 0) ∧
  (match substridesEmpty with
    | .ok strides => strides.length = 0
    | .error _ => False)

/-- The fallback cannot advertise the empty tuple's fast linear indexing.
Source: base/subarray.jl:52,65. -/
def FallbackRejectsLinearIndexing : Prop :=
  ∀ indices : List Index, viewIndexingFallback indices ≠ viewIndexingEmpty

/-- Identity trimming of an abstract range preserves its coordinate domain
and the distinction between scalar and nonscalar selectors.
Source: base/subarray.jl:151. -/
def RangeTrimmingPreservesObservations : Prop :=
  ∀ index : Index,
    Index.indexAxes (trimmedIndexRange index) = Index.indexAxes index ∧
    Index.scalarValue (trimmedIndexRange index) = Index.scalarValue index ∧
    Index.isRange (trimmedIndexRange index) = Index.isRange index

/-- Cached scalar parent addresses agree with the mathematical affine address
modulo the machine word size, including overflowing products and sums.
Source: base/subarray.jl:327,351. -/
def CachedAddressCongruence : Prop :=
  ∀ {P T : Type} (view : SubArray P T) (index : I64),
    ((reindexLinear view index).val -
      (view.offset1.val + view.stride1.val * index.val)) % (2 ^ 64 : Int) = 0 ∧
    ((reindexLinearContiguous view index).val -
      (view.offset1.val + index.val)) % (2 ^ 64 : Int) = 0

theorem CachedAddressCongruence_proven : CachedAddressCongruence := by
  intro P T view index
  constructor
  · change ((JuliaLean.base.int.add view.offset1
      (JuliaLean.base.int.mul view.stride1 index)).val -
        (view.offset1.val + view.stride1.val * index.val)) % (2 ^ 64 : Int) = 0
    rw [JuliaLean.Proofs.base.int.addWraps_proven,
      JuliaLean.Proofs.base.int.mulWraps_proven, JuliaLean.Proofs.base.int.wrapInt_add_right]
    simp only [wrapInt, IntTy.signed, IntTy.bits]
    omega
  · change ((JuliaLean.base.int.add view.offset1 index).val -
      (view.offset1.val + index.val)) % (2 ^ 64 : Int) = 0
    rw [JuliaLean.Proofs.base.int.addWraps_proven]
    simp only [wrapInt, IntTy.signed, IntTy.bits]
    omega

/-- Fast views advertise linear indexing; the two contiguity type leaves
distinguish an unrestricted view type from its fast-contiguous subtype.
Source: base/subarray.jl:433,461-462. -/
def FastTypeLeafClassification : Prop :=
  indexStyleFastSubArray ≠ IndexStyle.cartesian ∧
  iscontiguousSubArrayType = false ∧
  iscontiguousFastContiguousSubArrayType = true

/-- Invalid strided index types always fail with ArgumentError, independently
of the parent stride tuple and diagnostic type-label contents.
Source: base/subarray.jl:443-444. -/
def InvalidStrideExceptionClass : Prop :=
  ∀ (strides : List I64) (typeLabel : String),
    match substridesInvalid strides typeLabel with
    | .error (.argumentError _) => True
    | _ => False

end Models1Group17

end JuliaLean.Proofs.base.subarray

namespace JuliaLean.ChatGPT.Batch9.Group14

open JuliaLean JuliaLean.base.subarray
open JuliaLean.base.subarray.Models1Group17
open JuliaLean.Proofs.base.subarray
open JuliaLean.Proofs.base.subarray.Models1Group17

/-- The finite-domain test agrees with the stated representation domain. -/
theorem shape_supported_tag (index : Index) (h : ShapeIndexSupported index) :
    finiteAxesTag index = true := by
  cases index <;>
    simp only [ShapeIndexSupported, finiteAxesTag, concreteArrayAxes,
      List.all_eq_true, decide_eq_true_eq] at h ⊢ <;>
    first | exact h | trivial | contradiction

theorem shape_supported_all (indices : List Index)
    (h : ∀ index ∈ indices, ShapeIndexSupported index) :
    indices.all finiteAxesTag = true := by
  apply List.all_eq_true.mpr
  intro index member
  exact shape_supported_tag index (h index member)

theorem shape_axis_rank (index : Index) (supported : ShapeIndexSupported index) :
    index.indexAxes.length = retainedRankSpec index := by
  cases index <;> first | rfl | cases supported

theorem shape_axes_rank : ∀ (indices : List Index),
    (∀ index ∈ indices, ShapeIndexSupported index) →
    (viewAxesManual indices).length = (indices.map retainedRankSpec).sum
  | [], _ => rfl
  | index :: rest, supported => by
      have hi := supported index (List.mem_cons_self ..)
      have hr : ∀ next ∈ rest, ShapeIndexSupported next :=
        fun next member => supported next (List.mem_cons_of_mem index member)
      simp only [viewAxesManual, List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons]
      change index.indexAxes.length + (viewAxesManual rest).length =
        retainedRankSpec index + (rest.map retainedRankSpec).sum
      rw [shape_axis_rank index hi, shape_axes_rank rest hr]

theorem shape_axes_success {P T : Type} (input : ShapeAxesViewInput P T)
    (h : ∀ index ∈ input.view.indices, ShapeIndexSupported index) :
    axesSubArrayFinite input = some (.ok (viewAxesManual input.view.indices)) := by
  simp only [axesSubArrayFinite, shape_supported_all input.view.indices h,
    ite_true, partialPure]
  exact congrArg (fun axes => some (Except.ok axes)) (subArrayAxesContract_proven input.view)

/-- A direct Slice/Identity selector contributes its own sole axis. -/
theorem shape_origin_single (index : Index) (axis : Axis)
    (h : index = .slice axis ∨ index = .identity axis) : index.indexAxes = [axis] := by
  cases h with
  | inl h => subst index; rfl
  | inr h => subst index; rfl

theorem shape_get_after_append {A : Type} (before after : List A) (position : Nat) :
    (before ++ after)[before.length + position]? = after[position]? := by
  induction before with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons head before ih =>
      have h : (head :: before).length + position =
          (before.length + position) + 1 := by simp only [List.length_cons]; omega
      rw [h]
      exact ih

/-- Global positions are the sum of the retained ranks of the original prefix. -/
theorem shape_origin_position (indices : List Index)
    (supported : ∀ index ∈ indices, ShapeIndexSupported index) (position : Nat) (axis : Axis)
    (h : indices[position]? = some (.slice axis) ∨
      indices[position]? = some (.identity axis)) :
    (viewAxesManual indices)[((indices.take position).map retainedRankSpec).sum]? =
      some axis := by
  induction indices generalizing position with
  | nil =>
      simp only [List.getElem?_nil, reduceCtorEq, or_self] at h
  | cons index rest ih =>
      have hi := supported index (List.mem_cons_self ..)
      have hr : ∀ next ∈ rest, ShapeIndexSupported next :=
        fun next member => supported next (List.mem_cons_of_mem index member)
      cases position with
      | zero =>
          have hx : index = .slice axis ∨ index = .identity axis := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using h
          rw [show (viewAxesManual (index :: rest)) =
            index.indexAxes ++ viewAxesManual rest from rfl, shape_origin_single index axis hx]
          rfl
      | succ position =>
          have ht : rest[position]? = some (.slice axis) ∨
              rest[position]? = some (.identity axis) := h
          have rank : ((index :: rest).take (position + 1) |>.map retainedRankSpec).sum =
              index.indexAxes.length + ((rest.take position).map retainedRankSpec).sum := by
            simp only [List.take_succ_cons, List.map_cons, List.sum_cons, shape_axis_rank index hi]
          rw [rank]
          change (index.indexAxes ++ viewAxesManual rest)[index.indexAxes.length +
            ((rest.take position).map retainedRankSpec).sum]? = some axis
          rw [shape_get_after_append]
          exact ih hr position ht

theorem shape_index_offset_origin (index : Index) (supported : ShapeIndexSupported index)
    (axis : Axis) (member : axis ∈ index.indexAxes) (offset : axis.first.val ≠ 1) :
    index = .slice axis ∨ index = .identity axis := by
  cases index with
  | scalar value => cases member
  | colon => cases supported
  | slice origin =>
      have h : axis = origin := by simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact Or.inl rfl
  | identity origin =>
      have h : axis = origin := by simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact Or.inr rfl
  | values axes values =>
      have h := supported axis member
      have eq : axis.first.val = 1 := by rw [h]; decide
      exact (offset eq).elim
  | cartesianValues axes rank values =>
      have h := supported axis member
      have eq : axis.first.val = 1 := by rw [h]; decide
      exact (offset eq).elim
  | unitRange range =>
      have h : axis = {first := int64 1, last := int64 (range.last.val - range.first.val + 1)} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | oneTo count =>
      have h : axis = {first := int64 1, last := count} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | stepRange first step count =>
      have h : axis = {first := int64 1, last := count} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | stepRangeLen first step count =>
      have h : axis = {first := int64 1, last := count} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | linRange first last count =>
      have h : axis = {first := int64 1, last := count} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | mask bits =>
      have h : axis = {first := int64 1, last := int64 (bits.filter id).length} := by
        simpa only [Index.indexAxes, List.mem_singleton] using member
      subst axis
      exact (offset (by rfl)).elim
  | ordinalRange first step count => cases supported
  | other => cases supported
  | cartesian coordinates => cases supported

theorem shape_axes_offset_origin (indices : List Index)
    (supported : ∀ index ∈ indices, ShapeIndexSupported index)
    (axis : Axis) (member : axis ∈ viewAxesManual indices) (offset : axis.first.val ≠ 1) :
    Index.slice axis ∈ indices ∨ Index.identity axis ∈ indices := by
  obtain ⟨index, memberIndex, memberAxis⟩ := List.mem_flatMap.mp member
  have origin := shape_index_offset_origin index (supported index memberIndex) axis memberAxis offset
  cases origin with
  | inl eq => exact Or.inl (eq ▸ memberIndex)
  | inr eq => exact Or.inr (eq ▸ memberIndex)

theorem Models1G17FiniteAxesRankOrigins_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FiniteAxesRankAndOrigins := by
  intro P T input supported
  refine ⟨viewAxesManual input.view.indices, shape_axes_success input supported,
    shape_axes_rank input.view.indices supported, ?_, ?_⟩
  · exact shape_origin_position input.view.indices supported
  · exact shape_axes_offset_origin input.view.indices supported

/-- Scalar insertion is invisible to the whole-axis domain check. -/
theorem shape_all_insert (before after : List Index) (value : I64) :
    (before ++ Index.scalar value :: after).all finiteAxesTag =
      (before ++ after).all finiteAxesTag := by
  simp only [List.all_append, List.all_cons, finiteAxesTag, Bool.true_and]

theorem shape_axes_insert (before after : List Index) (value : I64) :
    indicesSubDispatch (before ++ Index.scalar value :: after) =
      indicesSubDispatch (before ++ after) := by
  simp only [indicesSubDispatch_spec, viewAxesManual, List.flatMap_append,
    List.flatMap_cons, Index.indexAxes, List.nil_append]

theorem shape_prefix_insert (before after : List Index) (value : I64) :
    axes1PrefixKnown (before ++ Index.scalar value :: after) =
      axes1PrefixKnown (before ++ after) := by
  induction before with
  | nil => rfl
  | cons index before ih =>
      cases index with
      | scalar x => exact ih
      | values axes values => cases axes <;> first | exact ih | rfl
      | cartesianValues axes rank values => cases axes <;> first | exact ih | rfl
      | colon => rfl
      | slice axis => rfl
      | identity axis => rfl
      | unitRange axis => rfl
      | oneTo n => rfl
      | stepRange first step count => rfl
      | stepRangeLen first step count => rfl
      | ordinalRange first step count => rfl
      | linRange first last count => rfl
      | mask bits => rfl
      | other => rfl
      | cartesian coords => rfl

theorem shape_first_insert (before after : List Index) (value : I64) :
    axes1SubDispatch (before ++ Index.scalar value :: after) =
      axes1SubDispatch (before ++ after) := by
  induction before with
  | nil => rfl
  | cons index before ih =>
      cases index with
      | scalar x => exact ih
      | values axes values => cases axes <;> first | exact ih | rfl
      | cartesianValues axes rank values => cases axes <;> first | exact ih | rfl
      | colon => rfl
      | slice axis => rfl
      | identity axis => rfl
      | unitRange axis => rfl
      | oneTo n => rfl
      | stepRange first step count => rfl
      | stepRangeLen first step count => rfl
      | ordinalRange first step count => rfl
      | linRange first last count => rfl
      | mask bits => rfl
      | other => rfl
      | cartesian coords => rfl

theorem shape_offset_insert (before after : List Index) (value : I64) :
    hasOffsetAxesFiniteCore (before ++ Index.scalar value :: after) =
      hasOffsetAxesFiniteCore (before ++ after) := by
  induction before with
  | nil => rfl
  | cons index before ih =>
      simp only [List.cons_append, hasOffsetAxesFiniteCore, ih]

theorem Models1G17ScalarInsertionShapeInvariance_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ScalarInsertionPreservesShapeObservations := by
  intro P T original changed before after value hOriginal hChanged hRank
  have hAxes : axesSubArrayFinite changed = axesSubArrayFinite original := by
    simp only [axesSubArrayFinite, axesSubArrayModel, axesSubArray,
      hOriginal, hChanged, shape_all_insert, shape_axes_insert]
  refine ⟨hAxes, ?_, ?_, ?_⟩
  · simp only [sizeSubArrayFinite, hAxes]
  · simp only [axes1SubArrayFinite, axes1SubArrayModel, axes1SubArray,
      hOriginal, hChanged, hRank, shape_prefix_insert, shape_first_insert]
  · simp only [hasOffsetAxesSubArrayFinite, hOriginal, hChanged, shape_offset_insert]


/-- Mathematical endpoint width, represented with the same machine wrap. -/
def shape_axis_size (axis : Axis) : I64 :=
  int64 (axis.last.val - axis.first.val + 1)

theorem shape_axis_length (axis : Axis) :
    axisLength axis = .ok (shape_axis_size axis) := by
  unfold axisLength
  split
  next origin =>
    unfold shape_axis_size
    rw [origin]
    simp only [Int.sub_add_cancel, int64_self]
  next other =>
    change Except.ok (iadd (int64 1) (isub axis.last axis.first)) =
      Except.ok (shape_axis_size axis)
    apply congrArg Except.ok
    apply JuliaLean.Proofs.base.int.jint_eq
    simp only [iadd, isub, JuliaLean.base.int.add, JuliaLean.base.int.sub,
      JuliaLean.Proofs.base.int.add_int_val, JuliaLean.Proofs.base.int.sub_int_val,
      shape_axis_size, int64, JuliaLean.Proofs.base.int.lit_val]
    rw [show wrapInt .i64 1 = 1 from rfl,
      JuliaLean.Proofs.base.int.wrapInt_add_right, Int.add_comm]

theorem shape_map_lengths (axes : List Axis) :
    mapAxisLengths axes = .ok (axes.map shape_axis_size) := by
  induction axes with
  | nil => rfl
  | cons axis rest ih =>
      simp only [mapAxisLengths, shape_axis_length, ih, Bind.bind, Except.bind,
        Pure.pure, Except.pure, List.map_cons]

theorem Models1G17FiniteSizeCardinality_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FiniteSizeCoordinateCardinality := by
  intro P T input supported
  let axes := viewAxesManual input.view.indices
  refine ⟨axes, axes.map shape_axis_size, shape_axes_success input supported, ?_,
    shape_axes_rank input.view.indices supported, ?_, ?_⟩
  · simp only [sizeSubArrayFinite, shape_axes_success input supported,
      partialBind, shape_map_lengths, axes]
  · exact List.length_map shape_axis_size
  · intro position axis member
    refine ⟨shape_axis_size axis, ?_, rfl⟩
    rw [List.getElem?_map, member]
    rfl

theorem shape_supported_stored (indices : List Index)
    (supported : ∀ index ∈ indices, ShapeIndexSupported index) : StoredIndices indices := by
  induction indices with
  | nil => trivial
  | cons index rest ih =>
      have hi := supported index (List.mem_cons_self ..)
      have hr : ∀ next ∈ rest, ShapeIndexSupported next :=
        fun next member => supported next (List.mem_cons_of_mem index member)
      refine ⟨?_, ih hr⟩
      cases index <;> first | trivial | cases hi

theorem shape_supported_prefix (indices : List Index)
    (supported : ∀ index ∈ indices, ShapeIndexSupported index) :
    axes1PrefixKnown indices = true := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have hi := supported index (List.mem_cons_self ..)
      have ht := shape_supported_tag index hi
      have hr : ∀ next ∈ rest, ShapeIndexSupported next :=
        fun next member => supported next (List.mem_cons_of_mem index member)
      cases index with
      | scalar x => exact ih hr
      | values axes values => cases axes <;> first | exact ih hr | exact ht
      | cartesianValues axes rank values => cases axes <;> first | exact ih hr | exact ht
      | colon => exact ht
      | slice axis => exact ht
      | identity axis => exact ht
      | unitRange axis => exact ht
      | oneTo n => exact ht
      | stepRange first step count => exact ht
      | stepRangeLen first step count => exact ht
      | ordinalRange first step count => exact ht
      | linRange first last count => exact ht
      | mask bits => exact ht
      | other => exact ht
      | cartesian coords => exact ht

theorem Models1G17FiniteAxes1Domain_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FiniteAxes1CoordinateDomain := by
  intro P T input supported
  refine ⟨viewAxesManual input.view.indices, axes1SubArrayModel input.view,
    shape_axes_success input supported, ?_, shape_axes_rank input.view.indices supported, ?_⟩
  · unfold axes1SubArrayFinite
    split
    next zero =>
      simp only [axes1SubArrayModel, zero, ite_true, partialPure]
    next nonzero =>
      simp only [shape_supported_prefix input.view.indices supported, ite_true, partialPure]
  · split
    next zero =>
      refine ⟨axes1ZeroDimSubArray, ?_, ?_, ?_, ?_⟩
      · simp only [axes1SubArrayModel, zero, ite_true]
      · decide
      · decide
      · decide
    next nonzero =>
      simp only [axes1SubArrayModel, nonzero, ite_false, axes1SubArray]
      exact axes1SubDispatch_spec input.view.indices
        (shape_supported_stored input.view.indices supported)


theorem shape_onebased_no_offset (axes : List Axis)
    (onebased : ∀ axis ∈ axes, axis.first = int64 1) :
    axes.any (fun axis => decide (axis.first.val ≠ 1)) = false := by
  induction axes with
  | nil => rfl
  | cons axis rest ih =>
      have first := onebased axis (List.mem_cons_self ..)
      have remaining : ∀ next ∈ rest, next.first = int64 1 :=
        fun next member => onebased next (List.mem_cons_of_mem axis member)
      simp only [List.any_cons, first, ih remaining]
      rfl

theorem shape_index_offset (index : Index) (supported : ShapeIndexSupported index) :
    hasOffsetAxesFiniteIndex index =
      partialPure (index.indexAxes.any (fun axis => decide (axis.first.val ≠ 1))) := by
  cases index with
  | scalar value => rfl
  | colon => cases supported
  | slice axis =>
      simp only [hasOffsetAxesFiniteIndex, Index.indexAxes, List.any_cons, List.any_nil,
        Bool.or_false]
  | identity axis =>
      simp only [hasOffsetAxesFiniteIndex, Index.indexAxes, List.any_cons, List.any_nil,
        Bool.or_false]
  | values axes values =>
      have concrete : concreteArrayAxes axes = true := shape_supported_tag (.values axes values) supported
      simp only [hasOffsetAxesFiniteIndex, concrete, ite_true, Index.indexAxes,
        shape_onebased_no_offset axes supported]
  | cartesianValues axes rank values =>
      have concrete : concreteArrayAxes axes = true :=
        shape_supported_tag (.cartesianValues axes rank values) supported
      simp only [hasOffsetAxesFiniteIndex, concrete, ite_true, Index.indexAxes,
        shape_onebased_no_offset axes supported]
  | unitRange axis => rfl
  | oneTo n => rfl
  | stepRange first step count => rfl
  | stepRangeLen first step count => rfl
  | linRange first last count => rfl
  | mask bits => rfl
  | ordinalRange first step count => cases supported
  | other => cases supported
  | cartesian coords => cases supported

theorem shape_offset_result (indices : List Index)
    (supported : ∀ index ∈ indices, ShapeIndexSupported index) :
    hasOffsetAxesFiniteCore indices =
      partialPure ((viewAxesManual indices).any (fun axis => decide (axis.first.val ≠ 1))) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have hi := supported index (List.mem_cons_self ..)
      have hr : ∀ next ∈ rest, ShapeIndexSupported next :=
        fun next member => supported next (List.mem_cons_of_mem index member)
      simp only [hasOffsetAxesFiniteCore, shape_index_offset index hi, partialPure, partialBind]
      rw [ih hr]
      simp only [viewAxesManual, List.flatMap_cons, List.any_append]
      cases index.indexAxes.any (fun axis => decide (axis.first.val ≠ 1)) <;> rfl

theorem Models1G17FiniteOffsetAxisCoherence_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FiniteOffsetAxisCoherence := by
  intro P T input supported
  let axes := viewAxesManual input.view.indices
  refine ⟨axes, axes.any (fun axis => decide (axis.first.val ≠ 1)),
    shape_axes_success input supported, shape_offset_result input.view.indices supported, ?_⟩
  simp only [List.any_eq_true, decide_eq_true_eq]

end JuliaLean.ChatGPT.Batch9.Group14

namespace JuliaLean.ChatGPT.Batch9.Group14

open JuliaLean JuliaLean.base.subarray
open JuliaLean.Proofs.base.subarray.Models1Group17

/-- One removal step retains exactly the nonscalar or in-rank head. -/
theorem singleton_remove_cons (dimensions : List Bool) (index : Index) (rest : List Index) :
    JuliaLean.base.subarray.Models1Group17.removeSingletonIndices dimensions (index :: rest) =
      if index.isScalar = false ∨ 0 < dimensions.length then
        index :: JuliaLean.base.subarray.Models1Group17.removeSingletonIndices (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])) rest
      else JuliaLean.base.subarray.Models1Group17.removeSingletonIndices (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])) rest := by
  cases dimensions <;> cases index <;> rfl

/-- Removal neither introduces values nor changes the nonscalar subsequence. -/
theorem Models1G17SingletonPreservesNonscalars_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.SingletonPreservesNonscalars := by
  intro dimensions indices
  induction indices generalizing dimensions with
  | nil => exact ⟨.slnil, rfl⟩
  | cons index rest ih =>
      dsimp only
      rw [singleton_remove_cons]
      have ht := ih (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index]))
      split
      · exact ⟨ht.1.cons_cons index, by simp only [List.filter_cons, ht.2]⟩
      · rename_i h
        have hscalar : index.isScalar = true := by
          cases hs : index.isScalar with
          | false => exact False.elim (h (Or.inl hs))
          | true => rfl
        refine ⟨ht.1.cons index, ?_⟩
        simp only [List.filter_cons, hscalar, Bool.not_true, Bool.false_eq_true,
          ite_false, ht.2]

/-- The tuple-tail helper removes the reference tuple's arity. -/
theorem singleton_split_length {A B : Type} (dimensions : List A) (reference : List B) :
    (JuliaLean.base.subarray.Models1Group17.splitRest dimensions reference).length = dimensions.length - reference.length := by
  induction reference generalizing dimensions with
  | nil => simp only [JuliaLean.base.subarray.Models1Group17.splitRest, List.length_nil, Nat.sub_zero]
  | cons b reference ih =>
      cases dimensions with
      | nil => simp only [JuliaLean.base.subarray.Models1Group17.splitRest, List.length_nil, Nat.zero_sub]
      | cons a dimensions =>
          change (JuliaLean.base.subarray.Models1Group17.splitRest dimensions reference).length =
            (dimensions.length + 1) - (reference.length + 1)
          rw [ih]
          omega

/-- The model's concrete dimension tuple has the independently specified rank. -/
theorem singleton_dims_length (index : Index) :
    (JuliaLean.base.subarray.Models1Group17.indexNdims [index]).length = effectiveRank index := by
  cases index <;> simp only [JuliaLean.base.subarray.Models1Group17.indexNdims,
    JuliaLean.base.subarray.Models1Group17.indexNdims, effectiveRank,
    List.length_cons, List.length_nil, List.length_map, List.length_append,
    List.length_replicate, Nat.add_zero]

/-- The prefix-rank specification obeys the same independent head/tail rule. -/
theorem singleton_retained_cons (dimensions : List Bool) (index : Index) (rest : List Index) :
    retainedByPrefix dimensions (index :: rest) =
      if index.isScalar = false ∨ 0 < dimensions.length then
        index :: retainedByPrefix (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])) rest
      else retainedByPrefix (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])) rest := by
  have hlength :
      (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])).length =
        dimensions.length - effectiveRank index := by
    rw [singleton_split_length, singleton_dims_length]
  have htail :
      (rest.zipIdx.map (Prod.map id (· + 1))).filterMap (fun pair =>
        if pair.1.isScalar = false ∨
          (((index :: rest).take pair.2).map effectiveRank).sum < dimensions.length then
          some pair.1 else none) =
      retainedByPrefix (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])) rest := by
    rw [List.filterMap_map]
    unfold retainedByPrefix
    apply congrArg (fun f : Index × Nat → Option Index => rest.zipIdx.filterMap f)
    funext pair
    rcases pair with ⟨entry, position⟩
    simp only [Function.comp_apply, Prod.map, id_eq,
      List.take_succ_cons, List.map_cons, List.sum_cons]
    have hc :
        (entry.isScalar = false ∨
          effectiveRank index + ((rest.take position).map effectiveRank).sum < dimensions.length) ↔
        (entry.isScalar = false ∨
          ((rest.take position).map effectiveRank).sum <
            (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index])).length) := by
      rw [hlength, Nat.lt_sub_iff_add_lt']
    simp only [hc]
  unfold retainedByPrefix
  rw [List.zipIdx_cons']
  simp only [List.filterMap_cons, List.take_zero, List.map_nil, List.sum_nil]
  rw [htail]
  by_cases hkeep : index.isScalar = false ∨ 0 < dimensions.length
  · simp only [hkeep, ite_true]
    rfl
  · simp only [hkeep, ite_false]
    rfl

/-- Removal equals the original-position prefix-rank selection exactly. -/
theorem Models1G17SingletonPrefixSelection_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.SingletonPrefixSelection := by
  intro dimensions indices
  induction indices generalizing dimensions with
  | nil => rfl
  | cons index rest ih =>
      rw [singleton_remove_cons, singleton_retained_cons,
        ih (JuliaLean.base.subarray.Models1Group17.splitRest dimensions (JuliaLean.base.subarray.Models1Group17.indexNdims [index]))]

end JuliaLean.ChatGPT.Batch9.Group14

namespace JuliaLean.ChatGPT.Batch9.Group14

open JuliaLean JuliaLean.base.subarray JuliaLean.Proofs.base.subarray

theorem Models1G17ColonViewObservations_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ColonViewPreservesObservations := by
  intro range
  exact ⟨rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem core_reindex_slices (parents subindices : List Index)
    (hs : ∀ parent ∈ parents, ∃ axis : Axis, parent = Index.slice axis)
    (hl : parents.length = subindices.length) :
    JuliaLean.base.subarray.Models1Group17.reindexPartialCore parents subindices =
      some (.ok subindices) := by
  induction parents generalizing subindices with
  | nil =>
      cases subindices with
      | nil => rfl
      | cons _ _ => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons parent parents ih =>
      obtain ⟨axis, rfl⟩ := hs parent (List.mem_cons_self ..)
      have ht : ∀ parent ∈ parents, ∃ axis : Axis, parent = Index.slice axis := by
        intro parent hp
        exact hs parent (List.mem_cons_of_mem _ hp)
      cases subindices with
      | nil => simp only [List.length_nil, List.length_cons] at hl; omega
      | cons subindex subindices =>
          have hl' : parents.length = subindices.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl
          change JuliaLean.base.subarray.Models1Group17.partialMap
            (fun indices => subindex :: indices)
            (JuliaLean.base.subarray.Models1Group17.reindexPartialCore parents subindices) = _
          rw [ih subindices ht hl']
          rfl

theorem Models1G17ReindexAllSlicesIdentity_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ReindexAllSlicesIdentity := by
  intro parents subindices hs hl
  exact core_reindex_slices parents.indices subindices.indices hs hl

theorem core_reindex_scalars (parents : List Index)
    (hs : ∀ parent ∈ parents, ∃ value : I64, parent = Index.scalar value) :
    JuliaLean.base.subarray.Models1Group17.reindexPartialCore parents [] =
      some (.ok parents) := by
  induction parents with
  | nil => rfl
  | cons parent parents ih =>
      obtain ⟨value, rfl⟩ := hs parent (List.mem_cons_self ..)
      have ht : ∀ parent ∈ parents, ∃ value : I64, parent = Index.scalar value := by
        intro parent hp
        exact hs parent (List.mem_cons_of_mem _ hp)
      change JuliaLean.base.subarray.Models1Group17.partialMap
        (fun indices => Index.scalar value :: indices)
        (JuliaLean.base.subarray.Models1Group17.reindexPartialCore parents []) = _
      rw [ih ht]
      rfl

theorem Models1G17ReindexAllScalarsPreserve_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ReindexAllScalarsPreserve := by
  intro parents subindices hs he
  unfold JuliaLean.base.subarray.Models1Group17.reindexPartial
  rw [he]
  exact core_reindex_scalars parents.indices hs

theorem Models1G17ContiguityValueIndependence_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityIgnoresValues := by
  intro P Q T view parent offset stride
  rfl

theorem core_allScalar_map (values : List I64) :
    Index.allScalar (values.map Index.scalar) = true := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (true && Index.allScalar (values.map Index.scalar)) = true
      rw [ih]
      rfl

theorem Models1G17ContiguityDispatchExtremes_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityDispatchExtremes := by
  constructor
  · intro P T view h
    unfold JuliaLean.base.subarray.Models1Group17.iscontiguous
    rw [h]
    rfl
  · intro P T view scalars
    cases scalars with
    | nil => rfl
    | cons value values =>
        change (if Index.allScalar ((value :: values).map Index.scalar) then true else false) = true
        rw [core_allScalar_map]
        rfl

theorem Models1G17ContiguityLeadingUnitranges_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityLeadingUnitRanges := by
  intro P T view axis length tail
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem Models1G17ScalarSubstridesArity_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ScalarSubstridesArity := by
  intro strides values
  induction values generalizing strides with
  | nil =>
      cases strides with
      | nil => rfl
      | cons stride strides =>
          simp only [List.map_nil, JuliaLean.base.subarray.Models1Group17.substrides,
            List.length_cons, List.length_nil, Nat.add_one_ne_zero, ite_false,
            Nat.not_lt_zero]
  | cons value values ih =>
      cases strides with
      | nil =>
          simp only [List.map_cons, JuliaLean.base.subarray.Models1Group17.substrides,
            JuliaLean.base.subarray.Models1Group17.tupleTail,
            JuliaLean.base.subarray.Models1Group17.partialBind,
            List.length_nil, List.length_cons, Nat.zero_ne_add_one,
            Nat.zero_lt_succ, ite_false, ite_true]
      | cons stride strides =>
          change JuliaLean.base.subarray.Models1Group17.substrides strides
            (values.map Index.scalar) = _
          rw [ih]
          simp only [List.length_cons, Nat.add_right_cancel_iff, Nat.add_lt_add_iff_right]

theorem Models1G17EmptyStrideErrorPrecedence_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.EmptyStrideFirstErrorPrecedence := by
  intro index rest h
  cases index <;>
    simp only [Index.isRange, Bool.false_eq_true] at h <;>
    simp only [JuliaLean.base.subarray.Models1Group17.substrides,
      Index.isRange, ite_true,
      JuliaLean.base.subarray.Models1Group17.partialBind,
      JuliaLean.base.subarray.Models1Group17.tupleFirst]

theorem Models1G17ScalarStrideNoAxisRead_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ScalarStrideDoesNotReadAxes := by
  intro stride axes values
  cases values with
  | nil => rfl
  | cons value values =>
      simp only [List.map_cons, JuliaLean.base.subarray.Models1Group17.computeStride1Rec,
        core_allScalar_map, ite_true, computeStride1Scalars]

theorem Models1G17EmptyLeafObservations_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.EmptyLeafObservations := by
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

theorem Models1G17FallbackRejectsLinearIndexing_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FallbackRejectsLinearIndexing := by
  intro indices h
  cases h

theorem Models1G17RangeTrimmingObservations_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.RangeTrimmingPreservesObservations := by
  intro index
  exact ⟨rfl, rfl, rfl⟩

theorem Models1G17FastTypeLeafClassification_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.FastTypeLeafClassification := by
  constructor
  · intro h
    cases h
  · exact ⟨rfl, rfl⟩

theorem Models1G17InvalidStrideExceptionClass_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.InvalidStrideExceptionClass := by
  intro strides typeLabel
  trivial

end JuliaLean.ChatGPT.Batch9.Group14

namespace JuliaLean.ChatGPT.Batch9.Group14

open JuliaLean JuliaLean.base.subarray JuliaLean.Proofs.base.subarray

namespace Lin

open JuliaLean.Proofs.base.subarray.Models1Group17

/-- Taking a constant multiple commutes with summation. -/
theorem sum_mul_left (factor : Int) (terms : List Int) :
    (terms.map (fun term => factor * term)).sum = factor * terms.sum := by
  induction terms with
  | nil => simp only [List.map_nil, List.sum_nil, Int.mul_zero]
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

/-- The global prefix-product definition has the usual column-major recurrence. -/
theorem denseOffset_cons (axis : Axis) (axes : List Axis)
    (coordinate : I64) (coordinates : List I64) :
    denseOffsetSpec (axis :: axes) (coordinate :: coordinates) =
      coordinate.val - axis.first.val +
        (axis.last.val - axis.first.val + 1) * denseOffsetSpec axes coordinates := by
  unfold denseOffsetSpec
  rw [List.zip_cons_cons, List.zipIdx_cons']
  simp only [List.map_cons, List.sum_cons, List.take_zero, List.map_nil,
    List.prod_nil, Int.mul_one, List.map_map, Function.comp_def,
    Prod.map, id_eq, List.take_succ_cons, List.prod_cons]
  rw [← sum_mul_left]
  congr 1
  rw [List.map_map]
  congr 1
  apply congrArg (fun f => List.map f ((axes.zip coordinates).zipIdx))
  funext pair
  simp only [Function.comp_def]
  exact Int.mul_left_comm _ _ _

/-- Scalar differences reduce the exact displacement to the machine type. -/
theorem difference_as_int64 (x y : I64) :
    isub x y = int64 (x.val - y.val) := by
  calc
    _ = isub (int64 x.val) (int64 y.val) := by
      rw [int64_self, int64_self]
    _ = _ := isub_lit _ _

/-- Every represented axis length is its endpoint width reduced to Int64. -/
theorem axisLength_as_int64 (axis : Axis) :
    JuliaLean.base.subarray.Models1Group17.axisLength axis =
      .ok (int64 (axis.last.val - axis.first.val + 1)) := by
  unfold JuliaLean.base.subarray.Models1Group17.axisLength
  split
  · rename_i hfirst
    rw [hfirst]
    have h : axis.last.val - 1 + 1 = axis.last.val := by omega
    rw [h, int64_self]
  · unfold JuliaLean.base.subarray.Models1Group17.unitLength
    change Except.ok (iadd (int64 1) (isub axis.last axis.first)) = _
    rw [difference_as_int64, iadd_lit]
    congr 2
    omega

/-- Scalar linearization is the independently specified global offset,
with exactly one final Int64 reduction in the statement. -/
theorem compute_as_int64 (axes : List Axis) (coordinates : List I64)
    (rank : axes.length = coordinates.length) (first stride : Int) :
    JuliaLean.base.subarray.Models1Group17.computeLinindexRec
      (int64 first) (int64 stride) axes (coordinates.map Index.scalar) =
      some (.ok (int64 (first + stride * denseOffsetSpec axes coordinates))) := by
  induction coordinates generalizing axes first stride with
  | nil =>
      simp only [List.map_nil,
        JuliaLean.base.subarray.Models1Group17.computeLinindexRec,
        computeLinindexEmpty, denseOffsetSpec, List.zip_nil_right,
        List.zipIdx_nil, List.sum_nil, Int.mul_zero, Int.add_zero]
  | cons coordinate coordinates ih =>
      cases axes with
      | nil => simp only [List.length_nil, List.length_cons] at rank; omega
      | cons axis axes =>
          have rankTail : axes.length = coordinates.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using rank
          cases coordinates with
          | nil =>
              rw [denseOffset_cons]
              simp only [denseOffsetSpec, List.zip_nil_right, List.zipIdx_nil,
                List.map_nil, List.sum_nil, Int.mul_zero, Int.add_zero,
                List.map_cons,
                JuliaLean.base.subarray.Models1Group17.computeLinindexRec,
                JuliaLean.base.subarray.Models1Group17.firstAsInt,
                JuliaLean.base.subarray.Models1Group17.partialPure,
                JuliaLean.base.subarray.Models1Group17.partialBind]
              rw [difference_as_int64, imul_lit, iadd_lit]
              rw [Int.mul_comm (coordinate.val - axis.first.val) stride]
          | cons next rest =>
              simp only [List.map_cons,
                JuliaLean.base.subarray.Models1Group17.computeLinindexRec,
                JuliaLean.base.subarray.Models1Group17.firstAsInt,
                JuliaLean.base.subarray.Models1Group17.partialPure,
                JuliaLean.base.subarray.Models1Group17.partialBind]
              rw [axisLength_as_int64]
              simp only
              rw [difference_as_int64, imul_lit, iadd_lit, imul_lit]
              have ih' := ih axes rankTail
                (first + (coordinate.val - axis.first.val) * stride)
                (stride * (axis.last.val - axis.first.val + 1))
              simp only [List.map_cons] at ih'
              rw [ih']
              rw [denseOffset_cons]
              congr 3
              rw [Int.mul_comm (coordinate.val - axis.first.val) stride,
                Int.mul_add stride (coordinate.val - axis.first.val)
                  ((axis.last.val - axis.first.val + 1) *
                    denseOffsetSpec axes (next :: rest))]
              simp only [Int.mul_assoc, Int.add_assoc]

end Lin

/-- The machine result agrees with the global column-major offset modulo 2^64. -/
theorem Models1G17ScalarLinearizationCongruence_proven :
    JuliaLean.Proofs.base.subarray.Models1Group17.ScalarLinearizationCongruence := by
  intro first stride axes coordinates _valid rank
  let exactValue := first.val + stride.val *
    JuliaLean.Proofs.base.subarray.Models1Group17.denseOffsetSpec axes coordinates
  refine ⟨int64 exactValue, ?_, ?_⟩
  · have h := Lin.compute_as_int64 axes coordinates rank first.val stride.val
    simpa only [int64_self] using h
  · change (wrapInt .i64 exactValue - exactValue) % (2 ^ 64 : Int) = 0
    have h := JuliaLean.Proofs.base.int.wrapInt_emod_self IntTy.i64 exactValue
    change wrapInt .i64 exactValue % (2 ^ 64 : Int) =
      exactValue % (2 ^ 64 : Int) at h
    rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod]


end JuliaLean.ChatGPT.Batch9.Group14

namespace JuliaLean.Proofs.base.subarray.Models1Group17
open JuliaLean JuliaLean.base.subarray JuliaLean.base.subarray.Models1Group17
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private def fullUnit : UnitRange64 :=
  ⟨⟨int64 (-(2^63)), int64 (2^63-1)⟩, Or.inl (by decide)⟩
private def oneUnit : UnitRange64 :=
  ⟨⟨int64 1, int64 1⟩, Or.inl (by decide)⟩
private def oneStep : StepRange64 :=
  ⟨⟨int64 1, int64 1, int64 1⟩, by unfold NormalizedStepRange; decide⟩
private def wideStep : StepRange64 :=
  ⟨⟨int64 (-(2^63)), int64 (2^62), int64 (2^62)⟩, by unfold NormalizedStepRange; decide⟩
private def everyOther : StepRange64 :=
  ⟨⟨int64 1, int64 2, int64 3⟩, by unfold NormalizedStepRange; decide⟩

theorem unitRangeViewElementsAndErrors_refuted : ¬ UnitRangeViewElementsAndErrors := by
  intro h
  have bad := h fullUnit oneUnit
  have computed : viewUnitRange64 fullUnit oneUnit = .error .boundsError := by decide
  simp only [computed] at bad
  obtain ⟨position, hp, hb⟩ := bad
  have hcount : selectorCountSpec (.unit oneUnit) = 1 := by decide
  rw [hcount] at hp
  have hp0 : position = 0 := by omega
  subst position
  exact (by decide : ¬ (selectorValueSpec (.unit oneUnit) 0 < 1 ∨
    Int.ofNat (unitCountSpec fullUnit.endpoints) < selectorValueSpec (.unit oneUnit) 0)) hb

theorem unitStepViewElementsAndErrors_refuted : ¬ UnitStepViewElementsAndErrors := by
  intro h
  have bad := h fullUnit oneStep
  have computed : viewUnitRangeStep64 fullUnit oneStep = .error .boundsError := by decide
  simp only [computed] at bad
  obtain ⟨position, hp, hb⟩ := bad
  have hcount : selectorCountSpec (.step oneStep) = 1 := by decide
  rw [hcount] at hp
  have hp0 : position = 0 := by omega
  subst position
  exact (by decide : ¬ (selectorValueSpec (.step oneStep) 0 < 1 ∨
    Int.ofNat (unitCountSpec fullUnit.endpoints) < selectorValueSpec (.step oneStep) 0)) hb

theorem stepRangeViewElementsAndErrors_refuted : ¬ StepRangeViewElementsAndErrors := by
  intro h
  have bad := h wideStep (.step everyOther)
  have computed : viewStepRangeOrdinal64 wideStep (.step everyOther) =
      .ok ⟨int64 (-(2^63)), int64 (-(2^63)), int64 (-(2^63)+1)⟩ := by decide
  simp only [computed] at bad
  exact (by decide : stepCountSpec
    ⟨int64 (-(2^63)), int64 (-(2^63)), int64 (-(2^63)+1)⟩ ≠
      selectorCountSpec (.step everyOther)) bad.2.1

end JuliaLean.Proofs.base.subarray.Models1Group17

namespace JuliaLean.Proofs.base.subarray

open JuliaLean.Registry

def entriesModels1Group17 : List Entry := [
  { id := "subarray-empty-leaf-observations",
    juliaFile := "base/subarray.jl",
    juliaFns := ["_trimmedshape()", "_trimmedpind()", "_trimmedvind()", "rm_singleton_indices(::Tuple)", "substrides(::Tuple{}, ::Tuple{})", "find_extended_dims(dim)"],
    statement := "Terminal tuple helpers introduce no dimensions, selectors or strides.",
    source := "base/subarray.jl:139,145,148,172,439,505 (empty coordinate-domain invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.EmptyLeafObservations, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17EmptyLeafObservations_proven },
  { id := "subarray-fallback-rejects-linear-indexing",
    juliaFile := "base/subarray.jl", juliaFns := ["viewindexing(I::Tuple{Vararg{Any}})"],
    statement := "The fallback indexing style cannot advertise the empty tuple's fast linear indexing.",
    source := "base/subarray.jl:52,65 (indexing-style classification invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FallbackRejectsLinearIndexing, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FallbackRejectsLinearIndexing_proven },
  { id := "subarray-range-trimming-observations",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::AbstractRange)"],
    statement := "Identity range trimming preserves coordinate domains and scalar-versus-range classification.",
    source := "base/subarray.jl:151 (range observation invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.RangeTrimmingPreservesObservations, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17RangeTrimmingObservations_proven },
  { id := "subarray-cached-address-congruence",
    juliaFile := "base/subarray.jl", juliaFns := ["_reindexlinear(V::FastSubArray, i::Int)", "_reindexlinear(V::FastContiguousSubArray, i::Int)"],
    statement := "Both cached scalar parent-address computations equal their mathematical affine addresses modulo the machine word size, including overflowing products and sums.",
    source := "base/subarray.jl:327,351 (machine-address invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.CachedAddressCongruence, thm := some ``JuliaLean.Proofs.base.subarray.Models1Group17.CachedAddressCongruence_proven },
  { id := "subarray-fast-type-leaf-classification",
    juliaFile := "base/subarray.jl", juliaFns := ["IndexStyle(::Type{<:FastSubArray})", "iscontiguous(::Type{<:SubArray})", "iscontiguous(::Type{<:FastContiguousSubArray})"],
    statement := "Fast view types advertise linear indexing, and the contiguity type leaves distinguish unrestricted from fast-contiguous view types.",
    source := "base/subarray.jl:433,461-462 (type-classification invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FastTypeLeafClassification, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FastTypeLeafClassification_proven },
  { id := "subarray-invalid-stride-exception-class",
    juliaFile := "base/subarray.jl", juliaFns := ["substrides(strds, I::Tuple{Any, Vararg{Any}})"],
    statement := "Invalid strided index types always raise ArgumentError, independently of the parent stride tuple and diagnostic type-label contents.",
    source := "base/subarray.jl:443-444 (exception-class invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.InvalidStrideExceptionClass, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17InvalidStrideExceptionClass_proven },
  { id := "subarray-finite-axes-rank-origins",
    juliaFile := "base/subarray.jl", juliaFns := ["axes(::SubArray)"],
    statement := "On the concrete finite representation domain, axes succeeds, has the total retained index-type rank, and preserves Slice/Identity endpoints at their global prefix-rank positions; every non-one-based result axis comes from such a selector.",
    source := "base/subarray.jl:525-531; base/indices.jl:343-345,370-372; doc/src/devdocs/subarrays.md:33-40 (rank and origin preservation)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FiniteAxesRankAndOrigins, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FiniteAxesRankOrigins_proven,
    notes := "Constructor and payload invariants are explicit. Concrete one-based Array metadata, direct range wrappers, and immutable logical-index construction snapshots only; generic row remains blocked." },
  { id := "subarray-finite-size-cardinality",
    juliaFile := "base/subarray.jl", juliaFns := ["size(::SubArray)"],
    statement := "On the concrete finite shape domain, size succeeds with the retained rank and each coordinate equals its observed axis's mathematical endpoint width modulo Int64, including wrapped and negative unchecked-OneTo lengths.",
    source := "base/subarray.jl:70,525-531; base/range.jl:503,705-706,794-817 (shape cardinality invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FiniteSizeCoordinateCardinality, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FiniteSizeCardinality_proven,
    notes := "Mathematical interval-width specification is independent of source machine-length dispatch and wrapping arithmetic. No no-overflow or supplied axes law. Generic row remains blocked." },
  { id := "subarray-finite-axes1-domain",
    juliaFile := "base/subarray.jl", juliaFns := ["axes1(::SubArray)"],
    statement := "On the finite domain, axes1 agrees with the first retained coordinate domain for nonzero-dimensional views, distinguishes an actual empty tuple, and gives zero-dimensional views the singleton linear coordinate domain containing one.",
    source := "base/subarray.jl:525-541; base/abstractarray.jl:140-142 (first-axis coordinate-domain coherence)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FiniteAxes1CoordinateDomain, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FiniteAxes1Domain_proven,
    notes := "Does not assume N equals the number of retained axes; direct SubArray N dispatch is preserved. The partial outer none is distinct from an empty-tuple result. Generic row remains blocked." },
  { id := "subarray-finite-offset-axis-coherence",
    juliaFile := "base/subarray.jl", juliaFns := ["has_offset_axes(::SubArray)"],
    statement := "On the finite domain, has_offset_axes succeeds and is true exactly when an observed output axis begins somewhere other than one.",
    source := "base/subarray.jl:543; base/abstractarray.jl:114-122 (offset-coordinate invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.FiniteOffsetAxisCoherence, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17FiniteOffsetAxisCoherence_proven,
    notes := "Observes output coordinate domains rather than copying the source OR over inputs; direct Slice/Identity origins are retained. Generic row remains blocked." },
  { id := "subarray-scalar-insertion-shape-invariance",
    juliaFile := "base/subarray.jl", juliaFns := ["size(::SubArray)", "axes(::SubArray)", "axes1(::SubArray)", "has_offset_axes(::SubArray)"],
    statement := "Inserting an arbitrary Int64 scalar selector at any tuple position while retaining the explicit N parameter preserves all four partial shape observations, including cases with unsupported tails.",
    source := "base/subarray.jl:70,525-543; doc/src/devdocs/subarrays.md:33-40 (scalar-dimension removal invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ScalarInsertionPreservesShapeObservations, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ScalarInsertionShapeInvariance_proven,
    notes := "Whole-input metamorphic specification; no model result is a premise and both input records carry representation proofs. Tests dispatch and short circuit across all represented inputs." },
  { id := "subarray-singleton-prefix-selection",
    juliaFile := "base/subarray.jl", juliaFns := ["rm_singleton_indices"],
    statement := "Singleton removal retains every nonscalar and exactly those scalar positions whose preceding original indices consume fewer dimensions than the parent rank, preserving their order and values.",
    source := "base/subarray.jl:163-172; base/multidimensional.jl:792-799 (index-rank and preservation invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.SingletonPrefixSelection, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17SingletonPrefixSelection_proven,
    notes := "Closed index_ndims and splitrest dependencies; complete represented input domain, including CartesianIndex{0}. Unchecked because the exact toolchain cannot start in this environment." },
  { id := "subarray-singleton-preserves-nonscalars",
    juliaFile := "base/subarray.jl", juliaFns := ["rm_singleton_indices"],
    statement := "Singleton removal produces a subsequence of the original indices and leaves its complete nonscalar subsequence unchanged.",
    source := "base/subarray.jl:169-172 (index-preservation invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.SingletonPreservesNonscalars, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17SingletonPreservesNonscalars_proven,
    notes := "No assumed bounds or callee correctness." },
  { id := "subarray-unitrange-view-elements-errors",
    juliaFile := "base/subarray.jl", juliaFns := ["view(::AbstractUnitRange, ::AbstractUnitRange{<:Integer})"],
    statement := "For the explicit UnitRange{Int64} specialization, a successful range view preserves the entire mathematical selector sequence and scalar observations; BoundsError needs a bad selected-element witness and OverflowError needs an unrepresentable empty stop.",
    source := "base/subarray.jl:177-188,230-233; base/range.jl:968-972,1002-1026 (documented view selection and concrete error behavior)",
    status := .refuted, refutationEvidence := .runtime, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.UnitRangeViewElementsAndErrors, thm := some ``JuliaLean.Proofs.base.subarray.Models1Group17.unitRangeViewElementsAndErrors_refuted,
    issue := "bugs/subarray-range-view-length-overflow.yaml",
    notes := "Concrete model counterexample confirmed on Julia 1.13.2 and the pinned source commit; see the bug report and reproducer." },
  { id := "subarray-unit-step-view-elements-errors",
    juliaFile := "base/subarray.jl", juliaFns := ["view(::AbstractUnitRange, ::StepRange{<:Integer})"],
    statement := "The concrete Int64 UnitRange/StepRange view preserves the full selector cardinality and element order and agrees with scalar parent indexing; BoundsError requires an invalid selected element and OverflowError requires an impossible empty stop.",
    source := "base/subarray.jl:177-188,234-237; base/range.jl:1002-1011,1034-1049; doc/src/manual/arrays.md:619-621 (view selection and error behavior)",
    status := .refuted, refutationEvidence := .runtime, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.UnitStepViewElementsAndErrors, thm := some ``JuliaLean.Proofs.base.subarray.Models1Group17.unitStepViewElementsAndErrors_refuted,
    issue := "bugs/subarray-range-view-length-overflow.yaml",
    notes := "Concrete model counterexample confirmed on Julia 1.13.2 and the pinned source commit; see the bug report and reproducer." },
  { id := "subarray-step-range-view-elements-errors",
    juliaFile := "base/subarray.jl", juliaFns := ["view(::StepRange, ::AbstractRange{<:Integer})"],
    statement := "The concrete Int64 StepRange view with a UnitRange/StepRange selector preserves the full mathematical selected sequence and scalar observations; bounds, empty-stop overflow, and zero-composed-step errors have independent necessary conditions.",
    source := "base/subarray.jl:177-188,238-241; base/range.jl:353-387,1002-1011,1051-1073; doc/src/manual/arrays.md:619-621 (view selection and error behavior)",
    status := .refuted, refutationEvidence := .runtime, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.StepRangeViewElementsAndErrors, thm := some ``JuliaLean.Proofs.base.subarray.Models1Group17.stepRangeViewElementsAndErrors_refuted,
    issue := "bugs/subarray-step-view-step-overflow.yaml",
    notes := "Concrete model counterexample confirmed on Julia 1.13.2 and the pinned source commit; see the bug report and reproducer." },
  { id := "subarray-colon-view-observations",
    juliaFile := "base/subarray.jl", juliaFns := ["view(::AbstractRange, ::Colon)"],
    statement := "Colon view of either supported immutable Int64 ordinal range succeeds and preserves the full mathematical sequence, scalar reads, and machine length.",
    source := "base/subarray.jl:177-188,252-255; base/range.jl:923,1000 (immutable range view contract)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ColonViewPreservesObservations, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ColonViewObservations_proven,
    notes := "Uses concrete closed copy/getindex dependencies and the existing source wrapper; no identity body or supplied copy law appears as the expected answer. Generic custom range dispatch remains blocked." },
  { id := "subarray-reindex-all-slices-identity",
    juliaFile := "base/subarray.jl", juliaFns := ["reindex"],
    statement := "A parent tuple consisting entirely of Slice indices passes the entire subindex tuple through unchanged when the tuple arities match, for every represented subindex value and type.",
    source := "base/subarray.jl:292,299-300; doc/src/devdocs/subarrays.md:109-119,189-192 (whole-sequence substitution invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ReindexAllSlicesIdentity, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ReindexAllSlicesIdentity_proven,
    notes := "Valid tuple accesses make this structural property independent of propagated inbounds context. Concrete partial reindex body, no getter callback. Generic rows remain blocked." },
  { id := "subarray-reindex-all-scalars-preserve",
    juliaFile := "base/subarray.jl", juliaFns := ["reindex"],
    statement := "Reindexing an all-Int64-scalar parent tuple with an empty subindex tuple preserves the entire original parent sequence, including order, duplicates, machine extremes, and the empty tuple.",
    source := "base/subarray.jl:292,295-296; doc/src/devdocs/subarrays.md:109-119 (whole-sequence substitution invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ReindexAllScalarsPreserve, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ReindexAllScalarsPreserve_proven,
    notes := "No scalar arithmetic or supplied correctness law; no invalid tuple access occurs. Unrepresented Real subtypes and generic array reads remain blocked." },
  { id := "subarray-contiguity-value-independence",
    juliaFile := "base/subarray.jl", juliaFns := ["iscontiguous(::SubArray)"],
    statement := "Changing parent value, cached offset, or cached stride without changing the index-type tags and linear-indexability flag cannot change the contiguity trait.",
    source := "base/subarray.jl:348-349,460-462 (type-trait invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityIgnoresValues, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ContiguityValueIndependence_proven,
    notes := "Uses concrete source type dispatch, not the old erased-Type callback." },
  { id := "subarray-contiguity-dispatch-extremes",
    juliaFile := "base/subarray.jl", juliaFns := ["iscontiguous(::SubArray)"],
    statement := "A slow SubArray is not fast-contiguous; a fast SubArray with an all-scalar stored index tuple, including the empty tuple, is fast-contiguous.",
    source := "base/subarray.jl:348-349,460-462 (source alias and type-trait invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityDispatchExtremes, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ContiguityDispatchExtremes_proven,
    notes := "All represented scalar values and cached layouts quantified." },
  { id := "subarray-contiguity-leading-unitranges",
    juliaFile := "base/subarray.jl", juliaFns := ["iscontiguous(::SubArray)"],
    statement := "A fast view with a leading Slice, IdentityUnitRange, UnitRange, or OneTo index has the fast-contiguous trait for every remaining index tuple.",
    source := "base/subarray.jl:348-349,460-462 (source alias and type-trait invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ContiguityLeadingUnitRanges, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ContiguityLeadingUnitranges_proven,
    notes := "Covers the non-scalar arm of the source type union; no callee or correctness-law inputs." },
  { id := "subarray-scalar-substrides-arity",
    juliaFile := "base/subarray.jl", juliaFns := ["substrides"],
    statement := "For all-scalar selections, equal tuple arities produce no strides; too few strides throw the empty-tail ArgumentError and excess strides reach a MethodError.",
    source := "base/subarray.jl:439-440; base/essentials.jl:541-542 (tuple/selection invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ScalarSubstridesArity, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ScalarSubstridesArity_proven,
    notes := "Complete all-scalar domain of a partial internal model, not completion of generic substrides." },
  { id := "subarray-empty-stride-error-precedence",
    juliaFile := "base/subarray.jl", juliaFns := ["substrides"],
    statement := "A range index with an empty parent-stride tuple raises the empty-first ArgumentError before any step conversion or recursion, including ranges whose later step semantics remain unmodelled.",
    source := "base/subarray.jl:441-442; base/tuple.jl:270 (exception-order invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.EmptyStrideFirstErrorPrecedence, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17EmptyStrideErrorPrecedence_proven,
    notes := "Explicit partial result preserves this known error before an unsupported callee. Generic method remains blocked." },
  { id := "subarray-scalar-stride-no-axis-read",
    juliaFile := "base/subarray.jl", juliaFns := ["compute_stride1"],
    statement := "An all-scalar index tuple returns the incoming machine stride without inspecting parent axes, including an empty parent-axis tuple.",
    source := "base/subarray.jl:450-451 (specialized dispatch invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ScalarStrideDoesNotReadAxes, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ScalarStrideNoAxisRead_proven,
    notes := "Tests recursive dispatch rather than a supplied callback. Generic non-scalar helper remains partial." },
  { id := "subarray-scalar-linearization-congruence",
    juliaFile := "base/subarray.jl", juliaFns := ["compute_linindex"],
    statement := "For every constructible represented parent shape and matching scalar-coordinate tuple, linearization equals the column-major weighted displacement plus the initial offset modulo 2^64, for all initial strides and coordinates.",
    source := "base/subarray.jl:491-501; doc/src/manual/arrays.md (column-major indexing invariant)",
    status := .proven, prop := ``JuliaLean.Proofs.base.subarray.Models1Group17.ScalarLinearizationCongruence, thm := some ``JuliaLean.ChatGPT.Batch9.Group14.Models1G17ScalarLinearizationCongruence_proven,
    notes := "Actual machine-size/shape invariants only; no bounds-success, no-overflow, or callee-correctness assumptions. Generic method remains partial." }
]

end JuliaLean.Proofs.base.subarray


namespace JuliaLean.Proofs.base.subarray.Models2Group14

open JuliaLean JuliaLean.Registry JuliaLean.base.subarray
open JuliaLean.base.subarray.Models2Group14

/-!
Unproved specifications for the full-domain inner-constructor model.
Static review only: these declarations are UNCHECKED. EStateM retains the
post-error world. No operation is assumed pure, correct, or an identity.
-/


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
abbrev ConstructorStateOps (E W P I PI II OI SI C B : Type) :=
  InnerOps (EStateM (Error E) W) P I PI II OI SI C B


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def FieldPreparationObserved {E W A Input B : Type}
    (convert : Input → EStateM (Error E) W (FieldInput A B))
    (input : FieldInput A Input) (before : W)
    (value : FieldInput A B) (after : W) : Prop :=
  match input with
  | .typed original => value = .typed original ∧ after = before
  | .needsConversion original => convert original before = .ok value after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def FieldPreparationFailed {E W A Input B : Type}
    (convert : Input → EStateM (Error E) W (FieldInput A B))
    (input : FieldInput A Input) (before : W)
    (error : Error E) (after : W) : Prop :=
  match input with
  | .typed _ => False
  | .needsConversion original => convert original before = .error error after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def InnerValidationFailureIsolation : Prop :=
  ∀ {E W Tag P I PI II OI SI C B : Type}
    (ops : ConstructorStateOps E W P I PI II OI SI C B)
    (target : ConstructorTarget Tag) (parent : FieldInput P PI) (indices : FieldInput I II)
    (offset : FieldInput I64 OI) (stride : FieldInput I64 SI)
    (before after : W) (error : Error E),
    ops.checkParentIndexMatch parent indices before = .error error after →
      inner (External := E) ops target parent indices offset stride before =
        .error error after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def InnerTypedFieldConservation : Prop :=
  ∀ {E W Tag P I PI II OI SI C B : Type}
    (ops replacements : ConstructorStateOps E W P I PI II OI SI C B)
    (target : ConstructorTarget Tag) (parent : P) (indices : I) (offset stride : I64) (before : W),
    target.parentFieldIsType = true →
    target.indicesFieldIsType = true →
    target.newEligible = true →
    let original := inner (External := E) ops target (.typed parent) (.typed indices)
      (.typed offset) (.typed stride) before
    let replaced := inner (External := E)
      { replacements with checkParentIndexMatch := ops.checkParentIndexMatch }
      target (.typed parent) (.typed indices) (.typed offset) (.typed stride) before
    original = replaced ∧
      match ops.checkParentIndexMatch (.typed parent) (.typed indices) before with
      | .error _ _ => True
      | .ok _ after =>
          ∃ view : View Tag P I,
            original = .ok view after ∧
            view.parent = parent ∧ view.indices = indices ∧
            view.offset1 = offset ∧ view.stride1 = stride ∧ view.typeTag = target.typeTag


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def InnerTypedTargetGateErrors : Prop :=
  ∀ {E W Tag P I PI II OI SI C B : Type}
    (ops : ConstructorStateOps E W P I PI II OI SI C B)
    (target : ConstructorTarget Tag) (parent : P) (indices : I)
    (offset stride : I64) (before after : W) (checked : C),
    ops.checkParentIndexMatch (.typed parent) (.typed indices) before =
      .ok checked after →
    let result := inner (External := E) ops target (.typed parent) (.typed indices)
      (.typed offset) (.typed stride) before
    (target.parentFieldIsType = false →
      result = .error (.isaTypeError .parent) after) ∧
    (target.parentFieldIsType = true → target.indicesFieldIsType = false →
      result = .error (.isaTypeError .indices) after) ∧
    (target.parentFieldIsType = true → target.indicesFieldIsType = true →
      target.newEligible = false → result = .error .newTargetTypeError after)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
def InnerConversionFailureIsolation : Prop :=
  ∀ {E W Tag P I PI II OI SI C B : Type}
    (ops : ConstructorStateOps E W P I PI II OI SI C B)
    (target : ConstructorTarget Tag) (parent : FieldInput P PI) (indices : FieldInput I II)
    (offset : FieldInput I64 OI) (stride : FieldInput I64 SI)
    (before afterCheck afterParent afterIndices afterOffset failedWorld : W)
    (checked : C) (preparedParent : FieldInput P B)
    (preparedIndices : FieldInput I B) (preparedOffset : FieldInput I64 B)
    (error : Error E),
    target.parentFieldIsType = true →
    target.indicesFieldIsType = true →
    ops.checkParentIndexMatch parent indices before = .ok checked afterCheck →
    let result := inner (External := E) ops target parent indices offset stride before
    (FieldPreparationFailed ops.convertParent parent afterCheck error failedWorld →
      result = .error error failedWorld) ∧
    (FieldPreparationObserved ops.convertParent parent afterCheck
        preparedParent afterParent →
      FieldPreparationFailed ops.convertIndices indices afterParent error failedWorld →
      result = .error error failedWorld) ∧
    (FieldPreparationObserved ops.convertParent parent afterCheck
        preparedParent afterParent →
      FieldPreparationObserved ops.convertIndices indices afterParent
        preparedIndices afterIndices →
      FieldPreparationFailed ops.convertOffset offset afterIndices error failedWorld →
      result = .error error failedWorld) ∧
    (FieldPreparationObserved ops.convertParent parent afterCheck
        preparedParent afterParent →
      FieldPreparationObserved ops.convertIndices indices afterParent
        preparedIndices afterIndices →
      FieldPreparationObserved ops.convertOffset offset afterIndices
        preparedOffset afterOffset →
      FieldPreparationFailed ops.convertStride stride afterOffset error failedWorld →
      result = .error error failedWorld)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-23. -/
-- Source: base/subarray.jl:19-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- /Source
theorem innerValidationFailureIsolation_proven : InnerValidationFailureIsolation := by
  intro E W Tag P I PI II OI SI C B ops target parent indices offset stride before after error h
  simp [inner, bind, EStateM.bind, h]

theorem innerTypedFieldConservation_proven : InnerTypedFieldConservation := by
  intro E W Tag P I PI II OI SI C B ops replacements target parent indices offset stride before hp hi hn
  cases h : ops.checkParentIndexMatch (.typed parent) (.typed indices) before with
  | error error after => simp [inner, bind, EStateM.bind, h]
  | ok checked after =>
    simp [inner, prepareField, hp, hi, hn, bind, pure, EStateM.bind, EStateM.pure, h]

theorem innerTypedTargetGateErrors_proven : InnerTypedTargetGateErrors := by
  intro E W Tag P I PI II OI SI C B ops target parent indices offset stride before after checked h
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    simp [inner, h, hp, bind, EStateM.bind]
    rfl
  · intro hp hi
    simp [inner, prepareField, h, hp, hi, bind, pure, EStateM.bind, EStateM.pure]
    rfl
  · intro hp hi hn
    simp [inner, prepareField, h, hp, hi, hn, bind, pure, EStateM.bind, EStateM.pure]
    rfl

private theorem prepareFieldObserved {E W A Input B : Type}
    (convert : Input → EStateM (Error E) W (FieldInput A B))
    (input : FieldInput A Input) (before : W) (value : FieldInput A B) (after : W)
    (h : FieldPreparationObserved convert input before value after) :
    prepareField convert input before = .ok value after := by
  cases input with
  | typed original =>
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | needsConversion original => exact h

private theorem prepareFieldFailed {E W A Input B : Type}
    (convert : Input → EStateM (Error E) W (FieldInput A B))
    (input : FieldInput A Input) (before : W) (error : Error E) (after : W)
    (h : FieldPreparationFailed convert input before error after) :
    prepareField convert input before = .error error after := by
  cases input with
  | typed original => exact False.elim h
  | needsConversion original => exact h

theorem innerConversionFailureIsolation_proven : InnerConversionFailureIsolation := by
  intro E W Tag P I PI II OI SI C B ops target parent indices offset stride
    before afterCheck afterParent afterIndices afterOffset failedWorld checked
    preparedParent preparedIndices preparedOffset error hp hi hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf
    have hf' := prepareFieldFailed _ _ _ _ _ hf
    simp [inner, bind, EStateM.bind, hp, hc, hf']
  · intro ho hf
    have ho' := prepareFieldObserved _ _ _ _ _ ho
    have hf' := prepareFieldFailed _ _ _ _ _ hf
    simp [inner, bind, EStateM.bind, hp, hi, hc, ho', hf']
  · intro hpo hio hf
    have hpo' := prepareFieldObserved _ _ _ _ _ hpo
    have hio' := prepareFieldObserved _ _ _ _ _ hio
    have hf' := prepareFieldFailed _ _ _ _ _ hf
    simp [inner, bind, EStateM.bind, hp, hi, hc, hpo', hio', hf']
  · intro hpo hio hoo hf
    have hpo' := prepareFieldObserved _ _ _ _ _ hpo
    have hio' := prepareFieldObserved _ _ _ _ _ hio
    have hoo' := prepareFieldObserved _ _ _ _ _ hoo
    have hf' := prepareFieldFailed _ _ _ _ _ hf
    simp [inner, bind, EStateM.bind, hp, hi, hc, hpo', hio', hoo', hf']

def constructorEntries : List Entry := [
  { id := "subarray-inner-validation-failure-isolation",
    juliaFile := "base/subarray.jl",
    juliaFns := ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)"],
    statement := "If validation of the original parent and indices throws, construction returns its exact exception and post-error world independently of layout arguments and converters.",
    source := "base/subarray.jl:19-23; invariant: validation failure isolates all field preparation",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.innerValidationFailureIsolation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.InnerValidationFailureIsolation,
    notes := "Arbitrary callbacks and mutable states; no callee correctness laws. Covers inner and its prepareField dependency. Kernel-checked proof registered." },
  { id := "subarray-inner-typed-field-conservation",
    juliaFile := "base/subarray.jl",
    juliaFns := ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)"],
    statement := "When actual fieldtypes and raw-new eligibility permit storage, already typed fields retain every reference, native layout value, and type tag after validation, with no further effects; changing converters cannot change outcomes.",
    source := "base/subarray.jl:14-23; base/essentials.jl:1468-1488; doc/src/manual/constructors.md:136-137; doc/src/manual/arrays.md:1225-1234",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.innerTypedFieldConservation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.InnerTypedFieldConservation,
    notes := "Actual field-type membership and target eligibility are representation conditions; validation remains arbitrary and effectful. Covers inner and prepareField. Kernel-checked proof registered." },
  { id := "subarray-inner-typed-target-gates",
    juliaFile := "base/subarray.jl",
    juliaFns := ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)"],
    statement := "After validation of already typed inputs, non-type actual fieldtype results raise the first isa TypeError; with both fieldtypes valid, an ineligible raw-new target raises its TypeError without additional effects.",
    source := "base/subarray.jl:19-23; src/builtins.c:703-707,1365-1371,1432-1445; src/jltypes.c:2949-2958; src/datatype.c:1709-1720",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.innerTypedTargetGateErrors_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.InnerTypedTargetGateErrors,
    notes := "Flags represent actual Core metadata, not nominal P/I. Arbitrary validation and converter dispatch; post-validation world retained. Covers inner and typed prepareField branches. Kernel-checked proof registered." },
  { id := "subarray-inner-conversion-failure-isolation",
    juliaFile := "base/subarray.jl",
    juliaFns := ["SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)"],
    statement := "A throwing conversion preserves its exact exception and post-error world and prevents later work, even when an earlier successful converter returned a value of the wrong field type or the raw-new target is ineligible.",
    source := "base/subarray.jl:19-23; base/essentials.jl:1468-1488; doc/src/manual/constructors.md:136-137",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.innerConversionFailureIsolation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.InnerConversionFailureIsolation,
    notes := "Actual fieldtype results are types; raw-new eligibility is unrestricted. Every argument tag, conversion outcome and mutable world is quantified. Detects premature target/field checks and lost errors/effects. Covers inner and prepareField. Kernel-checked proof registered." }
]

end JuliaLean.Proofs.base.subarray.Models2Group14


namespace JuliaLean.Proofs.base.subarray.Models2Group14

open JuliaLean JuliaLean.Registry JuliaLean.base.subarray
open JuliaLean.base.subarray.Models2Group14

/-!
Unproved, UNCHECKED invariants of the source mismatch wrapper at line 48.
EStateM is a concrete terminating state/exception interpretation; neither
purity nor any correctness law is imposed on its open-dispatch operations.
-/


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:48-49. -/
-- Source: base/subarray.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def MismatchTupleContentsIrrelevant : Prop :=
  ∀ {E W P Dim OtherMessage : Type}
    (ops : MismatchOps (EStateM (Error E) W) P Dim OtherMessage E)
    (parent : P)
    (left right : JuliaLean.base.subarray.Models2Group14.Tuple Bool),
    left.values.length = right.values.length →
      checkParentIndexMismatch (External := E) ops parent left =
        checkParentIndexMismatch (External := E) ops parent right


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:48-49. -/
-- Source: base/subarray.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def MismatchCannotReturnSuccess : Prop :=
  ∀ {E W P Dim OtherMessage : Type}
    (ops : MismatchOps (EStateM (Error E) W) P Dim OtherMessage E)
    (parent : P) (dimensions : JuliaLean.base.subarray.Models2Group14.Tuple Bool)
    (before after : W),
    checkParentIndexMismatch (External := E) ops parent dimensions before ≠
      .ok () after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:48-49. -/
-- Source: base/subarray.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
def MismatchNdimsFailureIsolation : Prop :=
  ∀ {E W P Dim OtherMessage : Type}
    (ops : MismatchOps (EStateM (Error E) W) P Dim OtherMessage E)
    (parent : P) (dimensions : JuliaLean.base.subarray.Models2Group14.Tuple Bool)
    (before after : W) (error : Error E),
    ops.ndims parent before = .error error after →
      checkParentIndexMismatch (External := E) ops parent dimensions before =
        .error error after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:48-49. -/
-- Source: base/subarray.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- /Source
theorem mismatchTupleContentsIrrelevant_proven : MismatchTupleContentsIrrelevant := by
  intro E W P Dim OtherMessage ops parent left right h
  simp only [checkParentIndexMismatch, h]

theorem mismatchNdimsFailureIsolation_proven : MismatchNdimsFailureIsolation := by
  intro E W P Dim OtherMessage ops parent dimensions before after error h
  simp [checkParentIndexMismatch, bind, EStateM.bind, h]

theorem mismatchCannotReturnSuccess_proven : MismatchCannotReturnSuccess := by
  intro E W P Dim OtherMessage ops parent dimensions before after
  cases hd : ops.ndims parent before with
  | error error final => simp [checkParentIndexMismatch, bind, EStateM.bind, hd]
  | ok dim middle =>
    cases hs : ops.string "number of indices (" (int64 (Int.ofNat dimensions.values.length))
        ") must match the parent dimensionality (" dim ")" middle with
    | error error final =>
      simp only [checkParentIndexMismatch, bind, EStateM.bind, hd, hs]
      intro hbad
      cases hbad
    | ok message final =>
      cases message with
      | typed text =>
        simp only [checkParentIndexMismatch, bind, EStateM.bind, hd, hs]
        intro hbad
        cases hbad
      | needsConversion other =>
        cases he : ops.argumentErrorOther other final <;>
          simp only [checkParentIndexMismatch, bind, EStateM.bind, hd, hs, he] <;>
          intro hbad <;> cases hbad

def wrapperEntries : List Entry := [
  { id := "subarray-mismatch-tuple-content-independence",
    juliaFile := "base/subarray.jl",
    juliaFns := ["check_parent_index_match(parent, ::NTuple{N, Bool}) where {N}"],
    statement := "Changing Bool tuple contents while preserving its arity cannot change the selected mismatch method's result, exception, or state effects.",
    source := "base/subarray.jl:48-49; invariant: only tuple arity is observed",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.mismatchTupleContentsIrrelevant_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.MismatchTupleContentsIrrelevant,
    notes := "Tuple arity is machine-representable. Parent, ndims result, interpolation and non-String constructor dispatch are unrestricted. Kernel-checked proof registered." },
  { id := "subarray-mismatch-no-success",
    juliaFile := "base/subarray.jl",
    juliaFns := ["check_parent_index_match(parent, ::NTuple{N, Bool}) where {N}"],
    statement := "Every completed invocation of the selected mismatch method throws, including all errors and nonstandard return types of its dispatch-selected callees.",
    source := "base/subarray.jl:48-49; invariant: the mismatch branch cannot return success",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.mismatchCannotReturnSuccess_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.MismatchCannotReturnSuccess,
    notes := "Does not assume interpolation returns String or that every thrown value is ArgumentError. No callee correctness laws. Kernel-checked proof registered." },
  { id := "subarray-mismatch-ndims-failure-isolation",
    juliaFile := "base/subarray.jl",
    juliaFns := ["check_parent_index_match(parent, ::NTuple{N, Bool}) where {N}"],
    statement := "If ndims(parent) throws, the mismatch method preserves that exact exception and post-error world before any interpolation or exception construction.",
    source := "base/subarray.jl:48-49; invariant: dimensionality-observation failure isolation",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.mismatchNdimsFailureIsolation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.MismatchNdimsFailureIsolation,
    notes := "All tuple contents and arities, result types, worlds and downstream dispatch are quantified. Kernel-checked proof registered." }
]

end JuliaLean.Proofs.base.subarray.Models2Group14


namespace JuliaLean.Proofs.base.subarray.Models2Group14

open JuliaLean JuliaLean.Registry JuliaLean.base.subarray
open JuliaLean.base.subarray.Models2Group14

/-!
Unproved, UNCHECKED specifications for the two similar wrappers. Every Dims
value is admitted, including negative entries. The observation helpers below
are ghost instrumentation for arbitrary selected allocators, not models of
Base allocation and not assumptions that the allocators satisfy any law.
-/


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def SimilarValueMetadataNoninterference : Prop :=
  ∀ {m : Type → Type} {TagLeft TagRight P ILeft IRight ElementType Result : Type}
    (ops : SimilarValueOps m P ElementType Result)
    (left : View TagLeft P ILeft) (right : View TagRight P IRight)
    (elementType : ElementType)
    (dims : JuliaLean.base.subarray.Models2Group14.Dims),
    left.parent = right.parent →
      similarValue ops left elementType dims = similarValue ops right elementType dims


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def SimilarTypeMetadataNoninterference : Prop :=
  ∀ {m : Type → Type} {ParentType BindingsLeft BindingsRight Result : Type}
    (ops : SimilarTypeOps m ParentType Result)
    (left : ViewType ParentType BindingsLeft)
    (right : ViewType ParentType BindingsRight)
    (dims : JuliaLean.base.subarray.Models2Group14.Dims),
    left.parentType = right.parentType →
      similarType ops left dims = similarType ops right dims


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure SimilarValueRequest (Parent ElementType : Type) where
  parent : Parent
  elementType : ElementType
  dims : JuliaLean.base.subarray.Models2Group14.Dims


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure SimilarTypeRequest (ParentType : Type) where
  parentType : ParentType
  dims : JuliaLean.base.subarray.Models2Group14.Dims


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
structure AllocationObservation (Request E W Result : Type) where
  request : Request
  outcome : Except E Result
  world : W


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def recordAllocation {Request E W Result : Type}
    (request : Request) (action : EStateM E W Result) :
    EStateM E (W × List (AllocationObservation Request E W Result)) Result :=
  fun (world, history) =>
    match action world with
    | .ok value after =>
        .ok value (after, history ++ [⟨request, .ok value, after⟩])
    | .error error after =>
        .error error (after, history ++ [⟨request, .error error, after⟩])


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def observeSimilarValueOps {E W Parent ElementType Result : Type}
    (ops : SimilarValueOps (EStateM E W) Parent ElementType Result) :
    SimilarValueOps
      (EStateM E (W × List
        (AllocationObservation (SimilarValueRequest Parent ElementType) E W Result)))
      Parent ElementType Result where
  similar := fun parent elementType dims =>
    recordAllocation (⟨parent, elementType, dims⟩ : SimilarValueRequest Parent ElementType)
      (ops.similar parent elementType dims)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def observeSimilarTypeOps {E W ParentType Result : Type}
    (ops : SimilarTypeOps (EStateM E W) ParentType Result) :
    SimilarTypeOps
      (EStateM E (W × List
        (AllocationObservation (SimilarTypeRequest ParentType) E W Result)))
      ParentType Result where
  similar := fun parentType dims =>
    recordAllocation (⟨parentType, dims⟩ : SimilarTypeRequest ParentType)
      (ops.similar parentType dims)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def SingleAllocationObserved {Request E W Result : Type}
    (before after : List (AllocationObservation Request E W Result))
    (request : Request) (outcome : Except E Result) (world : W) : Prop :=
  after.length = before.length + 1 ∧
  after.take before.length = before ∧
  ∃ observation,
    after.getLast? = some observation ∧
    observation.request = request ∧
    observation.outcome = outcome ∧
    observation.world = world


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def SimilarValueRequestIntegrity : Prop :=
  ∀ {E W Tag Parent Indices ElementType Result : Type}
    (ops : SimilarValueOps (EStateM E W) Parent ElementType Result)
    (view : View Tag Parent Indices) (elementType : ElementType)
    (dims : JuliaLean.base.subarray.Models2Group14.Dims) (world : W)
    (history : List
      (AllocationObservation (SimilarValueRequest Parent ElementType) E W Result)),
    match similarValue (observeSimilarValueOps ops) view elementType dims
        (world, history) with
    | .ok value (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory
          (⟨view.parent, elementType, dims⟩ : SimilarValueRequest Parent ElementType)
          (.ok value) afterWorld
    | .error error (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory
          (⟨view.parent, elementType, dims⟩ : SimilarValueRequest Parent ElementType)
          (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
def SimilarTypeRequestIntegrity : Prop :=
  ∀ {E W ParentType OtherBindings Result : Type}
    (ops : SimilarTypeOps (EStateM E W) ParentType Result)
    (viewType : ViewType ParentType OtherBindings)
    (dims : JuliaLean.base.subarray.Models2Group14.Dims) (world : W)
    (history : List
      (AllocationObservation (SimilarTypeRequest ParentType) E W Result)),
    match similarType (observeSimilarTypeOps ops) viewType dims (world, history) with
    | .ok value (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory
          (⟨viewType.parentType, dims⟩ : SimilarTypeRequest ParentType)
          (.ok value) afterWorld
    | .error error (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory
          (⟨viewType.parentType, dims⟩ : SimilarTypeRequest ParentType)
          (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:72-73. -/
-- Source: base/subarray.jl:72-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- /Source
theorem similarValueMetadataNoninterference_proven : SimilarValueMetadataNoninterference := by
  intro m TagLeft TagRight P ILeft IRight ElementType Result ops left right elementType dims h
  simp only [similarValue, h]

theorem similarTypeMetadataNoninterference_proven : SimilarTypeMetadataNoninterference := by
  intro m ParentType BindingsLeft BindingsRight Result ops left right dims h
  simp only [similarType, h]

private theorem singleAllocationAppend {Request E W Result : Type}
    (history : List (AllocationObservation Request E W Result))
    (request : Request) (outcome : Except E Result) (world : W) :
    SingleAllocationObserved history (history ++ [⟨request, outcome, world⟩])
      request outcome world := by
  refine ⟨by simp, by simp, ⟨request, outcome, world⟩, ?_, rfl, rfl, rfl⟩
  simp

theorem similarValueRequestIntegrity_proven : SimilarValueRequestIntegrity := by
  intro E W Tag Parent Indices ElementType Result ops view elementType dims world history
  cases h : ops.similar view.parent elementType dims world <;>
    simpa [similarValue, observeSimilarValueOps, recordAllocation, h] using
      singleAllocationAppend history
        (⟨view.parent, elementType, dims⟩ : SimilarValueRequest Parent ElementType) _ _

theorem similarTypeRequestIntegrity_proven : SimilarTypeRequestIntegrity := by
  intro E W ParentType OtherBindings Result ops viewType dims world history
  cases h : ops.similar viewType.parentType dims world <;>
    simpa [similarType, observeSimilarTypeOps, recordAllocation, h] using
      singleAllocationAppend history
        (⟨viewType.parentType, dims⟩ : SimilarTypeRequest ParentType) _ _

def similarEntries : List Entry := [
  { id := "subarray-similar-value-metadata-independence",
    juliaFile := "base/subarray.jl", juliaFns := ["similar(V::SubArray, T::Type, dims::Dims)"],
    statement := "Views sharing the same parent produce identical explicit-type, explicit-dimensions allocation effects and results, independently of every other view field.",
    source := "base/subarray.jl:72; doc/src/manual/interfaces.md:229,320,364",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.similarValueMetadataNoninterference_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.SimilarValueMetadataNoninterference,
    notes := "All effect carriers and allocators are quantified without laws; explicit element-type selector and allocated result have separate types. All native Dims tuples admitted. Kernel-checked proof registered." },
  { id := "subarray-similar-value-request-integrity",
    juliaFile := "base/subarray.jl", juliaFns := ["similar(V::SubArray, T::Type, dims::Dims)"],
    statement := "Each call issues exactly one allocator request with the exact parent identity, element-type selector and dimensions, preserving its observed returned value or exception and post-call world.",
    source := "base/subarray.jl:72; doc/src/manual/interfaces.md:229,320,364",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.similarValueRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.SimilarValueRequestIntegrity,
    notes := "Ghost observation wraps arbitrary allocators, not a callee-correctness premise. Negative dimensions remain in the domain. Kernel-checked proof registered." },
  { id := "subarray-similar-type-metadata-independence",
    juliaFile := "base/subarray.jl", juliaFns := ["similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}}"],
    statement := "SubArray types with the same selected parent-type binding produce identical allocation effects and results regardless of all unused type bindings.",
    source := "base/subarray.jl:73; doc/src/manual/interfaces.md:233",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.similarTypeMetadataNoninterference_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.SimilarTypeMetadataNoninterference,
    notes := "All effect carriers and selected parent allocators are quantified without correctness laws. Result is an allocated value, not a Lean Type. Kernel-checked proof registered." },
  { id := "subarray-similar-type-request-integrity",
    juliaFile := "base/subarray.jl", juliaFns := ["similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}}"],
    statement := "Each call issues exactly one request with the selected parent type and unchanged dimensions, retaining the observed allocator's value or exception and post-call world.",
    source := "base/subarray.jl:73; doc/src/manual/interfaces.md:233",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.similarTypeRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.SimilarTypeRequestIntegrity,
    notes := "Ghost recording wraps every arbitrary effectful allocator. Full Dims domain includes zero and negative entries. Kernel-checked proof registered." }
]

end JuliaLean.Proofs.base.subarray.Models2Group14


namespace JuliaLean.Proofs.base.subarray.Models2Group14

open JuliaLean JuliaLean.Registry JuliaLean.base.subarray
open JuliaLean.base.subarray.Models2Group14

/-!
Unproved, UNCHECKED internal invariants for source lines 150,153,154,165,166,168.
This fragment follows similar-statements.lean in StatementsGroup14.lean and
reuses its specification-only AllocationObservation, recordAllocation, and
SingleAllocationObserved helpers. Ghost histories are not Julia arrays.
-/


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def liftTrimHistory {E W History Result : Type} (action : EStateM E W Result) :
    EStateM E (W × History) Result :=
  fun (world, history) =>
    match action world with
    | .ok value after => .ok value (after, history)
    | .error error after => .error error (after, history)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def observeTrimScalarOps {E W Scalar Result : Type}
    (ops : TrimScalarOps (EStateM E W) Scalar Result) :
    TrimScalarOps
      (EStateM E (W × List (AllocationObservation (Scalar × I64) E W Result)))
      Scalar Result where
  oftype := fun index value => recordAllocation (index, value) (ops.oftype index value)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def TrimScalarRequestIntegrity : Prop :=
  ∀ {E W Scalar Result : Type}
    (ops : TrimScalarOps (EStateM E W) Scalar Result) (index : Scalar) (world : W)
    (history : List (AllocationObservation (Scalar × I64) E W Result)),
    match trimmedScalar (observeTrimScalarOps ops) index (world, history) with
    | .ok result (afterWorld, afterHistory) =>
        ∃ nativeOne : I64, nativeOne.val = 1 ∧
          SingleAllocationObserved history afterHistory (index, nativeOne)
            (.ok result) afterWorld
    | .error error (afterWorld, afterHistory) =>
        ∃ nativeOne : I64, nativeOne.val = 1 ∧
          SingleAllocationObserved history afterHistory (index, nativeOne)
            (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def TrimScalarArrayFailureIsolation : Prop :=
  ∀ {E W A Indices Axes Shaped Result : Type}
    (ops : TrimScalarArrayOps (EStateM E W) A Indices Axes Shaped Result)
    (index : A) (before afterIndices afterAxes failedWorld : W)
    (indices : Indices) (axes : Axes) (error : E),
    let result := trimmedScalarArray ops index before
    (ops.eachindex .linear index before = .error error failedWorld →
      result = .error error failedWorld) ∧
    (ops.eachindex .linear index before = .ok indices afterIndices →
      ops.axes index afterIndices = .error error failedWorld →
      result = .error error failedWorld) ∧
    (ops.eachindex .linear index before = .ok indices afterIndices →
      ops.axes index afterIndices = .ok axes afterAxes →
      ops.reshape indices axes afterAxes = .error error failedWorld →
      result = .error error failedWorld)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def observeTrimScalarArrayFinalOps {E W A Indices Axes Shaped Result : Type}
    (ops : TrimScalarArrayOps (EStateM E W) A Indices Axes Shaped Result) :
    TrimScalarArrayOps
      (EStateM E (W × List (AllocationObservation (A × Shaped) E W Result)))
      A Indices Axes Shaped Result where
  eachindex := fun style index => liftTrimHistory (ops.eachindex style index)
  axes := fun index => liftTrimHistory (ops.axes index)
  reshape := fun indices axes => liftTrimHistory (ops.reshape indices axes)
  oftype := fun index shaped => recordAllocation (index, shaped) (ops.oftype index shaped)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def TrimScalarArrayFinalRequestIntegrity : Prop :=
  ∀ {E W A Indices Axes Shaped Result : Type}
    (ops : TrimScalarArrayOps (EStateM E W) A Indices Axes Shaped Result)
    (index : A) (before afterIndices afterAxes afterShape : W)
    (indices : Indices) (axes : Axes) (shaped : Shaped)
    (history : List (AllocationObservation (A × Shaped) E W Result)),
    ops.eachindex .linear index before = .ok indices afterIndices →
    ops.axes index afterIndices = .ok axes afterAxes →
    ops.reshape indices axes afterAxes = .ok shaped afterShape →
    match trimmedScalarArray (observeTrimScalarArrayFinalOps ops) index
        (before, history) with
    | .ok result (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory (index, shaped)
          (.ok result) afterWorld
    | .error error (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory (index, shaped)
          (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def TrimCartesianZeroCopyFailureIsolation : Prop :=
  ∀ {E W A Copied Result : Type}
    (ops : TrimCartesianZeroOps (EStateM E W) A Copied Result)
    (index : A) (before after : W) (error : E),
    ops.copy index before = .error error after →
      trimmedCartesianZero ops index before = .error error after


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def observeTrimCartesianZeroFinalOps {E W A Copied Result : Type}
    (ops : TrimCartesianZeroOps (EStateM E W) A Copied Result) :
    TrimCartesianZeroOps
      (EStateM E (W × List (AllocationObservation (A × Copied) E W Result)))
      A Copied Result where
  copy := fun index => liftTrimHistory (ops.copy index)
  oftype := fun index copied => recordAllocation (index, copied) (ops.oftype index copied)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def TrimCartesianZeroFinalRequestIntegrity : Prop :=
  ∀ {E W A Copied Result : Type}
    (ops : TrimCartesianZeroOps (EStateM E W) A Copied Result)
    (index : A) (before afterCopy : W) (copied : Copied)
    (history : List (AllocationObservation (A × Copied) E W Result)),
    ops.copy index before = .ok copied afterCopy →
    match trimmedCartesianZero (observeTrimCartesianZeroFinalOps ops) index
        (before, history) with
    | .ok result (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory (index, copied)
          (.ok result) afterWorld
    | .error error (afterWorld, afterHistory) =>
        SingleAllocationObserved history afterHistory (index, copied)
          (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def ReshapeParentBooleanContentIndependence : Prop :=
  ∀ {m : Type → Type} {A Result : Type}
    (ops : ReshapeParentOps m A Result) (array : A) (leftBit rightBit : Bool)
    (left right : JuliaLean.base.subarray.Models2Group14.Tuple Bool),
    reshapeParentOne ops array leftBit = reshapeParentOne ops array rightBit ∧
    (left.values.length = right.values.length →
      reshapeParentRank ops array left = reshapeParentRank ops array right)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def observeReshapeParentOps {E W A Result : Type}
    (ops : ReshapeParentOps (EStateM E W) A Result) :
    ReshapeParentOps
      (EStateM E (W × List (AllocationObservation (A × ValRank) E W Result)))
      A Result where
  reshape := fun array rank => recordAllocation (array, rank) (ops.reshape array rank)


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def ReshapeParentOneRequestIntegrity : Prop :=
  ∀ {E W A Result : Type}
    (ops : ReshapeParentOps (EStateM E W) A Result) (array : A)
    (dimension : Bool) (world : W)
    (history : List (AllocationObservation (A × ValRank) E W Result)),
    match reshapeParentOne (observeReshapeParentOps ops) array dimension
        (world, history) with
    | .ok result (afterWorld, afterHistory) =>
        ∃ rank : ValRank, rank.value.val = 1 ∧
          SingleAllocationObserved history afterHistory (array, rank) (.ok result) afterWorld
    | .error error (afterWorld, afterHistory) =>
        ∃ rank : ValRank, rank.value.val = 1 ∧
          SingleAllocationObserved history afterHistory (array, rank) (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def ReshapeParentRankRequestIntegrity : Prop :=
  ∀ {E W A Result : Type}
    (ops : ReshapeParentOps (EStateM E W) A Result) (array : A)
    (dimensions : JuliaLean.base.subarray.Models2Group14.Tuple Bool) (world : W)
    (history : List (AllocationObservation (A × ValRank) E W Result)),
    match reshapeParentRank (observeReshapeParentOps ops) array dimensions
        (world, history) with
    | .ok result (afterWorld, afterHistory) =>
        ∃ rank : ValRank, rank.value.val = Int.ofNat dimensions.values.length ∧
          SingleAllocationObserved history afterHistory (array, rank) (.ok result) afterWorld
    | .error error (afterWorld, afterHistory) =>
        ∃ rank : ValRank, rank.value.val = Int.ofNat dimensions.values.length ∧
          SingleAllocationObserved history afterHistory (array, rank) (.error error) afterWorld


/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:150-168. -/
-- Source: base/subarray.jl:150-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
theorem trimScalarArrayFailureIsolation_proven : TrimScalarArrayFailureIsolation := by
  intro E W A Indices Axes Shaped Result ops index before afterIndices afterAxes failedWorld indices axes error
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [trimmedScalarArray, bind, EStateM.bind, h]
  · intro h1 h2
    simp [trimmedScalarArray, bind, EStateM.bind, h1, h2]
  · intro h1 h2 h3
    simp [trimmedScalarArray, bind, EStateM.bind, h1, h2, h3]

theorem trimCartesianZeroCopyFailureIsolation_proven : TrimCartesianZeroCopyFailureIsolation := by
  intro E W A Copied Result ops index before after error h
  simp [trimmedCartesianZero, bind, EStateM.bind, h]

theorem reshapeParentBooleanContentIndependence_proven : ReshapeParentBooleanContentIndependence := by
  intro m A Result ops array leftBit rightBit left right
  exact ⟨rfl, fun h => by simp only [reshapeParentRank, h]⟩

theorem trimScalarRequestIntegrity_proven : TrimScalarRequestIntegrity := by
  intro E W Scalar Result ops index world history
  cases h : ops.oftype index (int64 1) world <;>
    simp only [trimmedScalar, observeTrimScalarOps, recordAllocation, h] <;>
    exact ⟨int64 1, by decide, singleAllocationAppend history _ _ _⟩

theorem trimScalarArrayFinalRequestIntegrity_proven : TrimScalarArrayFinalRequestIntegrity := by
  intro E W A Indices Axes Shaped Result ops index before afterIndices afterAxes afterShape
    indices axes shaped history hi ha hs
  cases h : ops.oftype index shaped afterShape <;>
    simpa [trimmedScalarArray, observeTrimScalarArrayFinalOps, liftTrimHistory,
      recordAllocation, bind, EStateM.bind, hi, ha, hs, h] using
      singleAllocationAppend history (index, shaped) _ _

theorem trimCartesianZeroFinalRequestIntegrity_proven : TrimCartesianZeroFinalRequestIntegrity := by
  intro E W A Copied Result ops index before afterCopy copied history hc
  cases h : ops.oftype index copied afterCopy <;>
    simpa [trimmedCartesianZero, observeTrimCartesianZeroFinalOps, liftTrimHistory,
      recordAllocation, bind, EStateM.bind, hc, h] using
      singleAllocationAppend history (index, copied) _ _

theorem reshapeParentOneRequestIntegrity_proven : ReshapeParentOneRequestIntegrity := by
  intro E W A Result ops array dimension world history
  cases h : ops.reshape array ⟨int64 1⟩ world <;>
    simp only [reshapeParentOne, observeReshapeParentOps, recordAllocation, h] <;>
    exact ⟨⟨int64 1⟩, by decide, singleAllocationAppend history _ _ _⟩

theorem reshapeParentRankRequestIntegrity_proven : ReshapeParentRankRequestIntegrity := by
  intro E W A Result ops array dimensions world history
  have hval : (int64 dimensions.values.length).val = dimensions.values.length := by
    change wrapInt .i64 dimensions.values.length = dimensions.values.length
    apply wrapInt_of_inRange
    have := dimensions.nativeArity
    constructor <;> simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] <;> omega
  cases h : ops.reshape array ⟨int64 dimensions.values.length⟩ world <;>
    simp only [reshapeParentRank, observeReshapeParentOps, recordAllocation, h] <;>
    exact ⟨⟨int64 dimensions.values.length⟩, hval, singleAllocationAppend history _ _ _⟩

def trimReshapeEntries : List Entry := [
  { id := "subarray-trim-scalar-request-integrity",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::ScalarIndex)"],
    statement := "Scalar trimming issues exactly one oftype request using the original scalar and native one, retaining that request's value or exception and effects.",
    source := "base/subarray.jl:150; invariant: scalar normalization request and outcome provenance",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.trimScalarRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.TrimScalarRequestIntegrity,
    notes := "All custom/nonnative Real payloads and arbitrary effectful oftype implementations are quantified without laws. Kernel-checked proof registered." },
  { id := "subarray-trim-scalar-array-failure-isolation",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::AbstractArray{<:ScalarIndex})"],
    statement := "Errors from linear eachindex, axes, or reshape stop scalar-array trimming at that stage and retain the exact post-error world.",
    source := "base/subarray.jl:153; invariant: sequential failure isolation",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.trimScalarArrayFailureIsolation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.TrimScalarArrayFailureIsolation,
    notes := "All index/axis/result carriers and mutable effects remain unrestricted. Observations impose no callee-correctness laws. Kernel-checked proof registered." },
  { id := "subarray-trim-scalar-array-final-request",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::AbstractArray{<:ScalarIndex})"],
    statement := "After observed successful index, axes and reshape operations, the sole final conversion receives the original array and actual shaped value and preserves its observed outcome and effects.",
    source := "base/subarray.jl:153; doc/src/manual/interfaces.md:219-233; invariant: conversion argument/result provenance",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.trimScalarArrayFinalRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.TrimScalarArrayFinalRequestIntegrity,
    notes := "Arbitrary custom operations are instrumented, not assumed correct. Nonstandard indexing is unrestricted. Kernel-checked proof registered." },
  { id := "subarray-trim-cartesian-zero-copy-failure",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}})"],
    statement := "A copy exception is retained with its exact post-error world before any oftype request in Cartesian-zero index trimming.",
    source := "base/subarray.jl:154; invariant: copy-failure isolation",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.trimCartesianZeroCopyFailureIsolation_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.TrimCartesianZeroCopyFailureIsolation,
    notes := "Custom copy may allocate, mutate or throw; no freshness/correctness law is imposed. Kernel-checked proof registered." },
  { id := "subarray-trim-cartesian-zero-final-request",
    juliaFile := "base/subarray.jl", juliaFns := ["_trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}})"],
    statement := "The actual copy result is passed unchanged to one oftype request with the original array as witness, preserving the conversion's observed outcome and effects.",
    source := "base/subarray.jl:154; invariant: copy and conversion identity provenance",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.trimCartesianZeroFinalRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.TrimCartesianZeroFinalRequestIntegrity,
    notes := "All copied and returned object identities, mutation and errors are admitted; no callee correctness laws. Kernel-checked proof registered." },
  { id := "subarray-reshape-parent-bool-content-independence",
    juliaFile := "base/subarray.jl",
    juliaFns := ["_maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool})", "_maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool})", "_maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N}"],
    statement := "Changing Bool values without changing tuple arity cannot change parent reshape requests, returned values, errors, or effects.",
    source := "base/subarray.jl:165-166,168; invariant: type-arity-only Bool tuple use",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.reshapeParentBooleanContentIndependence_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.ReshapeParentBooleanContentIndependence,
    notes := "Generic effect carriers and arbitrary selected reshape methods, including custom vector behavior. Kernel-checked proof registered." },
  { id := "subarray-reshape-parent-one-request-integrity",
    juliaFile := "base/subarray.jl",
    juliaFns := ["_maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool})", "_maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool})"],
    statement := "Both rank-one methods make one request using the original parent and Val parameter one, retaining the selected reshape's observed result or exception and world.",
    source := "base/subarray.jl:165-166; base/essentials.jl:1199-1203; invariant: reshape request/rank provenance",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.reshapeParentOneRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.ReshapeParentOneRequestIntegrity,
    notes := "Covers concrete ValRank metadata and both shared-body source methods; no identity shortcut for vector parents. Kernel-checked proof registered." },
  { id := "subarray-reshape-parent-rank-request-integrity",
    juliaFile := "base/subarray.jl", juliaFns := ["_maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N}"],
    statement := "The generic fallback makes one request with the original parent and a native Val parameter exactly equal to tuple arity, retaining the observed reshape outcome and world.",
    source := "base/subarray.jl:168; base/essentials.jl:1199-1203; invariant: exact native rank/request provenance",
    status := .proven, thm := some ``JuliaLean.Proofs.base.subarray.Models2Group14.reshapeParentRankRequestIntegrity_proven, prop := ``JuliaLean.Proofs.base.subarray.Models2Group14.ReshapeParentRankRequestIntegrity,
    notes := "Existing Tuple native-arity bound ensures constructibility. Covers ValRank; no reshape correctness law is assumed. Kernel-checked proof registered." }
]

end JuliaLean.Proofs.base.subarray.Models2Group14

namespace JuliaLean.Proofs.base.subarray
/-- Recovered additive declaration; UNCHECKED. Source base/subarray.jl:19-168. -/
-- Source: base/subarray.jl:19-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function SubArray{T,N,P,I,L}(parent, indices, offset1, stride1) where {T,N,P,I,L}
--         @inline
--         check_parent_index_match(parent, indices)
--         new(parent, indices, offset1, stride1)
--     end
-- end
-- # Compute the linear indexability of the indices, and combine it with the linear indexing of the parent
-- function SubArray(parent::AbstractArray, indices::Tuple)
--     @inline
--     SubArray(IndexStyle(viewindexing(indices), IndexStyle(parent)), parent, ensure_indexable(indices), index_dimsum(indices...))
-- end
-- function SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     SubArray{eltype(P), N, P, I, false}(parent, indices, 0, 0)
-- end
-- function SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}
--     @inline
--     offset1, stride1 = _compute_linear_layout(parent, indices)
--     SubArray{eltype(P), N, P, I, true}(parent, indices, offset1, stride1)
-- end
-- 
-- function _compute_linear_layout(parent, indices)
--     @inline
--     stride1 = Int(compute_stride1(parent, indices))
--     return Int(compute_offset1(parent, stride1, indices)), stride1
-- end
-- 
-- check_parent_index_match(parent, indices) = check_parent_index_match(parent, index_ndims(indices...))
-- check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N, Bool}) where {T,N} = nothing
-- check_parent_index_match(parent, ::NTuple{N, Bool}) where {N} =
--     throw(ArgumentError("number of indices ($N) must match the parent dimensionality ($(ndims(parent)))"))
-- 
-- # This computes the linear indexing compatibility for a given tuple of indices
-- viewindexing(I::Tuple{}) = IndexLinear()
-- # Leading scalar indices simply increase the stride
-- viewindexing(I::Tuple{ScalarIndex, Vararg{Any}}) = (@inline; viewindexing(tail(I)))
-- # Slices may begin a section which may be followed by any number of Slices
-- viewindexing(I::Tuple{Slice, Slice, Vararg{Any}}) = (@inline; viewindexing(tail(I)))
-- # A UnitRange can follow Slices, but only if all other indices are scalar
-- viewindexing(I::Tuple{Slice, AbstractUnitRange, Vararg{ScalarIndex}}) = IndexLinear()
-- viewindexing(I::Tuple{Slice, Slice, Vararg{ScalarIndex}}) = IndexLinear() # disambiguate
-- # In general, scalar ranges are only fast if all other indices are scalar
-- # Other ranges, such as those of `CartesianIndex`es, are not fast even if these
-- # are followed by `ScalarIndex`es
-- viewindexing(I::Tuple{AbstractRange{<:ScalarIndex}, Vararg{ScalarIndex}}) = IndexLinear()
-- # All other index combinations are slow
-- viewindexing(I::Tuple{Vararg{Any}}) = IndexCartesian()
-- # Of course, all other array types are slow
-- viewindexing(I::Tuple{AbstractArray, Vararg{Any}}) = IndexCartesian()
-- 
-- # Simple utilities
-- size(V::SubArray) = (@inline; map(length, axes(V)))
-- 
-- similar(V::SubArray, T::Type, dims::Dims) = similar(V.parent, T, dims)
-- similar(::Type{TA}, dims::Dims) where {T,N,P,TA<:SubArray{T,N,P}} = similar(P, dims)
-- 
-- sizeof(V::SubArray) = length(V) * sizeof(eltype(V))
-- sizeof(V::SubArray{<:Any,<:Any,<:Array}) = length(V) * elsize(V.parent)
-- 
-- function Base.copy(V::SubArray)
--     v = V.parent[V.indices...]
--     ndims(V) == 0 || return v
--     x = similar(V) # ensure proper type of x
--     x[] = v
--     return x
-- end
-- 
-- parent(V::SubArray) = V.parent
-- parentindices(V::SubArray) = V.indices
-- 
-- """
--     parentindices(A)
-- 
-- Return the indices in the [`parent`](@ref) which correspond to the view `A`.
-- 
-- # Examples
-- ```jldoctest
-- julia> A = [1 2; 3 4];
-- 
-- julia> V = view(A, 1, :)
-- 2-element view(::Matrix{Int64}, 1, :) with eltype Int64:
--  1
--  2
-- 
-- julia> parentindices(V)
-- (1, Base.Slice(Base.OneTo(2)))
-- ```
-- """
-- function parentindices end
-- 
-- parentindices(a::AbstractArray) = map(oneto, size(a))
-- 
-- ## Aliasing detection
-- dataids(A::SubArray) = (dataids(A.parent)..., _splatmap(dataids, A.indices)...)
-- _splatmap(f, ::Tuple{}) = ()
-- _splatmap(f, t::Tuple) = (f(t[1])..., _splatmap(f, tail(t))...)
-- unaliascopy(A::SubArray) = typeof(A)(unaliascopy(A.parent), map(unaliascopy, A.indices), A.offset1, A.stride1)
-- 
-- # When the parent is an Array we can trim the size down a bit. In the future this
-- # could possibly be extended to any mutable array.
-- function unaliascopy(V::SubArray{T,N,A,I,LD}) where {T,N,A<:Array,I<:Tuple{Vararg{Union{ScalarIndex,AbstractRange{<:ScalarIndex},Array{<:Union{ScalarIndex,AbstractCartesianIndex}}}}},LD}
--     dest = Array{T}(undef, _trimmedshape(V.indices...))
--     trimmedpind = _trimmedpind(V.indices...)
--     vdest = trimmedpind isa Tuple{Vararg{Union{Slice,Colon}}} ? dest : view(dest, trimmedpind...)
--     copyto!(vdest, view(V, _trimmedvind(V.indices...)...))
--     indices = map(_trimmedindex, V.indices)
--     if LD
--         offset1, stride1 = _compute_linear_layout(dest, indices)
--     else
--         offset1, stride1 = 0, 0
--     end
--     SubArray{T,N,A,I,LD}(dest, indices, offset1, stride1)
-- end
-- # Get the proper trimmed shape
-- _trimmedshape(::ScalarIndex, rest...) = (1, _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractRange, rest...) = (isempty(i) ? zero(eltype(i)) : maximum(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::Union{UnitRange,StepRange,OneTo}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:ScalarIndex}, rest...) = (length(i), _trimmedshape(rest...)...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedshape(rest...)
-- _trimmedshape(i::AbstractArray{<:AbstractCartesianIndex{N}}, rest...) where {N} = (length(i), ntuple(Returns(1), Val(N - 1))..., _trimmedshape(rest...)...)
-- _trimmedshape() = ()
-- # We can avoid the repetition from `AbstractArray{CartesianIndex{0}}`
-- _trimmedpind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractRange, rest...) = (i, _trimmedpind(rest...)...)
-- _trimmedpind(i::Union{UnitRange,StepRange,OneTo}, rest...) = ((:), _trimmedpind(rest...)...)
-- _trimmedpind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = _trimmedpind(rest...)
-- _trimmedpind() = ()
-- _trimmedvind(i, rest...) = (map(Returns(:), axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind(i::AbstractArray{<:AbstractCartesianIndex{0}}, rest...) = (map(first, axes(i))..., _trimmedvind(rest...)...)
-- _trimmedvind() = ()
-- # Transform indices to be "dense"
-- _trimmedindex(i::ScalarIndex) = oftype(i, 1)
-- _trimmedindex(i::AbstractRange) = i
-- _trimmedindex(i::Union{UnitRange,StepRange,OneTo}) = oftype(i, oneto(length(i)))
-- _trimmedindex(i::AbstractArray{<:ScalarIndex}) = oftype(i, reshape(eachindex(IndexLinear(), i), axes(i)))
-- _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{0}}) = oftype(i, copy(i))
-- function _trimmedindex(i::AbstractArray{<:AbstractCartesianIndex{N}}) where {N}
--     padding = ntuple(Returns(1), Val(N - 1))
--     ax1 = eachindex(IndexLinear(), i)
--     return oftype(i, reshape(CartesianIndices((ax1, padding...)), axes(i)))
-- end
-- ## SubArray creation
-- # We always assume that the dimensionality of the parent matches the number of
-- # indices that end up getting passed to it, so we store the parent as a
-- # ReshapedArray view if necessary. The trouble is that arrays of `CartesianIndex`
-- # can make the number of effective indices not equal to length(I).
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,1}, ::NTuple{1, Bool}) = reshape(A, Val(1))
-- _maybe_reshape_parent(A::AbstractArray{<:Any,N}, ::NTuple{N, Bool}) where {N} = A
-- _maybe_reshape_parent(A::AbstractArray, ::NTuple{N, Bool}) where {N} = reshape(A, Val(N))
-- /Source
def entriesModels2Group14 : List JuliaLean.Registry.Entry :=
  Models2Group14.constructorEntries ++ Models2Group14.wrapperEntries ++
  Models2Group14.similarEntries ++ Models2Group14.trimReshapeEntries
end JuliaLean.Proofs.base.subarray

namespace JuliaLean.Proofs.base.subarray.LegacyRetired

open JuliaLean JuliaLean.base.subarray JuliaLean.Registry

def WholeSlices (axes : List Axis) (indices : List Index) : Prop :=
  ∀ pair ∈ axes.zip indices, ∀ selected,
    pair.2 = .slice selected → selected = pair.1

def WholeAxisLinearConstruction : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices →
    ∃ view : SubArray P T,
      subarrayLinear parent indices (List.replicate (viewAxesManual indices).length true)
        (checkParentIndexMatchWithOps ops) (computeLinearLayoutWithOps ops) = .ok view ∧
      view.parent = parent ∧ view.indices = indices ∧ view.linear = true ∧
      view.dimensions = List.replicate (viewAxesManual indices).length true ∧
      ViewAddressCorrect ops parent indices view

def WholeAxisAssignedInBounds : Prop :=
  ∀ {P T : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices → (viewAxesManual indices).length = 1 →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ (check : SubArray P T → I64 → Bool) (assigned : P → I64 → Jl Bool),
          check view (linearPosition (viewAxesManual indices) coordinates) = true →
          isassignedFastVectorSubArray view (linearPosition (viewAxesManual indices) coordinates)
            check assigned = assigned parent (linearPosition (ops.axes parent) selected)

def WholeAxisWriteInBounds : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices → (viewAxesManual indices).length = 1 →
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

def WholeAxisContiguousPointer : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices →
    (match indices with | [] => true | index :: _ => index.isUnitRange || Index.allScalar indices) = true →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ pointer : P → I64 → Jl R,
          pointerFastContiguousSubArray view (linearPosition (viewAxesManual indices) coordinates) pointer =
            pointer parent (linearPosition (ops.axes parent) selected)

def WholeAxisPointer : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices →
    (match indices with | [] => true | index :: _ => index.isUnitRange || Index.allScalar indices) = false →
    ∃ view : SubArray P T, constructSubArrayConfigured ops parent indices = .ok view ∧
      ∀ coordinates selected, TupleSelection indices coordinates selected →
        coordinatesInAxes (viewAxesManual indices) coordinates →
        coordinatesInAxes (ops.axes parent) selected →
        ∀ pointer : P → I64 → Jl R,
          pointerFastSubArray view (linearPosition (viewAxesManual indices) coordinates) pointer =
            pointer parent (linearPosition (ops.axes parent) selected)

def WholeAxisReadContract
    (read : {P T R : Type} → SubArray P T → I64 →
      (SubArray P T → I64 → Jl Unit) → (P → I64 → Jl R) → Jl R)
    (vectorOnly : Bool) : Prop :=
  ∀ {P T R : Type} (ops : ParentArrayOps P) (parent : P) (indices : List Index),
    WholeSlices (ops.axes parent) indices → FastViewInputs ops parent indices →
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

def WholeAxisRead : Prop := WholeAxisReadContract (@getindexFastSubArray) false ∧ FastViewBoundsErrors
def WholeAxisVectorRead : Prop := WholeAxisReadContract (@getindexFastVectorSubArray) true ∧ FastViewBoundsErrors
def WholeAxisVectorWrite : Prop := WholeAxisWriteInBounds ∧ FastViewBoundsErrors
def WholeAxisAssigned : Prop := WholeAxisAssignedInBounds ∧ IsassignedOutsideView

private def pending (id : String) (fns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := "multidimcov-subarray-v2-" ++ id, juliaFile := "base/subarray.jl", juliaFns := fns,
    statement, source, status := .todo, prop,
    notes := "The legacy certificate depends on its private view/layout carrier. The installed constructor and native-Int layout need an independent whole-axis layout/address correspondence; no carrier bridge is retained." }

def entries : List Entry := [
  pending "construct-linear-whole-axis" ["SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any}) where {P,I,N}"]
    "When every Slice spans its parent axis, the fast constructor's offset and stride map each view element to its parent position."
    "invariant: linear indexing of a FastSubArray, base/subarray.jl:17-18, 323-344" ``WholeAxisLinearConstruction,
  pending "getindex-fast-whole-axis" ["getindex(V::FastSubArray, i::Int)"]
    "When every Slice spans its parent axis, fast-view reads agree with their parent positions and out-of-bounds indices throw."
    "view docstring; linear indexing manual" ``WholeAxisRead,
  pending "getindex-fast-vector-whole-axis" ["getindex(V::FastSubArray{<:Any, 1}, i::Int)"]
    "When every Slice spans its parent axis, one-dimensional fast-view reads agree with their parent positions and out-of-bounds indices throw."
    "view docstring; linear indexing manual" ``WholeAxisVectorRead,
  pending "setindex-fast-vector-whole-axis" ["setindex!(V::FastSubArray{<:Any, 1}, x, i::Int)"]
    "When every Slice spans its parent axis, fast-vector writes modify exactly the selected element."
    "view docstring (writes through views modify the parent)" ``WholeAxisVectorWrite,
  pending "isassigned-fast-vector-whole-axis" ["isassigned(V::FastSubArray{<:Any, 1}, i::Int)"]
    "When every Slice spans its parent axis, isassigned checks the selected parent element."
    "isassigned docstring base/multidimensional.jl" ``WholeAxisAssigned,
  pending "pointer-fast-whole-axis" ["pointer(V::FastSubArray, i::Int)"]
    "When every Slice spans its parent axis, a non-contiguous fast-view pointer selects the corresponding parent element."
    "pointer docstring; linear indexing invariant" ``WholeAxisPointer,
  pending "pointer-contiguous-whole-axis" ["pointer(V::FastContiguousSubArray, i::Int)"]
    "When every Slice spans its parent axis, a contiguous fast-view pointer selects the corresponding parent element."
    "pointer docstring; linear indexing invariant" ``WholeAxisContiguousPointer
]

end JuliaLean.Proofs.base.subarray.LegacyRetired
