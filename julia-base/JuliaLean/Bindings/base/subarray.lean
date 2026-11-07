import JuliaLean.base.subarray
import JuliaLean.base.multidimensional

/-! Proposal only. View construction uses the installed source constructors and
layout dispatchers. Parent references remain unchanged. Foreign array, index,
bounds and reshape operations stay explicit and have no assumed laws. -/
namespace JuliaLean.Bindings.base.subarray
open JuliaLean JuliaLean.base.subarray

/-- Subarray owns the singleton-removal recursion; `_splitrest` is bound to the
installed multidimensional tuple-arity dispatcher. -/
def removeSingletons (indexNdims : List Index → List Bool) :
    List Bool → List Index → List Index
  | _, [] => removeSingletonIndicesEmpty
  | [], head :: tail =>
      if Index.isScalar head then
        removeSingletonScalarEmpty head tail (fun _ _ => removeSingletons indexNdims [] tail)
      else removeSingletonIndices [] head tail (fun i => indexNdims [i])
        JuliaLean.base.multidimensional.splitrestDispatch (fun dimensions _ => removeSingletons indexNdims dimensions tail)
  | dimensions@(_ :: _), head :: tail =>
      removeSingletonIndices dimensions head tail (fun i => indexNdims [i])
        JuliaLean.base.multidimensional.splitrestDispatch (fun dimensions _ => removeSingletons indexNdims dimensions tail)
termination_by _ indices => indices.length

/-- Trusted `_maybe_reshape_parent` dispatch for built-in Array. The vector
method precedes same-rank dispatch, as in Julia's overlapping methods. -/
def reshapeParent {P : Type} (rank : P → Nat) (reshape : P → Nat → Jl P)
    (parent : P) (dimensions : List Bool) : Jl P :=
  if dimensions.length = 1 then
    if rank parent = 1 then maybeReshapeVectorParent parent reshape
    else maybeReshapeParentOne parent reshape
  else if rank parent = dimensions.length then maybeReshapeParentSameRank parent dimensions
  else maybeReshapeParent parent dimensions reshape

/-- Trusted unsafe_view method selection from the concrete Julia parent type. -/
inductive ParentKind where
  | array | subarray

abbrev Parent (kind : ParentKind) (P T : Type) : Type :=
  match kind with
  | .array => P
  | .subarray => SubArray P T

abbrev ViewResult (kind : ParentKind) (P T : Type) : Type :=
  match kind with
  | .array => SubArray P T
  | .subarray => ReindexedView P T

def unsafeViewDispatch {P T : Type} (kind : ParentKind) (ops : ParentArrayOps P)
    (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index)) :
    Parent kind P T → List Index → Jl (ViewResult kind P T) :=
  match kind with
  | .array => fun p indices => unsafeViewArray p indices (constructSubArrayConfigured ops)
  | .subarray => unsafeViewSubArrayConfigured ops firstLinearIndex getVector getMatrix getArray toIndices

/-- `indices` is the normalized `J′` from `view` (base/subarray.jl:221-227).
The rank equality in `_maybe_reshape_parent` (base/subarray.jl:165-168)
keeps a SubArray parent unchanged through `reshape(A, Val(N))`
(base/reshapedarray.jl:186-189). Rank-changing inputs remain blocked. -/
def SubArrayReshapeKeepsKind {A : Type} (rank : A → Nat)
    (indexNdims : List Index → List Bool) (parent : A) (indices : List Index) : Prop :=
  (indexNdims indices).length = rank parent

instance {A : Type} (rank : A → Nat) (indexNdims : List Index → List Bool)
    (parent : A) (indices : List Index) :
    Decidable (SubArrayReshapeKeepsKind rank indexNdims parent indices) :=
  inferInstanceAs (Decidable ((indexNdims indices).length = rank parent))

/-- Restricted entry point needed by abstractarraymath.selectdim.
For SubArray inputs, the caller must establish the rank-preserving domain after
index conversion, unaliasing and singleton removal. The type-changing reshape
path is the explicit `subarray-bind3/reshape-type-change` gap; this binding does
not cover those inputs. Its result is the Julia `Jl (ViewResult kind P T)`. -/
def view {P T : Type} (kind : ParentKind) (ops : ParentArrayOps P)
    (rank : Parent kind P T → Nat) (reshape : Parent kind P T → Nat → Jl (Parent kind P T))
    (unalias : Parent kind P T → Index → Index)
    (toIndices : Parent kind P T → List Index → List Index)
    (checkBounds : Parent kind P T → List Index → Jl Unit)
    (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (flattenIndices : P → List Index → Jl (List Index))
    (parent : Parent kind P T) (indices : List Index)
    (_keepsKind : kind = .subarray →
      SubArrayReshapeKeepsKind rank ops.indexNdims parent
        (removeSingletons ops.indexNdims (List.replicate (rank parent) true)
          ((toIndices parent indices).map (unalias parent)))) : Jl (ViewResult kind P T) :=
  viewArray parent indices unalias toIndices checkBounds rank
    (removeSingletons ops.indexNdims) (reshapeParent rank reshape) ops.indexNdims
    (unsafeViewDispatch kind ops firstLinearIndex getVector getMatrix getArray flattenIndices)

/-- The configured installed nested-view path retains the source decision to
flatten or retain the SubArray parent. Index-array reads are foreign bindings. -/
def unsafeNested {P T : Type} (ops : ParentArrayOps P)
    (firstLinearIndex : SubArray P T → Jl I64)
    (getVector : Index → Index → Jl Index)
    (getMatrix : Index → Index → Index → Jl Index)
    (getArray : Index → List Index → Jl Index)
    (toIndices : P → List Index → Jl (List Index))
    (parent : SubArray P T) (indices : List Index) : Jl (ReindexedView P T) :=
  unsafeViewSubArrayConfigured ops firstLinearIndex getVector getMatrix getArray toIndices parent indices

/-- Public view reads select the installed fast/cartesian methods and reindex
through the stored parent reference, rather than indexing a copied value list. -/
def read {P T R : Type} (ops : ViewReadOps P T R)
    (parent : SubArray P T) (indices : List I64) : Jl R :=
  getindexSubArrayConfigured parent indices ops

/-- Numeric/range/scalar indices already indexable after to_indices select the
ordinary tuple dispatcher. LogicalIndex collection is a separate foreign path. -/
def ensureOrdinary (indices : List Index) : List Index :=
  JuliaLean.base.multidimensional.ensureIndexableDispatch indices

namespace Checks
-- These checks exercise installed layout and reindexing code, with actual native arithmetic.
def sample : SubArray Nat Unit :=
  ⟨7, [.unitRange ⟨int64 2, int64 4⟩], int64 1, int64 1, true, [true]⟩
#guard (reindexLinearDispatch sample (int64 2)).val == 3
#guard (axesSubArrayModel sample).map (fun axis => (axis.first.val, axis.last.val)) == [(1,3)]
#guard (ensureOrdinary [.scalar (int64 2), .oneTo (int64 3)]).length == 2
#guard (removeSingletons (fun _ => [true]) [] [.scalar (int64 1), .scalar (int64 1)]).isEmpty
#guard (removeSingletons (fun _ => [true]) [true] [.scalar (int64 1), .scalar (int64 1)]).length == 1
#guard match checkParentIndexMatchMismatch () [true,true] (fun _ => pure 1) with
  | .error (.argumentError message) => message == "number of indices (2) must match the parent dimensionality (1)"
  | _ => false
-- A zero-dimensional parent needs no foreign index-array reads or reshape.
def scalarOps : ParentArrayOps Nat where
  parentStyle := fun _ => .cartesian
  isArrayRank := fun _ rank => rank == 0
  ndims := fun _ => pure 0
  indexNdims := fun _ => []
  indexDimsum := fun _ => []
  ensureIndexable := id
  axes := fun _ => []
  strides := fun _ => pure []
  fillToLength := fun axes axis count => pure (axes ++ List.replicate (count-axes.length) axis)
  firstLinearIndex := fun _ => pure (int64 1)
  axisFirst := Axis.first
  axisLength := fun axis => iadd (isub axis.last axis.first) (int64 1)
  indexFirst := fun _ => .error .boundsError
  indexStep := fun _ => int64 1
  indexTypeName := fun _ => "Index"
  axes1First := fun _ => .error .boundsError
  isVector := fun _ => false

def scalarParent : SubArray Nat Unit :=
  ⟨7, [], int64 0, int64 0, false, []⟩

#guard match view .subarray scalarOps (fun _ => 0) (fun p _ => pure p)
    (fun _ index => index) (fun _ indices => indices) (fun _ _ => pure ())
    (fun _ => pure (int64 1)) (fun _ _ => .error .boundsError)
    (fun _ _ _ => .error .boundsError) (fun _ _ => .error .boundsError)
    (fun _ indices => pure indices) scalarParent [] (by intro _; decide) with
  | .ok (.flattened result) => result.parent == 7 && result.indices.isEmpty
  | _ => false

-- The ordinary-parent overload still calls its installed constructor.
#guard match view (T := Unit) .array scalarOps (fun _ => 0) (fun p _ => pure p)
    (fun _ index => index) (fun _ indices => indices) (fun _ _ => pure ())
    (fun _ => pure (int64 1)) (fun _ _ => .error .boundsError)
    (fun _ _ _ => .error .boundsError) (fun _ _ => .error .boundsError)
    (fun _ indices => pure indices) 7 [] (by intro impossible; cases impossible) with
  | .ok result => result.parent == 7 && result.indices.isEmpty
  | _ => false

-- The admitted domain includes same-rank parents and excludes rank changes.
#guard decide (SubArrayReshapeKeepsKind (fun _ : Nat => 2) (fun _ => [true,true]) 7 []) == true
#guard decide (SubArrayReshapeKeepsKind (fun _ : Nat => 2) (fun _ => [true]) 7 []) == false

#eval IO.println "SUBARRAY BIND3 CHECKS OK"
end Checks
end JuliaLean.Bindings.base.subarray
