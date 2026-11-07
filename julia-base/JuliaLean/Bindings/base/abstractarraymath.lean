import JuliaLean.base.abstractarraymath
import JuliaLean.base.essentials
import JuliaLean.base.reshapedarray
import JuliaLean.base.broadcast
import JuliaLean.base.subarray
import JuliaLean.base.multidimensional
import JuliaLean.base.number
import JuliaLean.base.complex
import JuliaLean.base.combinatorics
import JuliaLean.base.checked
import JuliaLean.base.range
import JuliaLean.base.tuple

/-!
Proposal only. Definitions in this namespace instantiate the installed source mirrors;
none reimplements an abstractarraymath.jl method. Foreign models that still require
callees are explicit parameters, recorded in the accompanying dependency inventory.
There are no correctness hypotheses or new runtime primitives.
-/
namespace JuliaLean.Bindings.base.abstractarraymath
open JuliaLean
abbrev I := JInt .i64
abbrev Result := JuliaLean.base.abstractarraymath.Result
abbrev MutationM := JuliaLean.base.abstractarraymath.MutationM

private def reshapeError : JuliaLean.base.reshapedarray.ReshapedError → JuliaLean.base.array.Error
  | .dimensionMismatch => .dimensionMismatch "reshape"
  | .errorException => .method "reshape"
  | .argumentError => .argument "reshape"
  | .boundsError => .bounds
  | .methodError s => .method s
  | .overflowError => .overflow
  | .inexactError s => .inexact
  | .divideError => .divide
  | .undefinedReference => .undefinedReference
  | .showError error => .showError error

/-- The single Except-to-mutable-heap lift; exceptions retain the current heap. -/
def liftResult {α E : Type} (result : Result E) : MutationM α E :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- This selected constructor can throw only InexactError (Core.lean:105-107). -/
def convertBits {t : IntTy} (target : IntTy) (x : JInt t) : Result (JInt target) :=
  (JuliaLean.base.int.convert target x).mapError (fun _ => .inexact)

/-- The installed `_foldoneto` over delayed effectful accumulators. Its positive-N
assertion executes before the first accumulated action; the actions then run in order. -/
def foldOneto {S : Type} (op : S → I → Result S) (initial : S) (count : I) : Result S := do
  let action ← (JuliaLean.base.combinatorics._foldoneto
    (fun action i => action >>= fun value => op value (JuliaLean.base.abstractarraymath.int i))
    (pure initial : Result S) count.val).mapError
      (fun e => match e with | .assertionError s => JuliaLean.base.array.Error.assertion s)
  action

/-- Array header representation already used by the installed reshape model.
The rank is existential because dropdims/insertdims change it. Storage is the original Ref. -/
abbrev Header (E Ref : Type) := (n : Nat) × JuliaLean.base.reshapedarray.ArrayValue E n Ref

def size {E Ref : Type} (a : Header E Ref) : List I :=
  JuliaLean.base.essentials.sizeArray (fun h _ => h.2.dims.toList) a

def rank {E Ref : Type} (a : Header E Ref) : I :=
  JuliaLean.base.abstractarray.ndimsValue (JuliaLean.base.abstractarraymath.int a.1) a

/-- Rank-one Array length uses its size-field accessor. Other ranks retain the
generic tuple-product callee as the next foreign binding. -/
def length {E Ref : Type} (tupleProduct : List I → I) (a : Header E Ref) : I :=
  match a with
  | ⟨1, header⟩ =>
      JuliaLean.base.essentials.lengthArray1
        (fun h _ => h.dims) (fun dims _ => dims[0]) header
  | a => JuliaLean.base.essentials.lengthAbstract size tupleProduct a

def axes {E Ref : Type} (a : Header E Ref) : Result (List (JuliaLean.base.range.OneTo I)) :=
  (JuliaLean.base.abstractarray.axesDefault (fun h => pure (size h))
    JuliaLean.base.range.unchecked_oneto a).mapError (fun _ => .bounds)

def axesDim {E Ref : Type} (a : Header E Ref) (d : I) : Result (JuliaLean.base.range.OneTo I) :=
  (JuliaLean.base.abstractarray.axesDim (fun x y => JuliaLean.base.int.le x y)
    (fun h => JuliaLean.base.abstractarray.axesDefault (fun h => pure (size h)) JuliaLean.base.range.unchecked_oneto h)
    JuliaLean.base.abstractarray.tupleGet JuliaLean.base.range.unchecked_oneto (rank a) a d).mapError (fun _ => .bounds)

/-- Native Int construction uses int.jl's nonthrowing same-width method. -/
private def nativeAxisCtor : JuliaLean.base.range.JCtor I I :=
  ⟨fun x => .ok (JuliaLean.base.int.widenTo .i64 x)⟩

/-- The installed OneTo{Int64} length method, including its selected constructor. -/
def axisLength (axis : JuliaLean.base.range.OneTo I) : Result I :=
  match h : @JuliaLean.base.range.length_OneTo_smallints I nativeAxisCtor axis with
  | .ok value => .ok value
  | .error error => False.elim (by
      change (Except.ok (JuliaLean.base.int.widenTo .i64 axis.stop) :
        JuliaLean.base.range.JlX I) = Except.error error at h
      cases h)

def tupleGet {E : Type} (values : List E) (i : I) : Result E :=
  (JuliaLean.base.tuple.getindexInt values i).mapError (fun _ => .bounds)

def tupleIndices {E : Type} (values : List E) : List I :=
  (JuliaLean.base.tuple.oneTo (JuliaLean.base.tuple.lengthTuple values)).map (fun n : Nat => JuliaLean.base.abstractarraymath.int n)

/-- The Array reshape specialization. Only its length callee's foreign tuple
product remains open; checked_dims is the installed boot.jl model. -/
def reshape {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List I) : Result (Header E Ref) := do
  let result ← (JuliaLean.base.reshapedarray.reshapeArray
    (fun ds => (JuliaLean.base.array.checkedDims ds.toList : Result I).mapError
      (fun _ => JuliaLean.base.reshapedarray.ReshapedError.argumentError))
    (fun h => pure (length tupleProduct ⟨a.1, h⟩)) a.2 dims.toArray.toVector).mapError reshapeError
  pure ⟨dims.length, result⟩

def reshapeAxes {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List (JuliaLean.base.range.OneTo I)) : Result (Header E Ref) := do
  let dims ← dims.mapM axisLength
  reshape tupleProduct a dims

def axesType (axes : List (JuliaLean.base.range.OneTo I)) : String := toString axes.length

def assertAxesType (expected : String) (axes : List (JuliaLean.base.range.OneTo I)) : Result (List (JuliaLean.base.range.OneTo I)) :=
  (JuliaLean.base.tuple.assertTupleType (fun values _ => axesType values == expected) axes
    (.tuple (List.replicate axes.length (.type (.atom "OneTo{Int64}"))))).mapError (fun _ => .typeError "Tuple")

/-- Trusted dispatch selects the AbstractVector identity before the generic method. -/
def vec {E Ref : Type} (tupleProduct : List I → I) (a : Header E Ref) : Result (Header E Ref) :=
  if a.1 = 1 then pure (JuliaLean.base.abstractarraymath.vecVector a)
  else JuliaLean.base.abstractarraymath.vecArray (fun h => pure (length tupleProduct h))
    (fun h n => reshape tupleProduct h [n]) a

def dropDims {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List I) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.dropdimsDims tupleIndices tupleGet rank axesDim (fun ax => axisLength ax) axes
    foldOneto (fun _ => true) (fun ax dims => JuliaLean.base.abstractarraymath.subTupleDispatch ax dims)
    axesType assertAxesType (reshapeAxes tupleProduct) a dims

def drop {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List I) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.dropdims (dropDims tupleProduct) a dims

def dropInteger {E Ref : Type} {t : IntTy} (tupleProduct : List I → I)
    (a : Header E Ref) (d : JInt t) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.dropdimsInteger (convertBits .i64)
    (dropDims tupleProduct) a d

def insertDims {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List I) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.insertdimsDims tupleIndices tupleGet a.1 axesDim JuliaLean.base.range.unchecked_oneto
    foldOneto (reshapeAxes tupleProduct) a dims

def insert {E Ref : Type} (tupleProduct : List I → I)
    (a : Header E Ref) (dims : List I) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.insertdims (insertDims tupleProduct) a dims

def insertInteger {E Ref : Type} {t : IntTy} (tupleProduct : List I → I)
    (a : Header E Ref) (d : JInt t) : Result (Header E Ref) :=
  JuliaLean.base.abstractarraymath.insertdimsInteger (convertBits .i64)
    (insertDims tupleProduct) a d

/-- The StateT/Except-to-ExceptT/State adapter commits a successful memory
result and retains the input memory on error, as required by VectorM's result
type. It is used only for the installed allocator, whose checks precede allocation. -/
def liftVector {α E : Type} (action : JuliaLean.base.array.VectorM α E) : MutationM α E := do
  let before ← get
  match action.run before.memories with
  | .ok (result, memories) =>
    modify fun state => { state with memories }
    pure result
  | .error error => throw error

def allocate {α Tag : Type} (layout : Tag → Option JuliaLean.base.array.MemoryLayout) (target : Tag)
    (dims : List I) : MutationM α (JuliaLean.base.array.HeapArray Tag) :=
  liftVector (JuliaLean.base.array.heapArrayUndef layout target dims)

def similarDims {α Tag : Type} (layout : Tag → Option JuliaLean.base.array.MemoryLayout)
    (a : JuliaLean.base.array.HeapArray Tag) (dims : List I) : MutationM α (JuliaLean.base.array.HeapArray Tag) :=
  JuliaLean.base.array.similar420 (allocate layout a.elementType) a dims

def similarVector {α Tag : Type} (layout : Tag → Option JuliaLean.base.array.MemoryLayout)
    (a : JuliaLean.base.array.HeapArray Tag) (n : I) : MutationM α (JuliaLean.base.array.HeapArray Tag) :=
  JuliaLean.base.array.similar418 (fun n => allocate layout a.elementType [n]) a n

def checkedMul {α : Type} (a b : I) : MutationM α I :=
  liftResult ((JuliaLean.base.checked.checkedMulBits a b).mapError (fun _ => .overflow))

/-- Bind the scalar side without assuming that a predicate is correct. The array
all callee is the next binding in reducedim/anyall and remains named explicitly. -/
def iszeroInts {t : IntTy} {Arr : Type}
    (arrayAll : (JInt t → Bool) → Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.iszeroArray arrayAll JuliaLean.base.complex.iszero_JInt a

def isrealComplexInts {t : IntTy} {Arr : Type}
    (arrayAll : (JuliaLean.base.complex.Complex (JInt t) → Bool) → Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.isrealArray arrayAll (JuliaLean.base.complex.isreal_Complex JuliaLean.base.complex.iszero_JInt) a

def iszeroComplexInts {t : IntTy} {Arr : Type}
    (arrayAll : (JuliaLean.base.complex.Complex (JInt t) → Bool) → Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.iszeroArray arrayAll (JuliaLean.base.complex.iszero_Complex JuliaLean.base.complex.iszero_JInt) a

/-- `broadcast_preserving_zero_d` is the installed broadcast.jl:908 method.
Its broadcasted/materialize/similar-fill callees remain the next foreign bindings. -/
def broadcastPreserving {E F Arr BC Out : Type}
    (broadcasted : (E → F) → Arr → BC) (materialize : BC → Result Out)
    (axes : BC → List I) (similarFill : BC → Out → Result Out)
    (f : E → F) (a : Arr) : Result Out := do
  let result ← JuliaLean.base.broadcast.Material.m908
    (fun f a => pure (broadcasted f a)) materialize (fun bc => pure (axes bc))
    similarFill f a
  pure (result.elim id id)

def conjComplexInts {t : IntTy} {Arr BC Out : Type}
    (broadcasted : (JuliaLean.base.complex.Complex (JInt t) → JuliaLean.base.complex.Complex (JInt t)) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.conjArray (broadcastPreserving broadcasted materialize axes similarFill)
    (JuliaLean.base.complex.conj_Complex JuliaLean.base.int.neg) a

def realComplex {E Arr BC Out : Type}
    (broadcasted : (JuliaLean.base.complex.Complex E → E) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.realArray (broadcastPreserving broadcasted materialize axes similarFill) JuliaLean.base.complex.real_Complex a

def imagComplex {E Arr BC Out : Type}
    (broadcasted : (JuliaLean.base.complex.Complex E → E) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.imagArray (broadcastPreserving broadcasted materialize axes similarFill) JuliaLean.base.complex.imag_Complex a

def negInts {t : IntTy} {Arr BC Out : Type}
    (broadcasted : (JInt t → JInt t) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.negArray (broadcastPreserving broadcasted materialize axes similarFill) JuliaLean.base.int.neg a

def iszeroFloats {t : JuliaLean.base.float.FTy} {Arr : Type}
    (arrayAll : (JuliaLean.base.float.FV t → Bool) → Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.iszeroArray arrayAll JuliaLean.base.float.iszero_float a

def isrealComplexFloats {t : JuliaLean.base.float.FTy} {Arr : Type}
    (arrayAll : (JuliaLean.base.complex.Complex (JuliaLean.base.float.FV t) → Bool) →
      Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.isrealArray arrayAll
    (JuliaLean.base.complex.isreal_Complex JuliaLean.base.float.iszero_float) a

def iszeroComplexFloats {t : JuliaLean.base.float.FTy} {Arr : Type}
    (arrayAll : (JuliaLean.base.complex.Complex (JuliaLean.base.float.FV t) → Bool) →
      Arr → Result Bool) (a : Arr) : Result Bool :=
  JuliaLean.base.abstractarraymath.iszeroArray arrayAll
    (JuliaLean.base.complex.iszero_Complex JuliaLean.base.float.iszero_float) a

def negFloats {t : JuliaLean.base.float.FTy} {Arr BC Out : Type}
    (broadcasted : (JuliaLean.base.float.FV t → JuliaLean.base.float.FV t) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.negArray
    (broadcastPreserving broadcasted materialize axes similarFill)
    JuliaLean.base.float.neg_IEEEFloat a

def conjComplexFloats {t : JuliaLean.base.float.FTy} {Arr BC Out : Type}
    (broadcasted : (JuliaLean.base.complex.Complex (JuliaLean.base.float.FV t) →
      JuliaLean.base.complex.Complex (JuliaLean.base.float.FV t)) → Arr → BC)
    (materialize : BC → Result Out) (axes : BC → List I)
    (similarFill : BC → Out → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.conjArray
    (broadcastPreserving broadcasted materialize axes similarFill)
    (JuliaLean.base.complex.conj_Complex JuliaLean.base.float.neg_IEEEFloat) a

/-- Source-owned repeat helpers are all bound here. Remaining arguments belong to
foreign array/tuple/iterator models and are listed individually in the proposal. -/
def repeatBound {α Arr E Count Iter Ix Selector : Type}
    (ops : JuliaLean.base.abstractarraymath.RepeatArrayOps α Arr E Count Ix Selector)
    (rank : Arr → Nat) (size : Arr → MutationM α (List Count))
    (collect : Iter → MutationM α (List Count)) (tuple : List Count → List Count)
    (fill : List Count → Count → Nat → List Count) (one : Count)
    (reshape : Arr → List Count → MutationM α Arr)
    (requireOneBased : Arr → MutationM α Unit)
    (isInteger isNegative : Count → Bool)
    (all any : (Count → MutationM α Bool) → JuliaLean.base.abstractarraymath.CountArg Count Iter → MutationM α Bool)
    (countLength : JuliaLean.base.abstractarraymath.CountArg Count Iter → MutationM α I)
    (ndims : Arr → I)
    (showCounts : JuliaLean.base.abstractarraymath.CountArg Count Iter → String) (a : Arr)
    (inner outer : Option (JuliaLean.base.abstractarraymath.CountArg Count Iter)) : MutationM α Arr :=
  JuliaLean.base.abstractarraymath.repeatKeyword
    (fun arr inner outer => JuliaLean.base.abstractarraymath.RepeatInnerOuter.repeatModule
      (JuliaLean.base.abstractarraymath.RepeatInnerOuter.checkDispatch requireOneBased isInteger isNegative all any countLength ndims showCounts)
      (JuliaLean.base.abstractarraymath.RepeatInnerOuter.resolveDispatch rank size collect tuple fill one reshape)
      (JuliaLean.base.abstractarraymath.RepeatInnerOuter.repeatInnerOuterDispatch ops rank) arr inner outer) a inner outer

/-- Two independent exception channels retain both array-source errors and the
Julia exception payload returned by the installed view model. -/
abbrev SelectM := ExceptT JuliaLean.base.array.Error (Except JlError)

def selectArrayResult {E : Type} (result : Result E) : SelectM E :=
  match result with
  | .ok value => pure value
  | .error error => throw error

def selectJuliaResult {E : Type} (result : Jl E) : SelectM E :=
  ExceptT.lift result

/-- Instantiation of the installed subarray view method. Its remaining callees
belong to subarray/abstractarray and are the next binding dependency. -/
def viewCall {Arr Out : Type}
    (unalias : Arr → JuliaLean.base.subarray.Index → JuliaLean.base.subarray.Index)
    (toIndices : Arr → List JuliaLean.base.subarray.Index → List JuliaLean.base.subarray.Index)
    (checkBounds : Arr → List JuliaLean.base.subarray.Index → Jl Unit)
    (ndims : Arr → Nat)
    (removeSingletons : List Bool → List JuliaLean.base.subarray.Index → List JuliaLean.base.subarray.Index)
    (reshapeParent : Arr → List Bool → Jl Arr)
    (indexNdims : List JuliaLean.base.subarray.Index → List Bool)
    (unsafeView : Arr → List JuliaLean.base.subarray.Index → Jl Out)
    (a : Arr) (indices : List JuliaLean.base.subarray.Index) : SelectM Out :=
  selectJuliaResult (JuliaLean.base.subarray.viewArray a indices unalias toIndices
    checkBounds ndims removeSingletons reshapeParent indexNdims unsafeView)

/-- The Int64 dimension/scalar-index branch uses the original selectdim and
_selectdim definitions. No view or selection algorithm is copied. -/
def selectdim {E Ref Out : Type}
    (ntuple : (Nat → JuliaLean.base.subarray.Index) → Nat → List JuliaLean.base.subarray.Index)
    (unalias : Header E Ref → JuliaLean.base.subarray.Index → JuliaLean.base.subarray.Index)
    (toIndices : Header E Ref → List JuliaLean.base.subarray.Index → List JuliaLean.base.subarray.Index)
    (checkBounds : Header E Ref → List JuliaLean.base.subarray.Index → Jl Unit)
    (removeSingletons : List Bool → List JuliaLean.base.subarray.Index → List JuliaLean.base.subarray.Index)
    (reshapeParent : Header E Ref → List Bool → Jl (Header E Ref))
    (indexNdims : List JuliaLean.base.subarray.Index → List Bool)
    (unsafeView : Header E Ref → List JuliaLean.base.subarray.Index → Jl Out)
    (a : Header E Ref) (d i : I) : SelectM Out :=
  JuliaLean.base.abstractarraymath.selectdim
    (fun a => selectArrayResult (axes a)) .colon
    (fun value dim indices => JuliaLean.base.tuple.setindexVarargs ntuple
      (fun condition yes no => if condition then yes else no)
      value (.integer .i64 dim) indices)
    (JuliaLean.base.abstractarraymath.selectdimInternal
      (fun dim => pure (JuliaLean.base.int.le (JuliaLean.base.abstractarraymath.int 1) dim))
      (fun dim => toString dim.val)
      rank
      (fun dim nd => pure (JuliaLean.base.int.lt nd dim))
      (fun index => pure (match index with
        | .scalar value => JuliaLean.base.int.eq value (JuliaLean.base.abstractarraymath.int 1)
        | _ => false))
      (fun dim => pure (JuliaLean.base.int.sub dim (JuliaLean.base.abstractarraymath.int 1)))
      (fun count => pure (ntuple (fun _ => .colon) count.val.toNat))
      (fun _ _ => .bounds)
      (viewCall unalias toIndices checkBounds (fun a => a.1)
        removeSingletons reshapeParent indexNdims unsafeView))
    a d (.scalar i)

/-- Arithmetic and Array allocation fields are instantiated once. Remaining
indexing/Cartesian/block-copy operations are next bindings in their source files. -/
def repeatArrayOps {α Tag E Ix Selector : Type}
    (layout : Tag → Option JuliaLean.base.array.MemoryLayout)
    (size : JuliaLean.base.array.HeapArray Tag → MutationM α (List I))
    (sizeAt : JuliaLean.base.array.HeapArray Tag → I → MutationM α I)
    (length : JuliaLean.base.array.HeapArray Tag → MutationM α I)
    (range : I → I → MutationM α (List I))
    (rangeSelector : I → I → MutationM α Selector)
    (matrixIndex : Selector → Selector → Ix) (vectorIndex : Selector → Ix)
    (cartesianIndicesArray : JuliaLean.base.array.HeapArray Tag → MutationM α (List Ix))
    (cartesianIndicesDims : List I → MutationM α (List Ix))
    (tupleIndex : Ix → List I) (cartesianIndex : List I → Ix)
    (zipMap3 : List I → List I → List I → (I → I → I → I) → List I)
    (getindex : JuliaLean.base.array.HeapArray Tag → Ix → MutationM α E)
    (setindex : JuliaLean.base.array.HeapArray Tag → Ix → E → MutationM α Unit)
    (setBlock : JuliaLean.base.array.HeapArray Tag → Ix → JuliaLean.base.array.HeapArray Tag → MutationM α Unit) :
    JuliaLean.base.abstractarraymath.RepeatArrayOps α
      (JuliaLean.base.array.HeapArray Tag) E I Ix Selector where
  size := size
  sizeAt := sizeAt
  length := length
  similar1 := similarVector layout
  similar2 := fun a rows cols => similarDims layout a [rows, cols]
  similarDims := similarDims layout
  one := JuliaLean.base.abstractarraymath.int 1
  add := JuliaLean.base.int.add
  sub := JuliaLean.base.int.sub
  mul := JuliaLean.base.int.mul
  checkedMul := checkedMul
  range := range
  rangeSelector := rangeSelector
  matrixIndex := matrixIndex
  vectorIndex := vectorIndex
  cartesianIndicesArray := cartesianIndicesArray
  cartesianIndicesDims := cartesianIndicesDims
  tupleIndex := tupleIndex
  cartesianIndex := cartesianIndex
  zipMap3 := zipMap3
  getindex := getindex
  setindex := setindex
  setBlock := setBlock

/-- Bind the nested method's foreach and recursive numeric-method dispatch.
The outer array iteration instance and broadcast! are the remaining foreign bindings. -/
def conjBangNestedComplexInts {α Outer Inner : Type} {t : IntTy}
    [ForIn (MutationM α) Outer Inner]
    (broadcastBang : (JuliaLean.base.complex.Complex (JInt t) → JuliaLean.base.complex.Complex (JInt t)) →
      Inner → Inner → MutationM α Unit)
    (outer : Outer) : MutationM α Outer :=
  JuliaLean.base.abstractarraymath.conjBangNested
    JuliaLean.base.abstractarray.foreach
    (fun inner => do
      let _ ← JuliaLean.base.abstractarraymath.conjBangNumbers broadcastBang
        (JuliaLean.base.complex.conj_Complex JuliaLean.base.int.neg) inner
      pure ()) outer

/-- The numeric-array zero overload is more specific than zero(AbstractArray).
Its allocation and fill callees remain the next abstractarray/array bindings. -/
def imagRealInts {t : IntTy} {Arr Out : Type}
    (similar : Arr → Unit → Result Out)
    (fill : Out → JInt t → Result Out) (a : Arr) : Result Out :=
  JuliaLean.base.abstractarraymath.imagRealArray
    (JuliaLean.base.abstractarray.zeroNumericArray
      (fun _ => (JuliaLean.base.number.zeroType
        (fun (_ : Unit) n => JInt.convert t.name t n) ()).mapError (fun _ => .inexact))
      (fun _ => ()) similar fill ()) a

namespace Checks
def layout (_ : Unit) : Option JuliaLean.base.array.MemoryLayout :=
  some ⟨8, false, false⟩

def allocation (dims : List I) : Except JuliaLean.base.array.Error
    (List Nat × Nat) × JuliaLean.base.array.MutableMemory I :=
  ((allocate (α := I) layout () dims).map fun a =>
    (a.dimensions, a.handle)).run ⟨[], []⟩

#guard (allocation [JInt.lit .i64 2, JInt.lit .i64 3]).1 == .ok ([2,3], 0)
#guard (allocation [JInt.lit .i64 2, JInt.lit .i64 3]).2.memories.map List.length == [6]
#guard (allocation [JInt.lit .i64 (-1)]).1 ==
  .error (.argument JuliaLean.base.array.genericMemorySizeMessage)
#guard (allocation [JInt.lit .i64 (-1)]).2.memories.isEmpty
#guard (allocation [JInt.lit .i64 (-1), JInt.lit .i64 0]).1 ==
  .error (.argument "invalid Array dimensions")
#guard (allocation []).1 == .ok ([], 0)
#guard (allocation []).2.memories.map List.length == [1]
#guard (allocation [JInt.lit .i64 0, JInt.lit .i64 5]).2.memories.map List.length == [0]
#guard (foldOneto (fun acc i => pure (acc ++ [i.val])) [] (JInt.lit .i64 3)) ==
  .ok [1,2,3]
#guard (foldOneto (fun (_ : Unit) _ => throw (.bounds)) () (JInt.lit .i64 0)) ==
  .error (.assertion "N must be positive")
#guard ((checkedMul (α := I) (JInt.lit .i64 (2^62)) (JInt.lit .i64 4)).run ⟨[], []⟩).1 ==
  .error .overflow

#eval IO.println "ABSTRACTARRAYMATH BIND CHECKS OK"
end Checks

end JuliaLean.Bindings.base.abstractarraymath
