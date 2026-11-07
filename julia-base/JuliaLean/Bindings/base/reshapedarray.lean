import JuliaLean.base.reshapedarray
import JuliaLean.base.subarray
import JuliaLean.base.array
import JuliaLean.base.genericmemory
import JuliaLean.base.pointer
import JuliaLean.base.abstractarray
import JuliaLean.base.essentials
import JuliaLean.base.int
import JuliaLean.base.div
import JuliaLean.base.promotion
import JuliaLean.base.reduce
import JuliaLean.base.indices
import JuliaLean.base.multinverses
import JuliaLean.base.intfuncs
import JuliaLean.base.tuple
import JuliaLean.base.range

namespace JuliaLean.Bindings.base.reshapedarray

open JuliaLean
open JuliaLean.base.reshapedarray

abbrev I64 := JInt .i64
abbrev RResult := JuliaLean.base.reshapedarray.RResult
abbrev IntegerValue := Sigma JInt
inductive ColonDim (Integer : Type) where
  | integer (value : Integer)
  | colon


private def arrayErrorToReshaped : JuliaLean.base.array.Error → ReshapedError
  | .argument _ => .argumentError
  | .bounds => .boundsError
  | .inexact => .inexactError "Int"
  | .overflow => .overflowError
  | .divide => .divideError
  | .typeError _ => .errorException
  | .dimensionMismatch _ => .dimensionMismatch
  | .method name => .methodError name
  | .assertion _ => .errorException
  | .concurrency _ => .errorException
  | .thrownNothing => .errorException
  | .undefinedReference => .undefinedReference
  | .showError error => .showError error
private def reshapeErrorOfJl : JlError → ReshapedError
  | .overflowError _ => .overflowError
  | .argumentError _ => .argumentError
  | .boundsError => .boundsError
  | .inexactError name => .inexactError name
  | .divideError => .divideError
  | .domainError _ => .errorException
  | .methodError name => .methodError name
  | .eofError => .methodError "EOFError"


def checkedDimsArrayList (dims : List I64) : RResult I64 :=
  (JuliaLean.base.array.checkedDims (m := Except JuliaLean.base.array.Error) dims).mapError
    arrayErrorToReshaped
def checkedDimsArray {N : Nat} (dims : Vector I64 N) : RResult I64 :=
  checkedDimsArrayList dims.toList

def arrayHeaderSize {T : Type} {N : Nat} {Ref : Type}
    (array : ArrayValue T N Ref) : List I64 := array.dims.toList

def arrayHeaderLength {T : Type} {N : Nat} {Ref : Type}
    (array : ArrayValue T N Ref) : RResult I64 :=
  .ok (JuliaLean.base.essentials.lengthAbstract arrayHeaderSize
    JuliaLean.base.essentials.prodDims array)

def reshapeArrayHeader {T : Type} {M N : Nat} {Ref : Type}
    (array : ArrayValue T M Ref) (dims : Vector I64 N) : RResult (ArrayValue T N Ref) :=
  JuliaLean.base.reshapedarray.reshapeArray checkedDimsArray arrayHeaderLength array dims

abbrev ReshapedMutation (α : Type) :=
  ExceptT ReshapedError (StateM (JuliaLean.base.array.MutableMemory α))

private def liftArrayMutation {α β : Type}
    (action : JuliaLean.base.array.MutationM α β) : ReshapedMutation α β :=
  ExceptT.mk do
    let result ← action.run
    pure (result.mapError arrayErrorToReshaped)

def arrayMutableGet {α : Type} {N : Nat}
    (array : ArrayValue α N Nat) (index : I64) : ReshapedMutation α α :=
  liftArrayMutation (JuliaLean.base.array.mutableGet array.ref index)

def arrayMutableSet {α : Type} {N : Nat}
    (array : ArrayValue α N Nat) (index : I64) (value : α) : ReshapedMutation α Unit :=
  liftArrayMutation (JuliaLean.base.array.mutableSet array.ref value index)

def setReshapedLinearArray {α : Type} {M N : Nat}
    (array : ReshapedArrayLF α N (ArrayValue α M Nat)) (index : I64) (value : α) :
    ReshapedMutation α α :=
  JuliaLean.base.reshapedarray.setindexReshapedLinear true
    (fun parent index => liftArrayMutation (JuliaLean.base.array.mutableBounds parent.parent.ref index))
    (fun _ => pure (JInt.lit .i64 1))
    (fun _ => pure (JInt.lit .i64 1))
    (fun parent index value =>
      liftArrayMutation (JuliaLean.base.array.mutableSet parent.ref value index))
    array value index

def setReshapedIndexArray {α : Type} {M N : Nat}
    (array : ReshapedArray α N (ArrayValue α M Nat) Unit)
    (index : ReshapedIndex I64) (value : α) : ReshapedMutation α α :=
  JuliaLean.base.reshapedarray.setindexReshapedIndex true
    (fun parent index => liftArrayMutation (JuliaLean.base.array.mutableBounds parent.ref index))
    (fun parent index value =>
      liftArrayMutation (JuliaLean.base.array.mutableSet parent.ref value index))
    array value index

def observeSharedArrayWrite {α : Type} {M N : Nat}
    (parent : ArrayValue α M Nat) (reshaped : ArrayValue α N Nat)
    (index : I64) (value : α) : ReshapedMutation α (α × α) := do
  arrayMutableSet parent index value
  let parentValue ← arrayMutableGet parent index
  let reshapedValue ← arrayMutableGet reshaped index
  pure (parentValue, reshapedValue)

private def sizeToStridesList (stride : I64) : List I64 → List I64
  | [] => JuliaLean.base.abstractarray.sizeToStridesEmpty stride
  | [dimension] => JuliaLean.base.abstractarray.sizeToStridesLast stride dimension
  | dimension :: tail =>
      let rest := sizeToStridesList (JuliaLean.base.int.mul_int stride dimension) tail
      let (first, _) := JuliaLean.base.abstractarray.sizeToStrides
        JuliaLean.base.int.mul_int (fun _ _ => rest) stride dimension tail
      first :: rest
termination_by sizes => sizes.length
decreasing_by simp_wf

def denseArrayReshapedStrides {T : Type} {N M : Nat} {MI : Type}
    (array : ReshapedArray T N (ArrayValue T M Nat) MI) : RResult (List I64) :=
  if JuliaLean.base.reshapedarray.checkcontiguousReshaped
      (fun parent => JuliaLean.base.reshapedarray.checkcontiguousDense Bool parent) Bool array then
    .ok (sizeToStridesList (JInt.lit .i64 1) (reshapedSize array).toList)
  else
    .error (.methodError "strides")














private def viewIndexFirst : JuliaLean.base.subarray.Index → Jl I64
  | .scalar value => .ok value
  | .cartesian (first :: _) => .ok first
  | index =>
      match JuliaLean.base.subarray.Index.indexAxes index with
      | axis :: _ => .ok axis.first
      | [] => .error .boundsError

private def vectorViewFirstIndex {T : Type}
    (view : JuliaLean.base.subarray.SubArray
      (ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T)) T) : RResult I64 :=
  match JuliaLean.base.subarray.axesSubArrayModel view with
  | [axis] =>
      .ok (JuliaLean.base.subarray.firstIndexFastSubArray view (fun _ => axis.first))
  | _ => .error .boundsError

private def vectorViewFirstIndices (indices : List JuliaLean.base.subarray.Index) :
    RResult (List I64) :=
  (indices.mapM viewIndexFirst).mapError reshapeErrorOfJl

private def abstractArrayErrorToReshaped : JuliaLean.base.abstractarray.ArrayError → ReshapedError
  | .julia error => reshapeErrorOfJl error
  | .dimensionMismatch _ => .dimensionMismatch
  | .canonicalIndex name _ => .methodError name
  | .errorException _ | .assertionError _ => .errorException
  | .showError error => .showError error

private def memoryOffsetMapOne (mapOne : I64 → I64 → I64 →
    JuliaLean.base.abstractarray.Result I64)
    (indices strides origins : List I64) : JuliaLean.base.abstractarray.Result (List I64) :=
  match indices, strides, origins with
  | [index], [stride], [origin] => do .ok [← mapOne index stride origin]
  | [], [], [] => .ok []
  | _, _, _ => .error (.julia .boundsError)

private def vectorArrayElementSize {T : Type}
    (parent : ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T)) :
    JuliaLean.base.abstractarray.Result I64 :=
  .ok (JuliaLean.base.genericmemory.elsize (T := T)
    (fun (_ : Type) => parent.ref.mem.layoutBytes)
    (JuliaLean.base.pointer.PointerMemoryRef T))

private def vectorArrayElementSizeReshaped {T : Type}
    (parent : ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T)) : RResult I64 :=
  (vectorArrayElementSize parent).mapError abstractArrayErrorToReshaped

private def vectorArrayMemoryOffset {T : Type}
    (parent : ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T))
    (indices : List I64) : RResult I64 :=
  (JuliaLean.base.abstractarray.memoryOffsetArray
    (fun _ (values : List I64) => .ok values)
    (fun array => .ok (sizeToStridesList (JInt.lit .i64 1) array.dims.toList))
    (fun _ => .ok [JInt.lit .i64 1])
    (fun index origin => .ok (JuliaLean.base.int.sub_int index origin))
    (fun stride delta => .ok (JuliaLean.base.int.mul_int stride delta))
    memoryOffsetMapOne
    (fun (products : List I64) =>
      .ok (products.foldl JuliaLean.base.int.add_int (JInt.lit .i64 0)))
    vectorArrayElementSize
    (fun total elementSize => .ok (JuliaLean.base.int.mul_int total elementSize))
    parent indices).mapError abstractArrayErrorToReshaped

def unsafeConvertVectorSubArray {T S : Type}
    (view : JuliaLean.base.subarray.SubArray
      (ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T)) T) : RResult (JuliaLean.base.pointer.Ptr S) :=
  JuliaLean.base.reshapedarray.unsafeConvertSubArray
    (fun parent => JuliaLean.base.reshapedarray.checkcontiguousDense Bool parent)
    vectorViewFirstIndex
    (fun _ => .ok (JInt.lit .i64 1))
    vectorArrayElementSizeReshaped vectorViewFirstIndices vectorArrayMemoryOffset
    (fun _ parent => .ok (JuliaLean.base.pointer.unsafeConvertArray parent.ref))
    (fun pointer offset => .ok (JuliaLean.base.pointer.ptrAddI64 pointer offset))
    (fun pointer => .ok (JuliaLean.base.pointer.convertPtrType pointer))
    (⟨JInt.wrap .u64 0⟩ : JuliaLean.base.pointer.Ptr T) view

def cconvertVectorSubArray {T : Type}
    (view : JuliaLean.base.subarray.SubArray
      (ArrayValue T 1 (JuliaLean.base.pointer.PointerMemoryRef T)) T) :
    RResult (OffsetCConvert T (JuliaLean.base.pointer.PointerMemoryRef T)) :=
  JuliaLean.base.reshapedarray.cconvertSubArray
    (fun _ parent => .ok (JuliaLean.base.pointer.cconvertArray (fun array => array.ref) parent))
    (fun parent => JuliaLean.base.reshapedarray.checkcontiguousDense Bool parent)
    vectorViewFirstIndex
    (fun _ => .ok (JInt.lit .i64 1))
    vectorArrayElementSizeReshaped vectorViewFirstIndices vectorArrayMemoryOffset
    (fun pointer offset parent =>
      JuliaLean.base.reshapedarray.offsetCconvertBase pointer offset parent)
    (⟨JInt.wrap .u64 0⟩ : JuliaLean.base.pointer.Ptr T) view

def unsafeConvertOffsetVector {T S : Type}
    (conversion : OffsetCConvert T (JuliaLean.base.pointer.PointerMemoryRef T)) :
    RResult (JuliaLean.base.pointer.Ptr S) :=
  JuliaLean.base.reshapedarray.unsafeConvertOffsetCconvert
    (fun _ parent => .ok (JuliaLean.base.pointer.unsafeConvertArray parent))
    (fun pointer offset => .ok (JuliaLean.base.pointer.ptrAddI64 pointer offset))
    (fun pointer => .ok (JuliaLean.base.pointer.convertPtrType pointer))
    (⟨JInt.wrap .u64 0⟩ : JuliaLean.base.pointer.Ptr T) conversion

def addNestedOffsetVector {T C : Type} (offset : I64) (parent : OffsetCConvert T C)
    (offsetCconvert : JuliaLean.base.pointer.Ptr T → I64 → C →
      RResult (OffsetCConvert T C)) : RResult (OffsetCConvert T C) :=
  JuliaLean.base.reshapedarray.offsetCconvertNested offsetCconvert
    (⟨JInt.wrap .u64 0⟩ : JuliaLean.base.pointer.Ptr T) offset parent

private def integerTypeOf (value : IntegerValue) : JuliaLean.base.promotion.PType :=
  JuliaLean.base.promotion.primitivePType (.int value.1)

private def integerPromoteType (left right : IntegerValue) :
    RResult JuliaLean.base.promotion.PType :=
  match JuliaLean.base.promotion.promoteType JuliaLean.base.promotion.primitivePromoteRule
      (integerTypeOf left) (integerTypeOf right) with
  | some target => .ok target
  | none => .error (.methodError "promote_type")

private def convertIntegerToType (target : JuliaLean.base.promotion.PType)
    (value : IntegerValue) : RResult IntegerValue := do
  match JuliaLean.base.promotion.primitiveTypeOfPType target with
  | some (.int t) =>
      let converted ← (JuliaLean.base.int.convert t value.2).mapError reshapeErrorOfJl
      .ok ⟨t, converted⟩
  | _ => .error (.methodError "convert")

private def promoteIntegerPair (left right : IntegerValue) :
    RResult (IntegerValue × IntegerValue) := do
  let target ← integerPromoteType left right
  let left ← convertIntegerToType target left
  let right ← convertIntegerToType target right
  .ok (left, right)





private def integerProduct (values : List IntegerValue) : RResult IntegerValue :=
  (JuliaLean.base.reduce.prod (fun {_} _ => .hasEltype) id
    (JuliaLean.base.reduce.valueReducer JuliaLean.base.reduce.integerMulProd
      JuliaLean.base.reduce.integerFirstProd JuliaLean.base.reduce._empty_reduce_error)
    (.values values) (.value ⟨.i64, JInt.lit .i64 1⟩)).mapError reshapeErrorOfJl

private def integerIsZero (value : IntegerValue) : RResult Bool :=
  .ok (JuliaLean.base.int.eqSame value.2 (JInt.lit value.1 0))

private def integerDivrem (left right : IntegerValue) : RResult (IntegerValue × IntegerValue) := do
  let (left, right) ← promoteIntegerPair left right
  match left, right with
  | ⟨t, x⟩, ⟨s, y⟩ =>
      if h : t = s then
        let y : JInt t := h ▸ y
        let (q, r) ← (JuliaLean.base.div.divremBitIntegerToZero x y).mapError reshapeErrorOfJl
        .ok (⟨t, q⟩, ⟨t, r⟩)
      else
        .error (.methodError "promote_type")

private def integerComputeNonempty (length : IntegerValue)
    (dims : List (ColonDim IntegerValue)) (product : IntegerValue) : RResult IntegerValue :=
  JuliaLean.base.reshapedarray.reshapeComputeNonempty integerIsZero integerDivrem length dims product

private def integerConvertToI64 (value : IntegerValue) : RResult I64 :=
  (JuliaLean.base.int.convert .i64 value.2).mapError reshapeErrorOfJl

private def promoteIntegerAtLeastInt (value : IntegerValue) : RResult IntegerValue := do
  let target ← integerPromoteType value ⟨.i64, JInt.lit .i64 1⟩
  convertIntegerToType target value

private def promoteColonDim : ColonDim IntegerValue → RResult (ColonDim IntegerValue)
  | .integer value => do
      let promoted ← promoteIntegerAtLeastInt value
      .ok (.integer promoted)
  | .colon => .ok .colon

private def anyColonDispatch {D : Type} (dims : List (ColonDim D)) : Bool :=
  let (_, found) := dims.foldr
    (fun dim (suffix, result) =>
      let result := match dim with
        | .colon => JuliaLean.base.reshapedarray.anyColonHeadColon suffix
        | .integer _ =>
            JuliaLean.base.reshapedarray.anyColonHeadAny (fun _ => result) dim suffix
      (dim :: suffix, result))
    ([], JuliaLean.base.reshapedarray.anyColonNone)
  found
private def beforeColonDispatch {D : Type} (dims : List (ColonDim D)) : List (ColonDim D) :=
  let (_, result) := dims.foldr
    (fun dim (suffix, before) =>
      let before := match dim with
        | .colon => JuliaLean.base.reshapedarray.beforeColonHeadColon suffix
        | .integer _ =>
            JuliaLean.base.reshapedarray.beforeColonHeadAny (fun _ => before) dim suffix
      (dim :: suffix, before))
    ([], [])
  result

private def afterColonDispatch {D : Type} (dims : List (ColonDim D)) : List (ColonDim D) :=
  let (_, result) := dims.foldr
    (fun dim (suffix, after) =>
      let after := match dim with
        | .colon => JuliaLean.base.reshapedarray.afterColonHeadColon suffix
        | .integer _ =>
            JuliaLean.base.reshapedarray.afterColonHeadAny (fun _ => after) dim suffix
      (dim :: suffix, after))
    ([], [])
  result

def reshapeColonArray {T : Type} {M : Nat} {Ref : Type}
    (array : ArrayValue T M Ref) (rawDims : List (ColonDim IntegerValue)) : RResult (List I64) := do
  let dimensions ← JuliaLean.base.reshapedarray.reshapeUncolon
    (fun dim => match dim with | .colon => true | .integer _ => false)
    promoteColonDim
    (fun dims => .ok (beforeColonDispatch dims))
    (fun dims => .ok (afterColonDispatch dims))
    anyColonDispatch
    arrayHeaderLength
    (fun length dims pre post =>
      JuliaLean.base.reshapedarray.reshapeComputeSizeGeneric
        integerProduct integerIsZero promoteIntegerPair integerComputeNonempty
        ⟨.i64, length⟩ dims
        (pre.map fun dim => match dim with | .integer value => value | .colon => ⟨.i64, JInt.lit .i64 1⟩)
        (post.map fun dim => match dim with | .integer value => value | .colon => ⟨.i64, JInt.lit .i64 1⟩))
    array rawDims
  let dims ← dimensions.mapM fun value => integerConvertToI64 value
  let _ ← checkedDimsArrayList dims
  .ok dims


private def cartesianZeroConstructorAs {T : Type} {N : Nat} {P MI : Type}
    (pair : P × IndexStyle) (dims : Vector I64 N) : RResult (ReshapedArray T N P MI) := do
  let result ← JuliaLean.base.reshapedarray.constructReshapedCartesianZero (T := T) (N := N) pair dims
  .ok (reshapedArrayConstructor result.parent result.dims [])



abbrev ReshapeRun (α : Type) := ExceptT ReshapedError Option α

private def liftResult {α : Type} : RResult α → ReshapeRun α
  | .ok value => pure value
  | .error error => throw error



private def reshapeStyleOfArrayIndex (style : JuliaLean.base.indices.IndexStyle) :
    JuliaLean.base.reshapedarray.IndexStyle :=
  match style with
  | .linear => .linear
  | .cartesian => .cartesian




private def subArrayBoundsLinear {T : Type}
    (view : JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T)
    (index : I64) : Bool :=
  match JuliaLean.base.subarray.axesSubArrayModel view with
  | [axis] =>
      match JuliaLean.base.abstractarray.checkindexReal
          (fun current => .ok current.first)
          (fun current => .ok current.last)
          (fun lower value => .ok (decide (lower.val ≤ value.val)))
          (fun value upper => .ok (decide (value.val ≤ upper.val)))
          axis index with
      | .ok result => result
      | .error _ => false
  | _ => false

private def getVectorSubArrayParent {T : Type}
    (view : JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T)
    (index : I64) : ReshapedMutation T T := do
  if !subArrayBoundsLinear view index then throw .boundsError
  arrayMutableGet view.parent (JuliaLean.base.subarray.reindexLinearDispatch view index)

private def setVectorSubArrayParent {T : Type}
    (view : JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T)
    (index : I64) (value : T) : ReshapedMutation T Unit := do
  if !subArrayBoundsLinear view index then throw .boundsError
  liftArrayMutation (JuliaLean.base.array.mutableSet view.parent.ref value
    (JuliaLean.base.subarray.reindexLinearDispatch view index))



private def checkReshapedLinearIndex {T : Type} {N : Nat} {P : Type}
    (array : ReshapedArrayLF T N P) (index : I64) : ReshapedMutation T Unit := do
  let length := JuliaLean.base.essentials.prodDims (reshapedSize array).toList
  if JuliaLean.base.abstractarray.checkindexOneTo length index then
    pure ()
  else
    throw .boundsError

def getReshapedArrayLinear {T : Type} {M N : Nat}
    (array : ReshapedArrayLF T N (ArrayValue T M Nat)) (index : I64) :
    ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.getindexReshapedLinear true checkReshapedLinearIndex
    (fun _ => pure (JInt.lit .i64 1)) (fun _ => pure (JInt.lit .i64 1))
    arrayMutableGet array index

def getReshapedVectorSubArrayLinear {T : Type} {N : Nat}
    (array : ReshapedArrayLF T N (JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T))
    (index : I64) : ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.getindexReshapedLinear true checkReshapedLinearIndex
    (fun _ => pure (JInt.lit .i64 1)) (fun _ => pure (JInt.lit .i64 1))
    getVectorSubArrayParent array index

def setReshapedVectorSubArrayLinear {T : Type} {N : Nat}
    (array : ReshapedArrayLF T N (JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T))
    (index : I64) (value : T) : ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.setindexReshapedLinear true checkReshapedLinearIndex
    (fun _ => pure (JInt.lit .i64 1)) (fun _ => pure (JInt.lit .i64 1))
    setVectorSubArrayParent array value index







private abbrev InverseI64 :=
  JuliaLean.base.multinverses.SignedMultiplicativeInverse
    JInt JuliaLean.base.multinverses.bitDomains .i64

private def inverseI64Run (divisor : I64) : ReshapeRun InverseI64 :=
  match JuliaLean.base.multinverses.signedInverseConstructor
      JuliaLean.base.multinverses.bitDomains
      (JuliaLean.base.multinverses.bitsCallees JuliaLean.base.intfuncs.divremBits)
      (T := .i64) rfl divisor with
  | none => none
  | some (.error error) => some (.error (reshapeErrorOfJl error))
  | some (.ok inverse) => some (.ok inverse)

private def tupleErrorToReshaped : JuliaLean.base.tuple.TupleError → ReshapedError
  | .julia error => reshapeErrorOfJl error
  | .dimensionMismatch => .dimensionMismatch
  | .typeError | .fieldError | .errorException => .errorException

private def tupleFront {S : Type} (values : List S) : RResult (List S) :=
  (JuliaLean.base.tuple.frontTuple values).mapError tupleErrorToReshaped














/- Trusted Julia dispatch domains. The linear flag is the stored type parameter L. -/
abbrev FastVectorSubArray (T : Type) :=
  {view : JuliaLean.base.subarray.SubArray (ArrayValue T 1 Nat) T //
    view.linear = true ∧ view.dimensions.count true = 1}

abbrev CartesianSubArray (T : Type) (M : Nat) :=
  {view : JuliaLean.base.subarray.SubArray (ArrayValue T M Nat) T // view.linear = false}

private def axisLength (axis : JuliaLean.base.subarray.Axis) : I64 :=
  letI : JuliaLean.base.range.JFirst JuliaLean.base.subarray.Axis I64 :=
    ⟨fun current => .ok current.first⟩
  letI : JuliaLean.base.range.JLast JuliaLean.base.subarray.Axis I64 :=
    ⟨fun current => .ok current.last⟩
  letI : JuliaLean.base.range.JCtor I64 I64 :=
    ⟨fun value => .ok (JuliaLean.base.int.widenTo .i64 value)⟩
  JuliaLean.base.int.okOf (JuliaLean.base.range.length_AbstractUnitRange_smallints axis)
    (by intro error equality; cases equality)

private def subArraySize {T P : Type}
    (view : JuliaLean.base.subarray.SubArray P T) : RResult (List I64) :=
  .ok (JuliaLean.base.subarray.sizeSubArray view
    JuliaLean.base.subarray.axesSubArrayModel axisLength)

private def subArrayLength {T P : Type}
    (view : JuliaLean.base.subarray.SubArray P T) : RResult I64 := do
  let sizes ← subArraySize view
  pure (JuliaLean.base.essentials.lengthAbstract (fun _ => sizes)
    JuliaLean.base.essentials.prodDims view)

private def reshapeFastSubArrayIndexStyle {T : Type}
    (_view : FastVectorSubArray T) : RResult IndexStyle :=
  .ok (match JuliaLean.base.subarray.indexStyleFastSubArray with
    | .linear => .linear
    | .cartesian => .cartesian)

def reshapeArrayValueLinear {T : Type} {M N : Nat}
    (array : ArrayValue T M Nat) (dims : Vector I64 N) :
    RResult (ArrayValue T N Nat) :=
  JuliaLean.base.reshapedarray.reshapeDenseArray reshapeArrayHeader array dims

def reshapeFastVectorSubArrayLinear {T : Type} {N : Nat}
    (view : FastVectorSubArray T) (dims : Vector I64 N) (_generalShape : N ≠ 1) :
    ReshapeRun (ReshapedArrayLF T N (FastVectorSubArray T)) :=
  JuliaLean.base.reshapedarray.reshapeAbstractArray
    (fun current => liftResult (subArrayLength current.val))
    (fun dims => liftResult (checkedDimsArray dims))
    (fun n kind dims => liftResult
      (JuliaLean.base.reshapedarray.throwDmrs checkedDimsArray n kind dims))
    (fun current => liftResult (reshapeFastSubArrayIndexStyle current))
    (fun pair dims => liftResult (constructReshapedLinear (T := T) pair dims)) view dims

def getReshapedFastVectorSubArrayLinear {T : Type} {N : Nat}
    (array : ReshapedArrayLF T N (FastVectorSubArray T))
    (index : I64) : ReshapedMutation T T :=
  getReshapedVectorSubArrayLinear
    ⟨array.parent.val, array.dims, array.mi⟩ index

def setReshapedFastVectorSubArrayLinear {T : Type} {N : Nat}
    (array : ReshapedArrayLF T N (FastVectorSubArray T))
    (index : I64) (value : T) : ReshapedMutation T T :=
  setReshapedVectorSubArrayLinear
    ⟨array.parent.val, array.dims, array.mi⟩ index value

/-- Trusted __reshape dispatch for the IndexCartesian SubArray type parameter. -/
def reshapeCartesianSubArray {T : Type} {M N : Nat}
    (view : CartesianSubArray T M) (dims : Vector I64 N)
    (_generalShape : view.val.dimensions.count true ≠ 1 ∨ N ≠ 1) :
    ReshapeRun (ReshapedArray T N (CartesianSubArray T M) InverseI64) :=
  JuliaLean.base.reshapedarray.reshapeAbstractArray
    (fun current => liftResult (subArrayLength current.val))
    (fun dims => liftResult (checkedDimsArray dims))
    (fun n kind dims => liftResult
      (JuliaLean.base.reshapedarray.throwDmrs checkedDimsArray n kind dims))
    (fun _ => pure (reshapeStyleOfArrayIndex JuliaLean.base.indices.IndexStyle_Type_AbstractArray))
    (fun pair dims =>
      if pair.1.val.dimensions.count true = 0 then
        liftResult (cartesianZeroConstructorAs pair dims)
      else
        JuliaLean.base.reshapedarray.constructReshapedCartesian
          (fun current => liftResult (subArraySize current.val))
          (fun shape => liftResult (tupleFront shape))
          (fun n => liftResult ((JuliaLean.base.int.convert .i64 n).mapError reshapeErrorOfJl))
          inverseI64Run pair dims)
    view dims

private def liftMutationResult {T A : Type} (value : RResult A) : ReshapedMutation T A :=
  match value with
  | .ok result => pure result
  | .error error => throw error

private abbrev Axis := JuliaLean.base.range.OneTo I64

private def oneToLength (axis : Axis) : I64 :=
  letI : JuliaLean.base.range.JCtor I64 I64 :=
    ⟨fun value => .ok (JuliaLean.base.int.widenTo .i64 value)⟩
  JuliaLean.base.int.okOf (JuliaLean.base.range.length_OneTo_smallints axis)
    (by intro error equality; cases equality)

private def axesFromDims (dims : List I64) : JuliaLean.base.abstractarray.Result (List Axis) :=
  JuliaLean.base.abstractarray.axesDefault (fun dims => .ok dims)
    JuliaLean.base.range.unchecked_oneto dims

private def arrayAxes {T : Type} {M : Nat} (parent : ArrayValue T M Nat) :
    RResult (List Axis) :=
  (JuliaLean.base.abstractarray.axesDefault
    (fun parent => .ok (JuliaLean.base.essentials.sizeArray (fun p _ => p.dims.toList) parent))
    JuliaLean.base.range.unchecked_oneto parent).mapError abstractArrayErrorToReshaped

private def boundsDims : List Axis → List I64 → JuliaLean.base.abstractarray.Result Bool
  | dims, [] => JuliaLean.base.abstractarray.checkboundsIndicesNil (fun n => .ok (oneToLength n)) dims
  | dims, index :: rest => JuliaLean.base.abstractarray.checkboundsIndicesCons
      (JuliaLean.base.range.unchecked_oneto (JInt.lit .i64 1))
      (fun axis i => .ok (JuliaLean.base.abstractarray.checkindexOneTo axis.stop i))
      (fun tail _ => boundsDims tail rest) dims index rest
termination_by _ indices => indices.length

private def checkDimensions {T : Type} (dims indices : List I64) : ReshapedMutation T Unit := do
  let valid ← liftMutationResult
    ((JuliaLean.base.abstractarray.checkboundsMany axesFromDims
      boundsDims dims indices).mapError abstractArrayErrorToReshaped)
  if !valid then throw .boundsError

private def sub2indLoop : List I64 → I64 → I64 → List I64 →
    JuliaLean.base.abstractarray.Result I64
  | dims, stride, position, [] =>
      .ok (JuliaLean.base.abstractarray.sub2indRecurseDone dims stride position)
  | [], stride, position, index :: rest =>
      JuliaLean.base.abstractarray.sub2indRecurseEmpty
        (fun a b => .ok (JuliaLean.base.int.sub a b))
        (fun a b => .ok (JuliaLean.base.int.mul a b))
        (fun a b => .ok (JuliaLean.base.int.add a b))
        (fun _ s p _ => sub2indLoop [] s p rest) stride position index rest
  | dim :: tail, stride, position, index :: rest =>
      JuliaLean.base.abstractarray.sub2indRecurse
        (fun _ => .ok dim) (fun _ => .ok tail)
        (JuliaLean.base.abstractarray.nextLInteger (fun a b => .ok (JuliaLean.base.int.mul a b)))
        (JuliaLean.base.abstractarray.offsetinInteger (fun a b => .ok (JuliaLean.base.int.sub a b)))
        (fun a b => .ok (JuliaLean.base.int.mul a b))
        (fun a b => .ok (JuliaLean.base.int.add a b))
        (fun dims s p _ => sub2indLoop dims s p rest)
        (dim :: tail) stride position index rest
termination_by _ _ _ indices => indices.length

private def sub2indDims {N : Nat} (dims : Vector I64 N) (indices : List I64) : RResult I64 :=
  (match indices with
    | [] => (Except.ok (JuliaLean.base.abstractarray.sub2indDimsNoIndices dims.toList) :
        JuliaLean.base.abstractarray.Result I64)
    | _ => JuliaLean.base.abstractarray.sub2indDims sub2indLoop dims.toList indices).mapError
      abstractArrayErrorToReshaped

private def arrayCartesianGet {T : Type} {M : Nat}
    (parent : ArrayValue T M Nat) (indices : List I64) : ReshapedMutation T T := do
  match indices with
  | [index] => arrayMutableGet parent index
  | first :: second :: rest =>
      JuliaLean.base.array.getindexCartesian
        (fun parent indices => checkDimensions parent.dims.toList indices)
        (fun parent indices => liftMutationResult (sub2indDims parent.dims indices))
        arrayMutableGet parent first second rest
  | [] =>
      checkDimensions parent.dims.toList []
      arrayMutableGet parent (JInt.lit .i64 1)

private def arrayCartesianSet {T : Type} {M : Nat}
    (parent : ArrayValue T M Nat) (indices : List I64) (value : T) : ReshapedMutation T Unit := do
  match indices with
  | [index] => arrayMutableSet parent index value
  | first :: second :: rest =>
      let _ ← JuliaLean.base.array.setindexCartesian
        (fun (value : T) => some value) (fun value => pure value) (fun value => pure value)
        (JuliaLean.base.array.setindexCartesianTyped
          (fun parent indices => checkDimensions parent.dims.toList indices)
          (fun parent indices => liftMutationResult (sub2indDims parent.dims indices))
          (fun parent index _ => liftArrayMutation
            (JuliaLean.base.array.mutableMemoryref parent.ref index))
          (fun reference value _ => liftArrayMutation
            (JuliaLean.base.array.memoryWrite reference.1 reference.2 (some value))))
        parent value first second rest
      pure ()
  | [] =>
      checkDimensions parent.dims.toList []
      arrayMutableSet parent (JInt.lit .i64 1) value

private def inverseDivrem (index : I64) (inverse : InverseI64) : RResult (I64 × I64) := do
  let ops := JuliaLean.base.multinverses.bitsCallees JuliaLean.base.intfuncs.divremBits
  let (q, r) ← (JuliaLean.base.multinverses.divremInverse ops index
    (JuliaLean.base.multinverses.signedView ops inverse)).mapError reshapeErrorOfJl
  let quotient ← (JuliaLean.base.int.convert .i64 q.2).mapError reshapeErrorOfJl
  let remainder ← (JuliaLean.base.int.convert .i64 r.2).mapError reshapeErrorOfJl
  pure (quotient, remainder)

private def ind2sub (axes : List Axis) (inverses : List InverseI64) (index : I64) :
    RResult (List I64) :=
  match inverses with
  | [] => .ok (JuliaLean.base.reshapedarray.ind2subRsEmpty axes index)
  | _ => JuliaLean.base.reshapedarray.ind2subRs
      (JuliaLean.base.reshapedarray.ind2subRsAuxDispatch inverseDivrem
        (fun axes => match axes with | [] => .error .boundsError | first :: _ => .ok first)
        (fun axis => .ok (JuliaLean.base.range.first_OneTo axis))
        (fun a b => .ok (JuliaLean.base.int.add a b))
        (fun axes => (JuliaLean.base.essentials.tail axes).mapError (fun _ => .argumentError))
        (fun axes => match axes.getLast? with | none => .error .boundsError | some axis => .ok axis)
        (fun axis => .ok (JuliaLean.base.range.first_OneTo axis))
        (fun a b => .ok (JuliaLean.base.int.add a b))) axes inverses index

private def offsetArray (index : I64) (axes : List Axis) : RResult I64 :=
  match axes with
  | [axis] => JuliaLean.base.reshapedarray.offsetIfVec
      (fun axis => .ok (JuliaLean.base.range.first_OneTo axis))
      (fun a b => .ok (JuliaLean.base.int.add a b))
      (fun a => .ok (JuliaLean.base.int.sub a (JInt.lit .i64 1))) index axis
  | _ => .ok (JuliaLean.base.reshapedarray.offsetIfGeneral index axes)

private def checkReshapedCartesian {T P MI : Type} {N : Nat}
    (array : ReshapedArray T N P MI) (indices : List I64) : ReshapedMutation T Unit :=
  checkDimensions array.dims.toList indices

def getReshapedArrayCartesian {T : Type} {M N : Nat}
    (array : ReshapedArray T N (ArrayValue T M Nat) InverseI64)
    (indices : List I64) : ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.getindexReshapedCartesian true checkReshapedCartesian
    (JuliaLean.base.reshapedarray.unsafeGetindexReshaped
      (fun parent => liftMutationResult (arrayAxes parent))
      (fun dims indices => liftMutationResult (sub2indDims dims indices))
      (fun index axes => liftMutationResult (offsetArray index axes))
      (fun axes inverses index => liftMutationResult (ind2sub axes inverses index))
      (JuliaLean.base.reshapedarray.unsafeGetindexReshapedTuple arrayCartesianGet)) array indices

def setReshapedArrayCartesian {T : Type} {M N : Nat}
    (array : ReshapedArray T N (ArrayValue T M Nat) InverseI64)
    (indices : List I64) (value : T) : ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.setindexReshapedCartesian true checkReshapedCartesian
    (JuliaLean.base.reshapedarray.unsafeSetindexReshaped
      (fun parent => liftMutationResult (arrayAxes parent))
      (fun dims indices => liftMutationResult (sub2indDims dims indices))
      (fun index axes => liftMutationResult (offsetArray index axes))
      (fun axes inverses index => liftMutationResult (ind2sub axes inverses index))
      arrayCartesianSet) array value indices

def getReshapedArrayStoredIndex {T : Type} {M N : Nat} {MI : Type}
    (array : ReshapedArray T N (ArrayValue T M Nat) MI) (index : ReshapedIndex I64) :
    ReshapedMutation T T :=
  JuliaLean.base.reshapedarray.getindexReshapedIndex true
    (fun parent index => liftArrayMutation (JuliaLean.base.array.mutableBounds parent.ref index))
    arrayMutableGet array index

end JuliaLean.Bindings.base.reshapedarray
