import JuliaLean.base.slicearray
import JuliaLean.base.subarray
import JuliaLean.base.multidimensional
import JuliaLean.base.intfuncs
import JuliaLean.Proofs.base.intfuncs
import JuliaLean.Bindings.base.reshapedarray

/-!
# Bindings of `base/slicearray.jl`

Binds the revised `base/slicearray.jl` model
(`JuliaLean/base/slicearray.lean`) to installed models and checks it.
Pinned Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

* Errors: one monad `SliceM` whose exception is `SliceError`, the sum of the `abstractarray.jl`
  `ArrayError` (carrying every shared `JlError` as `ArrayError.julia`), the `tuple.jl`
  `TupleError`, the `ntuple.jl` `NtupleError`, the `reshapedarray.jl` `ReshapedError` and the
  `strings/io.jl` printing `Error`. Every lift is a constructor injection.
* `Integer` values: the built-in fixed-width types (`JInt t`, `Int` being native) and a user type
  `MyInt`. Built-in `<=`, `==`, `isequal`, `max` and `convert(Int, x)` are the installed `int.jl`
  dispatchers `int.le`, `int.eq`, `int.max_BitInteger` and `int.convert`; their `show` is the
  installed `show.show_BitInteger`. `MyInt` has its own methods.
* Printing: `printing` supplies a sample `show.jl` environment (`AnyV`, `Ty`, `anyOps`,
  `typeOps`, `printstyled`, `===` and `typeof` of the tuple). These are inputs of `show.jl` with no
  installed counterpart; the checks use them only for a plain `IOBuffer` with no `IOContext`.
* Parents: `Array` headers (`reshapedarray.ArrayValue`), with `size(A)` the installed
  `Bindings.reshapedarray.arrayHeaderSize` and `axes(A)` the installed `abstractarray.axesDefault`;
  `reshape(::Array, dims)` is the installed `Bindings.reshapedarray.reshapeArrayHeader`. The
  `view` check uses a sample matrix with the installed `subarray.viewArray`.
-/

namespace JuliaLean.Bindings.base.slicearray

open JuliaLean JuliaLean.base.slicearray

abbrev Index := JuliaLean.base.subarray.Index
abbrev Axis := JuliaLean.base.subarray.Axis
abbrev SubArray := JuliaLean.base.subarray.SubArray
abbrev ParentArrayOps := JuliaLean.base.subarray.ParentArrayOps
abbrev ViewReadOps := JuliaLean.base.subarray.ViewReadOps
abbrev ReshapedError := JuliaLean.base.reshapedarray.ReshapedError
abbrev ArrayValue := JuliaLean.base.reshapedarray.ArrayValue

/-! ## 1. The exception channel -/

inductive SliceError where
  | array (error : ArrayError)
  | tuple (error : TupleError)
  | ntuple (error : NtupleError)
  | reshaped (error : ReshapedError)
  | print (error : JuliaLean.base.strings.io.Error String)

abbrev SliceM := Except SliceError

instance : MonadExceptOf ArrayError SliceM where
  throw e := .error (.array e)
  tryCatch x h := match x with
    | .error (.array e) => h e
    | r => r

instance : MonadExceptOf TupleError SliceM where
  throw e := .error (.tuple e)
  tryCatch x h := match x with
    | .error (.tuple e) => h e
    | r => r

instance : MonadExceptOf NtupleError SliceM where
  throw e := .error (.ntuple e)
  tryCatch x h := match x with
    | .error (.ntuple e) => h e
    | r => r

instance : MonadExceptOf (JuliaLean.base.strings.io.Error String) SliceM where
  throw e := .error (.print e)
  tryCatch x h := match x with
    | .error (.print e) => h e
    | r => r

def liftReshaped {α : Type} (r : JuliaLean.base.reshapedarray.RResult α) : SliceM α :=
  r.mapError .reshaped

/-! ## 2. `Integer` types -/

/-- A user `Integer` type. `convert(Int, x)` throws `InexactError` when `convertible` is false
or the value does not fit; `promote_rule(MyInt, ::BitInteger) = MyInt`. -/
structure MyInt where
  value : Int
  convertible : Bool := true

inductive Code where
  | bits (t : IntTy)
  | user

abbrev Payload : Code → Type
  | .bits t => JInt t
  | .user => MyInt

abbrev V := IntegerValue Code Payload

/-- A value of a built-in fixed-width type, with its type. -/
def asBits : V → Option (Σ t : IntTy, JInt t)
  | .native x => some ⟨.i64, x⟩
  | .other (.bits t) x => some ⟨t, x⟩
  | .other .user _ => none

/-- A `JInt t` result as an `Integer` value; `Int64` is the native `Int`. -/
def ofBits (t : IntTy) (x : JInt t) : V :=
  if h : t = .i64 then .native (by subst h; exact x) else .other (.bits t) x

def numericValue : V → Int
  | .native x => x.val
  | .other (.bits _) x => x.val
  | .other .user x => x.value

instance : DecidableEq Code := fun a b =>
  match a, b with
  | .bits s, .bits t => if h : s = t then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .user, .user => isTrue rfl
  | .bits _, .user => isFalse (by intro e; cases e)
  | .user, .bits _ => isFalse (by intro e; cases e)

def methods : IntegerMethods Code Payload where
  le x y := match asBits x, asBits y with
    | some ⟨_, a⟩, some ⟨_, b⟩ => JuliaLean.base.int.le a b
    | _, _ => decide (numericValue x ≤ numericValue y)
  eq x y := match asBits x, asBits y with
    | some ⟨_, a⟩, some ⟨_, b⟩ => JuliaLean.base.int.eq a b
    | _, _ => decide (numericValue x = numericValue y)
  isequal x y := match asBits x, asBits y with
    | some ⟨_, a⟩, some ⟨_, b⟩ => JuliaLean.base.int.eq a b
    | _, _ => decide (numericValue x = numericValue y)
  max x y := match asBits x, asBits y with
    | some ⟨s, a⟩, some ⟨t, b⟩ => ofBits (s.promote t) (JuliaLean.base.int.max_BitInteger a b)
    | _, _ => .other .user { value := Max.max (numericValue x) (numericValue y) }
  convertInt
    | .bits _, x => JuliaLean.base.int.convert .i64 x
    | .user, x => if x.convertible then JInt.convert "convert" .i64 x.value
        else .error (.inexactError "convert")
  sameType c c' := decide (c = c')

/-! ### `show.jl` context for printing (sample `IOContext` value and type universe) -/

inductive Ty where
  | any | nothing | bool | pair | tuple | dimsTuple | user
  | bits (t : IntTy)
  deriving DecidableEq

inductive AnyV where
  | bool (b : Bool)
  | type (t : Ty)
  | dims (d : List V)

def anyOps : JuliaLean.base.show.AnyOps AnyV Ty where
  ofBool := .bool
  asBool | .bool b => some b | _ => none
  ofType := .type
  asType | .type t => some t | _ => none
  asDims _ := none
  egal
    | .bool a, .bool b => a == b
    | .type a, .type b => a == b
    | _, _ => false

def typeOps : JuliaLean.base.show.TypeOps (JuliaLean.base.strings.io.BufferShowM String) Ty where
  any := .any
  nothing := .nothing
  bool := .bool
  pair := .pair
  tuple := .tuple
  bitInteger := .bits
  eq a b := pure (a == b)
  egal a b := a == b
  subtype a b := pure (a == b || b == .any || (a == .dimsTuple && b == .tuple))
  fieldtype _ _ := none
  parameter _ _ := .any
  nonnothingtype := pure
  nonmissingtype := pure

abbrev PrintM := JuliaLean.base.strings.io.BufferShowM String

def displaySize : JInt64 × JInt64 := (int 24, int 80)

def prims : JuliaLean.base.show.IOPrims PrintM Unit AnyV :=
  JuliaLean.base.strings.io.bufferPrims displaySize

def digitBytes {t : IntTy} (n : JInt t) : PrintM JuliaLean.base.show.Bytes :=
  JuliaLean.base.show.stringBits JuliaLean.Proofs.base.intfuncs.exactDigitCallees n
    (JuliaLean.base.show.i64 10) (JuliaLean.base.show.i64 1)

/-- `show(io, x)` of a payload: the installed `show(io, ::BitInteger)` dispatcher for built-in
types, `MyInt`'s own method otherwise. -/
def showPayload : (code : Code) → Payload code → JuliaLean.base.show.JIO Unit AnyV → PrintM Unit
  | .bits _, x, io => JuliaLean.base.show.show_BitInteger JuliaLean.Proofs.base.intfuncs.exactDigitCallees
      prims anyOps typeOps (fun io _ => JuliaLean.base.show.printStr prims io "UInt") io x
  | .user, x, io => JuliaLean.base.show.printStr prims io ("MyInt(" ++ toString x.value ++ ")")

/-- `print(io, x)` of a payload as a `print_to_string` argument: `UInt64`/`UInt32`/`Int32` have
their own `StrArg` kinds; other built-in types print `string(n)` under `lock` (`print(io, x) =
show(io, x)` for signed, `print(io, string(n))` for unsigned); `MyInt` prints its `show`. -/
def printPayload : (code : Code) → Payload code → JuliaLean.base.strings.io.StrArg String AnyV
  | .bits .u64, x => .uint64 x
  | .bits .u32, x => .uint32 x
  | .bits .i32, x => .int32 x
  | .bits _, x => .other fun io =>
      JuliaLean.base.show.locked prims io (JuliaLean.base.show.show_Signed prims digitBytes io x)
  | .user, x => .other fun io => JuliaLean.base.show.locked prims io (showPayload .user x io)

def printing : IntegerPrinting String AnyV Ty Code Payload where
  digits := JuliaLean.Proofs.base.intfuncs.exactDigitCallees
  displaySize := displaySize
  anyOps := anyOps
  typeOps := typeOps
  tupleType _ := .dimsTuple
  printstyled io xs _ _ := do for x in xs do x io
  egal _ _ := false
  ofAny := .dims
  printArg := printPayload
  showValue := showPayload

def i (z : Int) : V := .native (int z)
def bits (t : IntTy) (z : Int) : V := .other (.bits t) (JInt.lit t z)
def user (z : Int) (convertible : Bool := true) : V := .other .user { value := z, convertible }

/-! ## 3. `Array` parents -/

def oneToAxis (n : I64) : Axis := ⟨JuliaLean.base.subarray.int64 1, n⟩

def axisLength (axis : Axis) : I64 :=
  JuliaLean.base.subarray.iadd (JuliaLean.base.subarray.isub axis.last axis.first)
    (JuliaLean.base.subarray.int64 1)

/-- `size(a::Array) = getfield(a, :size)`, the installed header read. -/
def arraySize {N : Nat} (a : ArrayValue Int N Nat) : Result (List I64) :=
  .ok (JuliaLean.Bindings.base.reshapedarray.arrayHeaderSize a)

/-- The construction methods of `Array{Int,N}`: `ndims` is `N`, `axes(A)` is the installed
`axes(A) = map(unchecked_oneto, size(A))`. -/
def arrayOps (N : Nat) : SliceParentOps SliceM (ArrayValue Int N Nat) Axis where
  parentType := "Array{Int64, " ++ toString N ++ "}"
  ndims := fun _ => pure (int N)
  axes := JuliaLean.base.abstractarray.axesDefault arraySize oneToAxis
  oneTo := oneToAxis
  axisEltype := fun _ => "Int64"
  axisLength := fun axis => pure (axisLength axis)
  promoteView := fun parent args =>
    "SubArray{" ++ parent ++ "," ++ toString args.length ++ "}"

/-- `reshape(a::Array, dims::NTuple{2,Int})` (reshapedarray.jl:43-51), the installed
`reshapeArrayHeader`. The `eachrow`/`eachcol` vector methods always pass two dimensions; a
tuple of another length has no method returning a matrix. -/
def reshapeToMatrix (a : ArrayValue Int 1 Nat) (dims : List I64) : SliceM (ArrayValue Int 2 Nat) :=
  match dims with
  | [rows, cols] =>
      liftReshaped (JuliaLean.Bindings.base.reshapedarray.reshapeArrayHeader a #v[rows, cols])
  | _ => throwThe ArrayError (.julia (.methodError "reshape"))

/-! ## 4. `view` for the sample matrix -/

def removeSingletons (indexNdims : List Index → List Bool) :
    List Bool → List Index → List Index
  | _, [] => JuliaLean.base.subarray.removeSingletonIndicesEmpty
  | [], head :: tail =>
      if JuliaLean.base.subarray.Index.isScalar head then
        JuliaLean.base.subarray.removeSingletonScalarEmpty head tail
          (fun _ _ => removeSingletons indexNdims [] tail)
      else JuliaLean.base.subarray.removeSingletonIndices [] head tail (fun i => indexNdims [i])
        JuliaLean.base.multidimensional.splitrestDispatch
        (fun dimensions _ => removeSingletons indexNdims dimensions tail)
  | dimensions@(_ :: _), head :: tail =>
      JuliaLean.base.subarray.removeSingletonIndices dimensions head tail (fun i => indexNdims [i])
        JuliaLean.base.multidimensional.splitrestDispatch
        (fun dimensions _ => removeSingletons indexNdims dimensions tail)
termination_by _ indices => indices.length

def reshapeParent {P : Type} (rank : P → Nat) (reshape : P → Nat → Jl P)
    (parent : P) (dimensions : List Bool) : Jl P :=
  if dimensions.length = 1 then
    if rank parent = 1 then JuliaLean.base.subarray.maybeReshapeVectorParent parent reshape
    else JuliaLean.base.subarray.maybeReshapeParentOne parent reshape
  else if rank parent = dimensions.length then
    JuliaLean.base.subarray.maybeReshapeParentSameRank parent dimensions
  else JuliaLean.base.subarray.maybeReshapeParent parent dimensions reshape

/-- The parent operations the installed `subarray.viewArray` still takes as pure functions
(`to_indices`, `unalias`, `ndims`), `checkbounds`, `reshape(A, Val(N))` and reads. -/
structure ViewParent (P T R : Type) where
  rank : P → Nat
  toIndices : P → List Index → List Index
  unalias : P → Index → Index
  checkBounds : P → List Index → Jl Unit
  reshape : P → Nat → Jl P
  read : ViewReadOps P T R

def selectorIndex : Option I64 → Index
  | none => .colon
  | some i => .scalar i

def viewParent {P T R : Type} (pops : ParentArrayOps P) (vp : ViewParent P T R)
    (p : P) (indices : List Index) : Jl (SubArray P T) :=
  JuliaLean.base.subarray.viewArray p indices vp.unalias vp.toIndices vp.checkBounds vp.rank
    (removeSingletons pops.indexNdims) (reshapeParent vp.rank vp.reshape) pops.indexNdims
    (fun q J => JuliaLean.base.subarray.unsafeViewArray q J
      (JuliaLean.base.subarray.constructSubArrayConfigured pops))

namespace Checks

open JuliaLean.base.subarray (int64 iadd isub)

structure Mat where
  rows : Nat
  cols : Nat
  data : List Int

def sample : Mat := ⟨2, 3, [11, 21, 12, 22, 13, 23]⟩

def matAxes (p : Mat) : List Axis := [⟨int64 1, int64 p.rows⟩, ⟨int64 1, int64 p.cols⟩]

def indexFirst : Index → Jl I64
  | .scalar i => .ok i
  | .slice axis => .ok axis.first
  | _ => .error .boundsError

def matPops : ParentArrayOps Mat where
  parentStyle := fun _ => .linear
  isArrayRank := fun _ rank => rank == 2
  ndims := fun _ => pure 2
  indexNdims := fun indices => indices.map fun _ => true
  indexDimsum := fun indices =>
    (indices.filter fun i => !JuliaLean.base.subarray.Index.isScalar i).map fun _ => true
  ensureIndexable := JuliaLean.base.multidimensional.ensureIndexableDispatch
  axes := matAxes
  strides := fun p => pure [int64 1, int64 p.rows]
  fillToLength := fun axes axis count => pure (axes ++ List.replicate (count - axes.length) axis)
  firstLinearIndex := fun _ => pure (int64 1)
  axisFirst := JuliaLean.base.subarray.Axis.first
  axisLength := axisLength
  indexFirst := indexFirst
  indexStep := fun _ => int64 1
  indexTypeName := fun i =>
    if JuliaLean.base.subarray.Index.isScalar i then "Int64" else "Base.Slice{Base.OneTo{Int64}}"
  axes1First := indexFirst
  isVector := fun _ => false

def readAt (p : Mat) (linear : Int) : Jl Int :=
  if linear < 1 then .error .boundsError
  else match p.data[(linear - 1).toNat]? with
    | some x => .ok x
    | none => .error .boundsError

def matRead : ViewReadOps Mat Unit Int where
  cartesian := fun _ _ => pure ()
  linear := fun _ _ => pure ()
  getVector := fun _ _ => .error .boundsError
  getMatrix := fun _ _ _ => .error .boundsError
  getArray := fun _ _ => .error .boundsError
  getParentCartesian := fun p indices => match indices with
    | [.scalar i, .scalar j] => readAt p (i.val + (j.val - 1) * p.rows)
    | _ => .error .boundsError
  getParentLinear := fun p i => readAt p i.val

def matView : ViewParent Mat Unit Int where
  rank := fun _ => 2
  toIndices := fun p indices => (indices.zip (matAxes p)).map fun (i, axis) =>
    match i with
    | .colon => .slice axis
    | index => index
  unalias := fun _ i => i
  checkBounds := fun _ _ => pure ()
  reshape := fun p _ => pure p
  read := matRead

def matOps : SliceParentOps SliceM Mat Axis where
  parentType := "Matrix{Int64}"
  ndims := fun _ => pure (int 2)
  axes := fun p => .ok (matAxes p)
  oneTo := oneToAxis
  axisEltype := fun _ => "Int64"
  axisLength := fun axis => pure (axisLength axis)
  promoteView := fun parent args =>
    "SubArray{" ++ parent ++ "," ++ toString args.length ++ "}"

def matAccess : SliceAccessOps SliceM Mat (SubArray Mat Unit) Unit where
  view := fun p selectors => liftJl (viewParent matPops matView p (selectors.map selectorIndex))
  setindexParent := fun _ _ value => pure value

def axisPairs (axes : List Axis) : List (Int × Int) := axes.map fun a => (a.first.val, a.last.val)

def entryCode : Option V → Int
  | none => 0
  | some (.native i) => i.val
  | some (.other _ _) => -1

def outcome (r : SliceM (SliceConstruction Mat Axis Code Payload)) :
    Option (List (Int × Int) × List Int) :=
  match r with
  | .ok ⟨_, s⟩ => some (axisPairs s.axes, s.slicemap.map entryCode)
  | .error _ => none

-- eachcol of a matrix: drop the column dimension; the axes are the parent's own `axes(A, 2)`.
#guard outcome (eachcolMatrix matOps methods printing sample) == some ([(1, 3)], [0, 1])
-- eachrow of a matrix.
#guard outcome (eachrowMatrix matOps methods printing sample) == some ([(1, 2)], [1, 0])
-- Without drop, the unselected dimension gets `unitaxis(A)`.
#guard outcome (eachsliceTuple matOps methods printing sample [i 1] false) == some ([(1, 2), (1, 1)], [1, 0])
-- A dimension beyond the parent's rank gets `axes(A, 3) == OneTo(1)` from the installed axesDim.
#guard outcome (eachsliceTuple matOps methods printing sample [i 3] true) == some ([(1, 1)], [0, 0, 1])
-- Mixed types: dims = (Int8(2), 1). `max(2, Int8(2))` promotes to `Int`, and `axes(A, Int8(2))`
-- reads `axes(A)[Int8(2)]` through the generic tuple getter.
#guard outcome (eachsliceTuple matOps methods printing sample [bits .i8 2, i 1] true) ==
  some ([(1, 3), (1, 2)], [2, 1])
-- dims = (UInt64(1),): `max(2, UInt64(1))` is `UInt64(2)`, so the rank goes through
-- `ntuple(f, n::Integer)` and its checked conversion.
#guard outcome (eachsliceTuple matOps methods printing sample [bits .u64 1] true) == some ([(1, 2)], [1, 0])
#guard (match (methods.max (i 2) (bits .u64 1)) with
  | .other (.bits .u64) x => x.val == 2
  | _ => false)
-- dims = (UInt64(2)^63,): a valid dimension whose rank `convert(Int, N_)` overflows: InexactError
-- from the installed `ntupleInteger`, not a list.
#guard (match (eachsliceTuple matOps methods printing sample [bits .u64 (2 ^ 63)] true) with
  | .error (.ntuple (.base (.inexactError _))) => true
  | _ => false)
-- A user `Integer`: its own `<=`, `max`, `isequal` and `convert(Int, d)` run.
#guard outcome (eachsliceTuple matOps methods printing sample [user 2] true) == some ([(1, 3)], [0, 1])
-- A user dimension whose `convert(Int, d)` throws: `axes(A, d)` propagates the InexactError.
#guard (match (eachsliceTuple matOps methods printing sample [user 1 false] true) with
  | .error (.array (.julia (.inexactError _))) => true
  | _ => false)
-- `_slice_check_dims` messages: `string(...)` through the installed `print_to_string`, a tuple
-- through the installed `show(io, ::Tuple)`.
#guard (match (eachsliceTuple matOps methods printing sample [i 0] true) with
  | .error (.array (.dimensionMismatch msg)) => msg == "Invalid dimension 0"
  | _ => false)
#guard (match (eachsliceTuple matOps methods printing sample [bits .i8 (-3)] true) with
  | .error (.array (.dimensionMismatch msg)) => msg == "Invalid dimension -3"
  | _ => false)
#guard (match (eachsliceTuple matOps methods printing sample [i 2, bits .i8 2] true) with
  | .error (.array (.dimensionMismatch msg)) => msg == "Dimensions (2,) are not unique"
  | _ => false)
#guard (match (eachsliceTuple matOps methods printing sample [i 3, i 1, i 3, i 2] true) with
  | .error (.array (.dimensionMismatch msg)) => msg == "Dimensions (1, 3, 2) are not unique"
  | _ => false)
#guard (match (eachsliceTuple matOps methods printing sample [i 1, bits .u64 1] true) with
  | .error (.array (.dimensionMismatch msg)) => msg == "Dimensions (0x0000000000000001,) are not unique"
  | _ => false)

#guard JuliaLean.base.slicearray.invalidDimensionText.bytes == JuliaLean.base.show.lit "Invalid dimension "
#guard JuliaLean.base.slicearray.dimensionsText.bytes == JuliaLean.base.show.lit "Dimensions "
#guard JuliaLean.base.slicearray.notUniqueText.bytes == JuliaLean.base.show.lit " are not unique"

-- 32 or more remaining dims: `dim in dims` goes through `in(x, ::Any32)` and `any(f, ::Tuple)`.
def run (k : Nat) : List V := (List.range k).map fun (j : Nat) => i (Int.ofNat j + 2)
-- 33 distinct dims, the rest an `NTuple` (`_any(f, itr, :)` loop).
#guard (match (eachsliceTuple matOps methods printing sample (i 1 :: run 32) true) with
  | .ok ⟨n, _⟩ => n == 33
  | .error _ => false)
-- 33 distinct dims, the rest a 32-element tuple of mixed types (`_any_tuple`).
#guard (match (eachsliceTuple matOps methods printing sample (i 1 :: bits .i8 2 :: (run 32).drop 1) true) with
  | .ok ⟨n, _⟩ => n == 33
  | .error _ => false)
-- A repeat found by the `Any32` path.
#guard (match (eachsliceTuple matOps methods printing sample (i 1 :: (run 32 ++ [i 1])) true) with
  | .error (.array (.dimensionMismatch msg)) =>
      msg.startsWith "Dimensions (2, 3, 4," && msg.endsWith ", 33, 1) are not unique"
  | _ => false)
-- Slices(A, slicemap, ax) rejects a slicemap shorter than ndims(A).
#guard (match (slicesConstructor matOps methods sample [none] [] : SliceM _) with
  | .error (.array (.julia (.argumentError _))) => true
  | _ => false)

-- eachrow / eachcol of an `Array` vector: `size(A, 1)` and `reshape(A, n, 1)` are installed.
def vec3 : ArrayValue Int 1 Nat := ⟨0, #v[int 3]⟩

def vectorOutcome (r : SliceM (SliceConstruction (ArrayValue Int 2 Nat) Axis Code Payload)) :
    Option (List Int × List (Int × Int) × List Int) :=
  match r with
  | .ok ⟨_, s⟩ => some (s.parent.dims.toList.map (·.val), axisPairs s.axes, s.slicemap.map entryCode)
  | .error _ => none

#guard vectorOutcome (eachrowVector arraySize reshapeToMatrix (arrayOps 2) methods printing vec3) ==
  some ([3, 1], [(1, 3)], [1, 0])
#guard vectorOutcome (eachcolVector arraySize reshapeToMatrix (arrayOps 2) methods printing vec3) ==
  some ([3, 1], [(1, 1)], [0, 1])

-- `_slice_index` with a user `Integer` entry: its own conversion runs and its error propagates;
-- an out-of-range converted index is the installed getfield's BoundsError.
def userSlices (entry : V) : Slices Mat Axis Code Payload 1 :=
  ⟨sample, "SubArray", [none, some entry], [⟨int64 1, int64 3⟩], rfl⟩

#guard (match (sliceIndex methods (userSlices (user 1)) [int 3] : SliceM _) with
  | .ok selectors => selectors.map (·.map (·.val)) == [none, some 3]
  | .error _ => false)
#guard (match (sliceIndex methods (userSlices (user 1 false)) [int 3] : SliceM _) with
  | .error (.array (.julia (.inexactError _))) => true
  | _ => false)
#guard (match (sliceIndex methods (userSlices (user 5)) [int 3] : SliceM _) with
  | .error (.tuple (.julia .boundsError)) => true
  | _ => false)

-- getindex(s, 2) is view(A, :, 2): the installed viewArray builds the SubArray, whose installed
-- reader returns A[2, 2] for coordinate 2.
def colSlices : Slices Mat Axis Code Payload 1 :=
  ⟨sample, "SubArray", [none, some (i 1)], [⟨int64 1, int64 3⟩], rfl⟩

#guard (match (do
    let v ← getindex (fun _ _ => pure ()) matAccess methods colSlices ⟨[int 2], rfl⟩
    liftJl (JuliaLean.base.subarray.getindexSubArrayConfigured v [int 2] matRead) : SliceM Int) with
  | .ok x => x == 22
  | .error _ => false)

end Checks

end JuliaLean.Bindings.base.slicearray
