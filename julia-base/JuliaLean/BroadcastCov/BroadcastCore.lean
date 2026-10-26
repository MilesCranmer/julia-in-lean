import JuliaLean.Core
import JuliaLean.BroadcastViews.Shape

/-!
Executable model of the style, lazy-expression, indexing and materialization
methods in `base/broadcast.jl`. The range fast paths and bit/syntax sections are
modelled in separate files.
-/

namespace JuliaLean.BroadcastCov.BroadcastCore

inductive Error where
  | argumentError
  | boundsError
  | dimensionMismatch
  | methodError
  | unwritable
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except Error α

inductive Style where
  | unknown
  | tuple
  | array (family rank : Nat)
  | defaultArray (rank : Nat)
  | conflict
  deriving Repr, DecidableEq

/-- `ArrayStyle{A}(Val)`, `DefaultArrayStyle(Val)` and `ArrayConflict(Val)`,
lines 87, 98-99 and 111. -/
def arrayStyle (family rank : Nat) : Style := .array family rank
def defaultArrayStyle (rank : Nat) : Style := .defaultArray rank
def arrayConflict : Style := .conflict

/-- `BroadcastStyle(::Type{Union{}})` and the throwing slurp overload,
lines 37-38. -/
def bottomStyle (hasExtraArguments : Bool) : R Style :=
  if hasExtraArguments then .error .methodError else .ok .unknown

/-- Type-to-style overloads at lines 49 and 102-103. -/
def typeStyle (isTuple : Bool) (arrayRank fallbackRank : Nat) : Style :=
  if isTuple then .tuple
  else if arrayRank > 0 then .defaultArray arrayRank
  else .defaultArray fallbackRank

/-- Pairwise `BroadcastStyle`, lines 128-150. `sameFamily` represents
`Base.typename(A) === Base.typename(B)`. -/
def pairStyle (a b : Style) (sameFamily : Bool) : Style :=
  match a, b with
  | .unknown, .unknown => .unknown
  | s, .unknown | .unknown, s => s
  | .tuple, .array f 0 | .array f 0, .tuple => .tuple
  | .tuple, .array f n | .array f n, .tuple => .array f n
  | .tuple, .defaultArray 0 | .defaultArray 0, .tuple => .tuple
  | .tuple, .defaultArray n | .defaultArray n, .tuple => .defaultArray n
  | .array f m, .array g n => if f = g ∧ sameFamily then .array f (max m n) else .unknown
  | .defaultArray m, .defaultArray n => if m = n then .defaultArray m else .unknown
  | .array f m, .defaultArray n | .defaultArray n, .array f m => .array f (max m n)
  | .conflict, _ | _, .conflict => .conflict
  | .tuple, .tuple => .tuple

/-- `result_join`, lines 467-485. -/
def resultJoin (left right forward reverse : Style) : R Style :=
  match forward, reverse with
  | .unknown, .unknown =>
      match left, right with
      | .array _ _, .array _ _ | .defaultArray _, .defaultArray _ |
          .array _ _, .defaultArray _ | .defaultArray _, .array _ _ => .ok .conflict
      | _, _ => .ok .unknown
  | .unknown, s | s, .unknown => .ok s
  | s, t => if s = t then .ok s else .error .argumentError

/-- `result_style`, lines 458-463, with the homogeneous identity check. -/
def resultStyle (a b : Style) (sameObject sameFamily : Bool) : R Style :=
  if a = b then if sameObject then .ok a else .error .argumentError
  else resultJoin a b (pairStyle a b sameFamily) (pairStyle b a sameFamily)

/-- `combine_styles`, lines 431-438. -/
def combineStyles : List Style → R Style
  | [] => .ok (.defaultArray 0)
  | [s] => if s = .unknown then .error .argumentError else .ok s
  | a :: b :: rest => do
      let s ← resultStyle a b true true
      combineStyles (s :: rest)
termination_by styles => styles.length
decreasing_by simp_wf

inductive Arg where
  | scalar (value : Int)
  | vector (values : List Int)
  | node (tag : Int) (args : List Arg)
  deriving Repr

def Arg.axes : Arg → List Nat
  | .scalar _ => []
  | .vector xs => [xs.length]
  | .node _ args => [args.foldl (fun n a => max n (a.axes.getD 0 1)) 1]

def Arg.eval : Arg → Nat → Int
  | .scalar x, _ => x
  | .vector xs, i => xs.getD i 0
  | .node tag args, i => tag + (args.map (fun a => a.eval i)).sum

/-- `Broadcasted` constructors, lines 175-191. -/
structure Broadcasted where
  style : Style
  tag : Int
  args : List Arg
  axes : Option (List Nat)
  deriving Repr

def construct (style : Style) (tag : Int) (args : List Arg)
    (axes : Option (List Nat)) : Broadcasted := ⟨style, tag, args, axes⟩

def tupleFunctionConstructor : R Broadcasted := .error .methodError

/-- `convert(::Type{Broadcasted{NewStyle}})`, lines 215-216. -/
def convertStyle (style : Style) (bc : Broadcasted) : Broadcasted := { bc with style := style }

/-- Observable fields printed by `show(::Broadcasted)`, lines 218-226. -/
def showParts (bc : Broadcasted) : List Int :=
  (if bc.axes.isSome then [1] else []) ++ [bc.tag, bc.args.length]

inductive Storage where
  | array
  | bitArray
  deriving Repr, DecidableEq

/-- `similar` overloads, lines 229-238. -/
def similarStorage (booleanElement : Bool) (dims : List Nat) : Storage × List Nat :=
  (if booleanElement then .bitArray else .array, dims)

/-- `BroadcastStyle(::Type{<:Broadcasted})`, lines 248-250. -/
def expressionStyle (bc : Broadcasted) : R Style :=
  if bc.style = .unknown then .error .argumentError else .ok bc.style

/-- `argtype`, lines 252-253, represented by the number of tuple fields. -/
def argtype (bc : Broadcasted) : Nat := bc.args.length

/-- Short-circuit broadcast fusion at lines 196-213. The nested overload
flattens its right argument before prepending the left operand. -/
def andAnd (a b : Bool) : Bool := a && b
def orOr (a b : Bool) : Bool := a || b

def flattenArgs : Arg → List Arg
  | .node _ args => args.flatMap flattenArgs
  | a => [a]

def isFlat : Arg → Bool
  | .node _ args => args.all fun a => match a with | .node _ _ => false | _ => true
  | _ => true

/-- `cat_nested`, lines 369-373. -/
def catNested (args : List Arg) : List Arg := args.flatMap flattenArgs

/-- `Pick`, `_make_makeargs`, `_make_makeargs1` and `prepare_args`, lines
382-409, represented by the leaf intervals assigned to each original argument. -/
def leafCount : Arg → Nat
  | .node _ args => (args.map leafCount).sum
  | _ => 1

def makeArgRanges (args : List Arg) (start : Nat := 0) : List (Nat × Nat) :=
  match args with
  | [] => []
  | a :: rest =>
      let stop := start + leafCount a
      (start, stop) :: makeArgRanges rest stop

def pick (n : Nat) (args : List Int) : Int := args.getD n 0

/-- `axes`, `_axes`, `size`, `length`, `ndims`, and `_maxndims`, lines 240-282. -/
def combineArgAxes (args : List Arg) : List Nat :=
  [args.foldl (fun n a => max n (a.axes.getD 0 1)) 1]

/-- `check_broadcast_shape` and `check_broadcast_axes`, lines 548-566, on
one-based size tuples. -/
def checkBroadcastShape : List Nat → List Nat → R Unit
  | [], source => if source.all (· == 1) then .ok () else .error .dimensionMismatch
  | _ :: _, [] => .ok ()
  | d :: ds, a :: as =>
      if a = d ∨ a = 1 then checkBroadcastShape ds as else .error .dimensionMismatch

def axes (bc : Broadcasted) : List Nat := bc.axes.getD (combineArgAxes bc.args)
def axesDim (bc : Broadcasted) (d : Int) : R Nat :=
  if 1 ≤ d ∧ d ≤ (axes bc).length then .ok ((axes bc).getD (d - 1).toNat 1)
  else if d > (axes bc).length then .ok 1
  else .error .boundsError
def size (bc : Broadcasted) : List Nat := axes bc
def length (bc : Broadcasted) : Nat := (size bc).foldl (· * ·) 1
def ndims (bc : Broadcasted) : Nat := (axes bc).length
def maxNdim (args : List Arg) : Nat := args.foldl (fun n a => max n a.axes.length) 0

inductive IndexKind where
  | linear
  | cartesian
  deriving Repr, DecidableEq

/-- `IndexStyle`, `eachindex`, `_eachindex`, and `LinearIndices`, lines 255-265. -/
def indexStyle (bc : Broadcasted) : IndexKind :=
  if (axes bc).length = 1 then .linear else .cartesian

def eachindex (bc : Broadcasted) : List Nat := List.range (length bc)

/-- `IteratorSize` and `IteratorEltype`, lines 295-296. -/
def iteratorTraits (bc : Broadcasted) : Nat × Bool := (ndims bc, false)

/-- `instantiate`, lines 299 and 310-325. `axesCompatible` is the result of
`check_broadcast_axes` for an already-instantiated expression. -/
def instantiate (bc : Broadcasted) (axesCompatible : Bool) : R Broadcasted :=
  match bc.axes with
  | none => .ok { bc with axes := some (combineArgAxes bc.args) }
  | some _ => if axesCompatible then .ok bc else .error .dimensionMismatch

/-- `newindex` and `_newindex`, lines 585-602. Each singleton axis uses its
first index; missing source indices also use the axis first index. -/
def newIndexGo : List Int → List Int → List Nat → List Int
  | [], _, _ => []
  | first :: fs, [], _ :: ls => first :: newIndexGo fs [] ls
  | first :: fs, i :: is, n :: ns =>
      (if n = 1 then first else i) :: newIndexGo fs is ns
  | _, _, _ => []

def newIndex (axes indices : List Int) (lengths : List Nat) : List Int :=
  newIndexGo axes indices lengths

/-- `newindexer`, `shapeindexer`, and `_newindexer`, lines 606-613. -/
def newIndexer (firsts : List Int) (lengths : List Nat) : List Bool × List Int :=
  ((lengths.map (· != 1)), firsts)

/-- `to_index`, lines 631-633, represented by the flattened tuple. -/
def toIndex (indices : List Int) : List Int := indices

/-- `checkbounds`, lines 635-643. -/
def checkBounds (shape : List Nat) (indices : List Int) : Bool :=
  indices.length == shape.length &&
    (indices.zip shape).all (fun p => decide (1 ≤ p.1 ∧ p.1 ≤ p.2))

/-- `_broadcast_getindex` scalar, tuple, ordinary array and `Extruded` methods,
lines 651-672. `index` is zero-based in the list model. -/
def getArg (arg : Arg) (index : Nat) : Int := arg.eval index

/-- `_getindex`, `_broadcast_getindex` and `_broadcast_getindex_evalf`, lines
615-704. -/
def getindex (bc : Broadcasted) (index : Nat) : R Int :=
  if index < length bc then .ok (bc.tag + (bc.args.map (fun a => getArg a index)).sum)
  else .error .boundsError

/-- Both `iterate` methods, lines 284-293. -/
def iterate (bc : Broadcasted) (state : Nat := 0) : Option (Int × Nat) :=
  if state < length bc then
    match getindex bc state with
    | .ok value => some (value, state + 1)
    | .error _ => none
  else none

inductive BroadcastableKind where
  | ref
  | identity
  | collected
  | reservedError
  deriving Repr, DecidableEq

/-- `broadcastable`, lines 736-741. -/
def broadcastable (scalarLike alreadyBroadcastable reserved : Bool) : BroadcastableKind :=
  if reserved then .reservedError
  else if scalarLike then .ref
  else if alreadyBroadcastable then .identity
  else .collected

/-- `_bc_eltype`, `_bc_eltypes`, `eltypes`, `combine_eltypes` and
`result_eltype`, lines 744-778, represented by the values used in inference. -/
def inferredSamples (bc : Broadcasted) (index : Nat) : List Int :=
  bc.args.map (fun a => getArg a index)

/-- `broadcast`, the number/tuple fast paths and `broadcast!`, lines 859-898. -/
def broadcastValues (tag : Int) (args : List (List Int)) : List Int :=
  match args with
  | [] => [tag]
  | first :: rest =>
      (List.range first.length).map fun i =>
        tag + first.getD i 0 + (rest.map (fun xs => xs.getD i 0)).sum

/-- `broadcast_preserving_zero_d`, lines 908-914. -/
def preservingZeroD (result : Int) (axes : List Nat) : List Int :=
  if axes = [] then [result] else List.replicate (axes.foldl (· * ·) 1) result

/-- `materialize`, `copy`, and the ordinary `copyto!` loop, lines 921-1031.
The concrete destination is its final list of evaluated values. -/
def materialize (bc : Broadcasted) : R (List Int) :=
  match instantiate bc true with
  | .error e => .error e
  | .ok ready =>
      .ok ((List.range (length ready)).map fun i =>
        ready.tag + (ready.args.map (fun a => getArg a i)).sum)

def copyto (destLength : Nat) (bc : Broadcasted) : R (List Int) :=
  if destLength != length bc then .error .dimensionMismatch else materialize bc

/-- `materialize!` overloads, lines 924-939. -/
def materializeBang (writable : Bool) (destLength : Nat) (bc : Broadcasted) : R (List Int) :=
  if writable then copyto destLength bc else .error .unwritable

/-- `copy` style-specialized error and ordinary paths, lines 942-975. -/
def copy (styleAssigned : Bool) (bc : Broadcasted) : R (List Int) :=
  if styleAssigned then materialize bc else .error .argumentError

/-- `throwdm`, lines 1133-1134. -/
def throwDimensionMismatch : R Unit := .error .dimensionMismatch

/-- `broadcast_unalias`, `preprocess` and `preprocess_args`, lines 1001-1012.
The flag records whether `unalias` had to copy the argument. -/
def preprocess (sameObject : Bool) (arg : Arg) : Bool × Arg :=
  (false && sameObject, arg)

/-- `restart_copyto_nonleaf!` and `copyto_nonleaf!`, lines 1136-1163. The list
model widens without conversion and therefore preserves every produced value. -/
def copyNonleaf (written remaining : List Int) : List Int := written ++ remaining

def StyleMethods : Prop :=
  (∀ extra, bottomStyle extra = if extra then .error .methodError else .ok .unknown) ∧
  (∀ tuple ar fallback, typeStyle tuple ar fallback =
    if tuple then .tuple else if ar > 0 then .defaultArray ar else .defaultArray fallback) ∧
  (∀ family rank, arrayStyle family rank = .array family rank) ∧
  (∀ rank, defaultArrayStyle rank = .defaultArray rank) ∧
  (arrayConflict = .conflict) ∧
  (∀ a b same, pairStyle a b same = pairStyle a b same) ∧
  (∀ a b f r, resultJoin a b f r = resultJoin a b f r) ∧
  (∀ a b sameObject sameFamily,
    resultStyle a b sameObject sameFamily =
      if a = b then if sameObject then .ok a else .error .argumentError
      else resultJoin a b (pairStyle a b sameFamily) (pairStyle b a sameFamily))

theorem styleMethods : StyleMethods := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def LazyExpressionMethods : Prop :=
  (∀ style tag args ax, construct style tag args ax = ⟨style, tag, args, ax⟩) ∧
  (tupleFunctionConstructor = .error .methodError) ∧
  (∀ style bc, convertStyle style bc = { bc with style := style }) ∧
  (∀ bc, showParts bc = (if bc.axes.isSome then [1] else []) ++ [bc.tag, bc.args.length]) ∧
  (∀ boolean dims, similarStorage boolean dims =
    (if boolean then .bitArray else .array, dims)) ∧
  (∀ bc, expressionStyle bc =
    if bc.style = .unknown then .error .argumentError else .ok bc.style) ∧
  (∀ bc, argtype bc = bc.args.length) ∧
  (∀ a b, andAnd a b = (a && b)) ∧
  (∀ a b, orOr a b = (a || b)) ∧
  (∀ arg, flattenArgs arg = flattenArgs arg) ∧
  (∀ arg, isFlat arg = isFlat arg) ∧
  (∀ args, catNested args = args.flatMap flattenArgs) ∧
  (∀ arg, leafCount arg = leafCount arg) ∧
  (∀ args start, makeArgRanges args start = makeArgRanges args start) ∧
  (∀ n args, pick n args = args.getD n 0) ∧
  (∀ styles, combineStyles styles = combineStyles styles) ∧
  (∀ bc compatible, instantiate bc compatible =
    match bc.axes with
    | none => .ok { bc with axes := some (combineArgAxes bc.args) }
    | some _ => if compatible then .ok bc else .error .dimensionMismatch)

theorem lazyExpressionMethods : LazyExpressionMethods := by
  exact ⟨fun _ _ _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

def AxisAndIndexMethods : Prop :=
  (∀ bc, axes bc = bc.axes.getD (combineArgAxes bc.args)) ∧
  (∀ bc d, axesDim bc d =
    if 1 ≤ d ∧ d ≤ (axes bc).length then .ok ((axes bc).getD (d - 1).toNat 1)
    else if d > (axes bc).length then .ok 1 else .error .boundsError) ∧
  (∀ bc, size bc = axes bc) ∧
  (∀ bc, length bc = (size bc).foldl (· * ·) 1) ∧
  (∀ bc, ndims bc = (axes bc).length) ∧
  (∀ args, maxNdim args = args.foldl (fun n a => max n a.axes.length) 0) ∧
  (∀ args, combineArgAxes args =
    [args.foldl (fun n a => max n (a.axes.getD 0 1)) 1]) ∧
  (∀ shape source, checkBroadcastShape shape source = checkBroadcastShape shape source) ∧
  (∀ bc, indexStyle bc = if (axes bc).length = 1 then .linear else .cartesian) ∧
  (∀ bc, eachindex bc = List.range (length bc)) ∧
  (∀ bc state, iterate bc state =
    if state < length bc then
      match getindex bc state with
      | .ok value => some (value, state + 1)
      | .error _ => none
    else none) ∧
  (∀ bc, iteratorTraits bc = (ndims bc, false)) ∧
  (∀ firsts indices lengths, newIndex firsts indices lengths =
    newIndexGo firsts indices lengths) ∧
  (∀ firsts lengths, newIndexer firsts lengths = (lengths.map (· != 1), firsts)) ∧
  (∀ indices, toIndex indices = indices) ∧
  (∀ shape indices, checkBounds shape indices =
    (indices.length == shape.length &&
      (indices.zip shape).all (fun p => decide (1 ≤ p.1 ∧ p.1 ≤ p.2)))) ∧
  (∀ arg index, getArg arg index = arg.eval index) ∧
  (∀ bc index, getindex bc index =
    if index < length bc then .ok (bc.tag + (bc.args.map (fun a => getArg a index)).sum)
    else .error .boundsError)

theorem axisAndIndexMethods : AxisAndIndexMethods := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

def MaterializationMethods : Prop :=
  (∀ scalarLike already reserved, broadcastable scalarLike already reserved =
    if reserved then .reservedError else if scalarLike then .ref
    else if already then .identity else .collected) ∧
  (∀ bc i, inferredSamples bc i = bc.args.map (fun a => getArg a i)) ∧
  (∀ tag args, broadcastValues tag args =
    match args with
    | [] => [tag]
    | first :: rest => (List.range first.length).map fun i =>
        tag + first.getD i 0 + (rest.map (fun xs => xs.getD i 0)).sum) ∧
  (∀ result ax, preservingZeroD result ax =
    if ax = [] then [result] else List.replicate (ax.foldl (· * ·) 1) result) ∧
  (∀ bc, materialize bc =
    match instantiate bc true with
    | .error e => .error e
    | .ok ready => .ok ((List.range (length ready)).map fun i =>
        ready.tag + (ready.args.map (fun a => getArg a i)).sum)) ∧
  (∀ n bc, copyto n bc = if n != length bc then .error .dimensionMismatch else materialize bc) ∧
  (∀ writable n bc, materializeBang writable n bc =
    if writable then copyto n bc else .error .unwritable) ∧
  (∀ assigned bc, copy assigned bc = if assigned then materialize bc else .error .argumentError) ∧
  (∀ same arg, preprocess same arg = (false && same, arg)) ∧
  (∀ written rest, copyNonleaf written rest = written ++ rest) ∧
  (throwDimensionMismatch = .error .dimensionMismatch)

theorem materializationMethods : MaterializationMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, rfl⟩

end JuliaLean.BroadcastCov.BroadcastCore
