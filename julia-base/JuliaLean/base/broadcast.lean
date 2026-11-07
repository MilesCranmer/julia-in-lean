import JuliaLean.base.essentials
import JuliaLean.Core
import JuliaLean.base.iterators
import JuliaLean.base.int
import JuliaLean.base.boot
import JuliaLean.base.promotion
import JuliaLean.base.tuple
import JuliaLean.base.multidimensional
import JuliaLean.base.range
import JuliaLean.base.twiceprecision

/-!
# Model of `base/broadcast.jl`

Julia revision `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Julia dispatch is trusted. Function arguments represent extensible callees; mutable
arrays are threaded explicitly through writes. The numbered definitions follow
source order. Separate namespaces keep the different typed interfaces distinct.
-/

namespace JuliaLean.base.broadcast
open JuliaLean

namespace Style
inductive Rank where
  | any
  | fixed (n : Nat)
  deriving Repr, DecidableEq

inductive StyleKind where
  | unknown
  | tuple
  | array
  | defaultArray
  | arrayConflict
  | custom
  deriving Repr, DecidableEq

structure Style where
  kind : StyleKind
  family : String
  rank : Rank
  payload : Nat := 0
  deriving Repr, DecidableEq

def unknown : Style := { kind := .unknown, family := "Unknown", rank := .any }

def tupleStyle : Style := { kind := .tuple, family := "Style{Tuple}", rank := .any }

def arrayStyle (family : String) : Style := { kind := .array, family, rank := .any }

def defaultStyle (rank : Rank) : Style :=
  { kind := .defaultArray, family := "DefaultArrayStyle", rank }

def conflict : Style := { kind := .arrayConflict, family := "ArrayConflict", rank := .any }


def rebuildRank (style : Style) (rank : Rank) : Style := { style with rank }

inductive MethodArgument (α : Type) where
  | bottomType
  | value (value : α)
  deriving Repr, DecidableEq

structure MethodFailure (α : Type) where
  functionName : String
  arguments : List (MethodArgument α)
  deriving Repr, DecidableEq

inductive AssignedStyle where
  | assigned (style : Style)
  | nothing
  | unknown
  deriving Repr, DecidableEq


inductive StyleError where
  | inconsistent
  | conflicting
  | dispatch
  deriving Repr, DecidableEq

def isArrayStyle (style : Style) : Bool :=
  style.kind = .array || style.kind = .defaultArray || style.kind = .arrayConflict

def resultJoin (left right forward reverse : Style) : Except StyleError Style :=
  if forward.kind = .unknown then
    if reverse.kind = .unknown then
      if isArrayStyle left && isArrayStyle right then .ok conflict else .ok unknown
    else .ok reverse
  else if reverse.kind = .unknown then .ok forward
  else if forward.kind = reverse.kind then (if forward = reverse then .ok forward else .error .inconsistent)
  else .error .conflicting

end Style

namespace Lazy
open Style
inductive Error where
  | tupleNotCallable
  | typeError
  | argumentError
  | boundsError
  | dimensionMismatch
  deriving Repr, DecidableEq

structure Broadcasted (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

inductive Candidate (S : Type) where
  | style (value : S)
  | wrongType
  deriving Repr, DecidableEq

def requireStyle : Candidate S → Except Error S
  | .style style => .ok style
  | .wrongType => .error .typeError


structure BroadcastedType (ArgsType : Type) where
  argsType : ArgsType
  axesRank : Option Nat
  styleRank : Rank

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq

inductive IndexSet (Axis : Type) where
  | cartesian (axes : List Axis)
  | linear (axes : List Axis)
  | sole (axis : Axis)
  deriving Repr, DecidableEq

inductive ArgRank where | tuple | other (rank : Nat) deriving Repr, DecidableEq

def argRank : ArgRank → Nat | .tuple => 1 | .other rank => rank


abbrev I64 := JInt .i64


inductive IteratorEltype where | unknown deriving Repr, DecidableEq

end Lazy

namespace Flatten
abbrev Result (α : Type) := JuliaLean.base.tuple.R α

abbrev Cursor := JInt .i64

abbrev Selector (α : Type) := List α → Result α

inductive Tree (S X α : Type) where
  | leaf (value : α)
  | node (style : S) (f : List α → Result α) (args : List (Tree S X α)) (axes : X)

structure BroadcastNode (S X α : Type) where
  style : S
  f : List α → Result α
  args : List (Tree S X α)
  axes : X

def treeArgs : Tree S X α → List (Tree S X α)
  | .leaf _ => []
  | .node _ _ args _ => args

def isNode : Tree S X α → Bool
  | .leaf _ => false
  | .node .. => true


mutual
  def treeWeight : Tree S X α → Nat
    | .leaf _ => 1
    | .node _ _ args _ => argsWeight args + 1

  def argsWeight : List (Tree S X α) → Nat
    | [] => 0
    | head :: tail => treeWeight head + argsWeight tail
end

theorem treeWeight_pos (tree : Tree S X α) : 0 < treeWeight tree := by
  cases tree <;> simp only [treeWeight] <;> omega


end Flatten

namespace Shape
inductive Error where
  | dimensionMismatch
  | boundsError
  | inexactError
  | methodError
  | argumentError
  deriving Repr, DecidableEq, Inhabited

abbrev Result (α : Type) := Except Error α

structure Integer where
  typeName : String
  value : Int
  deriving Repr, DecidableEq

inductive AxisKind where
  | oneTo (typeName : String)
  | unitRange (typeName : String)
  | custom (typeName : String)
  deriving Repr, DecidableEq

structure Axis where
  kind : AxisKind
  first : Int
  last : Int
  length : Nat
  deriving Repr, DecidableEq

inductive Dim where
  | integer (value : Integer)
  | axis (value : Axis)
  deriving Repr, DecidableEq

def axisFirst (axis : Axis) : Int := axis.first

def axisLast (axis : Axis) : Int := axis.last

def dimLength : Dim → Nat
  | .integer value => if value.value < 0 then 0 else value.value.toNat
  | .axis axis => axis.length

def compatible (a b : Dim) : Bool := a = b || dimLength b = 1

def axisType (a b : Axis) : Axis :=
  if a.kind = b.kind then a
  else match a.kind, b.kind with
    | .oneTo _, .oneTo _ => { a with kind := .oneTo "Int" }
    | _, _ => { a with kind := .unitRange "Int" }

def bcs1 : Dim → Dim → Result Dim
  | .integer a, .integer b =>
      if a.value = 1 then .ok (.integer b)
      else if b.value = 1 then .ok (.integer a)
      else if a.value = b.value then .ok (.integer a)
      else .error .dimensionMismatch
  | .integer a, .axis b =>
      if a.value = 1 then .ok (.axis b)
      else if axisFirst b = 1 && axisLast b = a.value then .ok (.axis b)
      else .error .dimensionMismatch
  | .axis a, .integer b =>
      if b.value = 1 then .ok (.axis a)
      else if axisFirst a = 1 && axisLast a = b.value then .ok (.axis a)
      else .error .dimensionMismatch
  | .axis a, .axis b =>
      if compatible (.axis b) (.axis a) then .ok (.axis (axisType b a))
      else if compatible (.axis a) (.axis b) then .ok (.axis (axisType a b))
      else .error .dimensionMismatch


def combineAxes (axes : A → Result (List Dim))
    (combine : List Dim → List Dim → Result (List Dim)) : A → List A → Result (List Dim)
  | first, [] => axes first
  | first, next :: rest => do
      let firstAxes ← axes first
      let tailAxes ← combineAxes axes combine next rest
      combine firstAxes tailAxes


end Shape

namespace Index
abbrev Error := JuliaLean.base.tuple.TupleError
abbrev Result (α : Type) := JuliaLean.base.tuple.R α

structure Axis where
  values : List Int
  first : Int
  deriving Repr, DecidableEq

def axisFirst (axis : Axis) : Int := axis.first

inductive Index where
  | scalar (value : Int)
  | cartesian (values : List Int)
  deriving Repr, DecidableEq




def convertInt (value : Int) : Jl JInt64 := JInt.convert (IntTy.i64.name) .i64 value


structure Extruded (A : Type) where
  x : A
  keeps : List Bool
  defaults : List Int
  deriving Repr, DecidableEq

structure EvalBroadcasted (A V : Type) where
  f : List V → V
  args : List A



end Index

namespace Material
inductive Error where
  | argument
  | dimensionMismatch
  | bounds
  | typeError
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure RefValue (α : Type) where value : α deriving Repr, DecidableEq

structure TypeRef (T : Type) where value : T deriving Repr, DecidableEq

structure SampledBroadcast (A V : Type) where
  f : List V → V
  args : List A

def sampleArgs {A I V : Type} (sample : A → I → Result V) : List A → I → Result (List V)
  | [], _ => .ok []
  | head :: tail, index => do pure ((← sample head index) :: (← sampleArgs sample tail index))

structure TypedValue (T V : Type) where
  value : V
  hasType : Bool
  deriving Repr, DecidableEq

inductive JType where
  | bottom
  | known (name : String)
  | union (members : List String)
  | tuple (members : List JType)
  deriving Repr

def tupleOrBottom : List JType → JType := fun types =>
  if types.any (fun t => match t with | .bottom => true | _ => false)
  then .bottom else .tuple types

def eltypes : List JType → JType
  | [] => .tuple []
  | head :: tail =>
      match eltypes tail with
      | .bottom => .bottom
      | .tuple rest => tupleOrBottom (head :: rest)
      | _ => .bottom

def zipTuples {A V : Type} (f : List A → V) (tuples : List (List A)) : List V :=
  match tuples with
  | [] => []
  | first :: _ => (List.range first.length).filterMap fun i => (tuples.mapM fun values => values[i]?).map f

structure ZeroD (α : Type) where
  value : α
  deriving Repr, DecidableEq

abbrev MaterializedExpr := Lazy.Broadcasted

inductive Inferred where | bottom | concrete | abstract deriving Repr, DecidableEq

abbrev Expr := Lazy.Broadcasted

def preprocessArgs {m : Type → Type} [Monad m] {D A B : Type}
    (preprocess : D → A → m B) (dest : D) : List A → m (List B)
  | [] => pure []
  | head :: tail => do pure ((← preprocess dest head) :: (← preprocessArgs preprocess dest tail))

def copyLoop {m : Type → Type} [Monad m] {D B I V : Type}
    (getindex : B → I → m V) (setindex : D → I → V → m Unit)
    (dest : D) (bc : B) : List I → m D
  | [] => pure dest
  | i :: rest => do
    let value ← getindex bc i
    setindex dest i value
    copyLoop getindex setindex dest bc rest

/--
The for-loop of restart_copyto_nonleaf!: each iterator step, source read and target write uses the shared effect; only normal exhaustion returns.
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
def copyPrefix {E H D I V Taken TakenState : Type}
    (iterateTaken : Taken → Option TakenState → JuliaLean.base.iterators.Exec E H (Option (I × TakenState)))
    (getindex : D → I → JuliaLean.base.iterators.Exec E H V)
    (setindex : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (source target : D) (taken : Taken) (state : Option TakenState) :
    JuliaLean.base.iterators.Exec E H Unit :=
  fun heap => match iterateTaken taken state heap with
  | none => none
  | some (.error error, heap) => some (.error error, heap)
  | some (.ok none, heap) => some (.ok (), heap)
  | some (.ok (some (index, next)), heap) =>
      match getindex source index heap with
      | none => none
      | some (.error error, heap) => some (.error error, heap)
      | some (.ok value, heap) =>
          match setindex target index value heap with
          | none => none
          | some (.error error, heap) => some (.error error, heap)
          | some (.ok (), heap) =>
              copyPrefix iterateTaken getindex setindex source target taken (some next) heap
partial_fixpoint

end Material

namespace Bits
abbrev I64 := JInt .i64
private def int64 (x : Int) : I64 := JInt.lit .i64 x

/-- The destination axes are the nonnegative `OneTo{Int}` axes of a `BitArray`. -/
structure Axis64 where
  stop : I64
  nonnegative : 0 ≤ stop.val

private def shift63 (j : I64) : UInt64 :=
  UInt64.ofNat ((BitVec.ofInt 64 j.val &&& BitVec.ofNat 64 63).toNat)

def readWord {H ε B I V : Type}
    (getValue : B → I64 → I → StateT H (Except ε) V)
    (convertBool : V → StateT H (Except ε) Bool) (bc : B) (outer : I) :
    Nat → I64 → I64 → UInt64 → StateT H (Except ε) UInt64
  | 0, _, _, word => pure word
  | count + 1, i, j, word => do
    let i := i + int64 1
    let bit ← convertBool (← getValue bc i outer)
    let word := word ||| ((if bit then (1 : UInt64) else 0) <<< shift63 j)
    readWord getValue convertBool bc outer count i (j + int64 1) word
private theorem sub64_val (last : Axis64) : (last.stop - int64 64).val = last.stop.val - 64 := by
  change wrapInt .i64 (last.stop.val - 64) = _
  apply wrapInt_of_inRange
  have hb := last.stop.property
  have hn := last.nonnegative
  simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at hb ⊢
  omega

private theorem add64_val (i : I64) (last : Axis64)
    (h : i.val ≤ (last.stop - int64 64).val) : (i + int64 64).val = i.val + 64 := by
  change wrapInt .i64 (i.val + 64) = _
  apply wrapInt_of_inRange
  have hi := i.property
  have hl := last.stop.property
  rw [sub64_val] at h
  simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at hi hl ⊢
  omega

def fullWordLoop {H ε B I C V : Type}
    (getValue : B → I64 → I → StateT H (Except ε) V)
    (convertBool : V → StateT H (Except ε) Bool)
    (setChunk : C → I64 → UInt64 → StateT H (Except ε) Unit)
    (bc : B) (outer : I) (chunks : C) (last : Axis64) (i indc : I64) :
    StateT H (Except ε) (I64 × I64) := do
  if h : i.val ≤ (last.stop - int64 64).val then
    let word ← readWord getValue convertBool bc outer 64 i (int64 0) 0
    let indc := indc + int64 1
    setChunk chunks indc word
    fullWordLoop getValue convertBool setChunk bc outer chunks last (i + int64 64) indc
  else pure (i, indc)
termination_by (last.stop.val - i.val).toNat
decreasing_by
  have hstep := add64_val i last h
  have hg := h
  rw [sub64_val] at hg
  simp only [hstep]
  omega
inductive Nothing where | nothing

structure BitMasked (P M : Type) where
  parent : P
  mask : M

def forChunkIndices {H ε : Type} (body : I64 → StateT H (Except ε) Unit) :
    Nat → I64 → StateT H (Except ε) Unit
  | 0, _ => pure ()
  | count + 1, i => do
    body i
    forChunkIndices body count (i + int64 1)
end Bits

namespace Range
structure RangeView (T Ref Step Len Offset : Type) where
  first : T
  last : T
  step : Step
  ref : Ref
  start : T
  stop : T
  len : Len
  offset : Offset

end Range

namespace Syntax
inductive Value (Literal : Type) where
  | symbol (name : String)
  | expr (head : String) (args : List (Value Literal))
  | other (value : Literal)
  deriving Repr

def undot : Value L → Value L
  | .expr ".=" args => .expr "=" args
  | .expr "block" args => .expr "block" (args.map undot)
  | value => value

def dottable (isoperator : String → Bool) : Value L → Bool
  | .symbol name => ((!isoperator name || name.front ≠ '.' || name = "..") && name ≠ ":")
  | .expr head _ => head ≠ "$"
  | .other _ => false

def dotComparisonArg (isoperator : String → Bool) (index : Nat) : Value L → Value L
  | .symbol name =>
      if index % 2 = 1 && dottable isoperator (Value.symbol (Literal := L) name) && isoperator name
      then .symbol ("." ++ name) else .symbol name
  | value => value

inductive SyntaxError where | boundsError deriving Repr, DecidableEq
abbrev SyntaxResult (α : Type) := Except SyntaxError α

def syntaxArg (args : List (Value L)) (i : Nat) : SyntaxResult (Value L) :=
  match args[i]? with
  | some value => .ok value
  | none => .error .boundsError

def finishDot (head : String) (dotted : List (Value L)) : SyntaxResult (Value L) :=
  if head = "<:" then .ok (.expr "call" (.symbol ".<:" :: dotted))
  else if head = ">:" then .ok (.expr "call" (.symbol ".>:" :: dotted))
  else if head.isEmpty then .error .boundsError
  else if (head.endsWith "=" && !head.startsWith ".") || head = "&&" || head = "||" then
    .ok (.expr ("." ++ head) dotted)
  else .ok (.expr head dotted)

def dotSyntax (isoperator : String → Bool) : Value L → SyntaxResult (Value L)
  | .symbol name => .ok (.symbol name)
  | .other description => .ok (.other description)
  | .expr head args => do
    let dotted ← args.mapM (dotSyntax isoperator)
    if head = "call" then
      let originalFn ← syntaxArg args 0
      if dottable isoperator originalFn then
        return .expr "." [(← syntaxArg dotted 0), .expr "tuple" (dotted.drop 1)]
      else return .expr "call" dotted
    else if head = "comparison" then
      return .expr "comparison" ((dotted.zipIdx).map fun pair => dotComparisonArg isoperator pair.2 pair.1)
    else if head = "$" then syntaxArg args 0
    else if head = "let" || head = "for" then
      return .expr head [undot (← syntaxArg dotted 0), (← syntaxArg dotted 1)]
    else if head = "generator" || head = "filter" then
      return .expr head ((← syntaxArg dotted 0) :: (dotted.drop 1).map undot)
    else if head = "=" || head = "function" || head = "macro" then
      let first ← syntaxArg args 0
      match first with
      | .expr "call" _ => return .expr head [first, (← syntaxArg dotted 1)]
      | _ => finishDot head dotted
    else finishDot head dotted
termination_by value => sizeOf value

abbrev Broadcasted (S F A X : Type) :=
  Lazy.Broadcasted S F (List A) (Option X)

structure BroadcastFunction (F : Type) where
  f : F
  deriving Repr, DecidableEq

inductive ShowError where | failed deriving Repr, DecidableEq

abbrev ShowResult (α : Type) := Except ShowError α

end Syntax

namespace Style
/--
Julia source: base/broadcast.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{Union{}}) = Unknown()  # ambiguity resolution
```
-/
def m37 : Style := unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{Union{}}, slurp...) = throw(MethodError(BroadcastStyle, (Union{}, slurp...)))
```
-/
def m38 {α : Type} (slurp : List α) : Except (MethodFailure α) Style :=
  .error ⟨"BroadcastStyle", .bottomType :: slurp.map .value⟩
end Style

namespace Style
/--
Julia source: base/broadcast.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{<:Tuple}) = Style{Tuple}()
```
-/
def m49 : Style := tupleStyle
end Style

namespace Style
/--
Julia source: base/broadcast.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ArrayStyle{A}(::Val) where A = ArrayStyle{A}()
```
-/
def m87 {α : Type} (family : String) (_val : α) : Style := arrayStyle family
end Style

namespace Style
/--
Julia source: base/broadcast.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DefaultArrayStyle(::Val{N}) where N = DefaultArrayStyle{N}()
```
-/
def m98 (n : Rank) : Style := defaultStyle n
end Style

namespace Style
/--
Julia source: base/broadcast.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DefaultArrayStyle{M}(::Val{N}) where {N,M} = DefaultArrayStyle{N}()
```
-/
def m99 (_oldRank newRank : Rank) : Style := defaultStyle newRank
end Style

namespace Style
/--
Julia source: base/broadcast.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{<:AbstractArray{T,N}}) where {T,N} = DefaultArrayStyle{N}()
```
-/
def m102 (n : Rank) : Style := defaultStyle n
end Style

namespace Style
/--
Julia source: base/broadcast.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
```
-/
def m103 {μ : Type → Type} [Monad μ] {α : Type} (ndims : α → μ Rank) (T : α) : μ Style := do
  pure (defaultStyle (← ndims T))
end Style

namespace Style
/--
Julia source: base/broadcast.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ArrayConflict(::Val) = ArrayConflict()
```
-/
def m111 {α : Type} (_val : α) : Style := conflict
end Style

namespace Style
/--
Julia source: base/broadcast.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::S, ::S) where S<:BroadcastStyle = S() # homogeneous types preserved
```
-/
def m128 {S : Type} (_left _right : S) (construct : Unit → S) : S := construct ()
end Style

namespace Style
/--
Julia source: base/broadcast.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::BroadcastStyle, ::BroadcastStyle) = Unknown()
```
-/
def m130 (_left _right : Style) : Style := unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Unknown, ::Unknown) = Unknown()
```
-/
def m132 (_left _right : Unit) : Style := unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::S, ::Unknown) where S<:BroadcastStyle = S()
```
-/
def m133 {S U : Type} (_left : S) (_right : U) (construct : Unit → S) : S := construct ()
end Style

namespace Style
/--
Julia source: base/broadcast.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(a::AbstractArrayStyle{0}, b::Style{Tuple}) = b
```
-/
def m135 (_arrayStyle : Style) (tuple : Style) : Style := tuple
end Style

namespace Style
/--
Julia source: base/broadcast.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(a::AbstractArrayStyle, ::Style{Tuple})    = a
```
-/
def m136 (array : Style) (_tuple : Style) : Style := array
end Style

namespace Style
/--
Julia source: base/broadcast.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::A, ::A) where A<:ArrayStyle             = A()
```
-/
def m137 {A : Type} (_left _right : A) (construct : Unit → A) : A := construct ()
end Style

namespace Style
/--
Julia source: base/broadcast.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::ArrayStyle, ::ArrayStyle)               = Unknown()
```
-/
def m138 {A B : Type} (_left : A) (_right : B) (_different : A ≠ B) : Style := unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::A, ::A) where A<:AbstractArrayStyle     = A()
```
-/
def m139 {A : Type} (_left _right : A) (construct : Unit → A) : A := construct ()
end Style

namespace Style
/--
Julia source: base/broadcast.jl:140-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BroadcastStyle(a::A, b::B) where {A<:AbstractArrayStyle{M},B<:AbstractArrayStyle{N}} where {M,N}
    if Base.typename(A) === Base.typename(B)
        return A(Val(max(M, N)))
    end
    return Unknown()
end
```
-/
def m140 {ε : Type} (sameTypename : S → S → Bool)
    (maximum : Rank → Rank → Except ε Rank) (constructRank : S → Rank → Style)
    (a b : S) (rankA rankB : Rank) : Except ε Style := do
  if sameTypename a b then
    let rank ← maximum rankA rankB
    pure (constructRank a rank)
  else pure unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(a::AbstractArrayStyle{Any}, ::DefaultArrayStyle) = a
```
-/
def m147 (a : Style) (_default : Style) : Style := a
end Style

namespace Style
/--
Julia source: base/broadcast.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(a::AbstractArrayStyle{N}, ::DefaultArrayStyle{N}) where N = a
```
-/
def m148 (a : Style) (_default : Style) : Style := a
end Style

namespace Style
/--
Julia source: base/broadcast.jl:149-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(a::AbstractArrayStyle{M}, ::DefaultArrayStyle{N}) where {M,N} =
    typeof(a)(Val(max(M, N)))
```
-/
def m149 {ε : Type} (maximum : Rank → Rank → Except ε Rank)
    (constructRank : S → Rank → R) (a : S) (rankA rankDefault : Rank) : Except ε R := do
  let rank ← maximum rankA rankDefault
  pure (constructRank a rank)
end Style

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Broadcasted(style::Union{Nothing,BroadcastStyle}, f::Tuple, args::Tuple) = error() # disambiguation: tuple is not callable
```
-/
def m175 {α β : Type} (_tupleFunction : α) (_args : β) : Except Error Unit :=
  .error .tupleNotCallable
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:176-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Broadcasted(style::Union{Nothing,BroadcastStyle}, f::F, args::Tuple, axes=nothing) where {F}
        # using Core.Typeof rather than F preserves inferrability when f is a type
        return new{typeof(style), typeof(axes), Core.Typeof(f), typeof(args)}(style, f, args, axes)
    end
```
-/
def m176 (style : S) (f : F) (args : A) (axes : X) : Broadcasted S F A X :=
  ⟨style, f, args, axes⟩
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Broadcasted(f::F, args::Tuple, axes=nothing) where {F}
        Broadcasted(combine_styles(args...)::BroadcastStyle, f, args, axes)
    end
```
-/
def m181 {F A X : Type} (combineStyles : A → Candidate Style) (f : F) (args : A) (axes : X) :
    Except Error (Broadcasted Style F A X) :=
  match combineStyles args with
  | .style style => .ok (m176 style f args axes)
  | .wrongType => .error .typeError
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:185-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Broadcasted{Style}(f::F, args, axes=nothing) where {Style, F}
        return new{Style, typeof(axes), Core.Typeof(f), typeof(args)}(Style()::Style, f, args, axes)
    end
```
-/
def m185 {S F A X : Type} (constructStyle : Candidate S) (f : F) (args : A) (axes : X) :
    Except Error (Broadcasted S F A X) := do
  let style ← requireStyle constructStyle
  .ok ⟨style, f, args, axes⟩
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:189-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Broadcasted{Style,Axes,F,Args}(f, args, axes) where {Style,Axes,F,Args}
        return new{Style, Axes, F, Args}(Style()::Style, f, args, axes)
    end
```
-/
def m189 {E S F A X FIn AIn XIn : Type} (constructStyle : Except E S)
    (convertFunction : FIn → Except E F) (convertArguments : AIn → Except E A)
    (convertAxes : XIn → Except E X) (function : FIn) (arguments : AIn) (axisValue : XIn) :
    Except E (Broadcasted S F A X) := do
  let style ← constructStyle
  let f ← convertFunction function
  let args ← convertArguments arguments
  let axes ← convertAxes axisValue
  .ok ⟨style, f, args, axes⟩
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
```
-/
def m196 {A B R : Type} (broadcasted : (Bool → Bool → Bool) → A → B → R)
    (a : A) (b : B) : R := broadcasted (fun x y => x && y) a b
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:199-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function broadcasted(::AndAnd, a, bc::Broadcasted)
    bcf = flatten(bc)
    # Vararg type signature to specialize on args count. This is necessary for performance
    # and inexpensive because this should only ever get called with 1+N = length(bc.args)
    broadcasted(((a, args::Vararg{Any, N}) where {N}) -> a && bcf.f(args...), a, bcf.args...)
end
```
-/
def m199 {S X A R : Type}
    (flatten : Flatten.BroadcastNode S X Bool → Flatten.BroadcastNode S X Bool)
    (broadcasted : (Bool → List Bool → Flatten.Result Bool) →
      A → List (Flatten.Tree S X Bool) → R)
    (a : A) (bc : Flatten.BroadcastNode S X Bool) : R :=
  let bcf := flatten bc
  broadcasted (fun first rest => if first then bcf.f rest else .ok false) a bcf.args
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
```
-/
def m207 {A B R : Type} (broadcasted : (Bool → Bool → Bool) → A → B → R)
    (a : A) (b : B) : R := broadcasted (fun x y => x || y) a b
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:208-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function broadcasted(::OrOr, a, bc::Broadcasted)
    bcf = flatten(bc)
    # Vararg type signature to specialize on args count. This is necessary for performance
    # and inexpensive because this should only ever get called with 1+N = length(bc.args)
    broadcasted(((a, args::Vararg{Any, N}) where {N}) -> a || bcf.f(args...), a, bcf.args...)
end
```
-/
def m208 {S X A R : Type}
    (flatten : Flatten.BroadcastNode S X Bool → Flatten.BroadcastNode S X Bool)
    (broadcasted : (Bool → List Bool → Flatten.Result Bool) →
      A → List (Flatten.Tree S X Bool) → R)
    (a : A) (bc : Flatten.BroadcastNode S X Bool) : R :=
  let bcf := flatten bc
  broadcasted (fun first rest => if first then .ok true else bcf.f rest) a bcf.args
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.convert(::Type{Broadcasted{NewStyle}}, bc::Broadcasted{<:Any,Axes,F,Args}) where {NewStyle,Axes,F,Args} =
    Broadcasted{NewStyle,Axes,F,Args}(bc.f, bc.args, bc.axes)::Broadcasted{NewStyle,Axes,F,Args}
```
-/
def m215 (constructStyle : Unit → S2) (bc : Broadcasted S1 F A X) :
    Broadcasted S2 F A X :=
  ⟨constructStyle (), bc.f, bc.args, bc.axes⟩
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:218-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, bc::Broadcasted{Style}) where {Style}
    print(io, Broadcasted)
    # Only show the style parameter if we have a set of axes — representing an instantiated
    # "outermost" Broadcasted. The styles of nested Broadcasteds represent an intermediate
    # computation that is not relevant for dispatch, confusing, and just extra line noise.
    bc.axes isa Tuple && print(io, "{", Style, "}")
    print(io, "(", bc.f, ", ", bc.args, ")")
    nothing
end
```
-/
def m218 (printHead : O → Except Error O)
    (printStyle : O → StyleParam → Except Error O)
    (printBody : O → F → A → Except Error O) (styleType : Unit → StyleParam)
    (isTupleAxes : X → Bool) (io : O) (bc : Broadcasted S F A X) :
    Except Error (O × Unit) := do
  let io ← printHead io
  let io ← if isTupleAxes bc.axes then printStyle io (styleType ()) else .ok io
  let io ← printBody io bc.f bc.args
  .ok (io, ())
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(bc::Broadcasted, ::Type{T}) where {T} = similar(bc, T, axes(bc))
```
-/
def m229 {m : Type → Type} [Monad m] {S F A X T D R : Type}
    (axes : Broadcasted S F A X → m D)
    (similar : Broadcasted S F A X → T → D → m R)
    (bc : Broadcasted S F A X) (Tval : T) : m R := do
  similar bc Tval (← axes bc)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:230-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(::Broadcasted{DefaultArrayStyle{N}}, ::Type{ElType}, dims) where {N,ElType} =
    similar(Array{ElType, length(dims)}, dims)
```
-/
def m230 {T D R : Type} (similarArray : T → Nat → List D → R) (elementType : T) (dims : List D) : R :=
  similarArray elementType dims.length dims
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:232-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(::Broadcasted{DefaultArrayStyle{N}}, ::Type{Bool}, dims) where N =
    similar(BitArray, dims)
```
-/
def m232 {D R : Type} (similarBitArray : List D → R) (dims : List D) : R := similarBitArray dims
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:235-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(::Broadcasted{ArrayConflict}, ::Type{ElType}, dims) where ElType =
    similar(Array{ElType, length(dims)}, dims)
```
-/
def m235 {T D R : Type} (similarArray : T → Nat → List D → R) (elementType : T) (dims : List D) : R :=
  similarArray elementType dims.length dims
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:237-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.similar(::Broadcasted{ArrayConflict}, ::Type{Bool}, dims) =
    similar(BitArray, dims)
```
-/
def m237 {D R : Type} (similarBitArray : List D → R) (dims : List D) : R := similarBitArray dims
end Lazy


namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes(::Broadcasted, axes::Tuple) = axes
```
-/
def m241 {Axis : Type} (axes : List Axis) : List Axis := axes
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _axes(bc::Broadcasted, ::Nothing)  = combine_axes(bc.args...)
```
-/
def m242 {m : Type → Type} {A Axis : Type}
    (combineAxes : A → m (List Axis)) (args : A) : m (List Axis) := combineAxes args
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes(bc::Broadcasted{<:AbstractArrayStyle{0}}, ::Nothing) = ()
```
-/
def m243 {m : Type → Type} [Monad m] {A Axis : Type} (_args : A) : m (List Axis) :=
  pure []
end Lazy
namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.axes(bc::Broadcasted) = _axes(bc, bc.axes)
```
-/
def m240 {m : Type → Type} [Monad m] {S F A Axis : Type}
    (unsetAxes : A → m (List Axis))
    (bc : Broadcasted S F A (Option (List Axis))) : m (List Axis) :=
  match bc.axes with
  | some axes => pure (m241 axes)
  | none => unsetAxes bc.args
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:245-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.axes(bc::Broadcasted{<:Any, <:NTuple{N}}, d::Integer) where N =
    d <= N ? axes(bc)[d] : OneTo(1)
```
-/
def m245 (axes : B → Except Error (List Axis))
    (getindex : List Axis → Int → Except Error Axis) (oneToOne : Axis)
    (bc : B) (rank d : Int) : Except Error Axis :=
  if d ≤ rank then do getindex (← axes bc) d else .ok oneToOne
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{<:Broadcasted{Style}}) where {Style} = Style()
```
-/
def m248 {S : Type} (constructStyle : Unit → S) : S := constructStyle ()
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:249-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BroadcastStyle(::Type{<:Broadcasted{S}}) where {S<:Union{Nothing,Unknown}} =
    throw(ArgumentError("Broadcasted{Unknown} wrappers do not have a style assigned"))
```
-/
def m249 (_style : AssignedStyle) : Except Error Style := .error .argumentError
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argtype(::Type{BC}) where {BC<:Broadcasted} = fieldtype(BC, :args)
```
-/
def m252 (bcType : BroadcastedType A) : A := bcType.argsType
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argtype(bc::Broadcasted) = argtype(typeof(bc))
```
-/
def m253 {S F A X : Type} (typeof : Broadcasted S F A X → BroadcastedType A)
    (bc : Broadcasted S F A X) : A := m252 (typeof bc)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.eachindex(bc::Broadcasted) = eachindex(IndexStyle(bc), bc)
```
-/
def m255 {B I : Type} (indexStyle : B → IndexStyle) (eachindex : IndexStyle → B → I) (bc : B) : I :=
  eachindex (indexStyle bc) bc
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.eachindex(s::IndexStyle, bc::Broadcasted) = _eachindex(s, axes(bc))
```
-/
def m256 {B Axis I : Type} (axes : B → List Axis)
    (route : IndexStyle → List Axis → I) (style : IndexStyle) (bc : B) : I :=
  route style (axes bc)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eachindex(::IndexCartesian, t::Tuple) = CartesianIndices(t)
```
-/
def m257 {Axis : Type} (axes : List Axis) : IndexSet Axis := .cartesian axes
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eachindex(s::IndexLinear, t::Tuple) = eachindex(s, LinearIndices(t))
```
-/
def m258 (linearIndices : T → Except Error L)
    (eachindex : IndexStyle → L → Except Error I) (style : IndexStyle) (axes : T) :
    Except Error I := do
  eachindex style (← linearIndices axes)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_eachindex(::IndexLinear, t::Tuple{Any}) = t[1]
```
-/
def m259 {Axis : Type} (axis : Axis) : Axis := axis
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IndexStyle(bc::Broadcasted) = IndexStyle(typeof(bc))
```
-/
def m261 {B T : Type} (typeof : B → T) (indexStyle : T → IndexStyle) (bc : B) : IndexStyle :=
  indexStyle (typeof bc)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IndexStyle(::Type{<:Broadcasted{<:Any,<:Tuple{Any}}}) = IndexLinear()
```
-/
def m262 : IndexStyle := .linear
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IndexStyle(::Type{<:Broadcasted{<:Any}}) = IndexCartesian()
```
-/
def m263 : IndexStyle := .cartesian
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.LinearIndices(bc::Broadcasted{<:Any,<:Tuple{Any}}) = LinearIndices(axes(bc))::LinearIndices{1}
```
-/
def m265 {Axis : Type} (axes : List Axis) : IndexSet Axis := .linear axes
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.ndims(bc::Broadcasted) = ndims(typeof(bc))
```
-/
def m267 {B T : Type} (typeof : B → T) (ndims : T → Nat) (bc : B) : Nat := ndims (typeof bc)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:268-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.ndims(::Type{<:Broadcasted{<:Any,<:NTuple{N,Any}}}) where {N} = N
```
-/
def m268 (rank : Nat) : Nat := rank
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maxndims(::Type{Tuple{}}) = 0
```
-/
def m273 : Nat := 0
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maxndims(::Type{Tuple{T}}) where {T} = T <: Tuple ? 1 : Int(ndims(T))::Int
```
-/
def m274 (head : ArgRank) : Nat := argRank head
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:275-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _maxndims(Args::Type{<:Tuple{T,Vararg}}) where {T}
    m = T <: Tuple ? 1 : Int(ndims(T))::Int
    n = _maxndims(Base.tuple_type_tail(Args))
    max(m, n)
end
```
-/
def m275 (head : ArgRank) (tail : List ArgRank) : Nat :=
  let n := match tail with
    | [] => m273
    | [next] => m274 next
    | next :: after :: rest => m275 next (after :: rest)
  max (argRank head) n
termination_by tail.length

-- Arity dispatch selects the actual empty, singleton, or recursive Julia method.
def maxNdim : List ArgRank → Nat
  | [] => m273
  | [head] => m274 head
  | head :: next :: rest => m275 head (next :: rest)
end Lazy
namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.ndims(BC::Type{<:Broadcasted{<:Any,Nothing}}) = _maxndims(argtype(BC))
```
-/
def m269 (bcType : BroadcastedType (List ArgRank)) : Nat :=
  maxNdim (m252 bcType)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:270-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.ndims(BC::Type{<:Broadcasted{<:AbstractArrayStyle{N},Nothing}}) where {N}
    N isa Int ? N : _maxndims(argtype(BC))
end
```
-/
def m270 (bcType : BroadcastedType (List ArgRank)) : Nat :=
  match bcType.styleRank with | .fixed n => n | .any => maxNdim (m252 bcType)
end Lazy


namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.size(bc::Broadcasted) = map(length, axes(bc))
```
-/
def m281 {E B Axis : Type} (length : Axis → I64) (axes : B → Except E (List Axis)) (bc : B) :
    Except E (List I64) := do
  pure ((← axes bc).map length)
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.length(bc::Broadcasted) = prod(size(bc))
```
-/
def m282 {E B : Type} (prod : List I64 → Except E I64) (size : B → Except E (List I64))
    (bc : B) : Except E I64 := do
  prod (← size bc)
end Lazy


namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:288-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function Base.iterate(bc::Broadcasted, s)
    y = iterate(s...)
    y === nothing && return nothing
    i, newstate = y
    return (bc[i], (s[1], newstate))
end
```
-/
def m288 {E I V State : Type}
    (iterate : List I → Option State → Except E (Option (I × State)))
    (getindex : I → Except E V) (iter : List I) (state : Option State) :
    Except E (Option (V × (List I × State))) := do
  match ← iterate iter state with
  | none => pure none
  | some (index, nextState) => pure (some ((← getindex index), (iter, nextState)))
end Lazy
namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:284-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(bc::Broadcasted)
    iter = eachindex(bc)
    iterate(bc, (iter,))
end
```
-/
def m284 {E B I V State : Type} (eachindex : B → Except E (List I))
    (iterate : List I → Option State → Except E (Option (I × State)))
    (getindex : B → I → Except E V) (bc : B) : Except E (Option (V × (List I × State))) := do
  let iter ← eachindex bc
  m288 iterate (getindex bc) iter none
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
```
-/
def m295 (ndims : T → Except Error Nat) (hasShape : Nat → R) (broadcastedType : T) :
    Except Error R := do
  .ok (hasShape (← ndims broadcastedType))
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IteratorEltype(::Type{<:Broadcasted}) = Base.EltypeUnknown()
```
-/
def m296 : IteratorEltype := .unknown
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
instantiate(x) = x
```
-/
def m299 {T : Type} (x : T) : T := x
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:310-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function instantiate(bc::Broadcasted)
    if bc.axes isa Nothing # Not done via dispatch to make it easier to extend instantiate(::Broadcasted{Style})
        axes = combine_axes(bc.args...)
    else
        axes = bc.axes
        check_broadcast_axes(axes, bc.args...)
    end
    return Broadcasted(bc.style, bc.f, bc.args, axes)
end
```
-/
def m310 {m : Type → Type} [Monad m] {S F A Axis : Type} (combineAxes : A → m (List Axis))
    (checkAxes : List Axis → A → m Unit)
    (bc : Broadcasted S F A (Option (List Axis))) : m (Broadcasted S F A (Option (List Axis))) := do
  let axes ← match bc.axes with
    | none => combineAxes bc.args
    | some axes => do checkAxes axes bc.args; pure axes
  pure (m176 bc.style bc.f bc.args (some axes))
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
instantiate(bc::Broadcasted{<:AbstractArrayStyle{0}}) = bc
```
-/
def m319 {B : Type} (bc : B) : B := bc
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
instantiate(bc::Broadcasted{Style{Tuple}, Nothing}) = bc
```
-/
def m321 {B : Type} (bc : B) : B := bc
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:322-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function instantiate(bc::Broadcasted{Style{Tuple}})
    check_broadcast_axes(bc.axes, bc.args...)
    return bc
end
```
-/
def m322 {m : Type → Type} [Monad m] {S F A Axis : Type} (checkAxes : List Axis → A → m Unit)
    (bc : Broadcasted S F A (List Axis)) : m (Broadcasted S F A (List Axis)) := do
  checkAxes bc.axes bc.args
  pure bc
end Lazy


namespace Flatten
/--
Julia source: base/broadcast.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isflat(args::NestedTuple) = false
```
-/
def m365 {S X α : Type} (_head : BroadcastNode S X α)
    (_tail : List (Tree S X α)) : Bool := false

/--
Julia source: base/broadcast.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isflat(args::Tuple{}) = true
```
-/
def m367 : Bool := true

mutual
  def isFlatArgs : List (Tree S X α) → Bool
    | [] => m367
    | .leaf value :: tail => m366 value tail
    | .node style f args axes :: tail => m365 ⟨style, f, args, axes⟩ tail
  termination_by args => (argsWeight args, 0)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [argsWeight, treeWeight]
    all_goals omega

  /--
Julia source: base/broadcast.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isflat(args::Tuple) = _isflat(tail(args))
```
-/
  def m366 {S X α : Type} (_head : α) (tail : List (Tree S X α)) : Bool :=
    isFlatArgs tail
  termination_by (argsWeight tail, 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/--
Julia source: base/broadcast.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isflat(bc::Broadcasted) = _isflat(bc.args)
```
-/
def m364 (bc : BroadcastNode S X α) : Bool := isFlatArgs bc.args
end Flatten

namespace Flatten
/--
Julia source: base/broadcast.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_nested_args(::Tuple{}) = ()
```
-/
def m370 {S X α : Type} : List (Tree S X α) := []

/--
Julia source: base/broadcast.jl:373-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_nested(a) = (a,)
```
-/
def m373 (value : α) : List (Tree S X α) := [.leaf value]

mutual
  def catNested : Tree S X α → List (Tree S X α)
    | .leaf value => m373 value
    | .node style f args axes => m369 ⟨style, f, args, axes⟩
  termination_by tree => (treeWeight tree, 2)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [treeWeight]
    all_goals omega

  def catNestedArgs : List (Tree S X α) → List (Tree S X α)
    | [] => m370
    | [head] => m371 head
    | head :: next :: tail => m372 head (next :: tail)
  termination_by args => (argsWeight args, 4)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [argsWeight]
    all_goals omega

  /--
Julia source: base/broadcast.jl:369-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_nested(bc::Broadcasted) = cat_nested_args(bc.args)
```
-/
  def m369 (bc : BroadcastNode S X α) : List (Tree S X α) := catNestedArgs bc.args
  termination_by (argsWeight bc.args + 1, 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  /--
Julia source: base/broadcast.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_nested_args(t::Tuple{Any}) = cat_nested(t[1])
```
-/
  def m371 (head : Tree S X α) : List (Tree S X α) := catNested head
  termination_by (treeWeight head, 3)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  /--
Julia source: base/broadcast.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cat_nested_args(t::Tuple) = (cat_nested(t[1])..., cat_nested_args(tail(t))...)
```
-/
  def m372 (head : Tree S X α) (tail : List (Tree S X α)) : List (Tree S X α) :=
    catNested head ++ catNestedArgs tail
  termination_by (treeWeight head + argsWeight tail, 3)
  decreasing_by
    all_goals have hpos := treeWeight_pos head
    all_goals simp_wf
    all_goals omega
end
end Flatten

namespace Flatten
/--
Julia source: base/broadcast.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Pick{N})(@nospecialize(args::Tuple)) where {N} = args[N]
```
-/
def m395 {I : Type} (getindex : List α → I → Result α) (n : I) (args : List α) : Result α :=
  getindex args n

/--
Julia source: base/broadcast.jl:409-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepare_args(::Tuple{}, ::Tuple) = ()
```
-/
def m409 {α : Type} (_args : List α) : Result (List α) := .ok []

/--
Julia source: base/broadcast.jl:408-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline prepare_args(makeargs::Tuple{Any}, @nospecialize(x::Tuple)) = (makeargs[1](x),)
```
-/
def m408 (head : Selector α) (args : List α) : Result (List α) := do
  let first ← head args
  pure [first]

mutual
  def prepareArgs : List (Selector α) → List α → Result (List α)
    | [], args => m409 args
    | [head], args => m408 head args
    | head :: next :: tail, args => m407 head (next :: tail) args
  termination_by selectors _ => (selectors.length, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  /--
Julia source: base/broadcast.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline prepare_args(makeargs::Tuple, @nospecialize(x::Tuple)) = (makeargs[1](x), prepare_args(tail(makeargs), x)...)
```
-/
  def m407 (head : Selector α) (tail : List (Selector α)) (args : List α) : Result (List α) := do
    let first ← head args
    let rest ← prepareArgs tail args
    pure (first :: rest)
  termination_by (tail.length, 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/--
Julia source: base/broadcast.jl:391-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_make_makeargs(::Tuple{}, n::Int) = (), n
```
-/
def m391 {α : Type} (n : Cursor) : List (Selector α) × Cursor := ([], n)

/--
Julia source: base/broadcast.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _make_makeargs1(_, n::Int) = Pick{n}(), n + 1
```
-/
def m398 {α : Type} (getindex : List α → Cursor → Result α) (_leaf : α) (n : Cursor) :
    Selector α × Cursor :=
  (m395 getindex n, n + JInt.lit .i64 1)

mutual
  def makeOne (getindex : List α → Cursor → Result α)
      (maybeconstructor : (List α → Result α) → List α → Result α) :
      Tree S X α → Cursor → Selector α × Cursor
    | .leaf value, n => m398 getindex value n
    | .node _ f args _, n => m400 getindex maybeconstructor f args n
  termination_by tree _ => (treeWeight tree, 2)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [treeWeight]
    all_goals omega

  def makeMany (getindex : List α → Cursor → Result α)
      (maybeconstructor : (List α → Result α) → List α → Result α) :
      List (Tree S X α) → Cursor → List (Selector α) × Cursor
    | [], n => m391 n
    | head :: tail, n => m386 getindex maybeconstructor head tail n
  termination_by args _ => (argsWeight args, 4)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [argsWeight]
    all_goals omega

  /--
Julia source: base/broadcast.jl:386-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _make_makeargs(args::Tuple, n::Int)
    head, n = _make_makeargs1(args[1], n)
    rest, n = _make_makeargs(tail(args), n)
    (head, rest...), n
end
```
-/
  def m386 (getindex : List α → Cursor → Result α)
      (maybeconstructor : (List α → Result α) → List α → Result α)
      (head : Tree S X α) (tail : List (Tree S X α)) (n : Cursor) :
      List (Selector α) × Cursor :=
    let first := makeOne getindex maybeconstructor head n
    let rest := makeMany getindex maybeconstructor tail first.2
    (first.1 :: rest.1, rest.2)
  termination_by (treeWeight head + argsWeight tail, 3)
  decreasing_by
    all_goals have hpos := treeWeight_pos head
    all_goals simp_wf
    all_goals omega

  /--
Julia source: base/broadcast.jl:400-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _make_makeargs1(bc::Broadcasted, n::Int)
    makeargs, n = _make_makeargs(bc.args, n)
    f = Base.maybeconstructor(bc.f)
    makeargs1 = (args::Tuple) -> (@inline; f(prepare_args(makeargs, args)...))
    makeargs1, n
end
```
-/
  def m400 (getindex : List α → Cursor → Result α)
      (maybeconstructor : (List α → Result α) → List α → Result α)
      (f : List α → Result α) (args : List (Tree S X α)) (n : Cursor) :
      Selector α × Cursor :=
    let made := makeMany getindex maybeconstructor args n
    let callable := maybeconstructor f
    (fun flat => do callable (← prepareArgs made.1 flat), made.2)
  termination_by (argsWeight args + 1, 1)
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/--
Julia source: base/broadcast.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
make_makeargs(args::Tuple) = _make_makeargs(args, 1)[1]
```
-/
def m382 (getindex : List α → Cursor → Result α)
    (maybeconstructor : (List α → Result α) → List α → Result α)
    (args : List (Tree S X α)) : List (Selector α) :=
  (makeMany getindex maybeconstructor args (JInt.lit .i64 1)).1
end Flatten
namespace Flatten
/--
Julia source: base/broadcast.jl:346-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flatten(bc::Broadcasted)
    isflat(bc) && return bc
    # concatenate the nested arguments into {a, b, c, d}
    args = cat_nested(bc)
    # build a tuple of functions `makeargs`. Its elements take
    # the whole "flat" argument list and generate the appropriate
    # input arguments for the broadcasted function `f`, e.g.,
    #          makeargs[1] = ((w, x, y, z)) -> w
    #          makeargs[2] = ((w, x, y, z)) -> g(x, y)
    #          makeargs[3] = ((w, x, y, z)) -> z
    makeargs = make_makeargs(bc.args)
    f = Base.maybeconstructor(bc.f)
    # TODO: consider specializing on args... if performance problems emerge:
    newf = (args...) -> (@inline; f(prepare_args(makeargs, args)...))
    return Broadcasted(bc.style, newf, args, bc.axes)
end
```
-/
def m346 (getindex : List α → Cursor → Result α)
    (maybeconstructor : (List α → Result α) → List α → Result α) :
    BroadcastNode S X α → BroadcastNode S X α
  | bc =>
      if m364 bc then bc
      else
        let flatArgs := m369 bc
        let selectors := m382 getindex maybeconstructor bc.args
        let callable := maybeconstructor bc.f
        { bc with
          f := fun flat => do callable (← prepareArgs selectors flat)
          args := flatArgs }
end Flatten

/- Empty generic function declaration: dispatch is trusted.
Julia source: base/broadcast.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function combine_styles end
```
-/

namespace Style
/--
Julia source: base/broadcast.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
combine_styles() = DefaultArrayStyle{0}()
```
-/
def m431 : Style := defaultStyle (.fixed 0)
end Style

namespace Style
/--
Julia source: base/broadcast.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_style(s::BroadcastStyle) = s
```
-/
def m458 (style : Style) : Style := style
end Style

namespace Style
/--
Julia source: base/broadcast.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
combine_styles(c) = result_style(BroadcastStyle(typeof(c)))
```
-/
def m432 {μ : Type → Type} [Monad μ] {α : Type} (styleOf : α → μ Style) (value : α) : μ Style := do
  pure (m458 (← styleOf value))
end Style

namespace Style
/--
Julia source: base/broadcast.jl:433-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function combine_styles(bc::Broadcasted)
    bc.style isa Union{Nothing,Unknown} || return bc.style
    throw(ArgumentError("Broadcasted{Unknown} wrappers do not have a style assigned"))
end
```
-/
def m433 : AssignedStyle → Jl Style
  | .assigned style => .ok style
  | .nothing | .unknown => .error (.argumentError "Broadcasted wrapper has no assigned style")
end Style

namespace Style
/--
Julia source: base/broadcast.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
```
-/
def m437 {μ : Type → Type} [Monad μ] {α : Type}
    (combineUnary : α → μ Style) (resultStyle : Style → Style → μ Style)
    (left right : α) : μ Style := do
  let leftStyle ← combineUnary left
  let rightStyle ← combineUnary right
  resultStyle leftStyle rightStyle
end Style

namespace Style
/--
Julia source: base/broadcast.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
```
-/
def m438 {μ : Type → Type} [Monad μ] {α : Type}
    (combineUnary : α → μ Style) (resultBinary : Style → Style → μ Style)
    (first second : α) (rest : List α) : μ Style := do
  let firstStyle ← combineUnary first
  let restStyle ← match rest with
    | [] => combineUnary second
    | [next] => m437 combineUnary resultBinary second next
    | next :: after :: tail => m438 combineUnary resultBinary second next (after :: tail)
  resultBinary firstStyle restStyle
termination_by rest.length

-- Argument arity dispatch selects the zero-, one-, two-, or variadic source overload.
def combineStyles {μ : Type → Type} [Monad μ] {α : Type}
    (combineUnary : α → μ Style) (resultBinary : Style → Style → μ Style) :
    List α → μ Style
  | [] => pure m431
  | [first] => combineUnary first
  | [first, second] => m437 combineUnary resultBinary first second
  | first :: second :: third :: rest => m438 combineUnary resultBinary first second (third :: rest)
end Style

/- Empty generic function declaration: dispatch is trusted.
Julia source: base/broadcast.jl:456-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_style end
```
-/

namespace Style
/--
Operation boundary for the selected error(String) call in same-type result_style.
This record has no laws. A concrete instance must call the actual selected error
operation in the caller's effect; the record itself is not a runtime binding.
Julia source: base/broadcast.jl:459-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_style(s1::S, s2::S) where S<:BroadcastStyle
    s1 ≡ s2 ? s1 : error("inconsistent broadcast styles, custom rule needed")
end
```
-/
class SameStyleErrorCall (m : Type → Type) (S : Type) where
  error : String → m S

/--
Compatibility instance for the entire old Style/Except interpretation only.
It preserves the pre-existing abstract inconsistent tag. It is not a binding of
Julia's String error constructor and does not claim to retain its error object.
Julia source: base/broadcast.jl:459-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_style(s1::S, s2::S) where S<:BroadcastStyle
    s1 ≡ s2 ? s1 : error("inconsistent broadcast styles, custom rule needed")
end
```
-/
instance legacySameStyleErrorCall : SameStyleErrorCall (Except StyleError) Style where
  error _ := .error .inconsistent

/--
Operation boundary for the actual selected result_join call. The original
operands and both actual rule results reach this operation in the caller's
effect. No correctness law, expected answer or runtime type identity is added.
Julia source: base/broadcast.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_style(s1, s2) = result_join(s1, s2, BroadcastStyle(s1, s2), BroadcastStyle(s2, s1))
```
-/
class ResultJoinCall (m : Type → Type) (S : Type) where
  join : S → S → S → S → m S

/--
Compatibility instance for the existing state/StyleError interpretation.
The legacy resultJoin's kind-based type approximation and abstract errors remain
unchanged here. New source bindings must select actual result_join callees;
this instance is not full Julia runtime type equality or error construction.
Julia source: base/broadcast.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_style(s1, s2) = result_join(s1, s2, BroadcastStyle(s1, s2), BroadcastStyle(s2, s1))
```
-/
instance legacyResultJoinCall {σ : Type} :
    ResultJoinCall (StateT σ (Except StyleError)) Style where
  join left right forward reverse :=
    StateT.lift (resultJoin left right forward reverse)

/--
Julia source: base/broadcast.jl:459-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_style(s1::S, s2::S) where S<:BroadcastStyle
    s1 ≡ s2 ? s1 : error("inconsistent broadcast styles, custom rule needed")
end
```
-/
def m459 {m : Type → Type} [Monad m] {S : Type} [SameStyleErrorCall m S]
    (identical : S → S → Bool) (left right : S) : m S :=
  if identical left right then pure left
  else SameStyleErrorCall.error "inconsistent broadcast styles, custom rule needed"
end Style

namespace Style
/--
Julia source: base/broadcast.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_style(s1, s2) = result_join(s1, s2, BroadcastStyle(s1, s2), BroadcastStyle(s2, s1))
```
-/
def m463 {σ : Type} {m : Type → Type} [Monad m] {S : Type}
    [ResultJoinCall (StateT σ m) S]
    (pairRule : S → S → StateT σ m S) (left right : S) : StateT σ m S := do
  let forward ← pairRule left right
  let reverse ← pairRule right left
  ResultJoinCall.join left right forward reverse
end Style

namespace Style
/--
Julia source: base/broadcast.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_join(::Any, ::Any, ::Unknown, ::Unknown)   = Unknown()
```
-/
def m467 {α β : Type} (_left : α) (_right : β) (_forward _reverse : Unit) : Style := unknown
end Style

namespace Style
/--
Julia source: base/broadcast.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_join(::Any, ::Any, ::Unknown, s::BroadcastStyle) = s
```
-/
def m468 {α β : Type} (_left : α) (_right : β) (_unknown : Unit) (style : Style) : Style := style
end Style

namespace Style
/--
Julia source: base/broadcast.jl:469-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_join(::Any, ::Any, s::BroadcastStyle, ::Unknown) = s
```
-/
def m469 {α β : Type} (_left : α) (_right : β) (style : Style) (_unknown : Unit) : Style := style
end Style

namespace Style
/--
Julia source: base/broadcast.jl:474-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_join(::AbstractArrayStyle, ::AbstractArrayStyle, ::Unknown, ::Unknown) =
    ArrayConflict()
```
-/
def m474 (_left _right _forward _reverse : Style) : Style := conflict
end Style

namespace Style
/--
Julia source: base/broadcast.jl:477-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_join(::Any, ::Any, s1::S, s2::S) where S<:BroadcastStyle = result_style(s1, s2)
```
-/
def m477 {m : Type → Type} [Monad m] {α β S : Type} [SameStyleErrorCall m S]
    (identical : S → S → Bool) (_left : α) (_right : β) (forward reverse : S) : m S :=
  m459 identical forward reverse
end Style

namespace Style
/--
Julia source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
    error("""
conflicting broadcast rules defined
  Broadcast.BroadcastStyle(::$S, ::$T) = $U()
  Broadcast.BroadcastStyle(::$T, ::$S) = $V()
One of these should be undefined (and thus return Broadcast.Unknown).""")
end
```
-/
def m479 {α β γ δ : Type} (_left : α) (_right : β) (_forward : γ) (_reverse : δ) :
    Except StyleError Style := .error .conflicting
end Style

namespace Shape
/--
Julia source: base/broadcast.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
```
-/
def m502 {m : Type → Type} [Monad m] {A Args AxesA AxesRest Out : Type}
    (axes : A → m AxesA) (combineAxes : Args → m AxesRest)
    (broadcastShape : AxesA → AxesRest → m Out) (first : A) (rest : Args) : m Out := do
  let firstAxes ← axes first
  let restAxes ← combineAxes rest
  broadcastShape firstAxes restAxes
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
```
-/
def m503 {m : Type → Type} [Monad m] {A B AxesA AxesB Out : Type}
    (axesA : A → m AxesA) (axesB : B → m AxesB)
    (broadcastShape : AxesA → AxesB → m Out) (left : A) (right : B) : m Out := do
  let leftAxes ← axesA left
  let rightAxes ← axesB right
  broadcastShape leftAxes rightAxes
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
combine_axes(A) = axes(A)
```
-/
def m504 {m : Type → Type} {A Axis : Type}
    (axes : A → m (List Axis)) (value : A) : m (List Axis) := axes value
end Shape

/- Empty generic function declaration: dispatch is trusted.
Julia source: base/broadcast.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function broadcast_shape end
```
-/

namespace Shape
/--
Julia source: base/broadcast.jl:521-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_shape(shape::Tuple) = shape
```
-/
def m521 {D : Type} (shape : List D) : List D := shape
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_shape(shape::Tuple, shape1::Tuple, shapes::Tuple...) = broadcast_shape(_bcs(shape, shape1), shapes...)
```
-/
def m522 {D : Type} (combine : List D → List D → Result (List D))
    (shape next : List D) (rest : List (List D)) : Result (List D) := do
  let combined ← combine shape next
  match rest with
  | [] => pure (m521 combined)
  | after :: remaining => m522 combine combined after remaining
termination_by rest.length
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs(::Tuple{}, ::Tuple{}) = ()
```
-/
def m524 {D : Type} : List D := []
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs(::Tuple{}, newshape::Tuple) = (newshape[1], _bcs((), tail(newshape))...)
```
-/
def m525 {D : Type} (head : D) (tail : List D) : Result (List D) := do
  let rest ← match tail with
    | [] => pure m524
    | next :: remaining => m525 next remaining
  pure (head :: rest)
termination_by tail.length
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:526-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs(shape::Tuple, ::Tuple{}) = (shape[1], _bcs(tail(shape), ())...)
```
-/
def m526 {D : Type} (head : D) (tail : List D) : Result (List D) := do
  let rest ← match tail with
    | [] => pure m524
    | next :: remaining => m526 next remaining
  pure (head :: rest)
termination_by tail.length
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:527-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bcs(shape::Tuple, newshape::Tuple)
    return (_bcs1(shape[1], newshape[1]), _bcs(tail(shape), tail(newshape))...)
end
```
-/
def m527 {D : Type} (join : D → D → Result D)
    (headA : D) (tailA : List D) (headB : D) (tailB : List D) : Result (List D) := do
  let head ← join headA headB
  let tail ← match tailA, tailB with
    | [], [] => pure m524
    | [], head :: tail => m525 head tail
    | head :: tail, [] => m526 head tail
    | headA :: tailA, headB :: tailB => m527 join headA tailA headB tailB
  pure (head :: tail)
termination_by tailA.length + tailB.length

-- Tuple arity dispatch selects the matching source overload.
def bcsDispatch {D : Type} (join : D → D → Result D) :
    List D → List D → Result (List D)
  | [], [] => pure m524
  | [], head :: tail => m525 head tail
  | head :: tail, [] => m526 head tail
  | headA :: tailA, headB :: tailB => m527 join headA tailA headB tailB

def shapeDispatch {D : Type} (join : D → D → Result D) :
    List D → List (List D) → Result (List D)
  | shape, [] => pure (m521 shape)
  | shape, next :: rest => m522 (bcsDispatch join) shape next rest
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:531-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a::Integer, b::Integer) = a == 1 ? b : (b == 1 ? a : (a == b ? a : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size; got a dimension with lengths ", a, " and ", b)))))
```
-/
def m531 {t u : IntTy} (a : JInt t) (b : JInt u) : Result (Sum (JInt t) (JInt u)) :=
  if a.val = 1 then .ok (.inr b)
  else if b.val = 1 then .ok (.inl a)
  else if a.val = b.val then .ok (.inl a)
  else .error .dimensionMismatch

abbrev IntegerDimension := (t : IntTy) × JInt t

-- The sum result records which integer type Julia's selected branch returns.
def integerJoin (a b : IntegerDimension) : Result IntegerDimension := do
  match ← m531 a.2 b.2 with
  | .inl value => pure ⟨a.1, value⟩
  | .inr value => pure ⟨b.1, value⟩
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:532-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a::Integer, b) = a == 1 ? b : (first(b) == 1 && last(b) == a ? b : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size; got a dimension with lengths ", a, " and ", length(b)))))
```
-/
def m532 {t u v : IntTy} {B : Type}
    (first : B → JInt u) (last : B → JInt v) (a : JInt t) (b : B) : Result B :=
  if a.val = 1 then .ok b
  else if (first b).val = 1 ∧ (last b).val = a.val then .ok b
  else .error .dimensionMismatch
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:533-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a, b::Integer) = _bcs1(b, a)
```
-/
def m533 {t u v : IntTy} {A : Type}
    (first : A → JInt u) (last : A → JInt v) (a : A) (b : JInt t) : Result A :=
  m532 first last b a
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a, b) = _bcsm(b, a) ? axistype(b, a) : _bcsm(a, b) ? axistype(a, b) : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size: a has axes ", a, " and b has axes ", b)))
```
-/
def m534 {E A B Out : Type} (dimensionMismatch : E)
    (compatibleBA : B → A → Bool) (compatibleAB : A → B → Bool)
    (axisTypeBA : B → A → Except E Out) (axisTypeAB : A → B → Except E Out)
    (a : A) (b : B) : Except E Out :=
  if compatibleBA b a then axisTypeBA b a
  else if compatibleAB a b then axisTypeAB a b
  else .error dimensionMismatch
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcsm(a, b) = a == b || length(b) == 1
```
-/
def m536 {m : Type → Type} [Monad m] {A B N V : Type}
    (equal : A → B → m V) (length : B → m N) (equalOne : N → m V)
    (condition : V → m Bool) (trueValue : V)
    (a : A) (b : B) : m V := do
  let equality ← equal a b
  let same ← condition equality
  if same then pure trueValue
  else do
    let size ← length b
    equalOne size
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcsm(a, b::Number) = b == 1
```
-/
def m537 {A B : Type} (equalOne : B → Bool) (_a : A) (b : B) : Bool := equalOne b
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:538-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcsm(a::Number, b::Number) = a == b || b == 1
```
-/
def m538 {A B : Type} (equal : A → B → Bool) (equalOne : B → Bool)
    (a : A) (b : B) : Bool := equal a b || equalOne b
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axistype(a::T, b::T) where T = a
```
-/
def m542 {μ : Type → Type} [Monad μ] {T : Type} (a : T) (_b : T) : μ T := pure a
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:543-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axistype(a::OneTo, b::OneTo) = OneTo{Int}(a)
```
-/
def m543 {E A B Out : Type} (oneToInt : A → Except E Out) (a : A) (_b : B) :
    Except E Out := oneToInt a
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:544-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axistype(a, b) = UnitRange{Int}(a)
```
-/
def m544 {E A B Out : Type} (unitRangeInt : A → Except E Out) (a : A) (_b : B) :
    Except E Out := unitRangeInt a
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:548-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(shp) = nothing
```
-/
def m548 {m : Type → Type} [Monad m] {S : Type} (_shape : S) : m Unit := pure ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(shp, ::Tuple{}) = nothing
```
-/
def m549 {m : Type → Type} [Monad m] {S : Type} (_shape : S) : m Unit := pure ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:550-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(::Tuple{}, ::Tuple{}) = nothing
```
-/
def m550 {m : Type → Type} [Monad m] : m Unit := pure ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:551-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_broadcast_shape(::Tuple{}, Ashp::Tuple)
    if any(ax -> length(ax) != 1, Ashp)
        throw(DimensionMismatch("cannot broadcast array to have fewer non-singleton dimensions"))
    end
    nothing
end
```
-/
def m551 {m : Type → Type} [Monad m] {E Axis N V : Type} [MonadExceptOf E m]
    (length : Axis → m N) (notEqualOne : N → m V)
    (any : (Axis → m V) → List Axis → m V)
    (dimensionMismatch : String → m E) (condition : V → m Bool) (axes : List Axis) : m Unit := do
  let anyResult ← any (fun axis => do
    let size ← length axis
    notEqualOne size) axes
  let hasVarying ← condition anyResult
  if hasVarying then
    let error ← dimensionMismatch "cannot broadcast array to have fewer non-singleton dimensions"
    throw error
  else pure ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:557-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_broadcast_shape(shp, Ashp::Tuple)
    _bcsm(shp[1], Ashp[1]) || throw(DimensionMismatch("array could not be broadcast to match destination"))
    check_broadcast_shape(tail(shp), tail(Ashp))
end
```
-/
def m557 {m : Type → Type} [Monad m] {E D Axis N V : Type} [MonadExceptOf E m]
    (equal : D → Axis → m V) (length : Axis → m N)
    (equalOne notEqualOne : N → m V)
    (any : (Axis → m V) → List Axis → m V)
    (dimensionMismatch : String → m E)
    (condition : V → m Bool) (trueValue : V)
    (head : D) (tail : List D) (axis : Axis) (axes : List Axis) : m Unit := do
  let compatibility ← m536 equal length equalOne condition trueValue head axis
  let fits ← condition compatibility
  if !fits then
    let error ← dimensionMismatch "array could not be broadcast to match destination"
    throw error
  else match tail, axes with
    | [], [] => m550
    | _, [] => m549 tail
    | [], remaining => m551 length notEqualOne any dimensionMismatch condition remaining
    | next :: rest, nextAxis :: restAxes =>
        m557 equal length equalOne notEqualOne any dimensionMismatch condition trueValue next rest nextAxis restAxes
termination_by tail.length
/--
Tuple-arity dispatch for the existing tuple-field carrier. Generic runtime tuple and overload bindings remain open.
Julia source: base/broadcast.jl:548-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(shp) = nothing
check_broadcast_shape(shp, ::Tuple{}) = nothing
check_broadcast_shape(::Tuple{}, ::Tuple{}) = nothing
function check_broadcast_shape(::Tuple{}, Ashp::Tuple)
    if any(ax -> length(ax) != 1, Ashp)
        throw(DimensionMismatch("cannot broadcast array to have fewer non-singleton dimensions"))
    end
    nothing
end
function check_broadcast_shape(shp, Ashp::Tuple)
    _bcsm(shp[1], Ashp[1]) || throw(DimensionMismatch("array could not be broadcast to match destination"))
    check_broadcast_shape(tail(shp), tail(Ashp))
end
```
-/
def checkShape {m : Type → Type} [Monad m] {E D Axis N V : Type} [MonadExceptOf E m]
    (equal : D → Axis → m V) (length : Axis → m N)
    (equalOne notEqualOne : N → m V)
    (any : (Axis → m V) → List Axis → m V)
    (dimensionMismatch : String → m E)
    (condition : V → m Bool) (trueValue : V) :
    List D → List Axis → m Unit
  | [], [] => m550
  | [], axes => m551 length notEqualOne any dimensionMismatch condition axes
  | shape, [] => m549 shape
  | head :: tail, axis :: axes =>
      m557 equal length equalOne notEqualOne any dimensionMismatch condition trueValue head tail axis axes
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:561-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline check_broadcast_axes(shp, A) = check_broadcast_shape(shp, axes(A))
```
-/
def m561 {m : Type → Type} [Monad m] {E A D Axis N V : Type} [MonadExceptOf E m]
    (equal : D → Axis → m V) (length : Axis → m N)
    (equalOne notEqualOne : N → m V)
    (any : (Axis → m V) → List Axis → m V)
    (dimensionMismatch : String → m E)
    (condition : V → m Bool) (trueValue : V)
    (axes : A → m (List Axis)) (shape : List D) (array : A) : m Unit := do
  let sourceAxes ← axes array
  checkShape equal length equalOne notEqualOne any dimensionMismatch condition trueValue shape sourceAxes
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:563-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function check_broadcast_axes(shp, A, As...)
    check_broadcast_axes(shp, A)
    check_broadcast_axes(shp, As...)
end
```
-/
def m563 {m : Type → Type} [Monad m] {E A D Axis N V : Type} [MonadExceptOf E m]
    (equal : D → Axis → m V) (length : Axis → m N)
    (equalOne notEqualOne : N → m V)
    (any : (Axis → m V) → List Axis → m V)
    (dimensionMismatch : String → m E)
    (condition : V → m Bool) (trueValue : V)
    (axes : A → m (List Axis)) (shape : List D)
    (first second : A) (rest : List A) : m Unit := do
  m561 equal length equalOne notEqualOne any dimensionMismatch condition trueValue axes shape first
  match rest with
  | [] => m561 equal length equalOne notEqualOne any dimensionMismatch condition trueValue axes shape second
  | next :: tail => m563 equal length equalOne notEqualOne any dimensionMismatch condition trueValue axes shape second next tail
end Shape







namespace Index
/--
Julia source: base/broadcast.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(::Tuple{}) = CartesianIndex()
```
-/
def m631 : Index := .cartesian []
end Index

namespace Index
/--
Julia source: base/broadcast.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(Is::Tuple{Any}) = Is[1]
```
-/
def m632 {α : Type} (value : α) : α := value
end Index

namespace Index
/--
Julia source: base/broadcast.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
to_index(Is::Tuple) = CartesianIndex(Is)
```
-/
def m633 (values : List Int) : Index := .cartesian values

def toIndex : List Int → Index
  | [] => m631
  | [value] => .scalar (m632 value)
  | values => m633 values
end Index
namespace Index
/--
Julia source: base/broadcast.jl:588-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple{}, I::Tuple) = ()
```
-/
def m588 {I V : Type} (_indices : I) : List V := []
end Index
namespace Index
/--
Julia source: base/broadcast.jl:590-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple{}, I::Tuple{}) = ()
```
-/
def m590 {V : Type} : List V := []
end Index
namespace Index
/--
Julia source: base/broadcast.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple{}) = (ax[1][begin], _newindex(tail(ax), ())...)
```
-/
def m589 {m : Type → Type} [Monad m] {Axis K V : Type}
    (firstindex : Axis → m K) (getindex : Axis → K → m V)
    (axis : Axis) (axes : List Axis) : m (List V) := do
  let firstIndex ← firstindex axis
  let firstValue ← getindex axis firstIndex
  let rest ← match axes with
    | [] => pure m590
    | next :: tail => m589 firstindex getindex next tail
  pure (firstValue :: rest)
termination_by axes.length
end Index
namespace Index
/--
Julia source: base/broadcast.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple) = (ifelse(length(ax[1]) == 1, ax[1][begin], I[1]), _newindex(tail(ax), tail(I))...)
```
-/
def m587 {m : Type → Type} [Monad m] {Axis N C K V : Type}
    (length : Axis → m N) (equalOne : N → m C)
    (firstindex : Axis → m K) (getindex : Axis → K → m V)
    (ifelse : C → V → V → m V)
    (axis : Axis) (axes : List Axis) (index : V) (indices : List V) : m (List V) := do
  let size ← length axis
  let singleton ← equalOne size
  let firstIndex ← firstindex axis
  let firstValue ← getindex axis firstIndex
  let chosen ← ifelse singleton firstValue index
  let rest ← match axes, indices with
    | [], [] => pure m590
    | [], remaining => pure (m588 remaining)
    | next :: tail, [] => m589 firstindex getindex next tail
    | next :: tail, coordinate :: remaining =>
        m587 length equalOne firstindex getindex ifelse next tail coordinate remaining
  pure (chosen :: rest)
termination_by axes.length
/--
Tuple-arity dispatch on the existing tuple-field representation.
Julia source: base/broadcast.jl:587-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple) = (ifelse(length(ax[1]) == 1, ax[1][begin], I[1]), _newindex(tail(ax), tail(I))...)
Base.@propagate_inbounds _newindex(ax::Tuple{}, I::Tuple) = ()
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple{}) = (ax[1][begin], _newindex(tail(ax), ())...)
Base.@propagate_inbounds _newindex(ax::Tuple{}, I::Tuple{}) = ()
```
-/
def remapAxes {m : Type → Type} [Monad m] {Axis N C K V : Type}
    (length : Axis → m N) (equalOne : N → m C)
    (firstindex : Axis → m K) (getindex : Axis → K → m V)
    (ifelse : C → V → V → m V) : List Axis → List V → m (List V)
  | [], [] => pure m590
  | [], indices => pure (m588 indices)
  | axis :: axes, [] => m589 firstindex getindex axis axes
  | axis :: axes, index :: indices => m587 length equalOne firstindex getindex ifelse axis axes index indices
end Index
namespace Index
/--
Julia source: base/broadcast.jl:585-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds newindex(arg, I::CartesianIndex) = to_index(_newindex(axes(arg), I.I))
```
-/
def m585 {m : Type → Type} [Monad m] {A Axis N C K V R : Type}
    (length : Axis → m N) (equalOne : N → m C)
    (firstindex : Axis → m K) (getindex : Axis → K → m V)
    (ifelse : C → V → V → m V) {CI : Type}
    (axes : A → m (List Axis)) (coordinates : CI → m (List V))
    (toIndex : List V → m R) (arg : A) (index : CI) : m R := do
  let sourceAxes ← axes arg
  let sourceIndices ← coordinates index
  let mapped ← remapAxes length equalOne firstindex getindex ifelse sourceAxes sourceIndices
  toIndex mapped
end Index
namespace Index
/--
Julia source: base/broadcast.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds newindex(arg, I::Integer) = to_index(_newindex(axes(arg), (I,)))
```
-/
def m586 {m : Type → Type} [Monad m] {A Axis N C K V R : Type}
    (length : Axis → m N) (equalOne : N → m C)
    (firstindex : Axis → m K) (getindex : Axis → K → m V)
    (ifelse : C → V → V → m V)
    (axes : A → m (List Axis)) (toIndex : List V → m R)
    (arg : A) (index : V) : m R := do
  let sourceAxes ← axes arg
  let mapped ← remapAxes length equalOne firstindex getindex ifelse sourceAxes [index]
  toIndex mapped
end Index









namespace Index
/--
Julia source: base/broadcast.jl:600-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindex(I, keep::Tuple{}, Idefault) = ()  # truncate if keep is shorter than I
```
-/
def m600 {I D : Type} (_indices : I) (_defaults : D) : List Int := []
end Index

namespace Index
/--
Julia source: base/broadcast.jl:601-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindex(I::Tuple{}, keep, Idefault) = ()  # or I is shorter
```
-/
def m601 {K D : Type} (_keep : K) (_defaults : D) : List Int := []
end Index

namespace Index
/--
Julia source: base/broadcast.jl:602-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindex(I::Tuple{}, keep::Tuple{}, Idefault) = () # or both
```
-/
def m602 {D : Type} (_defaults : D) : List Int := []
end Index
namespace Index
/--
Julia source: base/broadcast.jl:598-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindex(I, keep, Idefault) =
    (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
```
-/
def m598 (index : Int) (indices : List Int) (keep : Bool) (keeps : List Bool)
    (default : Int) (defaults : List Int) : Result (List Int) := do
  let chosen := if keep then index else default
  let rest ← match indices, keeps, defaults with
    | [], [], defaults => pure (m602 defaults)
    | [], keeps, defaults => pure (m601 keeps defaults)
    | indices, [], defaults => pure (m600 indices defaults)
    | _ :: _, _ :: _, [] => .error (.julia .boundsError)
    | index :: indices, keep :: keeps, default :: defaults =>
        m598 index indices keep keeps default defaults
  pure (chosen :: rest)
termination_by indices.length

def remapKeep : List Int → List Bool → List Int → Result (List Int)
  | [], [], defaults => pure (m602 defaults)
  | [], keeps, defaults => pure (m601 keeps defaults)
  | indices, [], defaults => pure (m600 indices defaults)
  | _ :: _, _ :: _, [] => .error (.julia .boundsError)
  | index :: indices, keep :: keeps, default :: defaults =>
      m598 index indices keep keeps default defaults
end Index
namespace Index
/--
Julia source: base/broadcast.jl:593-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindex(I::CartesianIndex, keep, Idefault) = to_index(_newindex(I.I, keep, Idefault))
```
-/
def m593 (indices : List Int) (keep : List Bool) (defaults : List Int) : Result Index :=
  toIndex <$> remapKeep indices keep defaults
end Index
namespace Index
/--
Julia source: base/broadcast.jl:595-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindex(i::Integer, keep::Tuple, idefault) = CartesianIndex(ifelse(keep[1], Int(i), Int(idefault[1])), idefault[2])
```
-/
def m595 (cartesian : List Int → Result Index) (value : Int)
    (keep : List Bool) (defaults : List Int) : Result Index := do
  let flag ← JuliaLean.base.tuple.getfield keep 1
  let convertedValue ← (convertInt value).mapError JuliaLean.base.tuple.TupleError.julia
  let firstDefault ← JuliaLean.base.tuple.getfield defaults 1
  let convertedDefault ← (convertInt firstDefault).mapError JuliaLean.base.tuple.TupleError.julia
  let chosen := if flag then convertedValue.val else convertedDefault.val
  let secondDefault ← JuliaLean.base.tuple.getfield defaults 2
  cartesian [chosen, secondDefault]
end Index
namespace Index
/--
Julia source: base/broadcast.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindex(i::Integer, keep::Tuple{Bool}, idefault) = ifelse(keep[1], i, idefault[1])
```
-/
def m596 {A B : Type} (value : A) (keep : Bool) (default : B) : Sum A B :=
  if keep then .inl value else .inr default
end Index
namespace Index
/--
Julia source: base/broadcast.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindex(i::Integer, keep::Tuple{}, idefault) = CartesianIndex()
```
-/
def m597 {V D : Type} (_value : V) (_keep : List Bool) (_defaults : D) : Index := .cartesian []

def numericIndex (cartesian : List Int → Result Index) (value : Int) :
    List Bool → List Int → Result Index
  | [], defaults => pure (m597 value [] defaults)
  | [flag], defaults => do
      let firstDefault ← JuliaLean.base.tuple.getfield defaults 1
      pure (.scalar (Sum.elim id id (m596 value flag firstDefault)))
  | keep, defaults => m595 cartesian value keep defaults
end Index
namespace Index
/--
Julia source: base/broadcast.jl:594-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindex(I::CartesianIndex{1}, keep, Idefault) = newindex(I.I[1], keep, Idefault)
```
-/
def m594 (cartesian : List Int → Result Index) (value : Int)
    (keep : List Bool) (defaults : List Int) : Result Index :=
  numericIndex cartesian value keep defaults

def newIndex (cartesian : List Int → Result Index) (index : Index)
    (keep : List Bool) (defaults : List Int) : Result Index :=
  match index with
  | .scalar value => numericIndex cartesian value keep defaults
  | .cartesian [value] => m594 cartesian value keep defaults
  | .cartesian indices => m593 indices keep defaults
end Index
namespace Index
/--
Julia source: base/broadcast.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindexer(indsA::Tuple{}) = (), ()
```
-/
def m608 {Keep Default : Type} : List Keep × List Default := ([], [])
end Index

namespace Index
/--
Julia source: base/broadcast.jl:609-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _newindexer(indsA::Tuple)
    ind1 = indsA[1]
    keep, Idefault = _newindexer(tail(indsA))
    (Base.length(ind1)::Integer != 1, keep...), (first(ind1), Idefault...)
end
```
-/
def m609 {m : Type → Type} [Monad m] {Axis RawLength IntegerLength Ty Keep Default : Type}
    (length : Axis → m RawLength) (typeassert : RawLength → Ty → m IntegerLength)
    (integerType : Ty) (notEqualOne : IntegerLength → m Keep) (first : Axis → m Default)
    (axis : Axis) (axes : List Axis) : m (List Keep × List Default) := do
  let rest ← match axes with
    | [] => pure m608
    | next :: remaining => m609 length typeassert integerType notEqualOne first next remaining
  let rawLength ← length axis
  let integerLength ← typeassert rawLength integerType
  let keep ← notEqualOne integerLength
  let default ← first axis
  pure (keep :: rest.1, default :: rest.2)
termination_by axes.length
/--
Tuple-arity dispatch on the existing tuple-field representation.
Julia source: base/broadcast.jl:608-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _newindexer(indsA::Tuple{}) = (), ()
@inline function _newindexer(indsA::Tuple)
    ind1 = indsA[1]
    keep, Idefault = _newindexer(tail(indsA))
    (Base.length(ind1)::Integer != 1, keep...), (first(ind1), Idefault...)
end
```
-/
def newIndexer {m : Type → Type} [Monad m] {Axis RawLength IntegerLength Ty Keep Default : Type}
    (length : Axis → m RawLength) (typeassert : RawLength → Ty → m IntegerLength)
    (integerType : Ty) (notEqualOne : IntegerLength → m Keep) (first : Axis → m Default) : List Axis → m (List Keep × List Default)
  | [] => pure m608
  | axis :: axes => m609 length typeassert integerType notEqualOne first axis axes
end Index
namespace Index
/--
Julia source: base/broadcast.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline shapeindexer(ax) = _newindexer(ax)
```
-/
def m607 {m : Type → Type} [Monad m] {Axis RawLength IntegerLength Ty Keep Default : Type}
    (length : Axis → m RawLength) (typeassert : RawLength → Ty → m IntegerLength)
    (integerType : Ty) (notEqualOne : IntegerLength → m Keep) (first : Axis → m Default) (axes : List Axis) : m (List Keep × List Default) :=
  newIndexer length typeassert integerType notEqualOne first axes
end Index
namespace Index
/--
Julia source: base/broadcast.jl:606-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindexer(A) = shapeindexer(axes(A))
```
-/
def m606 {m : Type → Type} [Monad m] {A Axis RawLength IntegerLength Ty Keep Default : Type}
    (length : Axis → m RawLength) (typeassert : RawLength → Ty → m IntegerLength)
    (integerType : Ty) (notEqualOne : IntegerLength → m Keep) (first : Axis → m Default) (axes : A → m (List Axis)) (array : A) :
    m (List Keep × List Default) := do
  let sourceAxes ← axes array
  m607 length typeassert integerType notEqualOne first sourceAxes
end Index

namespace Index
/--
Julia source: base/broadcast.jl:615-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function Base.getindex(bc::Broadcasted, Is::Vararg{Union{Integer,CartesianIndex},N}) where {N}
    I = to_index(Base.IteratorsMD.flatten(Is))
    _getindex(IndexStyle(bc), bc, I)
end
```
-/
def m615 {m : Type → Type} [Monad m] {BC Raw Flat I S R : Type}
    (flatten : Raw → m Flat) (toIndexFn : Flat → m I)
    (indexStyle : BC → m S) (getindex : S → BC → I → m R)
    (bc : BC) (indices : Raw) : m R := do
  let flat ← flatten indices
  let index ← toIndexFn flat
  let style ← indexStyle bc
  getindex style bc index
end Index

namespace Index
/--
Julia source: base/broadcast.jl:619-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _getindex(::IndexStyle, bc, I)
    @boundscheck checkbounds(bc, I)
    @inbounds _broadcast_getindex(bc, I)
end
```
-/
/- `boundscheck` records whether the source @boundscheck block remains after
inlining/bounds-context selection (doc/src/devdocs/boundscheck.md:12-36,70-79).
It is not an additional Julia argument. The element-read operation is selected
for the explicit @inbounds context independently of that outer flag. Generic
callee effects remain unbound; this declaration makes no closure claim. -/
def m619 {m : Type → Type} [Monad m] {BC I V : Type}
    (checkbounds : BC → I → m Unit)
    (getindexInbounds : BC → I → m V) (_style : Bool) (bc : BC) (index : I)
    (boundscheck : Bool := true) : m V := do
  if boundscheck then checkbounds bc index
  getindexInbounds bc index
end Index

namespace Index
/--
Julia source: base/broadcast.jl:623-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
    C = CartesianIndices(axes(bc))
    _getindex(s, bc, C[I])
end
```
-/
def m623 {m : Type → Type} [Monad m] {BC Ax C I CI S V : Type}
    (axes : BC → m Ax) (cartesianIndices : Ax → m C)
    (indexCartesian : C → I → m CI) (getindex : S → BC → CI → m V)
    (style : S) (bc : BC) (index : I) : m V := do
  let shape ← axes bc
  let cartesian ← cartesianIndices shape
  let converted ← indexCartesian cartesian index
  getindex style bc converted
end Index

namespace Index
/--
Julia source: base/broadcast.jl:627-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
    L = LinearIndices(axes(bc))
    _getindex(s, bc, L[I])
end
```
-/
def m627 {m : Type → Type} [Monad m] {BC Ax L CI I S V : Type}
    (axes : BC → m Ax) (linearIndices : Ax → m L)
    (indexLinear : L → CI → m I) (getindex : S → BC → I → m V)
    (style : S) (bc : BC) (index : CI) : m V := do
  let shape ← axes bc
  let linear ← linearIndices shape
  let converted ← indexLinear linear index
  getindex style bc converted
end Index


namespace Index
/--
Julia source: base/broadcast.jl:635-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function Base.checkbounds(bc::Broadcasted, I::CartesianIndex)
    Base.checkbounds_indices(Bool, axes(bc), (I,)) || Base.throw_boundserror(bc, I)
    nothing
end
```
-/
def m635 {m : Type → Type} [Monad m] {BC Ax I P : Type}
    (axes : BC → m Ax) (checkboundsIndicesBool : Ax → List I → m P)
    (booleanContext : P → m Bool)
    (throwBoundsError : BC → I → m Unit) (bc : BC) (index : I) : m Unit := do
  let shape ← axes bc
  let checked ← checkboundsIndicesBool shape [index]
  if !(← booleanContext checked) then
    throwBoundsError bc index
  pure ()
end Index

namespace Index
/--
Julia source: base/broadcast.jl:640-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function Base.checkbounds(bc::Broadcasted, I::Integer)
    Base.checkindex(Bool, eachindex(IndexLinear(), bc), I) || Base.throw_boundserror(bc, I)
    nothing
end
```
-/
def m640 {m : Type → Type} [Monad m] {BC S R I P : Type}
    (indexLinear : m S) (eachindex : S → BC → m R)
    (checkindexBool : R → I → m P) (booleanContext : P → m Bool)
    (throwBoundsError : BC → I → m Unit)
    (bc : BC) (index : I) : m Unit := do
  let style ← indexLinear
  let indices ← eachindex style bc
  let checked ← checkindexBool indices index
  if !(← booleanContext checked) then
    throwBoundsError bc index
  pure ()
end Index

namespace Index
/--
Julia source: base/broadcast.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(A::Union{Ref,AbstractArray{<:Any,0},Number}, I) = A[] # Scalar-likes can just ignore all indices
```
-/
def m651 {A I V : Type} (getZero : A → V) (array : A) (_index : I) : V := getZero array
end Index

namespace Index
/--
Julia source: base/broadcast.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(::Ref{Type{T}}, I) where {T} = T
```
-/
def m652 {T I : Type} (typeValue : T) (_index : I) : T := typeValue
end Index

namespace Index
/--
Julia source: base/broadcast.jl:654-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(A::Tuple{Any}, I) = A[1]
```
-/
def m654 {α I : Type} (value : α) (_index : I) : α := value
end Index

namespace Index
/--
Julia source: base/broadcast.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(A::Tuple, I) = A[I[1]]
```
-/
def m655 {α : Type} (tuple : List α) (index : List Int) : Result α := do
  let i ← JuliaLean.base.tuple.getfield index 1
  JuliaLean.base.tuple.getfield tuple i
end Index

namespace Index
/--
Julia source: base/broadcast.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(A, I) = A[newindex(A, I)]
```
-/
def m657 {m : Type → Type} [Monad m] {A I J V : Type}
    (newindex : A → I → m J) (getindex : A → J → m V)
    (array : A) (index : I) : m V := do
  let mapped ← newindex array index
  getindex array mapped
end Index

namespace Index
/--
Julia source: base/broadcast.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline axes(b::Extruded) = axes(b.x)
```
-/
def m669 {A : Type} (axes : A → List Axis) (value : Extruded A) : List Axis := axes value.x
end Index

namespace Index
/--
Julia source: base/broadcast.jl:670-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _broadcast_getindex(b::Extruded, i) = b.x[newindex(i, b.keeps, b.defaults)]
```
-/
def m670 {A V : Type} (cartesian : List Int → Result Index)
    (getindex : A → Index → Result V) (value : Extruded A) (index : Index) : Result V := do
  let mapped ← newIndex cartesian index value.keeps value.defaults
  getindex value.x mapped
end Index

namespace Index
/--
Julia source: base/broadcast.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
extrude(x::AbstractArray) = Extruded(x, newindexer(x)...)
```
-/
def m671 {A : Type} (newindexer : A → Result (List Bool × List Int)) (array : A) :
    Result (Extruded A) := do
  let pair ← newindexer array
  pure ⟨array, pair.1, pair.2⟩
end Index

namespace Index
/--
Julia source: base/broadcast.jl:672-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
extrude(x) = x
```
-/
def m672 {A : Type} (value : A) : A := value
end Index

namespace Index
/- The old EvalBroadcasted record remains only for existing pure proof-domain
compatibility. These source methods read the installed Lazy.Broadcasted fields.
Tuple slot carriers may be runtime values, so A/V need not be uniform Julia
concrete types. Runtime tuple storage and dispatch are still unbound. A boundscheck
flag is effective compiler context metadata, not an additional Julia argument.
The source's non-propagating evalf boundary is the selected callDefault operation. -/
/--
Julia source: base/broadcast.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
```
-/
def m701 {m : Type → Type} [Monad m] {A I V : Type}
    (getindex : Bool → A → I → m V) (head : A) (index : I)
    (boundscheck : Bool := true) : m (List V) := do
  let value ← getindex boundscheck head index
  pure [value]
/--
Julia source: base/broadcast.jl:702-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
```
-/
def m702 {m : Type → Type} [Monad m] {I V : Type} (_index : I) : m (List V) := pure []
/--
Julia source: base/broadcast.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _broadcast_getindex_evalf(f::Tf, args::Vararg{Any,N}) where {Tf,N} = f(args...)  # not propagate_inbounds
```
-/
def m704 {m : Type → Type} {F Args V : Type}
    (callDefault : F → Args → m V) (f : F) (args : Args) : m V :=
  callDefault f args
mutual
/-- Source tuple dispatch for the following three source methods. The List
carrier stores tuple slots, not a prescribed output. Reads inherit the effective
bounds context; m704's selected callable receives its default context.
Julia source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
```
-/
def gather {m : Type → Type} [Monad m] {A I V : Type}
    (getindex : Bool → A → I → m V) (boundscheck : Bool) : List A → I → m (List V)
  | [], index => m702 index
  | [head], index => m701 getindex head index boundscheck
  | head :: next :: tail, index => m700 getindex head (next :: tail) index boundscheck
termination_by args _ => 2 * args.length
decreasing_by simp_wf <;> omega
/--
Julia source: base/broadcast.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
```
-/
def m700 {m : Type → Type} [Monad m] {A I V : Type}
    (getindex : Bool → A → I → m V) (head : A) (tail : List A) (index : I)
    (boundscheck : Bool := true) : m (List V) := do
  let firstValue ← getindex boundscheck head index
  let rest ← gather getindex boundscheck tail index
  pure (firstValue :: rest)
termination_by 2 * tail.length + 1
decreasing_by simp_wf <;> omega
end
/--
Julia source: base/broadcast.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Any}, I)
    args = _getindex(bc.args, I)
    return _broadcast_getindex_evalf(bc.f, args...)
end
```
-/
def m675 {m : Type → Type} [Monad m] {S F X A I V W : Type}
    (getindex : Bool → A → I → m V) (callDefault : F → List V → m W)
    (bc : Lazy.Broadcasted S F (List A) X) (index : I)
    (boundscheck : Bool := true) : m W := do
  let args ← gather getindex boundscheck bc.args index
  m704 callDefault bc.f args
/--
Julia source: base/broadcast.jl:685-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Vararg{Any}}}, I) where {T}
    args = _getindex(tail(bc.args), I)
    return _broadcast_getindex_evalf(bc.f, T, args...)
end
```
-/
def m685 {m : Type → Type} [Monad m] {S F X A I R T V W : Type}
    (getindex : Bool → A → I → m V) (callDefault : F → (T × List V) → m W)
    (typeValue : T) (bc : Lazy.Broadcasted S F (R × List A) X) (index : I)
    (boundscheck : Bool := true) : m W := do
  let args ← gather getindex boundscheck bc.args.2 index
  m704 callDefault bc.f (typeValue, args)
/--
Julia source: base/broadcast.jl:689-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Any,Ref{Type{T}},Vararg{Any}}}, I) where {T}
    arg1 = _broadcast_getindex(bc.args[1], I)
    args = _getindex(tail(tail(bc.args)), I)
    return _broadcast_getindex_evalf(bc.f, arg1, T, args...)
end
```
-/
def m689 {m : Type → Type} [Monad m] {S F X A I R T V W : Type}
    (getindex : Bool → A → I → m V) (callDefault : F → (V × T × List V) → m W)
    (typeValue : T) (bc : Lazy.Broadcasted S F (A × R × List A) X) (index : I)
    (boundscheck : Bool := true) : m W := do
  let firstValue ← getindex boundscheck bc.args.1 index
  let args ← gather getindex boundscheck bc.args.2.2 index
  m704 callDefault bc.f (firstValue, typeValue, args)
/--
Julia source: base/broadcast.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Ref{Type{S}},Vararg{Any}}}, I) where {T,S}
    args = _getindex(tail(tail(bc.args)), I)
    return _broadcast_getindex_evalf(bc.f, T, S, args...)
end
```
-/
def m694 {m : Type → Type} [Monad m] {S F X A I R Q T U V W : Type}
    (getindex : Bool → A → I → m V) (callDefault : F → (T × U × List V) → m W)
    (firstType : T) (secondType : U)
    (bc : Lazy.Broadcasted S F (R × Q × List A) X) (index : I)
    (boundscheck : Bool := true) : m W := do
  let args ← gather getindex boundscheck bc.args.2.2 index
  m704 callDefault bc.f (firstType, secondType, args)
end Index

namespace Material
/--
Julia source: base/broadcast.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(x::BroadcastScalars) = Ref(x)
```
-/
def m736 (value : α) : RefValue α := ⟨value⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(::Type{T}) where {T} = Ref{Type{T}}(T)
```
-/
def m737 (typeValue : T) : TypeRef T := ⟨typeValue⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:738-738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(x::Union{AbstractArray,Number,AbstractChar,Ref,Tuple,Broadcasted}) = x
```
-/
def m738 {μ : Type → Type} [Monad μ] (value : α) : μ α := pure value
end Material

namespace Material
/--
Julia source: base/broadcast.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(x) = collect(x)
```
-/
def m740 {m : Type → Type} {I R : Type} (collect : I → m R) (iterable : I) : m R :=
  collect iterable
end Material

namespace Material
/--
Julia source: base/broadcast.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(::Union{AbstractDict, NamedTuple}) = throw(ArgumentError("broadcasting over dictionaries and `NamedTuple`s is reserved"))
```
-/
def m741 {W L D R : Type} (ops : JuliaLean.base.boot.CoreOps W L) (_dict : D) :
    JuliaLean.base.boot.CoreM W L R :=
  JuliaLean.base.boot.throwArgumentError ops
    "broadcasting over dictionaries and `NamedTuple`s is reserved"
end Material

namespace Material
/--
Julia source: base/broadcast.jl:744-744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
```
-/
def m744 {A I V : Type} (sample : A → I → Result V) (bc : SampledBroadcast A V) (index : I) : Result V := do
  bc.f <$> sampleArgs sample bc.args index
end Material

namespace Material
/--
Julia source: base/broadcast.jl:747-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
```
-/
def m747 {A I V : Type} (broadcastGet : A → I → Result V) (value : A) (index : I) : Result V :=
  broadcastGet value index
end Material

namespace Material
/--
Julia source: base/broadcast.jl:748-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
```
-/
def m748 {A I V : Type} (broadcastGet : A → I → Result V) (value : A) (index : I) : Result V :=
  broadcastGet value index
end Material

namespace Material
/--
Julia source: base/broadcast.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
```
-/
def m751 {A I T V : Type} (inferenceBarrier : A → A) (broadcastGet : A → I → V)
    (eltype : A → T) (typecheck : V → T → Bool) (value : A) (index : I) : Result V :=
  let sampled := broadcastGet (inferenceBarrier value) index
  if typecheck sampled (eltype value) then .ok sampled else .error .typeError
end Material

namespace Material
/--
Julia source: base/broadcast.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
```
-/
def m753 {A I V : Type} (sample : A → I → Result V) (head : A) (tail : List A) (index : I) : Result (List V) := do
  pure ((← sample head index) :: (← sampleArgs sample tail index))
end Material

namespace Material
/--
Julia source: base/broadcast.jl:754-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bc_eltypes(::Tuple{}, i) = ()
```
-/
def m754 {I V : Type} (_index : I) : List V := []
end Material

namespace Material
/--
Julia source: base/broadcast.jl:756-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_eltype(bc::Broadcasted)
    argtypes = Iterators.TupleOrBottom(typeof(bc), eltype(eachindex(bc)))
    argtypes === Union{} && return Union{}
    rettype = Base._return_type(_bc_eltype, argtypes)
    return promote_typejoin_union(rettype)
end
```
-/
def m756 {m : Type → Type} [Monad m] {B Iter F : Type}
    (typeOf : B → m JuliaLean.base.promotion.PType)
    (eachindex : B → m Iter) (eltype : Iter → m JuliaLean.base.promotion.PType)
    (returnType : F → JuliaLean.base.promotion.PType → m JuliaLean.base.promotion.PType)
    (promoteUnion : JuliaLean.base.promotion.PType → m JuliaLean.base.promotion.PType)
    (bcEltypeFunction : F) (bc : B) : m JuliaLean.base.promotion.PType := do
  let broadcastType ← typeOf bc
  let indices ← eachindex bc
  let indexType ← eltype indices
  let argtypes := JuliaLean.base.promotion.tupleOrBottom [broadcastType, indexType]
  if JuliaLean.base.promotion.pIsBottom argtypes then pure .bottom
  else do
    let resultType ← returnType bcEltypeFunction argtypes
    promoteUnion resultType
end Material

namespace Material
/--
Julia source: base/broadcast.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_broadcast_getindex_eltype(bc::Broadcasted) = combine_eltypes(bc.f, bc.args)
```
-/
def m765 {F A : Type} (combineEltypes : F → A → JType) (f : F) (args : A) : JType :=
  combineEltypes f args
end Material

namespace Material
/--
Julia source: base/broadcast.jl:766-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_broadcast_getindex_eltype(A) = eltype(A)  # Tuple, Array, etc.
```
-/
def m766 {A : Type} (eltype : A → JType) (array : A) : JType := eltype array
end Material

namespace Material
/--
Julia source: base/broadcast.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypes(::Tuple{}) = Tuple{}
```
-/
def m768 : List JType := []
end Material

namespace Material
/--
Julia source: base/broadcast.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
```
-/
def m769 (element : JType) : JType := tupleOrBottom [element]
end Material

namespace Material
/--
Julia source: base/broadcast.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
```
-/
def m770 (left right : JType) : JType := tupleOrBottom [left, right]
end Material

namespace Material
/--
Julia source: base/broadcast.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
```
-/
def m771 (head : JType) (tail : List JType) : JType :=
  match eltypes tail with
  | .bottom => .bottom
  | .tuple rest => tupleOrBottom (head :: rest)
  | _ => .bottom
end Material

namespace Material
/--
Julia source: base/broadcast.jl:774-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function combine_eltypes(f, args::Tuple)
    argT = eltypes(args)
    argT === Union{} && return Union{}
    return promote_typejoin_union(Base._return_type(f, argT))
end
```
-/
def m774 {F : Type} (returnType : F → JType → JType) (promoteUnion : JType → JType)
    (f : F) (args : List JType) : JType :=
  match eltypes args with | .bottom => .bottom | argTypes => promoteUnion (returnType f argTypes)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast(f::Tf, As::Vararg{Any,N}) where {Tf,N} = materialize(broadcasted(f, As...))
```
-/
def m859 {F A B R : Type} (broadcasted : F → A → B) (materialize : B → R) (f : F) (args : A) : R :=
  materialize (broadcasted f args)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:862-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline broadcast(f, x::Number...) = f(x...)
```
-/
def m862 {N R : Type} (f : List N → R) (numbers : List N) : R := f numbers
end Material

namespace Material
/--
Julia source: base/broadcast.jl:863-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline broadcast(f, t::NTuple{N,Any}, ts::Vararg{NTuple{N,Any}}) where {N} = map(f, t, ts...)
```
-/
def m863 {A V : Type} (f : List A → V) (tuples : List (List A)) : List V := zipTuples f tuples
end Material

namespace Material
/--
Julia source: base/broadcast.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast!(f::Tf, dest, As::Vararg{Any,N}) where {Tf,N} = (materialize!(dest, broadcasted(f, As...)); dest)
```
-/
def m898 {m : Type → Type} [Monad m] {F D A B : Type} (broadcasted : F → A → m B)
    (materializeBang : D → B → m Unit) (f : F) (dest : D) (args : A) : m D := do
  let bc ← broadcasted f args
  materializeBang dest bc
  pure dest
end Material

namespace Material
/--
Julia source: base/broadcast.jl:908-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function broadcast_preserving_zero_d(f, As...)
    bc = broadcasted(f, As...)
    r = materialize(bc)
    return length(axes(bc)) == 0 ? fill!(similar(bc, typeof(r)), r) : r
end
```
-/
def m908 {m : Type → Type} [Monad m] {F A B R C T : Type}
    (broadcasted : F → A → m B) (materialize : B → m R)
    (axes : B → m (List C)) (similarFill : B → R → m T)
    (f : F) (args : A) : m (Sum T R) := do
  let bc ← broadcasted f args
  let result ← materialize bc
  if (← axes bc).isEmpty then return .inl (← similarFill bc result)
  else return .inr result
end Material

namespace Material
/--
Julia source: base/broadcast.jl:913-913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline broadcast_preserving_zero_d(f) = fill(f())
```
-/
def m913 {R : Type} (f : Unit → R) : ZeroD R := ⟨f ()⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline broadcast_preserving_zero_d(f, as::Number...) = fill(f(as...))
```
-/
def m914 {N R : Type} (f : List N → R) (numbers : List N) : ZeroD R := ⟨f numbers⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:921-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline materialize(bc::Broadcasted) = copy(instantiate(bc))
```
-/
def m921 {m : Type → Type} [Monad m] {B R : Type}
    (instantiate : B → m B) (copy : B → m R) (bc : B) : m R := do
  copy (← instantiate bc)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
materialize(x) = x
```
-/
def m922 (value : α) : α := value
end Material

namespace Material
/--
Julia source: base/broadcast.jl:924-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function materialize!(dest, x)
    return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
end
```
-/
def m924 {m : Type → Type} [Monad m] {D X I A B R : Type}
    (axes : D → m X) (make : I → List A → X → m B) (identity : I) (x : A)
    (instantiate : B → m B) (materializeBang : D → B → m R) (dest : D) : m R := do
  let bc ← make identity [x] (← axes dest)
  materializeBang dest (← instantiate bc)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:928-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function materialize!(dest, bc::Broadcasted{<:Any})
    return materialize!(combine_styles(dest, bc), dest, bc)
end
```
-/
def m928 {D B S R : Type} (combineStyles : D → B → S) (materializeStyled : S → D → B → R)
    (dest : D) (bc : B) : R := materializeStyled (combineStyles dest bc) dest bc
end Material

namespace Material
/--
Julia source: base/broadcast.jl:932-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function materialize!(::BroadcastStyle, dest, bc::Broadcasted{<:Any})
    return copyto!(dest, instantiate(Broadcasted(bc.style, bc.f, bc.args, axes(dest))))
end
```
-/
def m932 {m : Type → Type} [Monad m] {S D F A X R : Type}
    (axes : D → m X)
    (instantiate : MaterializedExpr S F A X → m (MaterializedExpr S F A X))
    (copyto : D → MaterializedExpr S F A X → m R) (_style : S) (dest : D)
    (bc : MaterializedExpr S F A X) : m R := do
  copyto dest (← instantiate ⟨bc.style, bc.f, bc.args, ← axes dest⟩)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:936-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
materialize!(dest::Union{BroadcastScalars,Number,AbstractChar}, bc::Broadcasted{<:Any}) = _throw_unwritable_dest(dest)
```
-/
def m936 {D : Type} (throwUnwritable : D → Result Unit) (dest : D) : Result Unit :=
  throwUnwritable dest
end Material

namespace Material
/--
Julia source: base/broadcast.jl:937-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _throw_unwritable_dest(@nospecialize dest)
    throw(ArgumentError(LazyString("cannot broadcast-assign (`.=`) into a value of type ", typeof(dest))))
end
```
-/
def m937 {D : Type} (_dest : D) : Result Unit := .error .argument
end Material

namespace Material
/--
Julia source: base/broadcast.jl:942-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline copy(bc::Broadcasted{<:AbstractArrayStyle{0}}) = bc[CartesianIndex()]
```
-/
def m942 {B V : Type} (getZero : B → V) (bc : B) : V := getZero bc
end Material

namespace Material
/--
Julia source: base/broadcast.jl:943-944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(bc::Broadcasted{<:Union{Nothing,Unknown}}) =
    throw(ArgumentError("broadcasting requires an assigned BroadcastStyle"))
```
-/
def m943 {B : Type} (_bc : B) : Result Unit := .error .argument
end Material

namespace Material
/--
Julia source: base/broadcast.jl:948-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copy(bc::Broadcasted)
    ElType = result_eltype(bc)
    if Base.isconcretetype(ElType)
        # We can trust it and defer to the simpler `copyto!`
        return copyto!(similar(bc, ElType), bc)
    end
    # When ElType is not concrete, use narrowing. Use the first output
    # value to determine the starting output eltype; copyto_nonleaf!
    # will widen `dest` as needed to accommodate later values.
    bc′ = preprocess(nothing, bc)
    iter = eachindex(bc′)
    y = iterate(iter)
    if y === nothing
        # if empty, take the ElType at face value
        return similar(bc′, ElType)
    end
    # Initialize using the first value
    I, state = y
    @inbounds val = bc′[I]
    dest = similar(bc′, typeof(val))
    @inbounds dest[I] = val
    # Now handle the remaining values
    # The typeassert gives inference a helping hand on the element type and dimensionality
    # (work-around for #28382)
    ElType′ = ElType === Union{} ? Any : ElType <: Type ? Type : ElType
    RT = dest isa AbstractArray ? AbstractArray{<:ElType′, ndims(dest)} : Any
    return copyto_nonleaf!(dest, bc′, iter, state, 1)::RT
end
```
-/
/- Type values are preserved in Ty rather than collapsed to Inferred tags.
The remaining operations are unbound source calls, not correctness assumptions.
The TypeVar/apply_type/UnionAll sequence is the pinned lowering of
AbstractArray{<:ElType′, ndims(dest)}; its RT is captured from the original dest
before copyto_nonleaf!, and asserted on the returned value afterwards. -/
def m948 {m : Type → Type} [Monad m] {B Iter I State V D Ty TyVar NDim : Type}
    (resultEltype : B → m Ty) (isConcreteType : Ty → m Bool)
    (similar : B → Ty → m D) (copyto : D → B → m D)
    (preprocess : B → m B) (eachindex : B → m Iter)
    (iterate : Iter → m (Option (I × State))) (getindexInbounds : B → I → m V)
    (typeOf : V → m Ty) (setindexInbounds : D → I → V → m Unit)
    (identicalType subtypeType : Ty → Ty → m Bool)
    (bottomType anyType typeType : Ty)
    (isaAbstractArray : D → m Bool)
    (newUpperTypeVar : Ty → m TyVar) (ndimsDest : D → m NDim)
    (applyAbstractArray : TyVar → NDim → m Ty) (unionAll : TyVar → Ty → m Ty)
    (copyNonleaf : D → B → Iter → State → JInt64 → m D)
    (typeassertReturn : D → Ty → m D) (bc : B) : m D := do
  let elementType ← resultEltype bc
  if ← isConcreteType elementType then
    let dest ← similar bc elementType
    copyto dest bc
  else
    let ready ← preprocess bc
    let iter ← eachindex ready
    match ← iterate iter with
    | none => similar ready elementType
    | some (index, state) => do
        let value ← getindexInbounds ready index
        let valueType ← typeOf value
        let dest ← similar ready valueType
        setindexInbounds dest index value
        let isBottom ← identicalType elementType bottomType
        let normalized ←
          if isBottom then pure anyType
          else do
            let isType ← subtypeType elementType typeType
            if isType then pure typeType else pure elementType
        let returnType ←
          if ← isaAbstractArray dest then do
            let typeVariable ← newUpperTypeVar normalized
            let dimensions ← ndimsDest dest
            let applied ← applyAbstractArray typeVariable dimensions
            unionAll typeVariable applied
          else pure anyType
        let result ← copyNonleaf dest ready iter state (JInt.lit .i64 1)
        typeassertReturn result returnType
end Material

namespace Material
/--
Julia source: base/broadcast.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
```
-/
def m980 {m : Type → Type} [Monad m] {D B : Type}
    (convertNothing : B → m B) (copyto : D → B → m D) (dest : D) (bc : B) : m D := do
  copyto dest (← convertNothing bc)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:983-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
    # Typically, we must independently execute bc for every storage location in `dest`, but:
    # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
    if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
        # THEN we can just extract the argument and `fill!` the destination with it
        return fill!(dest, bc.args[1][])
    else
        # Otherwise, fall back to the default implementation like above
        return copyto!(dest, convert(Broadcasted{Nothing}, bc))
    end
end
```
-/
def m983 {H ε D S F Args Axes A V : Type}
    (isIdentity : F → Bool) (singleArgument : Args → Bool)
    (isflat : Expr S F Args Axes → Bool) (firstArgument : Args → A)
    (getZero : A → StateT H (Except ε) V) (fill : D → V → StateT H (Except ε) D)
    (convertNothing : Expr S F Args Axes → Expr S F Args Axes)
    (copyto : D → Expr S F Args Axes → StateT H (Except ε) D)
    (dest : D) (bc : Expr S F Args Axes) : StateT H (Except ε) D := do
  if isIdentity bc.f && singleArgument bc.args && isflat bc then
    fill dest (← getZero (firstArgument bc.args))
  else
    copyto dest (convertNothing bc)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
```
-/
def m1001 {A : Type} (sameObject : A → A → Bool) (unalias : A → A → A) (dest src : A) : A :=
  if sameObject dest src then src else unalias dest src
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1002-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_unalias(::Nothing, src) = src
```
-/
def m1002 {A : Type} (src : A) : A := src
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1007-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
```
-/
def m1007 {m : Type → Type} [Monad m] {S F A X D : Type}
    (preprocessArgs : D → A → m A) (dest : D) (bc : Expr S F A X) : m (Expr S F A X) := do
  pure ⟨bc.style, bc.f, ← preprocessArgs dest bc.args, bc.axes⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
```
-/
def m1008 {m : Type → Type} [Monad m] {D A B : Type}
    (unalias : D → A → m B) (extrude : B → m B) (dest : D) (value : A) : m B := do
  extrude (← unalias dest value)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1010-1010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
```
-/
def m1010 {m : Type → Type} [Monad m] {D A B : Type}
    (preprocess : D → A → m B) (dest : D) (head : A) (tail : List A) : m (List B) := do
  pure ((← preprocess dest head) :: (← preprocessArgs preprocess dest tail))
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1011-1011 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
```
-/
def m1011 {m : Type → Type} [Monad m] {D A B : Type}
    (preprocess : D → A → m B) (dest : D) (value : A) : m (List B) := do
  pure [← preprocess dest value]
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1012-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess_args(dest, args::Tuple{}) = ()
```
-/
def m1012 {D B : Type} (_dest : D) : List B := []
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1015-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copyto!(dest::AbstractArray, bc::Broadcasted{Nothing})
    axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
    # Performance optimization: broadcast!(identity, dest, A) is equivalent to copyto!(dest, A) if indices match
    if bc.f === identity && bc.args isa Tuple{AbstractArray} # only a single input argument to broadcast!
        A = bc.args[1]
        if axes(dest) == axes(A)
            return copyto!(dest, A)
        end
    end
    bc′ = preprocess(dest, bc)
    # Performance may vary depending on whether `@inbounds` is placed outside the
    # for loop or not. (cf. https://github.com/JuliaLang/julia/issues/38086)
    @inbounds @simd for I in eachindex(bc′)
        dest[I] = bc′[I]
    end
    return dest
end
```
-/
def m1015 {m : Type → Type} [Monad m] {D S F Args Axes X I V : Type}
    (axesDest : D → m X)
    (axesExpr : Expr S F Args Axes → m X)
    (sameAxes : X → X → Bool) (isIdentity : F → Bool) (singleArray : Args → Option D)
    (throwdm : X → X → m D)
    (copyto : D → D → m D)
    (preprocess : D → Expr S F Args Axes → m (Expr S F Args Axes))
    (eachindex : Expr S F Args Axes → m (List I))
    (getindex : Expr S F Args Axes → I → m V)
    (setindex : D → I → V → m Unit)
    (dest : D) (bc : Expr S F Args Axes) : m D := do
  let destAxes ← axesDest dest
  let sourceAxes ← axesExpr bc
  if !sameAxes destAxes sourceAxes then
    throwdm (← axesDest dest) (← axesExpr bc)
  else
    if isIdentity bc.f then
      match singleArray bc.args with
      | some source =>
        let destAxes ← axesDest dest
        let sourceAxes ← axesDest source
        if sameAxes destAxes sourceAxes then
          return ← copyto dest source
      | none => pure ()
    let ready ← preprocess dest bc
    let indices ← eachindex ready
    copyLoop getindex setindex dest ready indices
end Material

namespace Bits
/--
Julia source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
    axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
    ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
    ndims(dest) == 0 && (dest[] = bc[]; return dest)
    bc′ = preprocess(dest, bc)
    # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
    # to keep the index arithmetic below from wrapping.
    ax = axes(dest)
    ax1, out = ax[1], CartesianIndices(tail(ax))
    destc, indc = dest.chunks, 0
    bitst, remain = 0, UInt64(0)
    for I in out
        i = first(ax1) - 1
        if ndims(bc) == 1 || bitst >= 64 - length(ax1)
            if ndims(bc) > 1 && bitst != 0
                @inbounds @simd for j = bitst:63
                    remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
                end
                @inbounds destc[indc+=1] = remain
                bitst, remain = 0, UInt64(0)
            end
            while i <= last(ax1) - 64
                z = UInt64(0)
                @inbounds @simd for j = 0:63
                    z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
                end
                @inbounds destc[indc+=1] = z
            end
        end
        @inbounds @simd for j = i+1:last(ax1)
            remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
            bitst += 1
        end
    end
    @inbounds if bitst != 0
        destc[indc+1] = remain
    end
    return dest
end
```
-/
def m1035 {H ε D B AxesB I C V : Type}
    (axesDest : D → StateT H (Except ε) (List Axis64))
    (axesExpr : B → StateT H (Except ε) AxesB)
    (sameAxes : List Axis64 → AxesB → Bool)
    (throwdm : List Axis64 → AxesB → StateT H (Except ε) D)
    (isChunked : D → B → StateT H (Except ε) Bool)
    (chunkedCopy : D → B → StateT H (Except ε) D)
    (ndimsDest : D → StateT H (Except ε) I64)
    (ndimsExpr : B → StateT H (Except ε) I64)
    (getZero : B → StateT H (Except ε) V)
    (setZero : D → V → StateT H (Except ε) Unit)
    (preprocess : D → B → StateT H (Except ε) B)
    (firstAxis : List Axis64 → StateT H (Except ε) Axis64)
    (outerIndices : List Axis64 → StateT H (Except ε) (List I))
    (getChunks : D → StateT H (Except ε) C)
    (getValue : B → I64 → I → StateT H (Except ε) V)
    (convertBool : V → StateT H (Except ε) Bool)
    (setChunk : C → I64 → UInt64 → StateT H (Except ε) Unit)
    (dest : D) (bc : B) : StateT H (Except ε) D := do
  let destAxes ← axesDest dest
  let sourceAxes ← axesExpr bc
  if !sameAxes destAxes sourceAxes then
    return ← throwdm (← axesDest dest) (← axesExpr bc)
  if ← isChunked dest bc then return ← chunkedCopy dest bc
  if (← ndimsDest dest).val = 0 then
    setZero dest (← getZero bc)
    return dest
  let ready ← preprocess dest bc
  let ax ← axesDest dest
  let ax1 ← firstAxis ax
  let out ← outerIndices ax.tail
  let chunks ← getChunks dest
  let mut indc := int64 0
  let mut bitst := int64 0
  let mut remain : UInt64 := 0
  for outer in out do
    let mut i := int64 1 - int64 1
    if (← ndimsExpr bc).val = 1 || bitst.val ≥ (int64 64 - ax1.stop).val then
      if (← ndimsExpr bc).val > 1 && bitst.val ≠ 0 then
        let count := (64 - bitst.val).toNat
        remain ← readWord getValue convertBool ready outer count i bitst remain
        i := i + int64 count
        indc := indc + int64 1
        setChunk chunks indc remain
        bitst := int64 0
        remain := 0
      let state ← fullWordLoop getValue convertBool setChunk ready outer chunks ax1 i indc
      i := state.1
      indc := state.2
    let count := (ax1.stop.val - i.val).toNat
    remain ← readWord getValue convertBool ready outer count i bitst remain
    bitst := bitst + int64 count
  if bitst.val ≠ 0 then setChunk chunks (indc + int64 1) remain
  return dest
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1083-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(f, args) = nothing
```
-/
def m1083 {F Args : Type} (_f : F) (_args : Args) : Nothing := .nothing
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1084-1084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::Union{typeof(&), typeof(*), typeof(min)}, args) = &
```
-/
def m1084 {Fn Marker Args : Type} (andFunction : Fn) (_f : Marker) (_args : Args) : Fn := andFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1085-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::Union{typeof(|), typeof(max)}, args) = |
```
-/
def m1085 {Fn Marker Args : Type} (orFunction : Fn) (_f : Marker) (_args : Args) : Fn := orFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1086-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(xor), args) = xor
```
-/
def m1086 {Fn Marker Args : Type} (xorFunction : Fn) (_f : Marker) (_args : Args) : Fn := xorFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1087-1087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(nand), args) = nand
```
-/
def m1087 {Fn Marker Args : Type} (nandFunction : Fn) (_f : Marker) (_args : Args) : Fn := nandFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1088-1088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(nor), args) = nor
```
-/
def m1088 {Fn Marker Args : Type} (norFunction : Fn) (_f : Marker) (_args : Args) : Fn := norFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1089-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::Union{typeof(~), typeof(!)}, args) = ~
```
-/
def m1089 {Fn Marker Args : Type} (notFunction : Fn) (_f : Marker) (_args : Args) : Fn := notFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1090-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(identity), args) = identity
```
-/
def m1090 {Fn Marker Args : Type} (identityFunction : Fn) (_f : Marker) (_args : Args) : Fn := identityFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1091-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
```
-/
def m1091 {H ε Marker A B C D Args : Type}
    (xor : A → B → StateT H (Except ε) C) (complement : C → StateT H (Except ε) D)
    (_f : Marker) (_args : Args) : A → B → StateT H (Except ε) D :=
  fun x y => do complement (← xor x y)
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1092-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
```
-/
def m1092 {Fn Marker Args : Type} (xorFunction : Fn) (_f : Marker) (_args : Args) : Fn := xorFunction
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1093-1093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
```
-/
def m1093 {H ε Marker A B C D Args : Type}
    (complement : A → StateT H (Except ε) C) (and : C → B → StateT H (Except ε) D)
    (_f : Marker) (_args : Args) : A → B → StateT H (Except ε) D :=
  fun x y => do and (← complement x) y
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
```
-/
def m1094 {H ε Marker A B C D Args : Type}
    (complement : A → StateT H (Except ε) C) (or : C → B → StateT H (Except ε) D)
    (_f : Marker) (_args : Args) : A → B → StateT H (Except ε) D :=
  fun x y => do or (← complement x) y
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1095-1095 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
```
-/
def m1095 {H ε Marker A B C D Args : Type}
    (complement : B → StateT H (Except ε) C) (and : A → C → StateT H (Except ε) D)
    (_f : Marker) (_args : Args) : A → B → StateT H (Except ε) D :=
  fun x y => do and x (← complement y)
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
```
-/
def m1096 {H ε Marker A B C D Args : Type}
    (complement : B → StateT H (Except ε) C) (or : A → C → StateT H (Except ε) D)
    (_f : Marker) (_args : Args) : A → B → StateT H (Except ε) D :=
  fun x y => do or x (← complement y)
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1098-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
```
-/
def m1098 {H ε R S F Args Axes Op : Type}
    (chunkop : F → Args → Op)
    (ischunked : R → Material.Expr S F Args Axes → Op → StateT H (Except ε) Bool)
    (result : R) (bc : Material.Expr S F Args Axes) : StateT H (Except ε) Bool :=
  ischunked result bc (chunkop bc.f bc.args)
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1099-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
```
-/
def m1099 {H ε R B : Type} (_result : R) (_bc : B) (_nothing : Nothing) :
    StateT H (Except ε) Bool := pure false
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
```
-/
def m1100 {H ε R S F Args Axes Op : Type}
    (ischunked : R → Args → StateT H (Except ε) Bool)
    (result : R) (bc : Material.Expr S F Args Axes) (_op : Op) : StateT H (Except ε) Bool :=
  ischunked result bc.args
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, args) = false
```
-/
def m1101 {H ε R A : Type} (_result : R) (_args : A) : StateT H (Except ε) Bool := pure false
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
```
-/
def m1102 {H ε R A Tail SX SY : Type}
    (sizeResult : R → StateT H (Except ε) SX) (sizeArray : A → StateT H (Except ε) SY)
    (equalSize : SX → SY → Bool) (ischunked : R → Tail → StateT H (Except ε) Bool)
    (result : R) (head : A) (tail : Tail) : StateT H (Except ε) Bool := do
  let sx ← sizeResult result
  let sy ← sizeArray head
  if equalSize sx sy then ischunked result tail else pure false
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1103-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
```
-/
def m1103 {H ε R Tail : Type} (ischunked : R → Tail → StateT H (Except ε) Bool)
    (result : R) (_head : Bool) (tail : Tail) : StateT H (Except ε) Bool := ischunked result tail
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
```
-/
def m1104 {H ε R Head Tail : Type}
    (ischunkedHead : R → Head → StateT H (Except ε) Bool)
    (ischunkedTail : R → Tail → StateT H (Except ε) Bool)
    (result : R) (head : Head) (tail : Tail) : StateT H (Except ε) Bool := do
  if ← ischunkedHead result head then ischunkedTail result tail else pure false
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1105-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ischunkedbroadcast(R, args::Tuple{}) = true
```
-/
def m1105 {H ε R : Type} (_result : R) (_args : Unit) : StateT H (Except ε) Bool := pure true
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1108-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftfuncs(bc::Broadcasted{<:Any,<:Any,<:Any}) = liftfuncs(bc, _chunkop(bc.f, bc.args))
```
-/
def m1108 {S F Args Axes Op Out : Type}
    (chunkop : F → Args → Op) (liftfuncs : Material.Expr S F Args Axes → Op → Out)
    (bc : Material.Expr S F Args Axes) : Out := liftfuncs bc (chunkop bc.f bc.args)
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1109-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftfuncs(bc::Broadcasted, ::Nothing) = Broadcasted(bc.style, bc.f, map(liftfuncs, bc.args), bc.axes)
```
-/
def m1109 {H ε S F Args Axes Lift NewArgs : Type}
    (map : Lift → Args → StateT H (Except ε) NewArgs) (liftfuncs : Lift)
    (bc : Material.Expr S F Args Axes) : StateT H (Except ε) (Material.Expr S F NewArgs Axes) := do
  let args ← map liftfuncs bc.args
  return ⟨bc.style, bc.f, args, bc.axes⟩
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1110-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftfuncs(bc::Broadcasted, f) = Broadcasted(bc.style, f, map(liftfuncs, bc.args), bc.axes)
```
-/
def m1110 {H ε S F G Args Axes Lift NewArgs : Type}
    (map : Lift → Args → StateT H (Except ε) NewArgs) (liftfuncs : Lift)
    (bc : Material.Expr S F Args Axes) (f : G) : StateT H (Except ε) (Material.Expr S G NewArgs Axes) := do
  let args ← map liftfuncs bc.args
  return ⟨bc.style, f, args, bc.axes⟩
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1111-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftfuncs(x) = x
```
-/
def m1111 (value : α) : α := value
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1113-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftchunks(::Tuple{}) = ()
```
-/
def m1113 {H ε : Type} (_args : Unit) : StateT H (Except ε) Unit := pure ()
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
```
-/
def m1114 {H ε A C Tail Values : Type} (chunks : A → C)
    (liftchunks : Tail → StateT H (Except ε) Values) (head : A) (tail : Tail) :
    StateT H (Except ε) (C × Values) := do
  let first := chunks head
  return (first, (← liftchunks tail))
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1116-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
```
-/
def m1116 {H ε Tail Values : Type}
    (liftchunks : Tail → StateT H (Except ε) Values) (head : Bool) (tail : Tail) :
    StateT H (Except ε) (UInt64 × Values) := do
  let first := if head then ~~~(0 : UInt64) else 0
  return (first, (← liftchunks tail))
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ithchunk(i) = ()
```
-/
def m1117 {H ε I : Type} (_index : I) (_args : Unit) : StateT H (Except ε) Unit := pure ()
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1118-1118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
```
-/
def m1118 {H ε I C Tail Values : Type}
    (getindex : C → I → StateT H (Except ε) UInt64)
    (ithchunk : I → Tail → StateT H (Except ε) Values)
    (index : I) (chunks : C) (tail : Tail) : StateT H (Except ε) (UInt64 × Values) := do
  let first ← getindex chunks index
  return (first, (← ithchunk index tail))
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1119-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
```
-/
def m1119 {H ε I Tail Values : Type}
    (ithchunk : I → Tail → StateT H (Except ε) Values)
    (index : I) (scalar : UInt64) (tail : Tail) : StateT H (Except ε) (UInt64 × Values) := do
  return (scalar, (← ithchunk index tail))
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
    isempty(dest) && return dest
    f = flatten(liftfuncs(bc))
    args = liftchunks(f.args)
    dc = dest.chunks
    @simd for i in eachindex(dc)
        @inbounds dc[i] = f.f(ithchunk(i, args...)...)
    end
    @inbounds dc[end] &= Base._msk_end(dest)
    return dest
end
```
-/
def m1120 {H ε D B Flat Args Lifted C I F Values V : Type}
    (isempty : D → StateT H (Except ε) Bool)
    (liftfuncs : B → StateT H (Except ε) B) (flatten : B → StateT H (Except ε) Flat)
    (arguments : Flat → Args) (function : Flat → F)
    (liftchunks : Args → StateT H (Except ε) Lifted)
    (chunks : D → StateT H (Except ε) C)
    (eachindex : C → StateT H (Except ε) (List I))
    (ithchunk : I → Lifted → StateT H (Except ε) Values)
    (apply : F → Values → StateT H (Except ε) V)
    (setChunk : C → I → V → StateT H (Except ε) Unit)
    (lastindex : C → StateT H (Except ε) I)
    (getChunk : C → I → StateT H (Except ε) UInt64)
    (maskEnd : D → StateT H (Except ε) UInt64)
    (setMaskedChunk : C → I → UInt64 → StateT H (Except ε) Unit)
    (dest : D) (bc : B) : StateT H (Except ε) D := do
  if ← isempty dest then return dest
  let f ← flatten (← liftfuncs bc)
  let args ← liftchunks (arguments f)
  let dc ← chunks dest
  for i in (← eachindex dc) do
    let value ← apply (function f) (← ithchunk i args)
    setChunk dc i value
  let last ← lastindex dc
  let word ← getChunk dc last
  let mask ← maskEnd dest
  setMaskedChunk dc last (word &&& mask)
  return dest
end Bits

namespace Material
/--
Julia source: base/broadcast.jl:1133-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throwdm(axdest, axsrc) =
    throw(DimensionMismatch(LazyString("destination axes ", axdest, " are not compatible with source axes ", axsrc)))
```
-/
def m1133 {m : Type → Type} [Monad m] {ε A B Message Out : Type} [MonadExceptOf ε m]
    (lazyString : String → A → String → B → m Message)
    (dimensionMismatch : Message → m ε)
    (destAxes : A) (sourceAxes : B) : m Out := do
  let message ← lazyString "destination axes " destAxes
    " are not compatible with source axes " sourceAxes
  throw (← dimensionMismatch message)
end Material

namespace Material

/- The same existing iterators.Exec effect is used throughout this recursive
source call graph. Its error result retains the current heap; none denotes
nontermination, never normal iterator exhaustion. Callee parameters below are
unresolved extensible source operations, not completed bindings or assumed laws.
D and V may be heterogeneous runtime-value carriers; no homogeneous-type fit law
or monotonicity of type widening is assumed. Counts follow the native Int caller. -/
mutual
/--
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
def m1136 {E H D B I V Iter State Taken TakenState Ty : Type}
    (eltype : D → JuliaLean.base.iterators.Exec E H Ty)
    (iterate : Iter → Option State → JuliaLean.base.iterators.Exec E H (Option (I × State)))
    (take : Iter → JInt64 → JuliaLean.base.iterators.Exec E H Taken)
    (iterateTaken : Taken → Option TakenState → JuliaLean.base.iterators.Exec E H (Option (I × TakenState)))
    (getindex : D → I → JuliaLean.base.iterators.Exec E H V)
    (getvalue : B → I → JuliaLean.base.iterators.Exec E H V)
    (setindexChecked : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (setindexInbounds : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (isa : V → Ty → JuliaLean.base.iterators.Exec E H Bool)
    (typeof : V → JuliaLean.base.iterators.Exec E H Ty)
    (promoteTypejoin : Ty → Ty → JuliaLean.base.iterators.Exec E H Ty)
    (similar : B → Ty → JuliaLean.base.iterators.Exec E H D)
    (newdest dest : D) (bc : B) (value : V) (index : I) (iter : Iter)
    (state : State) (count : JInt64) : JuliaLean.base.iterators.Exec E H D :=
  fun heap => match take iter count heap with
  | none => none
  | some (.error error, heap) => some (.error error, heap)
  | some (.ok taken, heap) =>
      match copyPrefix iterateTaken getindex setindexChecked dest newdest taken none heap with
      | none => none
      | some (.error error, heap) => some (.error error, heap)
      | some (.ok (), heap) =>
          match setindexChecked newdest index value heap with
          | none => none
          | some (.error error, heap) => some (.error error, heap)
          | some (.ok (), heap) =>
              m1145 eltype iterate take iterateTaken getindex getvalue setindexChecked setindexInbounds isa typeof promoteTypejoin similar
                newdest bc iter state (JuliaLean.base.int.add_int count (JInt.lit .i64 1)) heap
partial_fixpoint

/--
Julia source: base/broadcast.jl:1145-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
    T = eltype(dest)
    while true
        y = iterate(iter, state)
        y === nothing && break
        I, state = y
        @inbounds val = bc[I]
        if val isa T
            @inbounds dest[I] = val
        else
            # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
            # copy over old values, and continue
            newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
            return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
        end
        count += 1
    end
    return dest
end
```
-/
def m1145 {E H D B I V Iter State Taken TakenState Ty : Type}
    (eltype : D → JuliaLean.base.iterators.Exec E H Ty)
    (iterate : Iter → Option State → JuliaLean.base.iterators.Exec E H (Option (I × State)))
    (take : Iter → JInt64 → JuliaLean.base.iterators.Exec E H Taken)
    (iterateTaken : Taken → Option TakenState → JuliaLean.base.iterators.Exec E H (Option (I × TakenState)))
    (getindex : D → I → JuliaLean.base.iterators.Exec E H V)
    (getvalue : B → I → JuliaLean.base.iterators.Exec E H V)
    (setindexChecked : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (setindexInbounds : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (isa : V → Ty → JuliaLean.base.iterators.Exec E H Bool)
    (typeof : V → JuliaLean.base.iterators.Exec E H Ty)
    (promoteTypejoin : Ty → Ty → JuliaLean.base.iterators.Exec E H Ty)
    (similar : B → Ty → JuliaLean.base.iterators.Exec E H D)
    (dest : D) (bc : B) (iter : Iter) (state : State) (count : JInt64) :
    JuliaLean.base.iterators.Exec E H D :=
  fun heap => match eltype dest heap with
  | none => none
  | some (.error error, heap) => some (.error error, heap)
  | some (.ok elementType, heap) =>
      copyNonleafLoop eltype iterate take iterateTaken getindex getvalue setindexChecked setindexInbounds isa typeof promoteTypejoin similar
        dest bc iter state count elementType heap
partial_fixpoint

/--
The while-loop of copyto_nonleaf!: elementType is the cached T from this invocation, refreshed only when restart calls m1145 on the newly allocated destination.
Julia source: base/broadcast.jl:1145-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
    T = eltype(dest)
    while true
        y = iterate(iter, state)
        y === nothing && break
        I, state = y
        @inbounds val = bc[I]
        if val isa T
            @inbounds dest[I] = val
        else
            # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
            # copy over old values, and continue
            newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
            return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
        end
        count += 1
    end
    return dest
end
```
-/
def copyNonleafLoop {E H D B I V Iter State Taken TakenState Ty : Type}
    (eltype : D → JuliaLean.base.iterators.Exec E H Ty)
    (iterate : Iter → Option State → JuliaLean.base.iterators.Exec E H (Option (I × State)))
    (take : Iter → JInt64 → JuliaLean.base.iterators.Exec E H Taken)
    (iterateTaken : Taken → Option TakenState → JuliaLean.base.iterators.Exec E H (Option (I × TakenState)))
    (getindex : D → I → JuliaLean.base.iterators.Exec E H V)
    (getvalue : B → I → JuliaLean.base.iterators.Exec E H V)
    (setindexChecked : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (setindexInbounds : D → I → V → JuliaLean.base.iterators.Exec E H Unit)
    (isa : V → Ty → JuliaLean.base.iterators.Exec E H Bool)
    (typeof : V → JuliaLean.base.iterators.Exec E H Ty)
    (promoteTypejoin : Ty → Ty → JuliaLean.base.iterators.Exec E H Ty)
    (similar : B → Ty → JuliaLean.base.iterators.Exec E H D)
    (dest : D) (bc : B) (iter : Iter) (state : State) (count : JInt64)
    (elementType : Ty) : JuliaLean.base.iterators.Exec E H D :=
  fun heap => match iterate iter (some state) heap with
  | none => none
  | some (.error error, heap) => some (.error error, heap)
  | some (.ok none, heap) => some (.ok dest, heap)
  | some (.ok (some (index, next)), heap) =>
      match getvalue bc index heap with
      | none => none
      | some (.error error, heap) => some (.error error, heap)
      | some (.ok value, heap) =>
          match isa value elementType heap with
          | none => none
          | some (.error error, heap) => some (.error error, heap)
          | some (.ok true, heap) =>
              match setindexInbounds dest index value heap with
              | none => none
              | some (.error error, heap) => some (.error error, heap)
              | some (.ok (), heap) =>
                  copyNonleafLoop eltype iterate take iterateTaken getindex getvalue setindexChecked setindexInbounds isa typeof promoteTypejoin similar
                    dest bc iter next (JuliaLean.base.int.add_int count (JInt.lit .i64 1)) elementType heap
          | some (.ok false, heap) =>
              match typeof value heap with
              | none => none
              | some (.error error, heap) => some (.error error, heap)
              | some (.ok valueType, heap) =>
                  match promoteTypejoin elementType valueType heap with
                  | none => none
                  | some (.error error, heap) => some (.error error, heap)
                  | some (.ok widenedType, heap) =>
                      match similar bc widenedType heap with
                      | none => none
                      | some (.error error, heap) => some (.error error, heap)
                      | some (.ok newdest, heap) =>
                          m1136 eltype iterate take iterateTaken getindex getvalue setindexChecked setindexInbounds isa typeof promoteTypejoin similar
                            newdest dest bc value index iter next count heap
partial_fixpoint
end
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copy(bc::Broadcasted{Style{Tuple}})
    dim = axes(bc)
    length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
    N = length(dim[1])
    return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
end
```
-/
def m1167 {B I V : Type} (axes : B → List (List I)) (getindex : B → Nat → V) (bc : B) : Result (List V) :=
  match axes bc with
  | [axis] => .ok ((List.range axis.length).map fun k => getindex bc (k + 1))
  | _ => .error .dimensionMismatch
end Material

namespace Range
/--
Julia source: base/broadcast.jl:1176-1176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractRange) = r
```
-/
def m1176 (r : RangeView T Ref Step Len Offset) : RangeView T Ref Step Len Offset := r
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1178-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange) = range(-first(r), step=negate(step(r)), length=length(r))
```
-/
def m1178 {T Ref Step Out V0 V1 : Type} {Len Offset : Type}
    (neg0 : T → Jl V0) (negate0 : Step → Jl V1) (range0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← neg0 r.first
  let v1 ← negate0 r.step
  range0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1179-1179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange) = range(-first(r), -last(r), step=negate(step(r)))
```
-/
def m1179 {R T Step Out V0 V1 : Type}
    (first last : R → T) (step : R → Step)
    (neg : T → Jl V0) (negate : Step → Jl V1) (range : V0 → V0 → V1 → Jl Out)
    (r : R) : Jl Out := do
  let start ← neg (first r)
  let stop ← neg (last r)
  let stride ← negate (step r)
  range start stop stride
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1180-1180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::StepRangeLen) = StepRangeLen(-r.ref, negate(r.step), length(r), r.offset)
```
-/
def m1180 {T Ref Step Out V0 V1 : Type} {Len Offset : Type}
    (neg0 : Ref → Jl V0) (negate0 : Step → Jl V1) (makeStepRangeLen0 : V0 → V1 → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← neg0 r.ref
  let v1 ← negate0 r.step
  makeStepRangeLen0 v0 v1 r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1181-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::LinRange) = LinRange(-r.start, -r.stop, length(r))
```
-/
def m1181 {T Ref Step Out V0 : Type} {Len Offset : Type}
    (neg0 : T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← neg0 r.start
  let v1 ← neg0 r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractRange, x::Number) = range(first(r) + x, step=step(r), length=length(r))
```
-/
def m1184 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : T → X → Jl V0) (range0 : V0 → Step → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 r.first x
  range0 v0 r.step r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1185-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::AbstractRange) = range(x + first(r), step=step(r), length=length(r))
```
-/
def m1185 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : X → T → Jl V0) (range0 : V0 → Step → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 x r.first
  range0 v0 r.step r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1186-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::OrdinalRange, x::Integer) = range(first(r) + x, last(r) + x, step=step(r))
```
-/
def m1186 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : T → X → Jl V0) (range0 : V0 → V0 → Step → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 r.first x
  let v1 ← add0 r.last x
  range0 v0 v1 r.step
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1187-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Integer, r::OrdinalRange) = range(x + first(r), x + last(r), step=step(r))
```
-/
def m1187 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : X → T → Jl V0) (range0 : V0 → V0 → Step → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 x r.first
  let v1 ← add0 x r.last
  range0 v0 v1 r.step
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1188-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractUnitRange, x::Integer) = range(first(r) + x, last(r) + x)
```
-/
def m1188 {R T X Out V : Type} (first last : R → T)
    (add : T → X → Jl V) (range : V → V → Jl Out) (r : R) (x : X) : Jl Out := do
  let a ← add (first r) x
  let b ← add (last r) x
  range a b
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Integer, r::AbstractUnitRange) = range(x + first(r), x + last(r))
```
-/
def m1189 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : X → T → Jl V0) (range0 : V0 → V0 → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 x r.first
  let v1 ← add0 x r.last
  range0 v0 v1
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1190-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractUnitRange, x::Real) = range(first(r) + x, length=length(r))
```
-/
def m1190 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : T → X → Jl V0) (rangeStartLength0 : V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 r.first x
  rangeStartLength0 v0 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1191-1191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Real, r::AbstractUnitRange) = range(x + first(r), length=length(r))
```
-/
def m1191 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : X → T → Jl V0) (rangeStartLength0 : V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 x r.first
  rangeStartLength0 v0 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1192-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::StepRangeLen{T}, x::Number) where T =
    StepRangeLen{typeof(T(r.ref)+x)}(r.ref + x, r.step, length(r), r.offset)
```
-/
def m1192 {T Ref Step X Out V0 V1 V2 : Type} {Len Offset : Type}
    (convertRef0 : Ref → Jl T) (add0 : T → X → Jl V0) (typeOf0 : V0 → V1) (add1 : Ref → X → Jl V2) (makeTypedStepRangeLen0 : V1 → V2 → Step → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← convertRef0 r.ref
  let v1 ← add0 v0 x
  let v2 := typeOf0 v1
  let v3 ← add1 r.ref x
  makeTypedStepRangeLen0 v2 v3 r.step r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1194-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::StepRangeLen{T}) where T =
    StepRangeLen{typeof(x+T(r.ref))}(x + r.ref, r.step, length(r), r.offset)
```
-/
def m1194 {T Ref Step X Out V0 V1 V2 : Type} {Len Offset : Type}
    (convertRef0 : Ref → Jl T) (add0 : X → T → Jl V0) (typeOf0 : V0 → V1) (add1 : X → Ref → Jl V2) (makeTypedStepRangeLen0 : V1 → V2 → Step → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← convertRef0 r.ref
  let v1 ← add0 x v0
  let v2 := typeOf0 v1
  let v3 ← add1 x r.ref
  makeTypedStepRangeLen0 v2 v3 r.step r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1196-1196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::LinRange, x::Number) = LinRange(r.start + x, r.stop + x, length(r))
```
-/
def m1196 {R T X Out V Len : Type} (start stop : R → T) (length : R → Len)
    (add : T → X → Jl V) (makeLinRange : V → V → Len → Jl Out)
    (r : R) (x : X) : Jl Out := do
  let a ← add (start r) x
  let b ← add (stop r) x
  makeLinRange a b (length r)
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1197-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::LinRange) = LinRange(x + r.start, x + r.stop, length(r))
```
-/
def m1197 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (add0 : X → T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← add0 x r.start
  let v1 ← add0 x r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1198-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r1::AbstractRange, r2::AbstractRange) = r1 + r2
```
-/
def m1198 {ε A B Out : Type} (add : A → B → Except ε Out) (r1 : A) (r2 : B) :
    Except ε Out := add r1 r2
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange, x::Number) = range(first(r) - x, step=step(r), length=length(r))
```
-/
def m1200 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (sub0 : T → X → Jl V0) (range0 : V0 → Step → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 r.first x
  range0 v0 r.step r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1201-1201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::AbstractRange) = range(x - first(r), step=negate(step(r)), length=length(r))
```
-/
def m1201 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (sub0 : X → T → Jl V0) (negate0 : Step → Jl V1) (range0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 x r.first
  let v1 ← negate0 r.step
  range0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1202-1202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange, x::Integer) = range(first(r) - x, last(r) - x, step=step(r))
```
-/
def m1202 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (sub0 : T → X → Jl V0) (range0 : V0 → V0 → Step → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 r.first x
  let v1 ← sub0 r.last x
  range0 v0 v1 r.step
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Integer, r::OrdinalRange) = range(x - first(r), x - last(r), step=negate(step(r)))
```
-/
def m1203 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (sub0 : X → T → Jl V0) (negate0 : Step → Jl V1) (range0 : V0 → V0 → V1 → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 x r.first
  let v1 ← sub0 x r.last
  let v2 ← negate0 r.step
  range0 v0 v1 v2
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1204-1204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractUnitRange, x::Integer) = range(first(r) - x, last(r) - x)
```
-/
def m1204 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (sub0 : T → X → Jl V0) (range0 : V0 → V0 → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 r.first x
  let v1 ← sub0 r.last x
  range0 v0 v1
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1205-1205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractUnitRange, x::Real) = range(first(r) - x, length=length(r))
```
-/
def m1205 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (sub0 : T → X → Jl V0) (rangeStartLength0 : V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 r.first x
  rangeStartLength0 v0 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1206-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::StepRangeLen{T}, x::Number) where T =
    StepRangeLen{typeof(T(r.ref)-x)}(r.ref - x, r.step, length(r), r.offset)
```
-/
def m1206 {T Ref Step X Out V0 V1 V2 : Type} {Len Offset : Type}
    (convertRef0 : Ref → Jl T) (sub0 : T → X → Jl V0) (typeOf0 : V0 → V1) (sub1 : Ref → X → Jl V2) (makeTypedStepRangeLen0 : V1 → V2 → Step → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← convertRef0 r.ref
  let v1 ← sub0 v0 x
  let v2 := typeOf0 v1
  let v3 ← sub1 r.ref x
  makeTypedStepRangeLen0 v2 v3 r.step r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1208-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::StepRangeLen{T}) where T =
    StepRangeLen{typeof(x-T(r.ref))}(x - r.ref, negate(r.step), length(r), r.offset)
```
-/
def m1208 {T Ref Step X Out V0 V1 V2 V3 : Type} {Len Offset : Type}
    (convertRef0 : Ref → Jl T) (sub0 : X → T → Jl V0) (typeOf0 : V0 → V1) (sub1 : X → Ref → Jl V2) (negate0 : Step → Jl V3) (makeTypedStepRangeLen0 : V1 → V2 → V3 → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← convertRef0 r.ref
  let v1 ← sub0 x v0
  let v2 := typeOf0 v1
  let v3 ← sub1 x r.ref
  let v4 ← negate0 r.step
  makeTypedStepRangeLen0 v2 v3 v4 r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1210-1210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::LinRange, x::Number) = LinRange(r.start - x, r.stop - x, length(r))
```
-/
def m1210 {R T X Out V Len : Type} (start stop : R → T) (length : R → Len)
    (sub : T → X → Jl V) (makeLinRange : V → V → Len → Jl Out)
    (r : R) (x : X) : Jl Out := do
  let a ← sub (start r) x
  let b ← sub (stop r) x
  makeLinRange a b (length r)
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1211-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::LinRange) = LinRange(x - r.start, x - r.stop, length(r))
```
-/
def m1211 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (sub0 : X → T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← sub0 x r.start
  let v1 ← sub0 x r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1212-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r1::AbstractRange, r2::AbstractRange) = r1 - r2
```
-/
def m1212 {ε A B Out : Type} (sub : A → B → Except ε Out) (r1 : A) (r2 : B) :
    Except ε Out := sub r1 r2
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1215-1215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::Number, r::AbstractRange) = StepRangeLen(x*first(r), x*step(r), length(r))
```
-/
def m1215 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (mul0 : X → T → Jl V0) (mul1 : X → Step → Jl V1) (makeStepRangeLen0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← mul0 x r.first
  let v1 ← mul1 x r.step
  makeStepRangeLen0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1216-1217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::Number, r::StepRangeLen{T}) where {T} =
    StepRangeLen{typeof(x*T(r.ref))}(x*r.ref, x*r.step, length(r), r.offset)
```
-/
def m1216 {R T Ref Step X Out V0 V1 V2 V3 Len Offset : Type}
    (ref : R → Ref) (step : R → Step) (length : R → Len) (offset : R → Offset)
    (convertRef : Ref → Jl T) (mul : X → T → Jl V0) (typeOf : V0 → V1)
    (mulRef : X → Ref → Jl V2) (mulStep : X → Step → Jl V3)
    (makeTypedStepRangeLen : V1 → V2 → V3 → Len → Offset → Jl Out)
    (r : R) (x : X) : Jl Out := do
  let value ← convertRef (ref r)
  let product ← mul x value
  let elementType := typeOf product
  let newRef ← mulRef x (ref r)
  let newStep ← mulStep x (step r)
  makeTypedStepRangeLen elementType newRef newStep (length r) (offset r)
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1218-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::Number, r::LinRange) = LinRange(x * r.start, x * r.stop, r.len)
```
-/
def m1218 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (mul0 : X → T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← mul0 x r.start
  let v1 ← mul0 x r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1219-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::AbstractFloat, r::OrdinalRange) =
    Base.range_start_step_length(x*first(r), x*step(r), length(r))  # 0.2 .* (-2:2) needs TwicePrecision
```
-/
def m1219 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (mul0 : X → T → Jl V0) (mul1 : X → Step → Jl V1) (rangeStartStepLength0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← mul0 x r.first
  let v1 ← mul1 x r.step
  rangeStartStepLength0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1222-1222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::AbstractRange, x::Number) = StepRangeLen(first(r)*x, step(r)*x, length(r))
```
-/
def m1222 {R T Step X Out V0 V1 Len : Type}
    (first : R → T) (step : R → Step) (length : R → Jl Len)
    (mul : T → X → Jl V0) (mulStep : Step → X → Jl V1)
    (makeStepRangeLen : V0 → V1 → Len → Jl Out) (r : R) (x : X) : Jl Out := do
  let a ← mul (first r) x
  let s ← mulStep (step r) x
  let n ← length r
  makeStepRangeLen a s n
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1223-1224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::StepRangeLen{T}, x::Number) where {T} =
    StepRangeLen{typeof(T(r.ref)*x)}(r.ref*x, r.step*x, length(r), r.offset)
```
-/
def m1223 {T Ref Step X Out V0 V1 V2 V3 : Type} {Len Offset : Type}
    (convertRef0 : Ref → Jl T) (mul0 : T → X → Jl V0) (typeOf0 : V0 → V1) (mul1 : Ref → X → Jl V2) (mul2 : Step → X → Jl V3) (makeTypedStepRangeLen0 : V1 → V2 → V3 → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← convertRef0 r.ref
  let v1 ← mul0 v0 x
  let v2 := typeOf0 v1
  let v3 ← mul1 r.ref x
  let v4 ← mul2 r.step x
  makeTypedStepRangeLen0 v2 v3 v4 r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1225-1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::LinRange, x::Number) = LinRange(r.start * x, r.stop * x, r.len)
```
-/
def m1225 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (mul0 : T → X → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← mul0 r.start x
  let v1 ← mul0 r.stop x
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1226-1227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::OrdinalRange, x::AbstractFloat) =
    Base.range_start_step_length(first(r)*x, step(r)*x, length(r))
```
-/
def m1226 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (mul0 : T → X → Jl V0) (mul1 : Step → X → Jl V1) (rangeStartStepLength0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← mul0 r.first x
  let v1 ← mul1 r.step x
  rangeStartStepLength0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1230-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(/), r::AbstractRange, x::Number) = range(first(r)/x, step=step(r)/x, length=length(r))
```
-/
def m1230 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (div0 : T → X → Jl V0) (div1 : Step → X → Jl V1) (range0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← div0 r.first x
  let v1 ← div1 r.step x
  range0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1231-1232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(/), r::StepRangeLen{T}, x::Number) where {T} =
    StepRangeLen{typeof(T(r.ref)/x)}(r.ref/x, r.step/x, length(r), r.offset)
```
-/
def m1231 {R T Ref Step X Out V0 V1 V2 V3 Len Offset : Type}
    (ref : R → Ref) (step : R → Step) (length : R → Len) (offset : R → Offset)
    (convertRef : Ref → Jl T) (div : T → X → Jl V0) (typeOf : V0 → V1)
    (divRef : Ref → X → Jl V2) (divStep : Step → X → Jl V3)
    (makeTypedStepRangeLen : V1 → V2 → V3 → Len → Offset → Jl Out)
    (r : R) (x : X) : Jl Out := do
  let value ← convertRef (ref r)
  let quotient ← div value x
  let elementType := typeOf quotient
  let newRef ← divRef (ref r) x
  let newStep ← divStep (step r) x
  makeTypedStepRangeLen elementType newRef newStep (length r) (offset r)
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1233-1233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(/), r::LinRange, x::Number) = LinRange(r.start / x, r.stop / x, r.len)
```
-/
def m1233 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (div0 : T → X → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← div0 r.start x
  let v1 ← div0 r.stop x
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1235-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::AbstractRange) = range(x\first(r), step=x\step(r), length=length(r))
```
-/
def m1235 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (ldiv0 : X → T → Jl V0) (ldiv1 : X → Step → Jl V1) (range0 : V0 → V1 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← ldiv0 x r.first
  let v1 ← ldiv1 x r.step
  range0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) = StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)
```
-/
def m1236 {T Ref Step X Out V0 V1 : Type} {Len Offset : Type}
    (ldiv0 : X → Ref → Jl V0) (ldiv1 : X → Step → Jl V1) (makeStepRangeLen0 : V0 → V1 → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← ldiv0 x r.ref
  let v1 ← ldiv1 x r.step
  makeStepRangeLen0 v0 v1 r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::LinRange) = LinRange(x \ r.start, x \ r.stop, r.len)
```
-/
def m1237 {T Ref Step X Out V0 : Type} {Len Offset : Type}
    (ldiv0 : X → T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) (x : X) : Jl Out := do
  let v0 ← ldiv0 x r.start
  let v1 ← ldiv0 x r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1239-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::UnitRange) = big(r.start):big(last(r))
```
-/
def m1239 {T Ref Step Out V0 : Type} {Len Offset : Type}
    (big0 : T → Jl V0) (colon0 : V0 → V0 → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← big0 r.start
  let v1 ← big0 r.last
  colon0 v0 v1
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1240-1240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::StepRange) = big(r.start):big(r.step):big(last(r))
```
-/
def m1240 {T Ref Step Out V0 V1 : Type} {Len Offset : Type}
    (big0 : T → Jl V0) (big1 : Step → Jl V1) (colon0 : V0 → V1 → V0 → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← big0 r.start
  let v1 ← big1 r.step
  let v2 ← big0 r.last
  colon0 v0 v1 v2
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1241-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::StepRangeLen) = StepRangeLen(big(r.ref), big(r.step), length(r), r.offset)
```
-/
def m1241 {T Ref Step Out V0 V1 : Type} {Len Offset : Type}
    (big0 : Ref → Jl V0) (big1 : Step → Jl V1) (makeStepRangeLen0 : V0 → V1 → (Len) → (Offset) → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← big0 r.ref
  let v1 ← big1 r.step
  makeStepRangeLen0 v0 v1 r.len r.offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1242-1242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::LinRange) = LinRange(big(r.start), big(r.stop), length(r))
```
-/
def m1242 {T Ref Step Out V0 : Type} {Len Offset : Type}
    (big0 : T → Jl V0) (makeLinRange0 : V0 → V0 → (Len) → Jl Out)
    (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let v0 ← big0 r.start
  let v1 ← big0 r.stop
  makeLinRange0 v0 v1 r.len
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1245-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
    CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
```
-/
def m1245 {A X B Out : Type} (add : A → X → Jl B)
    (cartesianIndices : List B → Jl Out) (ranges : List A) (offsets : List X)
    (_sameRank : ranges.length = offsets.length) : Jl Out := do
  let shifted ← (ranges.zip offsets).mapM (fun pair => add pair.1 pair.2)
  cartesianIndices shifted
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1247-1248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
    I .+ j
```
-/
def m1247 {A X Out : Type} (broadcastAdd : A → X → Jl Out) (offset : X) (indices : A) : Jl Out :=
  broadcastAdd indices offset
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1249-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
    CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
```
-/
def m1249 {A X B Out : Type} (sub : A → X → Jl B)
    (cartesianIndices : List B → Jl Out) (ranges : List A) (offsets : List X)
    (_sameRank : ranges.length = offsets.length) : Jl Out := do
  let shifted ← (ranges.zip offsets).mapM (fun pair => sub pair.1 pair.2)
  cartesianIndices shifted
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1251-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
    diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
    Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
end
```
-/
def m1251 {T Ref Step X V Shifted Cart Out : Type} {Len Offset : Type}
    (sub : X → T → Jl V) (range : V → Len → Step → Jl Shifted)
    (cartesianIndices : List Shifted → Jl Cart) (reverse : Cart → Jl Out)
    (offsets : List X) (ranges : List (RangeView T Ref Step Len Offset))
    (_sameRank : offsets.length = ranges.length) : Jl Out := do
  let shifted ← (offsets.zip ranges).mapM fun pair => do
    let first ← sub pair.1 pair.2.last
    range first pair.2.len pair.2.step
  reverse (← cartesianIndices shifted)
end Range

namespace Range
/--
Julia source: base/broadcast.jl:1252-1252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
```
-/
def m1252 {T Ref Step X V Out : Type} {Len Offset : Type}
    (sub : X → T → Jl V) (range : V → Len → Step → Jl Out)
    (offset : X) (r : RangeView T Ref Step Len Offset) : Jl Out := do
  let first ← sub offset r.last
  range first r.len r.step
end Range

namespace Bits
/--
Julia source: base/broadcast.jl:1261-1261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    BitMaskedBitArray{N,M}(parent, mask) where {N,M} = new(parent, mask)
```
-/
def m1261 (parent : P) (mask : M) : BitMasked P M := ⟨parent, mask⟩
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1263-1266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function BitMaskedBitArray(parent::BitArray{N}, mask::BitArray{M}) where {N,M}
    @boundscheck checkbounds(parent, mask)
    BitMaskedBitArray{N,M}(parent, mask)
end
```
-/
def m1263 {H ε P M : Type} (checkbounds : P → M → StateT H (Except ε) Unit)
    (parent : P) (mask : M) : StateT H (Except ε) (BitMasked P M) := do
  checkbounds parent mask
  return ⟨parent, mask⟩
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds dotview(B::BitArray, i::BitArray) = BitMaskedBitArray(B, i)
```
-/
def m1267 {H ε P M : Type} (checkbounds : P → M → StateT H (Except ε) Unit)
    (parent : P) (mask : M) : StateT H (Except ε) (BitMasked P M) :=
  m1263 checkbounds parent mask
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
```
-/
def m1268 {H ε IO T P M R1 R2 : Type} (typeOf : BitMasked P M → T)
    (showType : IO → T → StateT H (Except ε) R1)
    (showPair : IO → P × M → StateT H (Except ε) R2)
    (io : IO) (value : BitMasked P M) : StateT H (Except ε) Unit := do
  let _ ← showType io (typeOf value)
  let _ ← showPair io (value.parent, value.mask)
  pure ()
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1270-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any,<:Any,typeof(identity),Tuple{Bool}}) = fill!(B, bc.args[1])
```
-/
def m1270 {D R : Type} (fill : D → Bool → R) (value : D) (bit : Bool) : R :=
  fill value bit
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1271-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any}) = materialize!(@inbounds(view(B.parent, B.mask)), bc)
```
-/
def m1271 {H ε P M View BC R : Type}
    (view : P → M → StateT H (Except ε) View)
    (materializeBang : View → BC → StateT H (Except ε) R)
    (value : BitMasked P M) (bc : BC) : StateT H (Except ε) R := do
  materializeBang (← view value.parent value.mask) bc
end Bits

namespace Bits
/--
Julia source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.fill!(B::BitMaskedBitArray, b::Bool)
    Bc = B.parent.chunks
    Ic = B.mask.chunks
    @inbounds if b
        for i = 1:length(Bc)
            Bc[i] |= Ic[i]
        end
    else
        for i = 1:length(Bc)
            Bc[i] &= ~Ic[i]
        end
    end
    return B
end
```
-/
def m1272 {H ε P M ParentChunks MaskChunks : Type}
    (parentChunks : P → StateT H (Except ε) ParentChunks)
    (maskChunks : M → StateT H (Except ε) MaskChunks)
    (length : ParentChunks → StateT H (Except ε) {n : I64 // 0 ≤ n.val})
    (getParent : ParentChunks → I64 → StateT H (Except ε) UInt64)
    (getMask : MaskChunks → I64 → StateT H (Except ε) UInt64)
    (setParent : ParentChunks → I64 → UInt64 → StateT H (Except ε) Unit)
    (value : BitMasked P M) (bit : Bool) : StateT H (Except ε) (BitMasked P M) := do
  let bc ← parentChunks value.parent
  let ic ← maskChunks value.mask
  if bit then
    let n ← length bc
    forChunkIndices (fun i => do
      let b ← getParent bc i
      let m ← getMask ic i
      setParent bc i (b ||| m)) n.val.val.toNat (int64 1)
  else
    let n ← length bc
    forChunkIndices (fun i => do
      let b ← getParent bc i
      let m ← getMask ic i
      setParent bc i (b &&& ~~~m)) n.val.val.toNat (int64 1)
  return value
end Bits

namespace Syntax
/--
Julia source: base/broadcast.jl:1297-1297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds dotview(args...) = Base.maybeview(args...)
```
-/
def m1297 {A R : Type} (maybeview : List A → R) (args : List A) : R := maybeview args
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1304-1304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dottable(x) = false # avoid dotting spliced objects (e.g. view calls inserted by @view)
```
-/
def m1304 {A : Type} (_value : A) : Bool := false
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1306-1306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dottable(x::Symbol) = (!isoperator(x) || first(string(x)) != '.' || x === :..) && x !== :(:)
```
-/
def m1306 (isoperator : String → Bool) (name : String) : Bool :=
  (!isoperator name || name.front ≠ '.' || name = "..") && name ≠ ":"
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1307-1307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dottable(x::Expr) = x.head !== :$
```
-/
def m1307 (head : String) (_args : List (Value L)) : Bool := head ≠ "$"
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1308-1308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
undot(x) = x
```
-/
def m1308 (value : Value L) : Value L := value
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1309-1317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function undot(x::Expr)
    if x.head === :.=
        Expr(:(=), x.args...)
    elseif x.head === :block # occurs in for x=..., y=...
        Expr(:block, Base.mapany(undot, x.args)...)
    else
        x
    end
end
```
-/
def m1309 (head : String) (args : List (Value L)) : Value L := undot (.expr head args)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1318-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__dot__(x) = x
```
-/
def m1318 (value : Value L) : Value L := value
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1319-1348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __dot__(x::Expr)
    dotargs = Base.mapany(__dot__, x.args)
    if x.head === :call && dottable(x.args[1])
        Expr(:., dotargs[1], Expr(:tuple, dotargs[2:end]...))
    elseif x.head === :comparison
        Expr(:comparison, (iseven(i) && dottable(arg) && arg isa Symbol && isoperator(arg) ?
                               Symbol('.', arg) : arg for (i, arg) in pairs(dotargs))...)
    elseif x.head === :$
        x.args[1]
    elseif x.head === :let # don't add dots to `let x=...` assignments
        Expr(:let, undot(dotargs[1]), dotargs[2])
    elseif x.head === :for # don't add dots to for x=... assignments
        Expr(:for, undot(dotargs[1]), dotargs[2])
    elseif x.head === :generator || x.head === :filter
        Expr(x.head, dotargs[1], map(undot, dotargs[2:end])...)
    elseif (x.head === :(=) || x.head === :function || x.head === :macro) &&
           Meta.isexpr(x.args[1], :call) # function or macro definition
        Expr(x.head, x.args[1], dotargs[2])
    elseif x.head === :(<:) || x.head === :(>:)
        tmp = x.head === :(<:) ? :.<: : :.>:
        Expr(:call, tmp, dotargs...)
    else
        head = String(x.head)::String
        if last(head) == '=' && first(head) != '.' || head == "&&" || head == "||"
            Expr(Symbol('.', head), dotargs...)
        else
            Expr(x.head, dotargs...)
        end
    end
end
```
-/
def m1319 (isoperator : String → Bool) (head : String) (args : List (Value L)) : SyntaxResult (Value L) :=
  dotSyntax isoperator (.expr head args)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1390-1392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro __dot__(x)
    esc(__dot__(x))
end
```
-/
def m1390 (isoperator : String → Bool) (escape : Value L → Value L) (value : Value L) : SyntaxResult (Value L) := do
  return escape (← dotSyntax isoperator value)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function broadcasted_kwsyntax(f, args...; kwargs...)
    if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
        return broadcasted(f, args...)
    else
        return broadcasted((args...) -> f(args...; kwargs...), args...)
    end
end
```
-/
def m1394 {F G A K R : Type} (broadcastedF : F → List A → R)
    (broadcastedClosure : G → List A → R) (capture : F → List K → G)
    (f : F) (args : List A) (kwargs : List K) : R :=
  if kwargs.isEmpty then broadcastedF f args
  else broadcastedClosure (capture f kwargs) args
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1401-1404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function broadcasted(f::F, args...) where {F}
    args′ = map(broadcastable, args)
    broadcasted(combine_styles(args′...), f, args′...)
end
```
-/
def m1401 {μ : Type → Type} [Monad μ] {F A B S R : Type}
    (broadcastable : A → μ B) (combineStyles : List B → μ S)
    (styled : S → F → List B → μ R) (f : F) (args : List A) : μ R := do
  let mapped ← args.mapM broadcastable
  let style ← combineStyles mapped
  styled style f mapped
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1409-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function broadcasted(f::F, arg1, args...) where {F}
    arg1′ = broadcastable(arg1)
    args′ = map(broadcastable, args)
    broadcasted(combine_styles(arg1′, args′...), f, arg1′, args′...)
end
```
-/
def m1409 {μ : Type → Type} [Monad μ] {F A B S R : Type}
    (broadcastable : A → μ B) (combineStyles : List B → μ S)
    (styled : S → F → List B → μ R) (f : F) (first : A) (rest : List A) : μ R := do
  let firstMapped ← broadcastable first
  let restMapped ← rest.mapM broadcastable
  let style ← combineStyles (firstMapped :: restMapped)
  styled style f (firstMapped :: restMapped)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1414-1419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function broadcasted(f::F, arg1, arg2, args...) where {F}
    arg1′ = broadcastable(arg1)
    arg2′ = broadcastable(arg2)
    args′ = map(broadcastable, args)
    broadcasted(combine_styles(arg1′, arg2′, args′...), f, arg1′, arg2′, args′...)
end
```
-/
def m1414 {μ : Type → Type} [Monad μ] {F A B S R : Type}
    (broadcastable : A → μ B) (combineStyles : List B → μ S)
    (styled : S → F → List B → μ R) (f : F) (first second : A) (rest : List A) : μ R := do
  let firstMapped ← broadcastable first
  let secondMapped ← broadcastable second
  let restMapped ← rest.mapM broadcastable
  let style ← combineStyles (firstMapped :: secondMapped :: restMapped)
  styled style f (firstMapped :: secondMapped :: restMapped)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1420-1420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline broadcasted(style::BroadcastStyle, f::F, args...) where {F} = Broadcasted(style, f, args)
```
-/
def m1420 {μ : Type → Type} [Monad μ] {S F A X : Type}
    (style : S) (f : F) (args : List A) : μ (Broadcasted S F A X) :=
  pure (Lazy.m176 style f args none)
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1452-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline (op::BroadcastFunction)(x...; kwargs...) = op.f.(x...; kwargs...)
```
-/
def m1452 {F A K R : Type} (broadcast : F → List A → List K → R)
    (op : BroadcastFunction F) (args : List A) (kwargs : List K) : R := broadcast op.f args kwargs
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1454-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, op::BroadcastFunction)
    print(io, BroadcastFunction, '(')
    show(io, op.f)
    print(io, ')')
    nothing
end
```
-/
def m1454 {F IO : Type} (print : IO → String → ShowResult IO)
    (showF : IO → F → ShowResult IO) (io : IO) (op : BroadcastFunction F) : ShowResult Unit := do
  let io ← print io "BroadcastFunction("
  let io ← showF io op.f
  let _ ← print io ")"
  pure ()
end Syntax

namespace Syntax
/--
Julia source: base/broadcast.jl:1460-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, ::MIME"text/plain", op::BroadcastFunction) = show(io, op)
```
-/
def m1460 {F : Type} (render : BroadcastFunction F → String) (op : BroadcastFunction F) : String := render op
end Syntax


namespace Sizes
open JuliaLean
abbrev Err := Shape.Error

abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

/--
Julia source: base/broadcast.jl:531-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a::Integer, b::Integer) = a == 1 ? b : (b == 1 ? a : (a == b ? a : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size; got a dimension with lengths ", a, " and ", b)))))
```
-/
def bcs1 (a b : I64) : R I64 :=
  (Shape.m531 a b).map (Sum.elim id id)


def ext (s : List I64) (d : Nat) : Int :=
  match s[d]? with
  | some x => x.val
  | none => 1

def maxLen (shapes : List (List I64)) : Nat := shapes.foldr (fun s m => max s.length m) 0

structure Ax where
  n : I64
  deriving DecidableEq, Repr

inductive Dim where
  | size (n : I64)
  | axis (a : Ax)
  deriving DecidableEq, Repr

def Dim.len : Dim → Int
  | .size n => n.val
  | .axis a => a.n.val

/--
Julia source: base/broadcast.jl:531-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_bcs1(a::Integer, b::Integer) = a == 1 ? b : (b == 1 ? a : (a == b ? a : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size; got a dimension with lengths ", a, " and ", b)))))
_bcs1(a::Integer, b) = a == 1 ? b : (first(b) == 1 && last(b) == a ? b : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size; got a dimension with lengths ", a, " and ", length(b)))))
_bcs1(a, b::Integer) = _bcs1(b, a)
_bcs1(a, b) = _bcsm(b, a) ? axistype(b, a) : _bcsm(a, b) ? axistype(a, b) : throw(DimensionMismatch(LazyString("arrays could not be broadcast to a common size: a has axes ", a, " and b has axes ", b)))
# _bcsm tests whether the second index is consistent with the first
_bcsm(a, b) = a == b || length(b) == 1
_bcsm(a, b::Number) = b == 1
_bcsm(a::Number, b::Number) = a == b || b == 1
```
-/
def bcs1Mixed : Dim → Dim → R Dim
  | .size a, .axis b =>
      (Shape.m532 (fun _ => i64 1) Ax.n a b).map Dim.axis
  | .axis b, .size a =>
      (Shape.m533 (fun _ => i64 1) Ax.n b a).map Dim.axis
  | .size a, .size b => (bcs1 a b).map Dim.size
  | .axis a, .axis b =>
      (Shape.m534 Shape.Error.dimensionMismatch
        (Shape.m536 (m := Id) (fun a b => pure (a = b)) (fun a => pure (Ax.n a))
          (fun n => pure (n.val == 1)) pure true) (Shape.m536 (m := Id) (fun a b => pure (a = b)) (fun a => pure (Ax.n a))
          (fun n => pure (n.val == 1)) pure true)
        Shape.m542 Shape.m542 a b).map Dim.axis


end Sizes




namespace Style
/-- Julia's BroadcastStyle type parameters, separate from the style value. -/
inductive StyleType where
  | abstractArray (rank : Nat)
  | tuple
  | other
  deriving DecidableEq, Repr

/-- A style value whose Julia type is recorded in its Lean type. In particular,
AbstractArrayStyle{0} cannot be selected by passing a separate runtime rank. -/
structure TypedStyle (type : StyleType) (Payload : Type) where
  value : Payload
  deriving DecidableEq, Repr
end Style

namespace Lazy
/-- Trusted method dispatch for instantiate. The style type and Nothing/axes
variant select the installed overload before any combine/check operation. -/
def instantiateByStyle {m : Type → Type} [Monad m] {family : Style.StyleType}
    {S F Args Axis : Type}
    (combineAxes : Args → m (List Axis)) (checkAxes : List Axis → Args → m Unit)
    (bc : Broadcasted (Style.TypedStyle family S) F Args (Option (List Axis))) :
    m (Broadcasted (Style.TypedStyle family S) F Args (Option (List Axis))) :=
  match family with
  | .abstractArray 0 => pure (m319 bc)
  | .tuple => do
      match bc.axes with
      | none => pure (m321 bc)
      | some axes =>
          let _ ← m322 checkAxes (m176 bc.style bc.f bc.args axes)
          pure bc
  | _ => m310 combineAxes checkAxes bc
end Lazy

namespace Material
/-
Trusted AbstractArrayStyle copy dispatcher: the zero-rank branch selects this method.
Julia source: base/broadcast.jl:942-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline copy(bc::Broadcasted{<:AbstractArrayStyle{0}}) = bc[CartesianIndex()]
```
-/
/--
Trusted AbstractArrayStyle copy dispatcher: the nonzero branch selects this method; the callback count now uses native Int.
Julia source: base/broadcast.jl:948-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function copy(bc::Broadcasted)
    ElType = result_eltype(bc)
    if Base.isconcretetype(ElType)
        # We can trust it and defer to the simpler `copyto!`
        return copyto!(similar(bc, ElType), bc)
    end
    # When ElType is not concrete, use narrowing. Use the first output
    # value to determine the starting output eltype; copyto_nonleaf!
    # will widen `dest` as needed to accommodate later values.
    bc′ = preprocess(nothing, bc)
    iter = eachindex(bc′)
    y = iterate(iter)
    if y === nothing
        # if empty, take the ElType at face value
        return similar(bc′, ElType)
    end
    # Initialize using the first value
    I, state = y
    @inbounds val = bc′[I]
    dest = similar(bc′, typeof(val))
    @inbounds dest[I] = val
    # Now handle the remaining values
    # The typeassert gives inference a helping hand on the element type and dimensionality
    # (work-around for #28382)
    ElType′ = ElType === Union{} ? Any : ElType <: Type ? Type : ElType
    RT = dest isa AbstractArray ? AbstractArray{<:ElType′, ndims(dest)} : Any
    return copyto_nonleaf!(dest, bc′, iter, state, 1)::RT
end
```
-/
def copyArrayStyle {m : Type → Type} [Monad m] {rank : Nat}
    {S F Args Axis D Index V Iter State Ty TyVar NDim : Type}
    (getZero : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → m V)
    (resultEltype : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → m Ty)
    (isConcreteType : Ty → m Bool)
    (similar : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → Ty → m D)
    (copyto : D → Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → m D)
    (preprocess : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → m (Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis))))
    (eachindex : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → m Iter)
    (iterate : Iter → m (Option (Index × State)))
    (getindexInbounds : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → Index → m V)
    (typeOf : V → m Ty) (setindexInbounds : D → Index → V → m Unit)
    (identicalType subtypeType : Ty → Ty → m Bool)
    (bottomType anyType typeType : Ty)
    (isaAbstractArray : D → m Bool)
    (newUpperTypeVar : Ty → m TyVar) (ndimsDest : D → m NDim)
    (applyAbstractArray : TyVar → NDim → m Ty) (unionAll : TyVar → Ty → m Ty)
    (nonleaf : D → Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis)) → Iter → State → JInt64 → m D)
    (typeassertReturn : D → Ty → m D)
    (bc : Lazy.Broadcasted (Style.TypedStyle (.abstractArray rank) S) F Args (Option (List Axis))) : m (Sum V D) :=
  if rank = 0 then Sum.inl <$> m942 getZero bc
  else Sum.inr <$> m948 resultEltype isConcreteType similar copyto preprocess eachindex iterate
    getindexInbounds typeOf setindexInbounds identicalType subtypeType bottomType anyType typeType
    isaAbstractArray newUpperTypeVar ndimsDest applyAbstractArray unionAll nonleaf typeassertReturn bc
end Material

end JuliaLean.base.broadcast

namespace JuliaLean.base.broadcast.Models1Group12

/-!
## Models batch 1, group 12: closed scalar-destination dispatch

These additions leave all numbered baseline declarations unchanged. Method names
refer to the selected Julia overload; Julia's dispatch itself remains trusted.
-/

/-- Scalar destinations cannot receive broadcast assignment. This closes the
existing internal error call by using `Material.m937`, rather than a supplied
implementation of `_throw_unwritable_dest`.
Julia source: base/broadcast.jl:936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
The existing error representation records the exception class, not its message.
-/
-- Source: base/broadcast.jl:936-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- materialize!(dest::Union{BroadcastScalars,Number,AbstractChar}, bc::Broadcasted{<:Any}) = _throw_unwritable_dest(dest)
-- /Source
def m936 {D S F A X : Type} (dest : D) (_bc : Lazy.Broadcasted S F A X) :
    Material.Result Unit :=
  Material.m937 dest

end JuliaLean.base.broadcast.Models1Group12

namespace JuliaLean.base.broadcast.Models1Group12

open JuliaLean

/-!
## Closed chunk-function objects and their BitInteger applications

The source returns first-class generic function objects or one of five
capture-free comparison closures. The code below represents their distinct
identities; it does not assume a supplied function callback is correct.

`chunkUnaryBitInteger` and `chunkBinaryBitInteger` are deliberately partial
application interfaces. `none` means this interface does not model that arity;
it is not a Julia value, error, or nontermination outcome. Their implemented
branches cover all same-type BitInteger widths, and use the existing callable
integer and Boolean combinator models. Mixed types, extensible Julia methods,
and further arities remain outside this application interface.
-/

/-- Distinct returned function objects at base/broadcast.jl:1084-1096.
Global objects retain their identity independently of the application arities
implemented below; the five anonymous closures have distinct source identities.
-/
-- Source: base/broadcast.jl:1084-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(&), typeof(*), typeof(min)}, args) = &
-- _chunkop(::Union{typeof(|), typeof(max)}, args) = |
-- _chunkop(::typeof(xor), args) = xor
-- _chunkop(::typeof(nand), args) = nand
-- _chunkop(::typeof(nor), args) = nor
-- _chunkop(::Union{typeof(~), typeof(!)}, args) = ~
-- _chunkop(::typeof(identity), args) = identity
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
inductive ChunkFunctionCode where
  | andGlobal | orGlobal | xorGlobal | nandGlobal | norGlobal
  | notGlobal | identityGlobal
  | equalClosure | lessClosure | lessEqualClosure | greaterClosure | greaterEqualClosure
  deriving Repr, DecidableEq

/-- Closed function-object binding for base/broadcast.jl:1084.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1084-1084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(&), typeof(*), typeof(min)}, args) = &
-- /Source
def m1084 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1084 ChunkFunctionCode.andGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1085.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1085-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(|), typeof(max)}, args) = |
-- /Source
def m1085 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1085 ChunkFunctionCode.orGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1086.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1086-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(xor), args) = xor
-- /Source
def m1086 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1086 ChunkFunctionCode.xorGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1087.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1087-1087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(nand), args) = nand
-- /Source
def m1087 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1087 ChunkFunctionCode.nandGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1088.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1088-1088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(nor), args) = nor
-- /Source
def m1088 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1088 ChunkFunctionCode.norGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1089.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1089-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(~), typeof(!)}, args) = ~
-- /Source
def m1089 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1089 ChunkFunctionCode.notGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1090.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1090-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(identity), args) = identity
-- /Source
def m1090 {Marker Args : Type} (f : Marker) (args : Args) : ChunkFunctionCode :=
  Bits.m1090 ChunkFunctionCode.identityGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1091.
The returned capture-free closure is identified here; its existing source body
is bound to concrete BitInteger callees in `chunkBinaryBitInteger`.
-/
-- Source: base/broadcast.jl:1091-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- /Source
def m1091 {A B : Type} (_args : A × B) : ChunkFunctionCode := .equalClosure

/-- Closed function-object binding for base/broadcast.jl:1092.
Reuses the existing numbered selection body with the actual global function
identity. `Marker` represents the already-selected Julia function singleton.
-/
-- Source: base/broadcast.jl:1092-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- /Source
def m1092 {Marker A B : Type} (f : Marker) (args : A × B) : ChunkFunctionCode :=
  Bits.m1092 ChunkFunctionCode.xorGlobal f args

/-- Closed function-object binding for base/broadcast.jl:1093.
The returned capture-free closure is identified here; its existing source body
is bound to concrete BitInteger callees in `chunkBinaryBitInteger`.
-/
-- Source: base/broadcast.jl:1093-1093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- /Source
def m1093 {A B : Type} (_args : A × B) : ChunkFunctionCode := .lessClosure

/-- Closed function-object binding for base/broadcast.jl:1094.
The returned capture-free closure is identified here; its existing source body
is bound to concrete BitInteger callees in `chunkBinaryBitInteger`.
-/
-- Source: base/broadcast.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- /Source
def m1094 {A B : Type} (_args : A × B) : ChunkFunctionCode := .lessEqualClosure

/-- Closed function-object binding for base/broadcast.jl:1095.
The returned capture-free closure is identified here; its existing source body
is bound to concrete BitInteger callees in `chunkBinaryBitInteger`.
-/
-- Source: base/broadcast.jl:1095-1095 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- /Source
def m1095 {A B : Type} (_args : A × B) : ChunkFunctionCode := .greaterClosure

/-- Closed function-object binding for base/broadcast.jl:1096.
The returned capture-free closure is identified here; its existing source body
is bound to concrete BitInteger callees in `chunkBinaryBitInteger`.
-/
-- Source: base/broadcast.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
def m1096 {A B : Type} (_args : A × B) : ChunkFunctionCode := .greaterEqualClosure

/-- Effect adapter for the existing capture-free closure bodies at
base/broadcast.jl:1091-1096. The supplied call in each use below is a closed
application of existing models; this helper is not an unresolved Julia callee.
-/
-- Source: base/broadcast.jl:1091-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
def runChunkWord {t : IntTy} (call : StateT Unit Jl (JInt t)) : Jl (JInt t) :=
  (call ()).map Prod.fst

/-- Executable unary BitInteger applications of the functions selected at
base/broadcast.jl:1089-1090. Other application arities return `none` to report
missing interpreter coverage, never to simulate a Julia error. The identity
branch is the direct base/operators.jl:605 identity body; that source model's
module has no supplied prebuilt import, so no repository rebuild is attempted.
-/
-- Source: base/broadcast.jl:1089-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(~), typeof(!)}, args) = ~
-- _chunkop(::typeof(identity), args) = identity
-- /Source
-- Source: base/operators.jl:605-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- identity(@nospecialize x) = x
-- /Source
def chunkUnaryBitInteger {t : IntTy} (f : ChunkFunctionCode) (x : JInt t) :
    Option (Jl (JInt t)) :=
  match f with
  | .notGlobal => some (.ok (JuliaLean.base.int.bnot x))
  | .identityGlobal => some (.ok x)
  | _ => none

/-- Executable same-type BitInteger applications of the binary returned
functions at base/broadcast.jl:1084-1096. All ten integer types are admitted.
Existing numbered closure bodies enforce the order of complement and combination;
their callees are closed bindings to `base.int` models. Nand and nor reuse the
existing `base.bool` models, with all their callbacks likewise concretely bound.
`none` marks an application arity not implemented by this interface.
-/
-- Source: base/broadcast.jl:1084-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::Union{typeof(&), typeof(*), typeof(min)}, args) = &
-- _chunkop(::Union{typeof(|), typeof(max)}, args) = |
-- _chunkop(::typeof(xor), args) = xor
-- _chunkop(::typeof(nand), args) = nand
-- _chunkop(::typeof(nor), args) = nor
-- _chunkop(::Union{typeof(~), typeof(!)}, args) = ~
-- _chunkop(::typeof(identity), args) = identity
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
def chunkBinaryBitInteger {t : IntTy} (f : ChunkFunctionCode) (x y : JInt t) :
    Option (Jl (JInt t)) :=
  match f with
  | .andGlobal => some (.ok (JuliaLean.base.int.band x y))
  | .orGlobal => some (.ok (JuliaLean.base.int.bor x y))
  | .xorGlobal => some (.ok (JuliaLean.base.int.bxor x y))
  | .nandGlobal => some (JuliaLean.base.bool.nand
      (fun p : JInt t × JInt t => .ok (JuliaLean.base.int.band p.1 p.2))
      (fun a => .ok (JuliaLean.base.int.bnot a)) (x, y))
  | .norGlobal => some (JuliaLean.base.bool.nor
      (fun p : JInt t × JInt t => .ok (JuliaLean.base.int.bor p.1 p.2))
      (fun a => .ok (JuliaLean.base.int.bnot a)) (x, y))
  | .equalClosure => some (runChunkWord (Bits.m1091
      (fun a b => pure (JuliaLean.base.int.bxor a b))
      (fun a => pure (JuliaLean.base.int.bnot a)) () ((), ()) x y))
  | .lessClosure => some (runChunkWord (Bits.m1093
      (fun a => pure (JuliaLean.base.int.bnot a))
      (fun a b => pure (JuliaLean.base.int.band a b)) () ((), ()) x y))
  | .lessEqualClosure => some (runChunkWord (Bits.m1094
      (fun a => pure (JuliaLean.base.int.bnot a))
      (fun a b => pure (JuliaLean.base.int.bor a b)) () ((), ()) x y))
  | .greaterClosure => some (runChunkWord (Bits.m1095
      (fun a => pure (JuliaLean.base.int.bnot a))
      (fun a b => pure (JuliaLean.base.int.band a b)) () ((), ()) x y))
  | .greaterEqualClosure => some (runChunkWord (Bits.m1096
      (fun a => pure (JuliaLean.base.int.bnot a))
      (fun a b => pure (JuliaLean.base.int.bor a b)) () ((), ()) x y))
  | _ => none

end JuliaLean.base.broadcast.Models1Group12

namespace JuliaLean.base.broadcast.Models1Group12

open JuliaLean

/-!
## Closed chunk-argument lifting

`ChunkRef` is the identity of a `Vector{UInt64}` object. It is carried as data,
never dereferenced or copied. These methods inspect only the `chunks` field of
BitArray arguments, so all dimensions, stored bits, and distinct parent-array
identities may vary independently of that field. Other Julia values share the
`unsupported` tag because the only observation made of them here is failed
method dispatch. No supplied operation stands in for a missing callee.
-/

/-- Relevant stored field of a BitArray at base/broadcast.jl:1114.
The field is a chunks-vector object reference, not a copy of its contents. -/
-- Source: base/broadcast.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- /Source
structure LiftBitArray (ChunkRef : Type) where
  chunks : ChunkRef

/-- Complete dispatch classes observed by liftchunks at
base/broadcast.jl:1113-1116. `unsupported` covers every non-BitArray/non-Bool
argument value, including nested Broadcasted objects. -/
-- Source: base/broadcast.jl:1113-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(::Tuple{}) = ()
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- # Transform scalars to repeated scalars the size of a chunk
-- liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
-- /Source
inductive LiftChunksInput (ChunkRef : Type) where
  | bitarray (array : LiftBitArray ChunkRef)
  | boolean (value : Bool)
  | unsupported

/-- Output slots at base/broadcast.jl:1114-1116: retained chunks-vector object
references or native UInt64 scalar values. -/
-- Source: base/broadcast.jl:1114-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- # Transform scalars to repeated scalars the size of a chunk
-- liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
-- /Source
inductive LiftChunksOutput (ChunkRef : Type) where
  | chunks (reference : ChunkRef)
  | word (value : JInt .u64)

/-- Tail of a constructible source argument tuple for either nonempty overload
at base/broadcast.jl:1114 or 1116. The additional head is included in the bound.
This is a representation invariant, not a success or compatibility premise;
the values may include unsupported elements and all chunk-reference aliases. -/
-- Source: base/broadcast.jl:1114-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- # Transform scalars to repeated scalars the size of a chunk
-- liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
-- /Source
structure LiftChunksTail (ChunkRef : Type) where
  values : List (LiftChunksInput ChunkRef)
  lengthFits : (values.length : Int) + 1 ≤ IntTy.max .i64

/-- Concrete structural dispatch for recursive calls of liftchunks.
Julia source: base/broadcast.jl:1113-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
The empty overload is the installed Bits.m1113. A failed dispatch raises the
existing MethodError class. Nat recursion is only Lean structural recursion;
no Julia length/index arithmetic is replaced with Nat. All external entry
points below enforce a constructible native-Int tuple length.
-/
-- Source: base/broadcast.jl:1113-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(::Tuple{}) = ()
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- # Transform scalars to repeated scalars the size of a chunk
-- liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
-- /Source
private def liftChunksList {ChunkRef : Type} :
    List (LiftChunksInput ChunkRef) → Jl (List (LiftChunksOutput ChunkRef))
  | [] => do
      let _ ← Bits.m1113 (H := Unit) (ε := JlError) () ()
      pure []
  | .bitarray array :: rest => do
      let first := array.chunks
      let suffix ← liftChunksList rest
      pure (.chunks first :: suffix)
  | .boolean value :: rest => do
      let maximum := JInt.typemax .u64
      let zero := JInt.lit .u64 0
      let first := if value then maximum else zero
      let suffix ← liftChunksList rest
      pure (.word first :: suffix)
  | .unsupported :: _ => .error (.methodError "liftchunks")

/-- Preserve the first BitArray's chunks object and lift its remaining
arguments in source order, propagating any unsupported-tail dispatch error.
Julia source: base/broadcast.jl:1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/broadcast.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(args::Tuple{<:BitArray,Vararg{Any}}) = (args[1].chunks, liftchunks(tail(args))...)
-- /Source
def m1114 {ChunkRef : Type} (head : LiftBitArray ChunkRef)
    (tail : LiftChunksTail ChunkRef) : Jl (List (LiftChunksOutput ChunkRef)) := do
  let first := head.chunks
  let suffix ← liftChunksList tail.values
  pure (.chunks first :: suffix)

/-- Expand the Boolean head into a native UInt64 word, then lift the remaining
arguments in source order. Both constant operands of Julia's eager ifelse are
formed before selection; neither can fail or mutate memory.
Julia source: base/broadcast.jl:1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/broadcast.jl:1116-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftchunks(args::Tuple{<:Bool,Vararg{Any}}) = (ifelse(args[1], typemax(UInt64), UInt64(0)), liftchunks(tail(args))...)
-- /Source
def m1116 {ChunkRef : Type} (head : Bool)
    (tail : LiftChunksTail ChunkRef) : Jl (List (LiftChunksOutput ChunkRef)) := do
  let maximum := JInt.typemax .u64
  let zero := JInt.lit .u64 0
  let first := if head then maximum else zero
  let suffix ← liftChunksList tail.values
  pure (.word first :: suffix)

end JuliaLean.base.broadcast.Models1Group12

namespace JuliaLean.base.broadcast.Models1Group12

/-- The dimension-mismatch path always throws the existing DimensionMismatch
exception class. Julia stores the diagnostic arguments in LazyString without
printing them: base/strings/lazy.jl:36-43 and base/array.jl:11-13. As with the
installed Material.m937 and m943, this error representation omits the message.
Julia source: base/broadcast.jl:1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
-- Source: base/broadcast.jl:1133-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline throwdm(axdest, axsrc) =
--     throw(DimensionMismatch(LazyString("destination axes ", axdest, " are not compatible with source axes ", axsrc)))
-- /Source
def m1133 {A B R : Type} (_destAxes : A) (_sourceAxes : B) : Material.Result R :=
  .error .dimensionMismatch

end JuliaLean.base.broadcast.Models1Group12

namespace JuliaLean.base.broadcast.Models1Group11

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The four type parameters of the selected `Broadcasted` type. The values are
runtime type objects, not callbacks and not asserted constructor results. -/
structure BroadcastedParameters (L : Type) where
  style : Value L
  axes : Value L
  function : Value L
  arguments : Value L

/-- Invoke the actual selected ArrayStyle{A} type with no arguments.
The Val argument and its parameter are ignored. A specialized zero-argument
constructor for a user array family may throw, mutate, diverge, or return a
different type; all those outcomes remain in the installed runtime boundary.
The fixed selected type object already contains the source parameter A.
Julia source: base/broadcast.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ArrayStyle{A}(::Val) where A = ArrayStyle{A}()
-- /Source
def arrayStyleValRuntime {W L : Type} (ops : CoreOps W L)
    (arrayStyleType : Value L) (_val : Value L) : CoreM W L (Value L) :=
  ops.call arrayStyleType []

/-- Retain the actual Julia Val type parameter N while applying the
fixed Base.Broadcast.DefaultArrayStyle type constructor and invoking the result.
The source binding is a runtime type value, not an invented Core constant.
N is not restricted or coerced to Nat, Int64 or the baseline Rank carrier.
Unit represents the zero fields of the Val{N} instance, with its type parameter
recorded separately. Type-application failures precede arbitrary constructor
effects; no constructor-return type assertion is introduced.
Julia source: base/broadcast.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- DefaultArrayStyle(::Val{N}) where N = DefaultArrayStyle{N}()
-- /Source
def defaultArrayStyleValRuntime {W L : Type} (ops : CoreOps W L)
    (defaultArrayStyleType dimension : Value L) (_val : Unit) : CoreM W L (Value L) := do
  let constructor ← ops.applyType defaultArrayStyleType [dimension]
  ops.call constructor []

/-- The selected AbstractArray type's actual N parameter determines the
type application and zero-argument construction. Its element type and concrete
array family are ignored. Reusing the identical constructor protocol at line98
is a Lean helper call and introduces no Julia Val allocation. Specialized user
constructors and unusual valid Julia type parameters remain at their existing
runtime boundaries, with no pure default-style approximation.
Julia source: base/broadcast.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::Type{<:AbstractArray{T,N}}) where {T,N} = DefaultArrayStyle{N}()
-- /Source
def broadcastStyleArrayTypeRuntime {W L : Type} (ops : CoreOps W L)
    (defaultArrayStyleType dimension : Value L) (_arrayType : Value L) :
    CoreM W L (Value L) :=
  defaultArrayStyleValRuntime ops defaultArrayStyleType dimension ()

/-- Invoke the actual selected zero-argument constructor. `S` is the source
method's type parameter, supplied by trusted dispatch; the two operands do not
determine a replacement constructor result. Exceptions, divergence, and world
changes stay in the installed runtime effect. No return-type assertion occurs
in this Julia body.
Julia source: base/broadcast.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::S, ::S) where S<:BroadcastStyle = S() # homogeneous types preserved
-- /Source
def broadcastStyleSame {W L : Type} (ops : CoreOps W L)
    (S : Value L) (_left _right : Value L) : CoreM W L (Value L) :=
  ops.call S []

/-- The selected style constructor is evaluated even when the right operand
is `Unknown`. Custom constructors remain at the existing `CoreOps.call`
boundary; their result is not assumed to equal the left operand.
Julia source: base/broadcast.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::S, ::Unknown) where S<:BroadcastStyle = S()
-- /Source
def broadcastStyleUnknown {W L : Type} (ops : CoreOps W L)
    (S : Value L) (_left _unknown : Value L) : CoreM W L (Value L) :=
  ops.call S []

/-- Complete selected-constructor route for homogeneous ArrayStyle values.
The runtime type already contains the array-family parameter. Its actual
zero-argument method can be specialized for a user-owned family; retain every
return value, error, divergence and world change without a return-type assertion.
The pure family-preservation helper is explicitly only the default-constructor
subdomain, not a restriction on this runtime route.
Julia source: base/broadcast.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::A, ::A) where A<:ArrayStyle             = A()
-- /Source
def broadcastStyleArraySameRuntime {W L : Type} (ops : CoreOps W L)
    (arrayStyleType : Value L) (_left _right : Value L) : CoreM W L (Value L) :=
  ops.call arrayStyleType []

/-- Preserve arbitrary custom `AbstractArrayStyle` constructor effects.
`A` is selected type metadata, and the returned value is deliberately not
restricted to that type: the Julia body contains no type assertion.
Julia source: base/broadcast.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::A, ::A) where A<:AbstractArrayStyle     = A()
-- /Source
def broadcastStyleAbstractSame {W L : Type} (ops : CoreOps W L)
    (A : Value L) (_left _right : Value L) : CoreM W L (Value L) :=
  ops.call A []

/-- Read the selected wrapper type's style parameter and invoke its
constructor. Dispatch to this overload excludes every Style parameter S with
S <: Union{Nothing,Unknown}, including union and bottom type parameters, which
have the existing error overload. Other wrapper type parameters are ignored,
and no constructor-result type assertion is silently inserted.
Julia source: base/broadcast.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/broadcast.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::Type{<:Broadcasted{Style}}) where {Style} = Style()
-- /Source
def broadcastStyleOfBroadcastedType {W L : Type} (ops : CoreOps W L)
    (parameters : BroadcastedParameters L) : CoreM W L (Value L) :=
  ops.call parameters.style []

end JuliaLean.base.broadcast.Models1Group11



namespace JuliaLean.base.broadcast.Models2Group5.DefaultStyle

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The selected zero-argument constructor method for a runtime
`DefaultArrayStyle{N}` type. `builtin` selects the generated zero-field
constructor from base/broadcast.jl:97. `custom` selects an open user method
(or lets the existing runtime report a failed method dispatch).
This is method-selection metadata, not a replacement constructor body. -/
-- Source: base/broadcast.jl:97-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct DefaultArrayStyle{N} <: AbstractArrayStyle{N} end
-- DefaultArrayStyle(::Val{N}) where N = DefaultArrayStyle{N}()
-- DefaultArrayStyle{M}(::Val{N}) where {N,M} = DefaultArrayStyle{N}()
-- const DefaultVectorStyle = DefaultArrayStyle{1}
-- const DefaultMatrixStyle = DefaultArrayStyle{2}
-- BroadcastStyle(::Type{<:AbstractArray{T,N}}) where {T,N} = DefaultArrayStyle{N}()
-- BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
-- /Source
inductive ConstructorMethod where
  | builtin
  | custom

/-- Operations for the fallback at base/broadcast.jl:103. All primitives and
open calls use the installed CoreOps interface. The extra field is trusted
runtime dispatch metadata: selection occurs in the world at the constructor
call, after effects of ndims and type application, and has no effect itself. -/
-- Source: base/broadcast.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedConstructor : Value L → W → ConstructorMethod

/-- Fixed module bindings used by base/broadcast.jl:103. Values are passed
explicitly because Base.Broadcast bindings are not constants of Core. -/
-- Source: base/broadcast.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
-- /Source
structure Bindings (L : Type) where
  ndims : Value L
  defaultArrayStyle : Value L

/-- The zero-field constructor generated by the struct at
base/broadcast.jl:97. There are no field conversions or type assertions.
The installed new primitive retains runtime singleton identity, allocation
behavior, errors and the runtime world. The constructor-generation rule is
specified in doc/src/manual/constructors.md:329-342. -/
-- Source: base/broadcast.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct DefaultArrayStyle{N} <: AbstractArrayStyle{N} end
-- /Source
def defaultStyleNew {W L : Type} (ops : CoreOps W L)
    (appliedType : Value L) : CoreM W L (Value L) :=
  ops.new appliedType []

/-- Resolve the constructor call of base/broadcast.jl:103 at its actual
runtime world. The canonical Base constructor calls the explicit generated
constructor model. Only a selected custom method uses the open call boundary.
There is no additional type assertion on the returned value. -/
-- Source: base/broadcast.jl:97-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct DefaultArrayStyle{N} <: AbstractArrayStyle{N} end
-- DefaultArrayStyle(::Val{N}) where N = DefaultArrayStyle{N}()
-- DefaultArrayStyle{M}(::Val{N}) where {N,M} = DefaultArrayStyle{N}()
-- const DefaultVectorStyle = DefaultArrayStyle{1}
-- const DefaultMatrixStyle = DefaultArrayStyle{2}
-- BroadcastStyle(::Type{<:AbstractArray{T,N}}) where {T,N} = DefaultArrayStyle{N}()
-- BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
-- /Source
def callConstructor {W L : Type} (ops : Ops W L)
    (appliedType : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedConstructor appliedType world with
  | .builtin => defaultStyleNew ops.toCoreOps appliedType world
  | .custom => ops.call appliedType [] world

/-- The full selected fallback at base/broadcast.jl:103. `T` is a Julia type
value supplied by method dispatch. Because this method leaves T unspecified,
ndims remains an open dispatched call with its exact argument. Its result is
an unrestricted Julia value: invalid type parameters fail at applyType,
without truncation to Nat, Int64, or the older Rank carrier. The final
constructor is selected only after those preceding operations finish.
Other BroadcastStyle overloads are separate methods, not alternate bodies of
this selected fallback. Errors, divergence and worlds use CoreM unchanged. -/
-- Source: base/broadcast.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(::Type{T}) where {T} = DefaultArrayStyle{ndims(T)}()
-- /Source
def fallback {W L : Type} (ops : Ops W L)
    (bindings : Bindings L) (T : Value L) : CoreM W L (Value L) := do
  let dimension ← ops.call bindings.ndims [T]
  let appliedType ← ops.applyType bindings.defaultArrayStyle [dimension]
  callConstructor ops appliedType

end JuliaLean.base.broadcast.Models2Group5.DefaultStyle


/- MODEL FRAGMENT: append after Models2Group5.DefaultStyle. -/
namespace JuliaLean.base.broadcast.Models2Group5.Constructors

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The already-supplied heterogeneous Julia argument tuple of
base/broadcast.jl:181. The equality is its native-Int length invariant, not a
success premise. Each Value may retain a mutable reference or an arbitrary
user object. `CoreOps.tuple` embeds these immutable slots as their tuple value;
this representation step is not an extra Julia allocation by the method. The stored tuple field count also fits UInt32, matching the DataTypeLayout
representation invariant at base/runtime_internals.jl:624-626. -/
-- Source: base/broadcast.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Broadcasted(f::F, args::Tuple, axes=nothing) where {F}
--         Broadcasted(combine_styles(args...)::BroadcastStyle, f, args, axes)
--     end
-- /Source
structure ArgumentTuple (L : Type) where
  values : List (Value L)
  fieldCountFits : values.length ≤ IntTy.u32.max.toNat
  size : JInt .i64
  size_eq : size.val = (values.length : Int)

/-- Fixed module bindings for the source constructor at base/broadcast.jl:181.
They are named Julia function/type values, not precomputed callee answers. -/
-- Source: base/broadcast.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Broadcasted(f::F, args::Tuple, axes=nothing) where {F}
--         Broadcasted(combine_styles(args...)::BroadcastStyle, f, args, axes)
--     end
-- /Source
structure Bindings (L : Type) where
  broadcasted : Value L
  broadcastStyle : Value L
  combineStyles : Value L
  defaultArrayStyle : Value L

/-- The concrete nullary combine_styles dependency at base/broadcast.jl:431.
The rank is the Julia Int literal zero. Reuse the group-specific complete
generated-constructor model, including actual constructor selection at its
call world; no callback replaces the known nullary method's body. The older
Style.m431 only encodes a closed Style marker and has no runtime type/value
representation, so it cannot supply this effectful bridge. -/
-- Source: base/broadcast.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles() = DefaultArrayStyle{0}()
-- /Source
def combineEmpty {W L : Type} (ops : DefaultStyle.Ops W L)
    (defaultArrayStyle : Value L) : CoreM W L (Value L) := do
  let constructor ← ops.applyType defaultArrayStyle
    [JuliaLean.base.boot.intV ops.toCoreOps (JInt.lit .i64 0)]
  DefaultStyle.callConstructor ops constructor

/-- Dispatch the splatted style query of base/broadcast.jl:181. A nonempty
argument tuple dispatches on its unfixed component types, so that selected
callee is retained at the existing CoreOps.call boundary under the packet's
dispatch-parameter rule. The zero-argument call has no such type-dependent
selection and uses its explicit Base body. Tuple splatting is the slots in
source order, with no invented element conversion or element evaluation. -/
-- Source: base/broadcast.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Broadcasted(f::F, args::Tuple, axes=nothing) where {F}
--         Broadcasted(combine_styles(args...)::BroadcastStyle, f, args, axes)
--     end
-- /Source
def inferStyle {W L : Type} (ops : DefaultStyle.Ops W L)
    (bindings : Bindings L) (args : ArgumentTuple L) : CoreM W L (Value L) :=
  match args.values with
  | [] => combineEmpty ops bindings.defaultArrayStyle
  | _ :: _ => ops.call bindings.combineStyles args.values

/-- Full selected inferred-style constructor at base/broadcast.jl:181-183.
It first resolves the splatted argument styles, performs the source's exact
BroadcastStyle assertion, then invokes the selected four-argument constructor.
That last target is open dispatch: the style, F, heterogeneous Args, and Axes
types are not fixed by this source method. In particular, a custom constructor
may return a non-Broadcasted value, throw, mutate or diverge; no field or
return-type law is imposed. This is not a callback replacing this method's
own body, or a callback on an already-fixed concrete Broadcasted type.
The omitted axes argument is represented by the existing runtime nothing value.
The source's f and argument references are forwarded without scalar evaluation
by this body; effects performed inside selected callees remain arbitrary. -/
-- Source: base/broadcast.jl:181-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Broadcasted(f::F, args::Tuple, axes=nothing) where {F}
--         Broadcasted(combine_styles(args...)::BroadcastStyle, f, args, axes)
--     end
-- /Source
def inferred {W L : Type} (ops : DefaultStyle.Ops W L)
    (bindings : Bindings L) (f : Value L) (args : ArgumentTuple L)
    (axes : Value L) : CoreM W L (Value L) := do
  let style ← inferStyle ops bindings args
  let style ← JuliaLean.base.boot.typeassert ops.toCoreOps style bindings.broadcastStyle
  ops.call bindings.broadcasted
    [style, f, JuliaLean.base.boot.tupleV ops.toCoreOps args.values, axes]

end JuliaLean.base.broadcast.Models2Group5.Constructors

namespace JuliaLean.base.broadcast.Models2Group5.StyleConversion

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual type arguments supplied by dispatch to base/broadcast.jl:215-216.
`style` is NewStyle; the remaining three are the original wrapper's declared
Axes, F and Args types, not types recomputed from property results. -/
-- Source: base/broadcast.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.convert(::Type{Broadcasted{NewStyle}}, bc::Broadcasted{<:Any,Axes,F,Args}) where {NewStyle,Axes,F,Args} =
--     Broadcasted{NewStyle,Axes,F,Args}(bc.f, bc.args, bc.axes)::Broadcasted{NewStyle,Axes,F,Args}
-- /Source
structure Parameters (L : Type) where
  style : Value L
  axes : Value L
  function : Value L
  arguments : Value L

/-- Fixed source bindings used by base/broadcast.jl:215-216. -/
-- Source: base/broadcast.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.convert(::Type{Broadcasted{NewStyle}}, bc::Broadcasted{<:Any,Axes,F,Args}) where {NewStyle,Axes,F,Args} =
--     Broadcasted{NewStyle,Axes,F,Args}(bc.f, bc.args, bc.axes)::Broadcasted{NewStyle,Axes,F,Args}
-- /Source
structure Bindings (L : Type) where
  broadcasted : Value L
  getproperty : Value L

/-- Full source expression at base/broadcast.jl:215-216. Evaluate the target
type, the three property accesses left to right, the selected constructor, and
then the independently evaluated assertion type. The installed typeassert
retains its exact TypeError and throw point. Property access and constructor
calls dispatch on unfixed wrapper/style/type parameters, so they use the
existing CoreOps.call boundary under the current packet rule. No law about a
custom property or constructor is assumed. The method does not inline the
separately selected constructor189, whose own new-lowering is a different task.
No return-field-preservation promise would hold for all allowed dispatchers. -/
-- Source: base/broadcast.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.convert(::Type{Broadcasted{NewStyle}}, bc::Broadcasted{<:Any,Axes,F,Args}) where {NewStyle,Axes,F,Args} =
--     Broadcasted{NewStyle,Axes,F,Args}(bc.f, bc.args, bc.axes)::Broadcasted{NewStyle,Axes,F,Args}
-- /Source
def convert {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (parameters : Parameters L)
    (bc : Value L) : CoreM W L (Value L) := do
  let target ← ops.applyType bindings.broadcasted
    [parameters.style, parameters.axes, parameters.function, parameters.arguments]
  let f ← ops.call bindings.getproperty [bc, .symbol "f"]
  let args ← ops.call bindings.getproperty [bc, .symbol "args"]
  let axes ← ops.call bindings.getproperty [bc, .symbol "axes"]
  let result ← ops.call target [f, args, axes]
  let assertedType ← ops.applyType bindings.broadcasted
    [parameters.style, parameters.axes, parameters.function, parameters.arguments]
  JuliaLean.base.boot.typeassert ops result assertedType

end JuliaLean.base.broadcast.Models2Group5.StyleConversion


namespace JuliaLean.base.broadcast.Models2Group5.ShortCircuit

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Distinct nominal identities of the capture-free source196/207 callables. Julia source: base/broadcast.jl:196,207. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
inductive ClosureName where
  | conjunction
  | disjunction
  deriving Repr, DecidableEq

/-- Fixed global broadcasted and actual source-function singleton embeddings. The latter is identity metadata, not a scalar answer or supplied lambda body. Julia source: base/broadcast.jl:196,207. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
structure Bindings (L : Type) where
  broadcasted : Value L
  functionValue : ClosureName → Value L

/-- Complete represented callable: source identity, actual runtime value and executable application at every constructible native tuple arity. No capture or supplied scalar callback is hidden in the selected outer method. Julia source: base/broadcast.jl:196,207. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
structure Closure (W L : Type) where
  name : ClosureName
  value : Value L
  invoke : Constructors.ArgumentTuple L → CoreM W L (Value L)

/-- The exact scalar short-circuit bodies preserve the selected original operand. Only the first operand enters Boolean context; a non-Bool raises TypeError(:if,"",Bool,left) in the unchanged world, even when the second operand is Bool. Both actual operands already exist when the lambda is called. Julia source: base/broadcast.jl:196,207; doc/src/manual/control-flow.md:377-395. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
def binary {W L : Type} (core : CoreOps W L) (name : ClosureName)
    (left right : Value L) : CoreM W L (Value L) :=
  let flag := match left with
    | .leaf value => core.asBool value
    | _ => none
  match flag, name with
  | some false, .conjunction => pure left
  | some true, .conjunction => pure right
  | some true, .disjunction => pure left
  | some false, .disjunction => pure right
  | none, _ => JuliaLean.base.boot.throwTypeError core "if" ""
      (JuliaLean.base.boot.coreV core "Bool") left

/-- Build the actual capture-free singleton callable, including its complete positional dispatch. Two arguments execute the explicit scalar body. Every other native-bounded arity throws MethodError for the exact callable and supplied tuple at the current world age, retaining failures or divergence of that runtime operation. Julia source: base/broadcast.jl:196,207. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
def closure {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (name : ClosureName) : Closure W L where
  name := name
  value := bindings.functionValue name
  invoke := fun arguments =>
    match arguments.values with
    | [left, right] => binary core name left right
    | _ => do
        let age ← core.worldAge
        JuliaLean.base.boot.throwObj core (.methodError (bindings.functionValue name)
          (JuliaLean.base.boot.tupleV core arguments.values)
          (JuliaLean.base.boot.intV core age))

/-- Existing runtime primitives plus the genuinely selected broadcasted target on unfixed a/b types. It receives the actual full callable identity and executable all-arity body, and may inspect or invoke it while retaining any effects, exceptions or divergence. There is no callee correctness law. Julia source: base/broadcast.jl:196,207. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  broadcasted : Closure W L → Value L → Value L → CoreM W L (Value L)

/-- Selected AndAnd body: one actual selected broadcasted invocation with its capture-free conjunction callable and unchanged arguments. Julia source: base/broadcast.jl:196. -/
-- Source: base/broadcast.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::AndAnd, a, b) = broadcasted((a, b) -> a && b, a, b)
-- /Source
def broadcastAnd {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (left right : Value L) : CoreM W L (Value L) :=
  ops.broadcasted (closure ops.toCoreOps bindings .conjunction) left right

/-- Selected OrOr body: one actual selected broadcasted invocation with its capture-free disjunction callable and unchanged arguments. Julia source: base/broadcast.jl:207. -/
-- Source: base/broadcast.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::OrOr, a, b) = broadcasted((a, b) -> a || b, a, b)
-- /Source
def broadcastOr {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (left right : Value L) : CoreM W L (Value L) :=
  ops.broadcasted (closure ops.toCoreOps bindings .disjunction) left right

end JuliaLean.base.broadcast.Models2Group5.ShortCircuit


namespace JuliaLean.base.broadcast.Models2Group5.Forward

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source bindings for the forwarding methods below. These are the actual
Base/Broadcast function and type objects, not replacement callees or answers.
The existing CoreOps.call boundary selects operations on the method's unfixed
parameterized Broadcasted type, returned values, or unconstrained dims.
A Value is used opaquely: mutable Julia inputs are represented by reference
leaves, and no input object is reconstructed or copied. Signature restrictions
are supplied by trusted Julia dispatch, as in the installed boot model.
Source reference: base/broadcast.jl:229. -/
-- Source: base/broadcast.jl:229-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.similar(bc::Broadcasted, ::Type{T}) where {T} = similar(bc, T, axes(bc))
-- Base.similar(::Broadcasted{DefaultArrayStyle{N}}, ::Type{ElType}, dims) where {N,ElType} =
--     similar(Array{ElType, length(dims)}, dims)
-- Base.similar(::Broadcasted{DefaultArrayStyle{N}}, ::Type{Bool}, dims) where N =
--     similar(BitArray, dims)
-- # In cases of conflict we fall back on Array
-- Base.similar(::Broadcasted{ArrayConflict}, ::Type{ElType}, dims) where ElType =
--     similar(Array{ElType, length(dims)}, dims)
-- Base.similar(::Broadcasted{ArrayConflict}, ::Type{Bool}, dims) =
--     similar(BitArray, dims)
-- 
-- @inline Base.axes(bc::Broadcasted) = _axes(bc, bc.axes)
-- _axes(::Broadcasted, axes::Tuple) = axes
-- @inline _axes(bc::Broadcasted, ::Nothing)  = combine_axes(bc.args...)
-- _axes(bc::Broadcasted{<:AbstractArrayStyle{0}}, ::Nothing) = ()
-- 
-- @inline Base.axes(bc::Broadcasted{<:Any, <:NTuple{N}}, d::Integer) where N =
--     d <= N ? axes(bc)[d] : OneTo(1)
-- 
-- BroadcastStyle(::Type{<:Broadcasted{Style}}) where {Style} = Style()
-- BroadcastStyle(::Type{<:Broadcasted{S}}) where {S<:Union{Nothing,Unknown}} =
--     throw(ArgumentError("Broadcasted{Unknown} wrappers do not have a style assigned"))
-- 
-- argtype(::Type{BC}) where {BC<:Broadcasted} = fieldtype(BC, :args)
-- argtype(bc::Broadcasted) = argtype(typeof(bc))
-- 
-- @inline Base.eachindex(bc::Broadcasted) = eachindex(IndexStyle(bc), bc)
-- @inline Base.eachindex(s::IndexStyle, bc::Broadcasted) = _eachindex(s, axes(bc))
-- _eachindex(::IndexCartesian, t::Tuple) = CartesianIndices(t)
-- _eachindex(s::IndexLinear, t::Tuple) = eachindex(s, LinearIndices(t))
-- _eachindex(::IndexLinear, t::Tuple{Any}) = t[1]
-- 
-- Base.IndexStyle(bc::Broadcasted) = IndexStyle(typeof(bc))
-- Base.IndexStyle(::Type{<:Broadcasted{<:Any,<:Tuple{Any}}}) = IndexLinear()
-- Base.IndexStyle(::Type{<:Broadcasted{<:Any}}) = IndexCartesian()
-- 
-- Base.LinearIndices(bc::Broadcasted{<:Any,<:Tuple{Any}}) = LinearIndices(axes(bc))::LinearIndices{1}
-- 
-- Base.ndims(bc::Broadcasted) = ndims(typeof(bc))
-- Base.ndims(::Type{<:Broadcasted{<:Any,<:NTuple{N,Any}}}) where {N} = N
-- Base.ndims(BC::Type{<:Broadcasted{<:Any,Nothing}}) = _maxndims(argtype(BC))
-- function Base.ndims(BC::Type{<:Broadcasted{<:AbstractArrayStyle{N},Nothing}}) where {N}
--     N isa Int ? N : _maxndims(argtype(BC))
-- end
-- _maxndims(::Type{Tuple{}}) = 0
-- _maxndims(::Type{Tuple{T}}) where {T} = T <: Tuple ? 1 : Int(ndims(T))::Int
-- function _maxndims(Args::Type{<:Tuple{T,Vararg}}) where {T}
--     m = T <: Tuple ? 1 : Int(ndims(T))::Int
--     n = _maxndims(Base.tuple_type_tail(Args))
--     max(m, n)
-- end
-- 
-- Base.size(bc::Broadcasted) = map(length, axes(bc))
-- Base.length(bc::Broadcasted) = prod(size(bc))
-- 
-- function Base.iterate(bc::Broadcasted)
--     iter = eachindex(bc)
--     iterate(bc, (iter,))
-- end
-- Base.@propagate_inbounds function Base.iterate(bc::Broadcasted, s)
--     y = iterate(s...)
--     y === nothing && return nothing
--     i, newstate = y
--     return (bc[i], (s[1], newstate))
-- end
-- 
-- Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
-- /Source
structure Bindings (L : Type) where
  similar : Value L
  bitArray : Value L
  axes : Value L
  axesHelper : Value L
  getproperty : Value L
  combineAxes : Value L
  argtype : Value L
  eachindex : Value L
  indexStyle : Value L
  eachindexHelper : Value L
  cartesianIndices : Value L
  linearIndices : Value L
  ndims : Value L
  size : Value L
  prod : Value L
  iterate : Value L

/-- The Boolean DefaultArrayStyle allocation adapter. Neither dims nor the
array rank parameter is narrowed. Although BitArray is a fixed UnionAll type
binding, the selected similar method also depends on the completely unspecified
dims type; that dispatched callee remains open under the packet's rule.
The unused wrapper is retained as an input solely to state noninterference.
Source reference: base/broadcast.jl:232. -/
-- Source: base/broadcast.jl:232-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.similar(::Broadcasted{DefaultArrayStyle{N}}, ::Type{Bool}, dims) where N =
--     similar(BitArray, dims)
-- /Source
def similarBooleanDefault {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (_bc dims : Value L) : CoreM W L (Value L) :=
  ops.call bindings.similar [bindings.bitArray, dims]

/-- The Boolean conflict-style allocation adapter has the same unrestricted
dims domain and open similar dispatch as source232. No allocation outcome,
exception, or default dimension is supplied by the wrapper itself.
Source reference: base/broadcast.jl:237. -/
-- Source: base/broadcast.jl:237-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.similar(::Broadcasted{ArrayConflict}, ::Type{Bool}, dims) =
--     similar(BitArray, dims)
-- /Source
def similarBooleanConflict {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (_bc dims : Value L) : CoreM W L (Value L) :=
  ops.call bindings.similar [bindings.bitArray, dims]

/-- Read the axes property through Julia's selected getproperty call, then
invoke the selected _axes method with that exact result and the original
wrapper. Broadcasted's type parameters are unfixed here, so specialized
property and _axes methods retain their actual errors and state effects.
No Option/List axis restriction or direct-field substitution is introduced.
Source reference: base/broadcast.jl:240. -/
-- Source: base/broadcast.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline Base.axes(bc::Broadcasted) = _axes(bc, bc.axes)
-- /Source
def axes {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let stored ← ops.call bindings.getproperty [bc, .symbol "axes"]
  ops.call bindings.axesHelper [bc, stored]

/-- The Nothing-axes overload first reads bc.args, then splats that returned
value. A custom property method may return any iterable or fail. The existing
Core builtin applyIterate receives the actual iterate binding and the argument
list [target function, iterable]; it preserves all splat errors and effects.
It is not a callback for combine_axes's own recursion or its body.
Source's more-specific zero-dimensional overload is a different method.
Source reference: base/broadcast.jl:242. -/
-- Source: base/broadcast.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _axes(bc::Broadcasted, ::Nothing)  = combine_axes(bc.args...)
-- /Source
def axesNothing {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
  ops.applyIterate bindings.iterate [bindings.combineAxes, arguments]

/-- The value-level argtype method queries the runtime type, never the current
args property's value or type. The type-level selected method may specialize
on the unfixed Broadcasted parameters; no fieldtype implementation is replaced
by a caller-supplied answer. The builtin typeof is the installed primitive.
Source reference: base/broadcast.jl:253. -/
-- Source: base/broadcast.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- argtype(bc::Broadcasted) = argtype(typeof(bc))
-- /Source
def argtype {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) :=
  ops.call bindings.argtype [.leaf (ops.typeOf bc)]

/-- Obtain the selected IndexStyle result before calling the selected
style-specific eachindex method. Custom traits may return arbitrary values,
throw, or change state; there is no silent restriction to two builtin tags.
The original wrapper is passed unchanged to both calls.
Source reference: base/broadcast.jl:255. -/
-- Source: base/broadcast.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline Base.eachindex(bc::Broadcasted) = eachindex(IndexStyle(bc), bc)
-- /Source
def eachindex {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.indexStyle [bc]
  ops.call bindings.eachindex [style, bc]

/-- Obtain axes before selecting _eachindex on the source style and exact
returned axis object. There is no assumption of one-based or ordinary axes,
and no coercion of custom axes into a native list.
Source reference: base/broadcast.jl:256. -/
-- Source: base/broadcast.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline Base.eachindex(s::IndexStyle, bc::Broadcasted) = _eachindex(s, axes(bc))
-- /Source
def eachindexByStyle {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (style bc : Value L) : CoreM W L (Value L) := do
  let actualAxes ← ops.call bindings.axes [bc]
  ops.call bindings.eachindexHelper [style, actualAxes]

/-- Forward the actual Tuple object to the CartesianIndices constructor.
Tuple element types are not fixed by this method, so selected construction
is an open dispatch target. Tuple identity and any nonstandard axis objects
are preserved; t is an opaque runtime tuple, not an unrestricted Lean list.
Source reference: base/broadcast.jl:257. -/
-- Source: base/broadcast.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _eachindex(::IndexCartesian, t::Tuple) = CartesianIndices(t)
-- /Source
def eachindexCartesian {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (t : Value L) : CoreM W L (Value L) :=
  ops.call bindings.cartesianIndices [t]

/-- Construct LinearIndices for the original tuple before dispatching
style-specific eachindex on the resulting object. Both calls may fail or
change state. The source IndexLinear singleton is passed to the second call;
no native range or List iterator is substituted.
Source reference: base/broadcast.jl:258. -/
-- Source: base/broadcast.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _eachindex(s::IndexLinear, t::Tuple) = eachindex(s, LinearIndices(t))
-- /Source
def eachindexLinear {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (style t : Value L) : CoreM W L (Value L) := do
  let indices ← ops.call bindings.linearIndices [t]
  ops.call bindings.eachindex [style, indices]

/-- The value trait delegates using the original wrapper's declared runtime
type, independently of its current field values. More-specific user type
traits are kept effectful and may return any value; no fixed IndexStyle
enumeration is imposed.
Source reference: base/broadcast.jl:261. -/
-- Source: base/broadcast.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.IndexStyle(bc::Broadcasted) = IndexStyle(typeof(bc))
-- /Source
def indexStyle {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) :=
  ops.call bindings.indexStyle [.leaf (ops.typeOf bc)]

/-- Keep the full constructor and final LinearIndices{1} assertion. The
assertion's type expression is evaluated after axes and construction. A
custom axes/constructor result is neither assumed one-dimensional nor coerced
to a List. TypeError is the installed Core assertion error, at the same point.
The numeric type parameter is a Julia native Int, not an unbounded Nat.
Source reference: base/broadcast.jl:265. -/
-- Source: base/broadcast.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.LinearIndices(bc::Broadcasted{<:Any,<:Tuple{Any}}) = LinearIndices(axes(bc))::LinearIndices{1}
-- /Source
def linearIndices {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let actualAxes ← ops.call bindings.axes [bc]
  let result ← ops.call bindings.linearIndices [actualAxes]
  let target ← ops.applyType bindings.linearIndices
    [JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
  JuliaLean.base.boot.typeassert ops result target

/-- Delegate dimensionality using typeof(bc), retaining arbitrary selected
ndims outcomes. The source does not assert Int or a nonnegative result, so
neither a Nat carrier nor a native-Int conversion is introduced.
Source reference: base/broadcast.jl:267. -/
-- Source: base/broadcast.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.ndims(bc::Broadcasted) = ndims(typeof(bc))
-- /Source
def ndims {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) :=
  ops.call bindings.ndims [.leaf (ops.typeOf bc)]

/-- Call size first and pass its exact returned value to prod. Both are
selected on types the method leaves unfixed, so custom size results, product
semantics, failures and state effects remain in CoreM. No mathematical product
or restricted machine-integer list replaces these source calls.
Source reference: base/broadcast.jl:282. -/
-- Source: base/broadcast.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.length(bc::Broadcasted) = prod(size(bc))
-- /Source
def length {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let shape ← ops.call bindings.size [bc]
  ops.call bindings.prod [shape]

/-- Start iteration by obtaining eachindex, then call the selected two-argument
iterate method with the actual singleton tuple (iter,). The tuple has exactly
one field and is constructible at every runtime; its element is the exact
returned iterator object. This method has no propagate_inbounds annotation.
The selected second method depends on unfixed bc and iterator types, so its
own implementation and any custom effects remain at the open call boundary.
Source reference: base/broadcast.jl:284. -/
-- Source: base/broadcast.jl:284-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.iterate(bc::Broadcasted)
--     iter = eachindex(bc)
--     iterate(bc, (iter,))
-- end
-- /Source
def iterateStart {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let iterator ← ops.call bindings.eachindex [bc]
  ops.call bindings.iterate [bc, JuliaLean.base.boot.tupleV ops [iterator]]

end JuliaLean.base.broadcast.Models2Group5.Forward


namespace JuliaLean.base.broadcast.Models2Group5.Iteration

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Runtime operations selected for the compiler's bounds context at
base/broadcast.jl:288. The Bool is metadata, not an added Julia argument:
true denotes retained checks and false an applicable elided-check context,
using the same convention as the installed Index.m619. Each interface member
has the behavior selected for that call site, including the callee's own
inlining/propagation rules. The source's @propagate_inbounds passes this
context through its extra inline layer (devdocs/boundscheck.md:70-79).
No effectful action implements context selection. -/
-- Source: base/broadcast.jl:288-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function Base.iterate(bc::Broadcasted, s)
--     y = iterate(s...)
--     y === nothing && return nothing
--     i, newstate = y
--     return (bc[i], (s[1], newstate))
-- end
-- /Source
structure ContextOps (W L : Type) where
  inContext : Bool → CoreOps W L

/-- Fixed Base function bindings for the selected method at
base/broadcast.jl:288. Returned values and selected methods are not supplied
as answers: calls retain the existing CoreOps dispatch/runtime boundary. -/
-- Source: base/broadcast.jl:288-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function Base.iterate(bc::Broadcasted, s)
--     y = iterate(s...)
--     y === nothing && return nothing
--     i, newstate = y
--     return (bc[i], (s[1], newstate))
-- end
-- /Source
structure Bindings (L : Type) where
  iterate : Value L
  indexedIterate : Value L
  getindex : Value L

/-- Full selected two-argument iterate body at base/broadcast.jl:288-293.
The state is any Julia value; splatting is the installed _apply_iterate
primitive, not a List specialization. If its result is not nothing, the
assignment destructures by the source's generic indexed_iterate protocol,
then evaluates bc[i] before s[1]. The two-element assignment order matches
the installed flfrontend.destructure2 (flfrontend.lean:59-66), with no extra
final state extraction. base/tuple.jl:161-172 defines the selected iteration
methods; manual/functions.md:394-409 specifies sequential destructuring.
Unfixed state, result and Broadcasted parameter types retain open dispatch.
Mutable inputs/results remain original reference-valued leaves in CoreM's
world; tuple construction stores these values without copying their objects.
All failures and divergence remain at their exact runtime operation. -/
-- Source: base/broadcast.jl:288-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function Base.iterate(bc::Broadcasted, s)
--     y = iterate(s...)
--     y === nothing && return nothing
--     i, newstate = y
--     return (bc[i], (s[1], newstate))
-- end
-- /Source
def iterateStep {W L : Type} (contexts : ContextOps W L)
    (bindings : Bindings L) (bc s : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let one := JuliaLean.base.boot.intV ops (JInt.lit .i64 1)
  let two := JuliaLean.base.boot.intV ops (JInt.lit .i64 2)
  let y ← ops.applyIterate bindings.iterate [bindings.iterate, s]
  if ops.same y (JuliaLean.base.boot.nothingV ops) then
    pure (JuliaLean.base.boot.nothingV ops)
  else do
    let firstPair ← ops.call bindings.indexedIterate [y, one]
    let index ← ops.getfield firstPair one
    let destructureState ← ops.getfield firstPair two
    let secondPair ← ops.call bindings.indexedIterate [y, two, destructureState]
    let newState ← ops.getfield secondPair one
    let value ← ops.call bindings.getindex [bc, index]
    let iterator ← ops.call bindings.getindex [s, one]
    pure (JuliaLean.base.boot.tupleV ops
      [value, JuliaLean.base.boot.tupleV ops [iterator, newState]])

end JuliaLean.base.broadcast.Models2Group5.Iteration


namespace JuliaLean.base.broadcast.Models2Group5.IteratorSize

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The method actually selected for a zero-argument HasShape constructor.
The builtin case is the constructor generated at base/generator.jl:66; the
custom case is an open selected specialization. This is method metadata,
not a callback supplying the result of the known constructor body. -/
-- Source: base/generator.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct HasShape{N} <: IteratorSize end
-- /Source
inductive ConstructorMethod where
  | builtin
  | custom

/-- Existing runtime operations plus world-sensitive method-selection
metadata for base/broadcast.jl:295. Selection is read only at the constructor
call, after any effects of ndims and type application. It performs no extra
source action and cannot itself supply a constructor result. -/
-- Source: base/broadcast.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedConstructor : Value L → W → ConstructorMethod

/-- Fixed Base function/type bindings used at base/broadcast.jl:295. -/
-- Source: base/broadcast.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
-- /Source
structure Bindings (L : Type) where
  ndims : Value L
  hasShape : Value L

/-- The zero-field inner constructor generated at base/generator.jl:66.
The existing new primitive receives the actual applied HasShape type and no
fields; no conversion or type assertion is added. The generation rule is
specified in doc/src/manual/constructors.md:329-342. The installed generator
IteratorSize.hasShape tag admits only Nat metadata, so it cannot represent
arbitrary Julia type parameters, type-application errors or runtime identity;
this is the necessary full-value runtime bridge, not a replacement for that
existing closed tag. -/
-- Source: base/generator.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct HasShape{N} <: IteratorSize end
-- /Source
def hasShapeNew {W L : Type} (ops : CoreOps W L)
    (appliedType : Value L) : CoreM W L (Value L) :=
  ops.new appliedType []

/-- Select construction at the actual call world of base/broadcast.jl:295.
Known generated construction invokes hasShapeNew. Only a genuinely selected
custom constructor uses the open call boundary. The source does not assert
that the result is an IteratorSize, so arbitrary custom returns are retained. -/
-- Source: base/broadcast.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
-- /Source
def callConstructor {W L : Type} (ops : Ops W L)
    (appliedType : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedConstructor appliedType world with
  | .builtin => hasShapeNew ops.toCoreOps appliedType world
  | .custom => ops.call appliedType [] world

/-- Full selected IteratorSize method at base/broadcast.jl:295. T is the
original subtype of Broadcasted supplied by method dispatch, including all
style, argument and axes type parameters. Its ndims method remains open
because those parameters are unfixed. The returned dimension is a full Julia
value, passed unchanged to HasShape type application: unusual valid parameters
are retained and invalid ones fail at the runtime's original check. No Nat or
native-Int narrowing is inserted. Errors, state changes and divergence remain
in the installed CoreM effect, with construction after the type query. -/
-- Source: base/broadcast.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.IteratorSize(::Type{T}) where {T<:Broadcasted} = Base.HasShape{ndims(T)}()
-- /Source
def iteratorSize {W L : Type} (ops : Ops W L)
    (bindings : Bindings L) (T : Value L) : CoreM W L (Value L) := do
  let dimension ← ops.call bindings.ndims [T]
  let appliedType ← ops.applyType bindings.hasShape [dimension]
  callConstructor ops appliedType

end JuliaLean.base.broadcast.Models2Group5.IteratorSize


namespace JuliaLean.base.broadcast.Models2Group5.CombineStyles

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source bindings used by the style-combination methods at
base/broadcast.jl:432,437-438. They are generic-function identities. -/
-- Source: base/broadcast.jl:432-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c) = result_style(BroadcastStyle(typeof(c)))
-- function combine_styles(bc::Broadcasted)
--     bc.style isa Union{Nothing,Unknown} || return bc.style
--     throw(ArgumentError("Broadcasted{Unknown} wrappers do not have a style assigned"))
-- end
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
structure Bindings (L : Type) where
  broadcastStyle : Value L
  combineStyles : Value L
  resultStyle : Value L

/-- Full selected unary method at base/broadcast.jl:432. Builtin typeof
observes the original value. BroadcastStyle and unary result_style dispatch
on the unfixed input type and returned style type, respectively; the existing
CoreOps.call boundary retains their arbitrary values, effects and failures.
No assertion that either callee returned a style is added. -/
-- Source: base/broadcast.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c) = result_style(BroadcastStyle(typeof(c)))
-- /Source
def combineOne {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (value : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.broadcastStyle [.leaf (ops.typeOf value)]
  ops.call bindings.resultStyle [style]

/-- Full selected binary method at base/broadcast.jl:437. The left unary
query finishes before the right query starts; their exact results then reach
result_style. The unary targets are selected on the two unconstrained value
types, so each remains an open call, including custom and wrapper overloads.
This body has no recursive binary call and assumes no law about any callee. -/
-- Source: base/broadcast.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- /Source
def combineTwo {W L : Type} (ops : CoreOps W L)
    (bindings : Bindings L) (left right : Value L) : CoreM W L (Value L) := do
  let leftStyle ← ops.call bindings.combineStyles [left]
  let rightStyle ← ops.call bindings.combineStyles [right]
  ops.call bindings.resultStyle [leftStyle, rightStyle]

/-- Selected method metadata for a recursive call with at least two inputs.
`builtin` selects source437 at arity two and source438 at larger arities;
`custom` means a genuinely selected different method on the unfixed types.
The selector does not supply or compute a method result. 
Source reference: base/broadcast.jl:437-438.
-/
-- Source: base/broadcast.jl:437-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
inductive Method where
  | builtin
  | custom

/-- Runtime operations and pure current-world dispatch metadata for the
recursive suffix at base/broadcast.jl:438. The selector is consulted after
preceding source calls have finished. All actual effects and exceptions remain
in the installed CoreOps interface. The three value arguments to the selector
are the first, second and remaining slots of that recursive call. -/
-- Source: base/broadcast.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedCombine : Value L → Value L → List (Value L) → W → Method

/-- The supplied vararg tuple of source438. The native-Int size invariant
counts both mandatory inputs as well as cs, so the full splatted argument
sequence is constructible. Slots can contain heterogeneous Julia values and
retain arbitrary mutable aliases. Structural list traversal below is Lean
representation recursion, not substituted Julia integer arithmetic. The stored tuple field count also fits UInt32, matching the DataTypeLayout
representation invariant at base/runtime_internals.jl:624-626. -/
-- Source: base/broadcast.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
structure Tail (L : Type) where
  values : List (Value L)
  fieldCountFits : values.length ≤ IntTy.u32.max.toNat
  totalSize : JInt .i64
  totalSize_eq : totalSize.val = (values.length : Int) + 2

/-- Execute a nonempty recursive suffix of source438. Singleton calls remain
open unary dispatch. A selected source437 call uses its real model. A selected
source438 call performs its own left query, recursively executes the smaller
suffix, then joins their results; its recursion is never supplied as a
callback. Only selected different methods use the open multiargument call.
The current world is read at each dispatch, so a prior unary query can affect
which recursive method is selected. Every internal list is a suffix of the
machine-bounded tuple supplied to combineMany; no array or tuple is synthesized
with a larger length. Source: base/broadcast.jl:437-438. -/
-- Source: base/broadcast.jl:437-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
def combineSuffix {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (first : Value L) (rest : List (Value L)) : CoreM W L (Value L) :=
  match rest with
  | [] => ops.call bindings.combineStyles [first]
  | [second] => fun world =>
      match ops.selectedCombine first second [] world with
      | .builtin => combineTwo ops.toCoreOps bindings first second world
      | .custom => ops.call bindings.combineStyles [first, second] world
  | second :: third :: tail => fun world =>
      match ops.selectedCombine first second (third :: tail) world with
      | .custom => ops.call bindings.combineStyles (first :: second :: third :: tail) world
      | .builtin => (do
          let firstStyle ← ops.call bindings.combineStyles [first]
          let restStyle ← combineSuffix ops bindings second (third :: tail)
          ops.call bindings.resultStyle [firstStyle, restStyle]) world
termination_by rest.length

/-- Full selected variadic source body at base/broadcast.jl:438. It performs
the first unary call, then the actual recursively dispatched suffix, and only
then the right-associated result_style call. Tuple splatting uses the concrete
vararg slots without user element evaluation. The two-required-argument case
with empty cs is represented too; ordinary top-level dispatch normally prefers
source437 there, but this selected method body remains faithful on that input.
Source errors, worlds and divergence propagate without replacement values. -/
-- Source: base/broadcast.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
def combineMany {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (first second : Value L) (rest : Tail L) : CoreM W L (Value L) := do
  let firstStyle ← ops.call bindings.combineStyles [first]
  let restStyle ← combineSuffix ops bindings second rest.values
  ops.call bindings.resultStyle [firstStyle, restStyle]

end JuliaLean.base.broadcast.Models2Group5.CombineStyles


namespace JuliaLean.base.broadcast.Models2Group5.ResultJoin

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Selected method metadata for the single-argument error call at
base/broadcast.jl:480. The canonical method is the N=1 instance of
base/error.jl:47-57. A selected custom method may have arbitrary outcomes. -/
-- Source: base/error.jl:47-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function error(s::Vararg{Any,N}) where {N}
--     @noinline
--     exc = if s === ()
--         ErrorException("")
--     elseif s isa Tuple{AbstractString}
--         ErrorException(s...)
--     else
--         ErrorException(Main.Base.string(s...))
--     end
--     throw(exc)
-- end
-- /Source
inductive ErrorMethod where
  | canonicalOne
  | custom

/-- Selected ErrorException constructor metadata. canonicalAbstractString
selects the actual typed method below; custom includes a more-specific method
or a failed dispatch for a non-AbstractString value. 
Source reference: base/boot.jl:470-473.
-/
-- Source: base/boot.jl:470-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct ErrorException <: Exception
--     msg::AbstractString
--     ErrorException(msg::AbstractString) = new(msg)
-- end
-- /Source
inductive ExceptionMethod where
  | canonicalAbstractString
  | custom

/-- Existing primitives/open calls plus pure, world-aware selected-method
metadata. Neither selector executes or supplies an error implementation.
Selection occurs at the actual call after all preceding rendering effects.
Source reference: base/broadcast.jl:479-485. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedError : Value L → W → ErrorMethod
  selectedException : Value L → W → ExceptionMethod

/-- Fixed Base function bindings at base/broadcast.jl:479-485. The core type
bindings ErrorException and AbstractString use the existing coreV operation. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
structure Bindings (L : Type) where
  string : Value L
  error : Value L

/-- Actual S,T,U,V type parameters supplied by dispatch at
base/broadcast.jl:479. They are type values, not strings already rendered by
user code, and the four operand payloads are not inspected by this method. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
structure TypeParameters (L : Type) where
  left : Value L
  right : Value L
  forward : Value L
  reverse : Value L

/-- The selected typed constructor at base/boot.jl:472, represented with the
installed Obj.errorException constructor. Both its argument type and its
single field type are AbstractString, so the argument already satisfies the
field type and no conversion is performed. Conditional typed-field lowering
is documented in the pinned base/essentials.jl:1468-1483. This exact typed
case uses the existing immutable-object representation and preserves the
original message value. It does not reuse the older boot.ErrorException
adapter that unconditionally calls convertField. The method selection
metadata supplies the signature invariant, as for other installed CoreOps
models; no claim about arbitrary non-AbstractString calls is made here. -/
-- Source: base/boot.jl:470-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct ErrorException <: Exception
--     msg::AbstractString
--     ErrorException(msg::AbstractString) = new(msg)
-- end
-- /Source
def canonicalException {W L : Type} (ops : CoreOps W L)
    (message : Value L) : Value L :=
  JuliaLean.base.boot.objV ops (.errorException message)

/-- ErrorException(message), resolved in the current runtime world. The
known typed Base constructor uses its real object model; only genuinely
selected custom methods or dispatch errors use the existing call boundary.
Source reference: base/boot.jl:472; base/error.jl:52,54. -/
-- Source: base/boot.jl:470-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct ErrorException <: Exception
--     msg::AbstractString
--     ErrorException(msg::AbstractString) = new(msg)
-- end
-- /Source
def constructException {W L : Type} (ops : Ops W L)
    (message : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedException message world with
  | .canonicalAbstractString =>
      some (.ok (canonicalException ops.toCoreOps message, world))
  | .custom =>
      ops.call (JuliaLean.base.boot.coreV ops.toCoreOps "ErrorException") [message] world

/-- Exact one-argument specialization needed by base/broadcast.jl:480 of
base/error.jl:47-57. The statically singleton argument tuple is nonempty;
its Tuple{AbstractString} test is precisely its one element's AbstractString
test. AbstractString messages are used directly. Every other value is passed
to string again, with that call's actual effects and result, before the
constructor is selected and the resulting value is thrown. In particular a
custom interpolation method need not have returned a String. This helper
claims only the full N=1 callee domain required by the queued method.
No field-correctness law, eager rendering, default message or error recovery
is assumed. -/
-- Source: base/error.jl:47-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function error(s::Vararg{Any,N}) where {N}
--     @noinline
--     exc = if s === ()
--         ErrorException("")
--     elseif s isa Tuple{AbstractString}
--         ErrorException(s...)
--     else
--         ErrorException(Main.Base.string(s...))
--     end
--     throw(exc)
-- end
-- /Source
def errorOne {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (message : Value L) : CoreM W L (Value L) := do
  let exception ←
    if ops.isa message (JuliaLean.base.boot.coreV ops.toCoreOps "AbstractString") then
      constructException ops message
    else do
      let rendered ← ops.call bindings.string [message]
      constructException ops rendered
  throw exception

/-- The selected error(message) call at base/broadcast.jl:480. Known Base
behavior calls errorOne; an actual selected user override remains open. The
selector observes the world after interpolation rather than its initial world. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
def callError {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (message : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedError message world with
  | .canonicalOne => errorOne ops bindings message world
  | .custom => ops.call bindings.error [message] world

/-- Literal interpolation arguments from base/broadcast.jl:480-484. The
opening triple-quoted newline is stripped; indentation is zero because the
text begins in column one. All six interpolated occurrences retain their
actual type values in source order S,T,U,T,S,V. The thirteen-element list is
fixed compiler argument storage, never an unbounded Julia container. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
def interpolationArguments {W L : Type} (ops : CoreOps W L)
    (types : TypeParameters L) : List (Value L) :=
  [JuliaLean.base.boot.strV ops
      "conflicting broadcast rules defined\n  Broadcast.BroadcastStyle(::",
   types.left, JuliaLean.base.boot.strV ops ", ::", types.right,
   JuliaLean.base.boot.strV ops ") = ", types.forward,
   JuliaLean.base.boot.strV ops "()\n  Broadcast.BroadcastStyle(::",
   types.right, JuliaLean.base.boot.strV ops ", ::", types.left,
   JuliaLean.base.boot.strV ops ") = ", types.reverse,
   JuliaLean.base.boot.strV ops
      "()\nOne of these should be undefined (and thus return Broadcast.Unknown)."]

/-- Full conflicting-rule diagnostic method at base/broadcast.jl:479-485.
Julia string interpolation calls string once on the literal pieces and type
values (manual/strings.md:534-573). Its dispatch depends on unspecified S,T,U,V
and may mutate, throw, diverge or return any value. The subsequent error call
is selected after these effects and uses the concrete Base body when selected.
No extra type assertion is inserted, and the operand payloads are ignored.
Both custom error returns and the exact canonical ErrorException are retained. -/
-- Source: base/broadcast.jl:479-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @noinline function result_join(::S, ::T, ::U, ::V) where {S,T,U,V}
--     error("""
-- conflicting broadcast rules defined
--   Broadcast.BroadcastStyle(::$S, ::$T) = $U()
--   Broadcast.BroadcastStyle(::$T, ::$S) = $V()
-- One of these should be undefined (and thus return Broadcast.Unknown).""")
-- end
-- /Source
def conflicting {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (types : TypeParameters L) (_left _right _forward _reverse : Value L) :
    CoreM W L (Value L) := do
  let message ← ops.call bindings.string (interpolationArguments ops.toCoreOps types)
  callError ops bindings message

end JuliaLean.base.broadcast.Models2Group5.ResultJoin


namespace JuliaLean.base.broadcast.Models2Group5.CombineAxes

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed bindings of the three generic functions used by the combination
methods. These are source function identities, not supplied results.
Source reference: base/broadcast.jl:502-504. -/
-- Source: base/broadcast.jl:502-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- combine_axes(A) = axes(A)
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  combineAxes : Value L
  broadcastShape : Value L

/-- Pure metadata for a nonempty recursive combine_axes call. The canonical
branch selects source504 for one argument, source503 for two, and source502
for more. A custom branch is a genuinely selected additional method on the
unfixed input types; it does not replace a known body or return a supplied
answer. Julia source: base/broadcast.jl:502-504. -/
-- Source: base/broadcast.jl:502-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- combine_axes(A) = axes(A)
-- /Source
inductive Method where
  | builtin
  | custom

/-- Existing runtime primitives plus nonempty-call dispatch metadata. Method
selection observes the current world after every preceding axes call. No
behavioral law is imposed on axes, broadcast_shape, or custom combine_axes.
The zero-argument function has no method in the pinned Base method table,
and does not involve type-dependent selection.
Source reference: base/broadcast.jl:502-504. -/
-- Source: base/broadcast.jl:502-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- combine_axes(A) = axes(A)
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedCombine : Value L → List (Value L) → W → Method

/-- The actual supplied vararg tuple. The native length bound counts the
mandatory first argument too, so every full argument list and recursively
selected suffix is constructible. List traversal is representation-level
structural recursion, not substituted Julia integer arithmetic. Runtime
values keep heterogeneous types and mutable aliases.
Source reference: base/broadcast.jl:502. The stored tuple field count also fits UInt32, matching the DataTypeLayout
representation invariant at base/runtime_internals.jl:624-626. -/
-- Source: base/broadcast.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- /Source
structure Tail (L : Type) where
  values : List (Value L)
  fieldCountFits : values.length ≤ IntTy.u32.max.toNat
  totalSize : JInt .i64
  totalSize_eq : totalSize.val = (values.length : Int) + 1

/-- Bind the installed complete binary source driver to its actual selected
runtime calls. Shape.m503 already preserves the left axes query, the right
axes query, and the subsequent shape call in that order. The input and axes
result types remain unrestricted; offset axes and custom axes are never
replaced by native ranges or integer lists.
Source reference: base/broadcast.jl:503. -/
-- Source: base/broadcast.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- /Source
def combineTwo {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (left right : Value L) : CoreM W L (Value L) :=
  Shape.m503
    (fun value => ops.call bindings.axes [value])
    (fun value => ops.call bindings.axes [value])
    (fun leftAxes rightAxes => ops.call bindings.broadcastShape [leftAxes, rightAxes])
    left right

/-- Full selected unary source504. Unlike the older List-valued adapter, this
call retains every selected axes result, error, runtime world, and divergence.
The source places no additional type assertion on the result.
Source reference: base/broadcast.jl:504. -/
-- Source: base/broadcast.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_axes(A) = axes(A)
-- /Source
def combineOne {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value : Value L) : CoreM W L (Value L) :=
  ops.call bindings.axes [value]

/-- The pinned table has no combine_axes() method. Preserve the installed
runtime missing-method protocol (boot.noMethod), but use the actual Base
function binding rather than an invented Core constant. The throw retains
the current world age and the genuine empty argument tuple. This primitive
dependency is reached only if source502 is explicitly selected with no B
arguments; ordinary unary dispatch selects source504 instead.
Julia source context: base/broadcast.jl:502-504; installed runtime protocol:
JuliaLean/base/boot.lean:noMethod. -/
-- Source: base/broadcast.jl:502-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- combine_axes(A) = axes(A)
-- /Source
def missingNullary {W L : Type} (ops : CoreOps W L) (bindings : Bindings L) :
    CoreM W L (Value L) := do
  let age ← ops.worldAge
  JuliaLean.base.boot.throwObj ops
    (.methodError bindings.combineAxes (JuliaLean.base.boot.tupleV ops [])
      (JuliaLean.base.boot.intV ops age))

/-- Real recursion for every nonempty suffix. Canonical unary and binary
branches call their actual source models. The binary branch does not recurse
through a unary combine_axes call: its second axes query belongs directly to
source503. A canonical variadic branch obtains the first axes, recursively
executes the strictly smaller suffix, then combines their exact results.
Only a selected custom method is an open call on the whole remaining suffix.
Every raw list here is a suffix of the public machine-bounded Tail.
Source reference: base/broadcast.jl:502-504. -/
-- Source: base/broadcast.jl:502-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- @inline combine_axes(A, B) = broadcast_shape(axes(A), axes(B))
-- combine_axes(A) = axes(A)
-- /Source
def combineSuffix {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (first : Value L) (rest : List (Value L)) : CoreM W L (Value L) :=
  match rest with
  | [] => fun world =>
      match ops.selectedCombine first [] world with
      | .builtin => combineOne ops.toCoreOps bindings first world
      | .custom => ops.call bindings.combineAxes [first] world
  | [second] => fun world =>
      match ops.selectedCombine first [second] world with
      | .builtin => combineTwo ops.toCoreOps bindings first second world
      | .custom => ops.call bindings.combineAxes [first, second] world
  | second :: third :: tail => fun world =>
      match ops.selectedCombine first (second :: third :: tail) world with
      | .custom => ops.call bindings.combineAxes (first :: second :: third :: tail) world
      | .builtin => (do
          let firstAxes ← ops.call bindings.axes [first]
          let restAxes ← combineSuffix ops bindings second (third :: tail)
          ops.call bindings.broadcastShape [firstAxes, restAxes]) world
termination_by rest.length

/-- Full selected variadic source502, including its explicit-invoke one- and
 two-argument cases. Reuse the installed ordered source driver, with its
recursive dependency now bound to the actual locally defined dispatcher.
The first axes call always precedes suffix dispatch, so changes to the world
can affect the selected suffix method. No source recursion is supplied by a
caller. The empty suffix raises the real missing-method error after axes(A).
Source reference: base/broadcast.jl:502. -/
-- Source: base/broadcast.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline combine_axes(A, B...) = broadcast_shape(axes(A), combine_axes(B...))
-- /Source
def combineMany {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (first : Value L) (rest : Tail L) : CoreM W L (Value L) :=
  Shape.m502
    (fun value => ops.call bindings.axes [value])
    (fun suffix => match suffix with
      | [] => missingNullary ops.toCoreOps bindings
      | second :: tail => combineSuffix ops bindings second tail)
    (fun firstAxes restAxes => ops.call bindings.broadcastShape [firstAxes, restAxes])
    first rest.values

end JuliaLean.base.broadcast.Models2Group5.CombineAxes


namespace JuliaLean.base.broadcast.Models2Group5.AxisTypes

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source type bindings, with native Int represented by Core.Int64
on this packet's 64-bit runtime. Constructor method selection still depends
on the unspecified source argument type. Julia source: base/broadcast.jl:543-544. -/
-- Source: base/broadcast.jl:543-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axistype(a::OneTo, b::OneTo) = OneTo{Int}(a)
-- axistype(a, b) = UnitRange{Int}(a)
-- /Source
structure Bindings (L : Type) where
  oneTo : Value L
  unitRange : Value L

/-- Full selected OneTo/OneTo overload. The type application is concrete,
but the constructor call dispatches on the unfixed OneTo element type of a;
it may select native, non-native integer or user methods. The original a is
passed unchanged, while b is not observed. All constructor conversions/errors
occur inside that actual selected callee, without a native-only replacement.
The two-OneTo overload is selected even if the two element types coincide.
Source reference: base/broadcast.jl:543. -/
-- Source: base/broadcast.jl:543-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axistype(a::OneTo, b::OneTo) = OneTo{Int}(a)
-- /Source
def oneTo {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (a _b : Value L) : CoreM W L (Value L) := do
  let constructor ← ops.applyType bindings.oneTo [JuliaLean.base.boot.coreV ops "Int64"]
  ops.call constructor [a]

/-- Full selected fallback for unspecified axis types. UnitRange{Int} is
applied before selecting the conversion constructor on the original a. There
is no native-axis, finite-width, zero-based/one-based, or nonempty restriction.
Dispatch has already selected this fallback rather than a more-specific
axistype overload. The ignored second axis cannot trigger conversion or
property effects in this method. Julia source: base/broadcast.jl:544. -/
-- Source: base/broadcast.jl:544-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axistype(a, b) = UnitRange{Int}(a)
-- /Source
def unitRange {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (a _b : Value L) : CoreM W L (Value L) := do
  let constructor ← ops.applyType bindings.unitRange [JuliaLean.base.boot.coreV ops "Int64"]
  ops.call constructor [a]

end JuliaLean.base.broadcast.Models2Group5.AxisTypes


namespace JuliaLean.base.broadcast.Models2Group5.NewIndex

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual selected Base.ifelse dispatch. The boolean tag carries the original
Bool argument when the canonical Bool method was selected, not an arbitrary
return value. custom covers selected user methods on unfixed argument types;
missing records failed/ambiguous dispatch. These are runtime dispatch/value
metadata, not a callable substitute for Base's Bool method. 
Source reference: base/essentials.jl:894-894.
-/
-- Source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
-- /Source
inductive IfElseMethod where
  | boolean (flag : Bool)
  | custom
  | missing

/-- The existing Core interface plus current-world Base.ifelse selection.
The selection occurs after all three operands have been evaluated. A boolean
payload is the actual condition's stored Bool; custom callees remain arbitrary.
The runtime interface supplied to an inline body is that of its applicable
compiler bounds context, retaining the actual behavior of indexing primitives. 
Source reference: base/broadcast.jl:595-596.
-/
-- Source: base/broadcast.jl:595-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(i::Integer, keep::Tuple, idefault) = CartesianIndex(ifelse(keep[1], Int(i), Int(idefault[1])), idefault[2])
-- @inline newindex(i::Integer, keep::Tuple{Bool}, idefault) = ifelse(keep[1], i, idefault[1])
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedIfElse : Value L → Value L → Value L → W → IfElseMethod

/-- Failed Base.ifelse dispatch produces MethodError, not the TypeError of
calling the Core.ifelse builtin on a non-Bool. This uses the same installed
runtime exception construction as boot.noMethod, but preserves the supplied
Base generic function identity rather than inventing a Core binding. The
runtime world-age query and thrown object are retained exactly.
Sources: base/essentials.jl:894; base/boot.jl:561-568; installed
base/essentials.lean:ifelseCall and base/boot.lean:noMethod. -/
-- Source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
-- /Source
def missingIfElse {W L : Type} (ops : CoreOps W L)
    (function condition first second : Value L) : CoreM W L (Value L) := do
  let age ← ops.worldAge
  JuliaLean.base.boot.throwObj ops (.methodError function
    (JuliaLean.base.boot.tupleV ops [condition, first, second])
    (JuliaLean.base.boot.intV ops age))

/-- Complete selected Base.ifelse call after eager operand evaluation.
Canonical Bool selection reuses the installed Index.m596 value-preserving
selector. A genuine custom method is invoked with the original three values;
failed dispatch raises its actual MethodError only at this point. No Int
conversion, Boolean-context TypeError or short-circuit operand evaluation is
inserted. This helper is shared by the source595/596 and598 callers. 
Source reference: base/essentials.jl:894-894.
-/
-- Source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
-- /Source
def callIfElse {W L : Type} (ops : Ops W L)
    (function condition first second : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedIfElse condition first second world with
  | .boolean flag =>
      some (.ok (Sum.elim id id (Index.m596 first flag second), world))
  | .custom => ops.call function [condition, first, second] world
  | .missing => missingIfElse ops.toCoreOps function condition first second world

/-- Fixed source bindings at base/broadcast.jl:593-596. Integer conversion and
constructor/getindex targets with unfixed argument types use the existing
CoreOps.call interface with these original function identities. -/
-- Source: base/broadcast.jl:593-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(I::CartesianIndex, keep, Idefault) = to_index(_newindex(I.I, keep, Idefault))
-- @inline newindex(I::CartesianIndex{1}, keep, Idefault) = newindex(I.I[1], keep, Idefault)
-- @inline newindex(i::Integer, keep::Tuple, idefault) = CartesianIndex(ifelse(keep[1], Int(i), Int(idefault[1])), idefault[2])
-- @inline newindex(i::Integer, keep::Tuple{Bool}, idefault) = ifelse(keep[1], i, idefault[1])
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  remap : Value L
  toIndex : Value L
  newIndex : Value L
  getindex : Value L
  intConstructor : Value L
  cartesianIndex : Value L
  ifElse : Value L

/-- Actual source593 property selection. CartesianIndex's rank parameter is
unfixed, so a specialized getproperty method may be selected for that rank.
The canonical branch retains the concrete Base field projection; only an
actually selected extension is an open generic property call.
Source reference: base/broadcast.jl:593; base/Base_compiler.jl:59. -/
-- Source: base/broadcast.jl:593-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(I::CartesianIndex, keep, Idefault) = to_index(_newindex(I.I, keep, Idefault))
-- /Source
inductive CartesianPropertyMethod where
  | builtin
  | custom

/-- Existing Core primitives with pure current-world selection of source593's
rank-dependent property method. The metadata supplies no coordinate result.
Source reference: base/broadcast.jl:593. -/
-- Source: base/broadcast.jl:593-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(I::CartesianIndex, keep, Idefault) = to_index(_newindex(I.I, keep, Idefault))
-- /Source
structure CartesianOps (W L : Type) extends CoreOps W L where
  selectedIndexProperty : Value L → W → CartesianPropertyMethod

/-- The selected CartesianIndex method at base/broadcast.jl:593. The canonical
property fallback reads the actual I field through the installed primitive;
a selected extension can specialize the unfixed rank N and returns its actual
value/effects. This distinction is absent from fixed-rank source594.
The remapper dispatches on unfixed keep/default types, and to_index dispatches
on its arbitrary returned type. The last callee is exactly to_index, not an
unconditional CartesianIndex constructor or an Int64-only remapper.
Source reference: base/broadcast.jl:593; base/multidimensional.jl:75-78;
base/Base_compiler.jl:59. -/
-- Source: base/broadcast.jl:593-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(I::CartesianIndex, keep, Idefault) = to_index(_newindex(I.I, keep, Idefault))
-- /Source
def cartesian {W L : Type} (ops : CartesianOps W L) (bindings : Bindings L)
    (index keep defaults : Value L) : CoreM W L (Value L) := do
  let selected ← (show CoreM W L CartesianPropertyMethod from fun world =>
    some (.ok (ops.selectedIndexProperty index world, world)))
  let coordinates ← match selected with
    | .builtin => ops.getfield index (.symbol "I")
    | .custom => ops.call bindings.getproperty [index, .symbol "I"]
  let mapped ← ops.call bindings.remap [coordinates, keep, defaults]
  ops.call bindings.toIndex [mapped]

/-- The concrete one-dimensional specialization at base/broadcast.jl:594.
Read the stored I field and its first native-Int coordinate by the installed
getfield primitive. These are the known Base property and Tuple/Int getindex
bodies (Base_compiler.jl:59; tuple.jl:33); the fixed CartesianIndex{1} field has
type Tuple{Int64}, so this read needs no integer conversion or user getter.
The subsequent newindex target remains open on keep/default argument types. -/
-- Source: base/broadcast.jl:594-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(I::CartesianIndex{1}, keep, Idefault) = newindex(I.I[1], keep, Idefault)
-- /Source
def cartesianOne {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (index keep defaults : Value L) : CoreM W L (Value L) := do
  let coordinates ← ops.getfield index (.symbol "I")
  let coordinate ← ops.getfield coordinates
    (JuliaLean.base.boot.intV ops (JInt.lit .i64 1))
  ops.call bindings.newIndex [coordinate, keep, defaults]

/-- A Tuple with unfixed element types may select a specialized getindex
method. The canonical Tuple/Int branch has its actual getfield body below;
only genuinely selected extensions remain generic calls. 
Source reference: base/tuple.jl:33-33.
-/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
inductive TupleGetMethod where
  | builtin
  | custom

/-- Extra dispatch metadata for the source595 keep::Tuple, whose element
and arity parameters are unfixed. The fixed Tuple{Bool} of source596 does not
use this selector: it directly reads its known sole field. 
Source reference: base/broadcast.jl:595-596.
-/
-- Source: base/broadcast.jl:595-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(i::Integer, keep::Tuple, idefault) = CartesianIndex(ifelse(keep[1], Int(i), Int(idefault[1])), idefault[2])
-- @inline newindex(i::Integer, keep::Tuple{Bool}, idefault) = ifelse(keep[1], i, idefault[1])
-- /Source
structure IntegerOps (W L : Type) extends Ops W L where
  selectedKeepGet : Value L → JInt .i64 → W → TupleGetMethod

/-- Runtime-value form of the existing tuple.getindexInt source body. It
retains concrete tuple field behavior in the applicable compiler context;
the list-based installed model cannot represent the opaque runtime tuple and
its contextual primitive directly. The custom case remains an open call only
when the unfixed tuple type actually selects that method.
Source: base/tuple.jl:33; base/broadcast.jl:595. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
def tupleGet {W L : Type} (ops : IntegerOps W L) (getindex : Value L)
    (tuple : Value L) (index : JInt .i64) : CoreM W L (Value L) := fun world =>
  match ops.selectedKeepGet tuple index world with
  | .builtin => ops.getfield tuple (JuliaLean.base.boot.intV ops.toOps.toCoreOps index) world
  | .custom => ops.call getindex
      [tuple, JuliaLean.base.boot.intV ops.toOps.toCoreOps index] world

/-- Full source595 expression. Read keep[1], evaluate Int(i), read idefault[1],
and evaluate its Int conversion before invoking Base.ifelse. Thus even a
true keep does not suppress the first default read or either conversion.
Only after ifelse returns is idefault[2] read and the two-argument
CartesianIndex constructor selected. Both Integer conversions and the final
constructor allow arbitrary custom methods and results; no conversion law or
native-only input restriction is imposed. The source literally supplies two
constructor arguments, regardless of additional keep/default dimensions. 
Source reference: base/broadcast.jl:595-595.
-/
-- Source: base/broadcast.jl:595-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(i::Integer, keep::Tuple, idefault) = CartesianIndex(ifelse(keep[1], Int(i), Int(idefault[1])), idefault[2])
-- /Source
def integerMany {W L : Type} (ops : IntegerOps W L) (bindings : Bindings L)
    (index keep defaults : Value L) : CoreM W L (Value L) := do
  let one := JuliaLean.base.boot.intV ops.toOps.toCoreOps (JInt.lit .i64 1)
  let two := JuliaLean.base.boot.intV ops.toOps.toCoreOps (JInt.lit .i64 2)
  let condition ← tupleGet ops bindings.getindex keep (JInt.lit .i64 1)
  let convertedIndex ← ops.call bindings.intConstructor [index]
  let firstDefault ← ops.call bindings.getindex [defaults, one]
  let convertedDefault ← ops.call bindings.intConstructor [firstDefault]
  let chosen ← callIfElse ops.toOps bindings.ifElse condition convertedIndex convertedDefault
  let secondDefault ← ops.call bindings.getindex [defaults, two]
  ops.call bindings.cartesianIndex [chosen, secondDefault]

/-- Full source596 expression. The exact Tuple{Bool} keep argument has a
known first field, so its read is the concrete tuple/Int getfield body. The
default getter still runs eagerly before Bool selection, even for true keep.
The installed Index.m596 selector preserves the actual original Integer or
default value through callIfElse's canonical branch, without Int conversion.
Custom ifelse selection can depend on the unfixed Integer/default types; its
actual results and effects remain open. Source: base/broadcast.jl:596. -/
-- Source: base/broadcast.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindex(i::Integer, keep::Tuple{Bool}, idefault) = ifelse(keep[1], i, idefault[1])
-- /Source
def integerOne {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (index keep defaults : Value L) : CoreM W L (Value L) := do
  let one := JuliaLean.base.boot.intV ops.toCoreOps (JInt.lit .i64 1)
  let condition ← ops.getfield keep one
  let firstDefault ← ops.call bindings.getindex [defaults, one]
  callIfElse ops bindings.ifElse condition index firstDefault

end JuliaLean.base.broadcast.Models2Group5.NewIndex


namespace JuliaLean.base.broadcast.Models2Group5.Remap

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual selected method for a recursive _newindex call. The four Base
bodies are explicit below; custom represents a genuinely selected other
method (including dispatch failure), never this method's recursive body.
Source reference: base/broadcast.jl:598-602. -/
-- Source: base/broadcast.jl:598-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _newindex(I, keep, Idefault) =
--     (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
-- @inline _newindex(I, keep::Tuple{}, Idefault) = ()  # truncate if keep is shorter than I
-- @inline _newindex(I::Tuple{}, keep, Idefault) = ()  # or I is shorter
-- @inline _newindex(I::Tuple{}, keep::Tuple{}, Idefault) = () # or both
-- /Source
inductive Method where
  | generic
  | emptyKeep
  | emptyIndex
  | emptyBoth
  | custom

/-- Existing ifelse/runtime operations with pure, world-aware metadata for
the recursive method selection. The selector sees all three actual tail
results after their effects have completed. It supplies no result or method
body. The inherited runtime interface carries the applicable compiler bounds
context for this @inline body. Source: base/broadcast.jl:598-602. -/
-- Source: base/broadcast.jl:598-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _newindex(I, keep, Idefault) =
--     (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
-- @inline _newindex(I, keep::Tuple{}, Idefault) = ()  # truncate if keep is shorter than I
-- @inline _newindex(I::Tuple{}, keep, Idefault) = ()  # or I is shorter
-- @inline _newindex(I::Tuple{}, keep::Tuple{}, Idefault) = () # or both
-- /Source
structure Ops (W L : Type) extends NewIndex.Ops W L where
  selectedRemap : Value L → Value L → Value L → W → Method

/-- Fixed source function identities used at base/broadcast.jl:598-599. -/
-- Source: base/broadcast.jl:598-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _newindex(I, keep, Idefault) =
--     (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
-- /Source
structure Bindings (L : Type) where
  getindex : Value L
  ifElse : Value L
  tail : Value L
  remap : Value L
  iterate : Value L

/-- Source-body recursion for base/broadcast.jl:598-602. Each generic frame
reads keep[1], I[1] and Idefault[1] eagerly and in that order. It then calls
the actual selected ifelse, evaluates the three tail calls left to right,
selects the recursive method in the resulting world, executes that method,
and finally splats the suffix with the chosen head through the installed
_apply_iterate/Core.tuple boundary. The empty cases reuse Index.m600/m601/m602;
their always-empty Int lists are encoded as the empty runtime tuple.

The actual input/tail values are opaque Julia references, not Lean lists;
tail may return a custom object, cycle, throw, mutate or diverge. The recursive
body uses the same CoreM partial_fixpoint mechanism as boot._contains_typeapp
and boot.typename. There is no caller-supplied fuel, structural-size premise,
termination promise, callback for the method's own recursion, or recovery
value. A nonterminating recursive chain is CoreM divergence. The singleton
prefix is fixed-size compiler argument storage and retains the selected
value's reference identity. -/
-- Source: base/broadcast.jl:598-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _newindex(I, keep, Idefault) =
--     (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
-- @inline _newindex(I, keep::Tuple{}, Idefault) = ()  # truncate if keep is shorter than I
-- @inline _newindex(I::Tuple{}, keep, Idefault) = ()  # or I is shorter
-- @inline _newindex(I::Tuple{}, keep::Tuple{}, Idefault) = () # or both
-- /Source
def selected {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (indices keep defaults : Value L) : CoreM W L (Value L) := do
  let core := ops.toOps.toCoreOps
  match method with
  | .emptyKeep =>
      pure (JuliaLean.base.boot.tupleV core ((Index.m600 indices defaults).map
        (fun value => JuliaLean.base.boot.intV core (JInt.lit .i64 value))))
  | .emptyIndex =>
      pure (JuliaLean.base.boot.tupleV core ((Index.m601 keep defaults).map
        (fun value => JuliaLean.base.boot.intV core (JInt.lit .i64 value))))
  | .emptyBoth =>
      pure (JuliaLean.base.boot.tupleV core ((Index.m602 defaults).map
        (fun value => JuliaLean.base.boot.intV core (JInt.lit .i64 value))))
  | .custom => ops.call bindings.remap [indices, keep, defaults]
  | .generic =>
      let one := JuliaLean.base.boot.intV core (JInt.lit .i64 1)
      let condition ← ops.call bindings.getindex [keep, one]
      let coordinate ← ops.call bindings.getindex [indices, one]
      let fallback ← ops.call bindings.getindex [defaults, one]
      let chosen ← NewIndex.callIfElse ops.toOps bindings.ifElse condition coordinate fallback
      let tuplePrefix := JuliaLean.base.boot.tupleV core [chosen]
      let nextIndices ← ops.call bindings.tail [indices]
      let nextKeep ← ops.call bindings.tail [keep]
      let nextDefaults ← ops.call bindings.tail [defaults]
      let nextMethod ← (fun world =>
        some (.ok (ops.selectedRemap nextIndices nextKeep nextDefaults world, world)) :
        CoreM W L Method)
      let suffix ← selected ops bindings nextMethod nextIndices nextKeep nextDefaults
      ops.applyIterate bindings.iterate
        [JuliaLean.base.boot.coreV core "tuple", tuplePrefix, suffix]
partial_fixpoint

/-- The selected generic method at base/broadcast.jl:598-599 enters its own
body directly. Only its recursive calls consult selectedRemap. This preserves
its full source domain, including explicitly invoked generic calls on values
whose ordinary top-level dispatch would choose an empty specialization. -/
-- Source: base/broadcast.jl:598-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _newindex(I, keep, Idefault) =
--     (ifelse(keep[1], I[1], Idefault[1]), _newindex(tail(I), tail(keep), tail(Idefault))...)
-- /Source
def remap {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (indices keep defaults : Value L) : CoreM W L (Value L) :=
  selected ops bindings .generic indices keep defaults

end JuliaLean.base.broadcast.Models2Group5.Remap


namespace JuliaLean.base.broadcast.Models2Group5.IndexForward

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source function identities for the selected forwarding bodies.
Input and returned types remain full runtime values. Julia source:
base/broadcast.jl:606,651,655,657. -/
-- Source: base/broadcast.jl:651-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(A::Union{Ref,AbstractArray{<:Any,0},Number}, I) = A[] # Scalar-likes can just ignore all indices
-- Base.@propagate_inbounds _broadcast_getindex(::Ref{Type{T}}, I) where {T} = T
-- # Tuples are statically known to be singleton or vector-like
-- Base.@propagate_inbounds _broadcast_getindex(A::Tuple{Any}, I) = A[1]
-- Base.@propagate_inbounds _broadcast_getindex(A::Tuple, I) = A[I[1]]
-- # Everything else falls back to dynamically dropping broadcasted indices based upon its axes
-- Base.@propagate_inbounds _broadcast_getindex(A, I) = A[newindex(A, I)]
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  shapeIndexer : Value L
  getindex : Value L
  newIndex : Value L

/-- The source606 composition keeps the actual axes result and selects
shapeindexer on its unfixed type. Both selected methods may mutate, throw,
return arbitrary values or diverge. No native-range or List specialization
replaces the original axes object. Source: base/broadcast.jl:606. -/
-- Source: base/broadcast.jl:606-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline newindexer(A) = shapeindexer(axes(A))
-- /Source
def newIndexer {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (array : Value L) : CoreM W L (Value L) := do
  let axes ← ops.call bindings.axes [array]
  ops.call bindings.shapeIndexer [axes]

/-- Bind the unchanged one-call source driver Index.m651 to the real
selected zero-index getindex. Its generic result parameter is the whole
CoreM action, so a thrown exception is propagated and is never stored as an
element. Ref parameters, zero-dimensional custom arrays and Number subtypes
are unfixed, and hence their selected getter stays open. The supplied index
is never read or converted. Applicable compiler bounds context is propagated
through the existing ContextOps interface. Source: base/broadcast.jl:651. -/
-- Source: base/broadcast.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(A::Union{Ref,AbstractArray{<:Any,0},Number}, I) = A[] # Scalar-likes can just ignore all indices
-- /Source
def scalar {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (array index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  Index.m651 (fun value => (contexts.inContext boundscheck).call bindings.getindex [value])
    array index

/-- The selected generic Tuple method first indexes the unrestricted index
object by native one, then invokes getindex on the original tuple and that
exact result. The tuple element parameters and returned index type are
unfixed, permitting selected custom methods; neither call is replaced by
List access or an Int-only conversion. The same propagated compiler context
selects both actual operations. Source: base/broadcast.jl:655. -/
-- Source: base/broadcast.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(A::Tuple, I) = A[I[1]]
-- /Source
def tuple {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (array index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let coordinate ← ops.call bindings.getindex
    [index, JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
  ops.call bindings.getindex [array, coordinate]

/-- Reuse unchanged Index.m657 for the selected fallback. It preserves
remapping before indexing and forwards the actual remapped object without
converting it or rebuilding the original array. Both operations dispatch on
unfixed types. Their runtime worlds, exception identities and divergence
remain in CoreM. Source: base/broadcast.jl:657. -/
-- Source: base/broadcast.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(A, I) = A[newindex(A, I)]
-- /Source
def fallback {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (array index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  let ops := contexts.inContext boundscheck
  Index.m657
    (fun array index => ops.call bindings.newIndex [array, index])
    (fun array mapped => ops.call bindings.getindex [array, mapped]) array index

end JuliaLean.base.broadcast.Models2Group5.IndexForward


namespace JuliaLean.base.broadcast.Models2Group5.IndexAccess

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source function and constructor bindings for base/broadcast.jl:615-633.
Bindings identify runtime functions; none supplies a callee answer. -/
-- Source: base/broadcast.jl:615-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function Base.getindex(bc::Broadcasted, Is::Vararg{Union{Integer,CartesianIndex},N}) where {N}
--     I = to_index(Base.IteratorsMD.flatten(Is))
--     _getindex(IndexStyle(bc), bc, I)
-- end
-- @inline function _getindex(::IndexStyle, bc, I)
--     @boundscheck checkbounds(bc, I)
--     @inbounds _broadcast_getindex(bc, I)
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
--     C = CartesianIndices(axes(bc))
--     _getindex(s, bc, C[I])
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
--     L = LinearIndices(axes(bc))
--     _getindex(s, bc, L[I])
-- end
-- to_index(::Tuple{}) = CartesianIndex()
-- to_index(Is::Tuple{Any}) = Is[1]
-- to_index(Is::Tuple) = CartesianIndex(Is)
-- /Source
structure Bindings (L : Type) where
  flatten : Value L
  toIndex : Value L
  indexStyle : Value L
  getindex : Value L
  getindexHelper : Value L
  checkbounds : Value L
  broadcastGetindex : Value L
  axes : Value L
  cartesianIndices : Value L
  linearIndices : Value L
  cartesianIndex : Value L

/-- The selected public indexing body, using the installed Index.m615 driver.
The machine-bounded heterogeneous tuple retains every coordinate and mutable
reference. Its tuple embedding represents the already-supplied varargs, not a
new source operation. The carrier is also usable for explicit invocation of
this body on a wider tuple; its ordinary dispatch domain has Integer or
CartesianIndex slots. All four targets depend on input or intermediate types
the source does not fix. The incoming bounds context is propagated as specified
by devdocs/boundscheck.md:70-79 and each contextual runtime operation retains
the callee's own inline/propagation behavior. 
Source reference: base/broadcast.jl:615-618.
-/
-- Source: base/broadcast.jl:615-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function Base.getindex(bc::Broadcasted, Is::Vararg{Union{Integer,CartesianIndex},N}) where {N}
--     I = to_index(Base.IteratorsMD.flatten(Is))
--     _getindex(IndexStyle(bc), bc, I)
-- end
-- /Source
def getindexBroadcasted {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (bc : Value L)
    (indices : Constructors.ArgumentTuple L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  let ops := contexts.inContext boundscheck
  Index.m615
    (fun tuple => ops.call bindings.flatten [tuple])
    (fun flat => ops.call bindings.toIndex [flat])
    (fun array => ops.call bindings.indexStyle [array])
    (fun style array index => ops.call bindings.getindexHelper [style, array, index])
    bc (JuliaLean.base.boot.tupleV ops indices.values)

/-- Bind the installed Index.m619 to the complete runtime-value domain. The
outer compiler flag determines only whether checkbounds runs. The element
reader always uses the source's explicit @inbounds context, independently of
that flag. A successful check's return value is discarded exactly as in Julia;
its arbitrary error, mutation or divergence is retained. The IndexStyle
argument is unused by this method, hence the installed driver's erased Bool
slot adds no source restriction or operation. 
Source reference: base/broadcast.jl:619-622.
-/
-- Source: base/broadcast.jl:619-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _getindex(::IndexStyle, bc, I)
--     @boundscheck checkbounds(bc, I)
--     @inbounds _broadcast_getindex(bc, I)
-- end
-- /Source
def getindexGeneric {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (_style bc index : Value L)
    (boundscheck : Bool := true) : CoreM W L (Value L) :=
  Index.m619
    (fun array coordinate => do
      let _ ← (contexts.inContext boundscheck).call bindings.checkbounds [array, coordinate]
      pure ())
    (fun array coordinate =>
      (contexts.inContext false).call bindings.broadcastGetindex [array, coordinate])
    false bc index boundscheck

/-- Pure current-world method-selection metadata for recursive _getindex
dispatch. The first three cases name the actual bodies at619,623,627;
custom means a genuinely selected different method on the unfixed argument
types. The selector does not compute or supply an indexing result. 
Source reference: base/broadcast.jl:619-630.
-/
-- Source: base/broadcast.jl:619-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _getindex(::IndexStyle, bc, I)
--     @boundscheck checkbounds(bc, I)
--     @inbounds _broadcast_getindex(bc, I)
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
--     C = CartesianIndices(axes(bc))
--     _getindex(s, bc, C[I])
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
--     L = LinearIndices(axes(bc))
--     _getindex(s, bc, L[I])
-- end
-- /Source
inductive Method where
  | generic
  | cartesianInteger
  | linearCartesian
  | custom

/-- The existing contextual runtime primitives and pure method selection.
Selection is read after all conversion effects have happened, so it sees the
actual resulting world. No law restricts any open callee's outcomes. 
Source reference: base/broadcast.jl:619-630.
-/
-- Source: base/broadcast.jl:619-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _getindex(::IndexStyle, bc, I)
--     @boundscheck checkbounds(bc, I)
--     @inbounds _broadcast_getindex(bc, I)
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
--     C = CartesianIndices(axes(bc))
--     _getindex(s, bc, C[I])
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
--     L = LinearIndices(axes(bc))
--     _getindex(s, bc, L[I])
-- end
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedGetindex : Value L → Value L → Value L → W → Method

/-- Execute a selected _getindex body. Each conversion branch evaluates axes,
its corresponding indices constructor and ordinary indexing, then explicitly
redispatches the resulting value. Returned values are never assumed to have
the usual Base type: custom axes, constructors and getindex methods may cause
the same conversion method to be selected again. Consequently this is the
installed CoreM least partial fixed point, with genuine divergence and no
fuel cutoff. Only a selected different method uses the open _getindex call.
The generic case reuses the existing complete model; conversion bodies remain
explicit so no callback replaces their own recursion. The context flag is
compiler metadata propagated by both conversion methods. 
Source reference: base/broadcast.jl:619-630.
-/
-- Source: base/broadcast.jl:619-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _getindex(::IndexStyle, bc, I)
--     @boundscheck checkbounds(bc, I)
--     @inbounds _broadcast_getindex(bc, I)
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
--     C = CartesianIndices(axes(bc))
--     _getindex(s, bc, C[I])
-- end
-- Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
--     L = LinearIndices(axes(bc))
--     _getindex(s, bc, L[I])
-- end
-- /Source
def runMethod {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (style bc index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let core := ops.contexts.inContext boundscheck
  match method with
  | .generic => getindexGeneric ops.contexts bindings style bc index boundscheck
  | .custom => core.call bindings.getindexHelper [style, bc, index]
  | .cartesianInteger =>
      let shape ← core.call bindings.axes [bc]
      let cartesian ← core.call bindings.cartesianIndices [shape]
      let converted ← core.call bindings.getindex [cartesian, index]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedGetindex style bc converted world, world)))
      runMethod ops bindings selected style bc converted boundscheck
  | .linearCartesian =>
      let shape ← core.call bindings.axes [bc]
      let linear ← core.call bindings.linearIndices [shape]
      let converted ← core.call bindings.getindex [linear, index]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedGetindex style bc converted world, world)))
      runMethod ops bindings selected style bc converted boundscheck
partial_fixpoint

/-- Selected source623 entry. Its first body is known; only subsequent calls
consult dispatch metadata after the constructor/indexing effects. 
Source reference: base/broadcast.jl:623-626.
-/
-- Source: base/broadcast.jl:623-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _getindex(s::IndexCartesian, bc, I::Integer)
--     C = CartesianIndices(axes(bc))
--     _getindex(s, bc, C[I])
-- end
-- /Source
def getindexCartesianInteger {W L : Type} (ops : Ops W L)
    (bindings : Bindings L) (style bc index : Value L)
    (boundscheck : Bool := true) : CoreM W L (Value L) :=
  runMethod ops bindings .cartesianInteger style bc index boundscheck

/-- Selected source627 entry, sharing the explicit partial recursive dispatcher
with source623. The original style and broadcast value are forwarded unchanged
through every recursive conversion. 
Source reference: base/broadcast.jl:627-630.
-/
-- Source: base/broadcast.jl:627-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _getindex(s::IndexLinear, bc, I::CartesianIndex)
--     L = LinearIndices(axes(bc))
--     _getindex(s, bc, L[I])
-- end
-- /Source
def getindexLinearCartesian {W L : Type} (ops : Ops W L)
    (bindings : Bindings L) (style bc index : Value L)
    (boundscheck : Bool := true) : CoreM W L (Value L) :=
  runMethod ops bindings .linearCartesian style bc index boundscheck

/-- Full selected source633 body. The tuple has native bounded size but keeps
arbitrary heterogeneous coordinates, including nested CartesianIndex values
and user Integer objects. Constructor dispatch depends on the tuple element
types left unfixed by this method, so it is the existing open CoreOps.call.
No conversion to mathematical Int lists, nested-coordinate flattening or
successful constructor result is silently imposed. Empty/singleton overloads
at631/632 are different selected methods and are not reimplemented here. 
Source reference: base/broadcast.jl:633-633.
-/
-- Source: base/broadcast.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_index(Is::Tuple) = CartesianIndex(Is)
-- /Source
def toIndexTuple {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (indices : Constructors.ArgumentTuple L) : CoreM W L (Value L) :=
  ops.call bindings.cartesianIndex [JuliaLean.base.boot.tupleV ops indices.values]

end JuliaLean.base.broadcast.Models2Group5.IndexAccess


namespace JuliaLean.base.broadcast.Models2Group5.CheckedBounds

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Source bindings and the nominal runtime encoding of the installed finite
IndexStyle carrier. indexStyleValue is a value embedding, not a constructor
callback: the actual concrete IndexLinear singleton is the encoding of
Lazy.IndexStyle.linear, as already modelled by Lazy.m262. The two generic
bounds bodies below keep every unfixed Broadcasted/Integer/axes type.
Source reference: base/broadcast.jl:635-643; base/indices.jl:37. -/
-- Source: base/broadcast.jl:635-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function Base.checkbounds(bc::Broadcasted, I::CartesianIndex)
--     Base.checkbounds_indices(Bool, axes(bc), (I,)) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- 
-- @inline function Base.checkbounds(bc::Broadcasted, I::Integer)
--     Base.checkindex(Bool, eachindex(IndexLinear(), bc), I) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  checkboundsIndices : Value L
  eachindex : Value L
  checkindex : Value L
  throwBoundsError : Value L
  indexStyleValue : Lazy.IndexStyle → Value L

/-- The source Boolean context of ||. This is the installed flfrontend.cond
lowering written against the already-imported CoreOps: a non-Bool raises
TypeError(:if, "", Bool, value), whereas a genuine Bool controls the branch.
No custom truth conversion or Base.ifelse call is inserted. The target
flfrontend module is not in the supplied import closure. This necessary
lowering helper is covered by both registered full-outcome bounds contracts.
Source reference: base/broadcast.jl:636,641. -/
-- Source: base/broadcast.jl:635-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function Base.checkbounds(bc::Broadcasted, I::CartesianIndex)
--     Base.checkbounds_indices(Bool, axes(bc), (I,)) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- 
-- @inline function Base.checkbounds(bc::Broadcasted, I::Integer)
--     Base.checkindex(Bool, eachindex(IndexLinear(), bc), I) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- /Source
def booleanContext {W L : Type} (ops : CoreOps W L) (value : Value L) :
    CoreM W L Bool :=
  match value with
  | .leaf leaf =>
      match ops.asBool leaf with
      | some flag => pure flag
      | none => JuliaLean.base.boot.throwTypeError ops "if" ""
          (JuliaLean.base.boot.coreV ops "Bool") value
  | _ => JuliaLean.base.boot.throwTypeError ops "if" ""
      (JuliaLean.base.boot.coreV ops "Bool") value

/-- Reuse unchanged Index.m635's ordered effectful driver. The original
Cartesian index is packed into a singleton tuple only for checkbounds_indices;
throw_boundserror receives the original index itself. The Bool type is an
explicit first argument to the selected bounds predicate. A true result
skips the error call; false invokes it and discards any custom successful
return before returning nothing. Non-Bool results fail at the Boolean
context. All selected calls depend on unfixed Broadcasted/axis types.
Source reference: base/broadcast.jl:635-638. -/
-- Source: base/broadcast.jl:635-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function Base.checkbounds(bc::Broadcasted, I::CartesianIndex)
--     Base.checkbounds_indices(Bool, axes(bc), (I,)) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- /Source
def cartesian {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc index : Value L) : CoreM W L (Value L) := do
  let _ ← Index.m635
    (fun bc => ops.call bindings.axes [bc])
    (fun axes indices => ops.call bindings.checkboundsIndices
      [JuliaLean.base.boot.coreV ops "Bool", axes, JuliaLean.base.boot.tupleV ops indices])
    (booleanContext ops)
    (fun bc index => do
      let _ ← ops.call bindings.throwBoundsError [bc, index]
      pure ()) bc index
  pure (JuliaLean.base.boot.nothingV ops)

/-- Reuse unchanged Index.m640's ordered driver. The concrete zero-field
IndexLinear singleton is the installed Lazy.m262 value, embedded without an
open constructor callback. Forced-linear eachindex precedes checkindex;
the original Integer is forwarded unchanged, with no native conversion or
range assumption. Both custom predicate/error-call results and every failure
remain at their source sites. Successful completion returns Julia nothing.
Source reference: base/broadcast.jl:640-643; base/broadcast.jl:262;
base/indices.jl:37 (the same singleton used by the installed model). -/
-- Source: base/broadcast.jl:640-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function Base.checkbounds(bc::Broadcasted, I::Integer)
--     Base.checkindex(Bool, eachindex(IndexLinear(), bc), I) || Base.throw_boundserror(bc, I)
--     nothing
-- end
-- /Source
def integer {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc index : Value L) : CoreM W L (Value L) := do
  let _ ← Index.m640
    (pure (bindings.indexStyleValue Lazy.m262))
    (fun style bc => ops.call bindings.eachindex [style, bc])
    (fun indices index => ops.call bindings.checkindex
      [JuliaLean.base.boot.coreV ops "Bool", indices, index])
    (booleanContext ops)
    (fun bc index => do
      let _ ← ops.call bindings.throwBoundsError [bc, index]
      pure ()) bc index
  pure (JuliaLean.base.boot.nothingV ops)

end JuliaLean.base.broadcast.Models2Group5.CheckedBounds


namespace JuliaLean.base.broadcast.Models2Group5.Extrusion

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed bindings for the source669-671 expressions. Extruded's type
parameters and all stored argument types are unfixed, so property access,
indexing and constructor selection use the existing runtime dispatch hooks.
The actual returned values may preserve mutable aliases or arbitrary types.
Source reference: base/broadcast.jl:664-671. -/
-- Source: base/broadcast.jl:664-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Extruded{T, K, D}
--     x::T
--     keeps::K    # A tuple of booleans, specifying which indices should be passed normally
--     defaults::D # A tuple of integers, specifying the index to use when keeps[i] is false (as defaults[i])
-- end
-- @inline axes(b::Extruded) = axes(b.x)
-- Base.@propagate_inbounds _broadcast_getindex(b::Extruded, i) = b.x[newindex(i, b.keeps, b.defaults)]
-- extrude(x::AbstractArray) = Extruded(x, newindexer(x)...)
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  axes : Value L
  newIndex : Value L
  getindex : Value L
  newIndexer : Value L
  extruded : Value L
  iterate : Value L

/-- Runtime metadata distinguishing a recursively selected source669 from a
selected different axes method. The selector supplies no axis result and can
observe mutations made by the preceding property getter. Unknown x types
permit genuinely different axes methods to remain open. 
Source reference: base/broadcast.jl:669-669.
-/
-- Source: base/broadcast.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline axes(b::Extruded) = axes(b.x)
-- /Source
inductive AxesMethod where
  | extruded
  | other

/-- Existing runtime primitives with pure current-world axes dispatch metadata.
Only an actually selected source669 body follows the explicit recursive edge.
Source reference: base/broadcast.jl:669. -/
-- Source: base/broadcast.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline axes(b::Extruded) = axes(b.x)
-- /Source
structure AxesOps (W L : Type) extends CoreOps W L where
  selectedAxes : Value L → W → AxesMethod

/-- Complete axes forwarding at source669. A nested Extruded stored x can
select this same method again, so its own recursion is a genuine least
partial fixed point rather than a supplied callback or bounded traversal.
The unfixed Extruded type parameters also permit selected property extensions;
therefore x is read by the actual generic getter before axes redispatch.
Cyclic custom getters can diverge. A genuinely different axes target receives
the exact stored/property result, with every exception and world preserved.
Source reference: base/broadcast.jl:669. -/
-- Source: base/broadcast.jl:669-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline axes(b::Extruded) = axes(b.x)
-- /Source
def axes {W L : Type} (ops : AxesOps W L) (bindings : Bindings L)
    (value : Value L) : CoreM W L (Value L) := do
  let underlying ← ops.call bindings.getproperty [value, .symbol "x"]
  let selected ← (fun world =>
    some (.ok (ops.selectedAxes underlying world, world)))
  match selected with
  | .extruded => axes ops bindings underlying
  | .other => ops.call bindings.axes [underlying]
partial_fixpoint

/-- Full source670 expression, including evaluation of b.x before the two
metadata properties. The original index and exact keeps/defaults values are
passed to newindex; the array reference obtained before remapping is then
indexed with its returned coordinate. Thus getter/remapper mutations cannot
cause an invented second b.x read. All Extruded parameters, index types and
intermediate result types remain unfixed; the selected calls are open under
the packet rule. The incoming @propagate_inbounds context is retained through
the existing contextual CoreOps interface. Julia source: base/broadcast.jl:670;
doc/src/devdocs/boundscheck.md:70-79. -/
-- Source: base/broadcast.jl:670-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(b::Extruded, i) = b.x[newindex(i, b.keeps, b.defaults)]
-- /Source
def broadcastGetindex {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (value index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let underlying ← ops.call bindings.getproperty [value, .symbol "x"]
  let keeps ← ops.call bindings.getproperty [value, .symbol "keeps"]
  let defaults ← ops.call bindings.getproperty [value, .symbol "defaults"]
  let mapped ← ops.call bindings.newIndex [index, keeps, defaults]
  ops.call bindings.getindex [underlying, mapped]

/-- Complete source671 expression. The actual newindexer dispatch is open on
the unfixed AbstractArray type; its returned value is splatted by the installed
_apply_iterate primitive. The source does not assert that result is a pair of
Boolean/native-Int lists, or that the selected Extruded constructor returns a
particular record. The original array remains the first constructor argument,
with all iterator/constructor failures, mutation and arbitrary results retained.
Source reference: base/broadcast.jl:671. -/
-- Source: base/broadcast.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- extrude(x::AbstractArray) = Extruded(x, newindexer(x)...)
-- /Source
def extrude {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (array : Value L) : CoreM W L (Value L) := do
  let metadata ← ops.call bindings.newIndexer [array]
  ops.applyIterate bindings.iterate
    [bindings.extruded, JuliaLean.base.boot.tupleV ops [array], metadata]

end JuliaLean.base.broadcast.Models2Group5.Extrusion


namespace JuliaLean.base.broadcast.Models2Group5.BroadcastEvaluation

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed generic function identities for source675-697. Broadcasted's type
parameters, the coordinate type, tuple element types and scalar callable type
remain unfixed. Their selected property, tail, gather and evaluation targets
therefore use the installed runtime call/splat interfaces. The source's evalf
boundary is retained as a function target: its own non-propagating behavior
is not replaced by a direct call to f in the caller's inbounds context.
Source reference: base/broadcast.jl:675-704. -/
-- Source: base/broadcast.jl:675-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Any}, I)
--     args = _getindex(bc.args, I)
--     return _broadcast_getindex_evalf(bc.f, args...)
-- end
-- # Hack around losing Type{T} information in the final args tuple. Julia actually
-- # knows (in `code_typed`) the _value_ of these types, statically displaying them,
-- # but inference is currently skipping inferring the type of the types as they are
-- # transiently placed in a tuple as the argument list is lispily constructed. These
-- # additional methods recover type stability when a `Type` appears in one of the
-- # first two arguments of a function.
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     args = _getindex(tail(bc.args), I)
--     return _broadcast_getindex_evalf(bc.f, T, args...)
-- end
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Any,Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     arg1 = _broadcast_getindex(bc.args[1], I)
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, arg1, T, args...)
-- end
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Ref{Type{S}},Vararg{Any}}}, I) where {T,S}
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, T, S, args...)
-- end
-- 
-- # Utilities for _broadcast_getindex
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- 
-- @inline _broadcast_getindex_evalf(f::Tf, args::Vararg{Any,N}) where {Tf,N} = f(args...)  # not propagate_inbounds
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  getindex : Value L
  tail : Value L
  gather : Value L
  evalf : Value L
  broadcastGetindex : Value L
  iterate : Value L

/-- Full selected general Broadcasted element body. Read the actual args
property, gather at the original coordinate, then read f and invoke the exact
evalf binding with f followed by the arbitrary gathered object's runtime
splat. No forced list/tuple result, type assertion, argument conversion or
associative rewrite is introduced. The intermediate function is read after
all gathering effects; incoming bounds context propagates through this body
while each runtime target retains its own call-boundary behavior.
Source reference: base/broadcast.jl:675-678. -/
-- Source: base/broadcast.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Any}, I)
--     args = _getindex(bc.args, I)
--     return _broadcast_getindex_evalf(bc.f, args...)
-- end
-- /Source
def generic {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (bc index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let stored ← ops.call bindings.getproperty [bc, .symbol "args"]
  let arguments ← ops.call bindings.gather [stored, index]
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  ops.applyIterate bindings.iterate
    [bindings.evalf, JuliaLean.base.boot.tupleV ops [function], arguments]

/-- The first-type specialization supplies the method's actual static T as a
value, never reading the first type-reference payload. After the property
getter and selected tail method, gathering uses the original coordinate and
only then reads f. The final runtime splat has prefix (f,T), preserving all
custom getter/tail/gather/evalf effects without any payload-correctness law.
The typeValue argument is dispatch metadata, not an additional Julia argument.
Source reference: base/broadcast.jl:685-688; rationale at679-684. -/
-- Source: base/broadcast.jl:685-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     args = _getindex(tail(bc.args), I)
--     return _broadcast_getindex_evalf(bc.f, T, args...)
-- end
-- /Source
def firstType {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (typeValue bc index : Value L)
    (boundscheck : Bool := true) : CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let stored ← ops.call bindings.getproperty [bc, .symbol "args"]
  let remaining ← ops.call bindings.tail [stored]
  let arguments ← ops.call bindings.gather [remaining, index]
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  ops.applyIterate bindings.iterate
    [bindings.evalf, JuliaLean.base.boot.tupleV ops [function, typeValue], arguments]

/-- Selection metadata for source689's direct _broadcast_getindex call.
A same-method tag carries the actual type parameter of that selected recursive
invocation. Every genuinely different selected method remains an open call on
the unfixed first argument and coordinate; no callback replaces self689.
Source reference: base/broadcast.jl:689-693. -/
-- Source: base/broadcast.jl:689-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Any,Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     arg1 = _broadcast_getindex(bc.args[1], I)
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, arg1, T, args...)
-- end
-- /Source
inductive ElementMethod (L : Type) where
  | same (typeValue : Value L)
  | other

/-- Contextual runtime operations and pure current-world selection metadata
for the one source specialization with a direct self-recursive call. Selection
happens only after bc.args[1] has actually been evaluated. It does not supply
a scalar result or assume a terminating/acyclic broadcast tree.
Source reference: base/broadcast.jl:689-693. -/
-- Source: base/broadcast.jl:689-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Any,Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     arg1 = _broadcast_getindex(bc.args[1], I)
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, arg1, T, args...)
-- end
-- /Source
structure SecondOps (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedElement : Value L → Value L → W → ElementMethod L

/-- Complete source689 body with genuine recursion. The first args property
is indexed once, then its selected element is evaluated before any remaining
gather. A selected self689 call executes this actual body at its own T and
input, permitting cyclic custom getters and genuine divergence. After it
returns, bc.args is read again: effects in the first read/element evaluation
may change that result. Two tails precede gathering; f is read last, and the
evalf splat prefix is exactly (f, firstResult, T). No type-reference payload
read or frozen first args-property snapshot is substituted. The source's
incoming bounds context is propagated across recursive calls.
Source reference: base/broadcast.jl:689-693; rationale at679-684. -/
-- Source: base/broadcast.jl:689-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Any,Ref{Type{T}},Vararg{Any}}}, I) where {T}
--     arg1 = _broadcast_getindex(bc.args[1], I)
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, arg1, T, args...)
-- end
-- /Source
def secondType {W L : Type} (ops : SecondOps W L) (bindings : Bindings L)
    (typeValue bc index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let core := ops.contexts.inContext boundscheck
  let stored ← core.call bindings.getproperty [bc, .symbol "args"]
  let first ← core.call bindings.getindex
    [stored, JuliaLean.base.boot.intV core (JInt.lit .i64 1)]
  let selected ← (fun world =>
    some (.ok (ops.selectedElement first index world, world)))
  let firstValue ← match selected with
    | .same nestedType => secondType ops bindings nestedType first index boundscheck
    | .other => core.call bindings.broadcastGetindex [first, index]
  let storedAgain ← core.call bindings.getproperty [bc, .symbol "args"]
  let tailOnce ← core.call bindings.tail [storedAgain]
  let tailTwice ← core.call bindings.tail [tailOnce]
  let arguments ← core.call bindings.gather [tailTwice, index]
  let function ← core.call bindings.getproperty [bc, .symbol "f"]
  core.applyIterate bindings.iterate
    [bindings.evalf, JuliaLean.base.boot.tupleV core [function, firstValue, typeValue],
      arguments]
partial_fixpoint

/-- Complete source694 body. The actual static T and S parameters precede
all remaining gathered arguments; neither type-reference payload is indexed.
Property access, both ordered tail calls and gathering retain their arbitrary
selected results/effects before f is obtained. Existing runtime splatting
preserves any returned iterable and every failure at the evalf boundary.
Source reference: base/broadcast.jl:694-697; rationale at679-684. -/
-- Source: base/broadcast.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Ref{Type{S}},Vararg{Any}}}, I) where {T,S}
--     args = _getindex(tail(tail(bc.args)), I)
--     return _broadcast_getindex_evalf(bc.f, T, S, args...)
-- end
-- /Source
def bothTypes {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (firstTypeValue secondTypeValue bc index : Value L)
    (boundscheck : Bool := true) : CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let stored ← ops.call bindings.getproperty [bc, .symbol "args"]
  let tailOnce ← ops.call bindings.tail [stored]
  let tailTwice ← ops.call bindings.tail [tailOnce]
  let arguments ← ops.call bindings.gather [tailTwice, index]
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  ops.applyIterate bindings.iterate
    [bindings.evalf,
      JuliaLean.base.boot.tupleV ops [function, firstTypeValue, secondTypeValue], arguments]

end JuliaLean.base.broadcast.Models2Group5.BroadcastEvaluation


namespace JuliaLean.base.broadcast.Models2Group5.Gather

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual selected recursive _getindex method. Tuple element/arity parameters
remain unfixed; a custom method is a genuinely selected other method, never
a replacement for either Base recursive body. Source: base/broadcast.jl:700-702. -/
-- Source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- /Source
inductive Method where
  | generic
  | singleton
  | empty
  | custom

/-- Existing tuple-get/runtime operations plus current-world recursive
selection. NewIndex.IntegerOps already distinguishes the concrete Tuple/Int
getfield body from genuinely custom tuple getindex methods; its ifelse field
is unused here. Tail dispatch stays open on the tuple's unfixed element and
arity parameters. Source: base/broadcast.jl:700-702. -/
-- Source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- /Source
structure Ops (W L : Type) extends NewIndex.IntegerOps W L where
  selectedGather : Value L → Value L → W → Method

/-- Runtime operations in the applicable propagated compiler bounds context.
The Bool is metadata, not a Julia argument. This follows the installed
Index.m700/m701 and the source @propagate_inbounds convention, including the
native tuple getfield used by a canonical tuple getindex call.
Source: base/broadcast.jl:700-702; devdocs/boundscheck.md:70-79. -/
-- Source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- /Source
structure ContextOps (W L : Type) where
  inContext : Bool → Ops W L

/-- Fixed generic function identities in base/broadcast.jl:700-702. -/
-- Source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- /Source
structure Bindings (L : Type) where
  getindex : Value L
  broadcastGetindex : Value L
  tail : Value L
  gather : Value L
  iterate : Value L

/-- Full selected singleton body at base/broadcast.jl:701. The source's
Tuple{Any} signature includes covariant one-element tuples with any actual
element type. The native Tuple/Int case executes its installed getfield body;
a genuinely selected custom tuple getter remains open. Then reuse Index.m701
to call _broadcast_getindex once and construct the singleton result. The
input tuple is an opaque runtime value, so actual native bounds/error/context
behavior is not replaced by total Lean head access. Returned mutable values
are stored by identity in the new immutable tuple, never copied. -/
-- Source: base/broadcast.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- /Source
def singleton {W L : Type} (contexts : ContextOps W L)
    (bindings : Bindings L) (args index : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let core := ops.toIntegerOps.toOps.toCoreOps
  let head ← NewIndex.tupleGet ops.toIntegerOps bindings.getindex args (JInt.lit .i64 1)
  let values ← Index.m701 (m := CoreM W L)
    (fun _ value coordinate => ops.call bindings.broadcastGetindex [value, coordinate])
    head index boundscheck
  pure (JuliaLean.base.boot.tupleV core values)

/-- Explicit source recursion for base/broadcast.jl:700-702. The generic body
reads args[1], evaluates its broadcast index, calls tail, recursively executes
the actual selected _getindex body in the resulting world, then splats the
resulting suffix with the first value. Recursive dispatch is explicit and
can select either Base case or another method. Custom tail results may be
arbitrary values, aliases or cycles, so recursion uses the installed CoreM
partial_fixpoint mechanism; no List restriction, fuel or termination promise
is imposed. Concrete tuple reads retain their native error point, even when
the generic method is explicitly invoked on an empty tuple. The final splat
uses the existing _apply_iterate primitive and may itself fail or diverge. -/
-- Source: base/broadcast.jl:700-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- /Source
def selected {W L : Type} (contexts : ContextOps W L) (bindings : Bindings L)
    (boundscheck : Bool) (method : Method) (args index : Value L) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  let core := ops.toIntegerOps.toOps.toCoreOps
  match method with
  | .empty =>
      let values ← Index.m702 (m := CoreM W L) (V := Value L) index
      pure (JuliaLean.base.boot.tupleV core values)
  | .singleton => singleton contexts bindings args index boundscheck
  | .custom => ops.call bindings.gather [args, index]
  | .generic =>
      let head ← NewIndex.tupleGet ops.toIntegerOps bindings.getindex args (JInt.lit .i64 1)
      let first ← ops.call bindings.broadcastGetindex [head, index]
      let remaining ← ops.call bindings.tail [args]
      let nextMethod ← (fun world =>
        some (.ok (ops.selectedGather remaining index world, world)) : CoreM W L Method)
      let suffix ← selected contexts bindings boundscheck nextMethod remaining index
      ops.applyIterate bindings.iterate
        [JuliaLean.base.boot.coreV core "tuple", JuliaLean.base.boot.tupleV core [first], suffix]
partial_fixpoint

/-- The selected generic method enters its source body directly. This permits
explicit invocation independently of the ordinary top-level dispatch that
would choose an empty or singleton overload. Source: base/broadcast.jl:700. -/
-- Source: base/broadcast.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- /Source
def gather {W L : Type} (contexts : ContextOps W L) (bindings : Bindings L)
    (args index : Value L) (boundscheck : Bool := true) : CoreM W L (Value L) :=
  selected contexts bindings boundscheck .generic args index

end JuliaLean.base.broadcast.Models2Group5.Gather


namespace JuliaLean.base.broadcast.Models2Group5.ScalarBroadcastable

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Full selected BroadcastScalars method at base/broadcast.jl:736. The scalar
union includes unfixed AbstractString/Function and other parameterized types,
so Ref constructor dispatch stays at the existing CoreOps.call boundary. It
receives the exact original scalar and preserves its actual returned runtime
reference, allocation world, exception or divergence. The returned mutable
Ref is not replaced with an immutable Lean payload record. The canonical
Ref/RefValue chain is in refpointer.jl:145 and refvalue.jl:5-10; this caller
fixes no concrete scalar type selecting that one constructor implementation.
The source adds no post-call Ref assertion or copy. -/
-- Source: base/broadcast.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcastable(x::BroadcastScalars) = Ref(x)
-- /Source
def scalar {W L : Type} (ops : CoreOps W L) (value : Value L) :
    CoreM W L (Value L) :=
  ops.call (JuliaLean.base.boot.coreV ops "Ref") [value]

/-- Full selected type-object method at base/broadcast.jl:737. T is the
original dispatch-bound type value, including arbitrary Julia type objects.
Construct Type{T}, then Ref{Type{T}}, then invoke that actual applied type on T.
The constructor target depends on the unfixed T, so selected custom and Base
constructors remain in the existing generic-call interface without laws.
Mutable allocation identity is the actual returned Value in CoreM's world;
no type object, mutable Ref, or field contents are replaced by Lean metadata.
All type-application errors precede the constructor at their original sites,
and no extra typeof, conversion, assertion or payload read is inserted.
Source: base/broadcast.jl:737; refpointer.jl:147; manual/types.md:1276-1323. -/
-- Source: base/broadcast.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcastable(::Type{T}) where {T} = Ref{Type{T}}(T)
-- /Source
def typeObject {W L : Type} (ops : CoreOps W L) (type : Value L) :
    CoreM W L (Value L) := do
  let selector ← ops.applyType (JuliaLean.base.boot.coreV ops "Type") [type]
  let refType ← ops.applyType (JuliaLean.base.boot.coreV ops "Ref") [selector]
  ops.call refType [type]

end JuliaLean.base.broadcast.Models2Group5.ScalarBroadcastable


namespace JuliaLean.base.broadcast.Models2Group5.RuntimeTypes

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Full builtin isa at a dynamic RHS type value. The installed primitive
CoreOps.isa is a pure membership test; its use with the fixed Core.Type RHS
first validates the supplied target. A non-type target raises the runtime
TypeError(:isa,"",Type,target) before membership evaluation. A valid target
uses the installed primitive directly without conversion or custom dispatch.
Necessary for eltype(dest) replies at base/broadcast.jl:1152. Core exports
both builtins at boot.jl:252; runtime JL_TYPECHK in jl_f_isa verifies argument2.
This is a local completion of the dynamic argument check, not a shared
interface change or an additional Julia user-level call.
Source: base/broadcast.jl:1145-1163. -/
-- Source: base/broadcast.jl:1145-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
def checkedIsa {W L : Type} (ops : CoreOps W L) (value type : Value L) :
    CoreM W L Bool :=
  if ops.isa type (JuliaLean.base.boot.coreV ops "Type") then
    pure (ops.isa value type)
  else JuliaLean.base.boot.throwTypeError ops "isa" ""
    (JuliaLean.base.boot.coreV ops "Type") type

/-- Full builtin typeassert when the RHS is dynamically computed. The same
runtime argument2 check precedes membership; its invalid-target TypeError
expects Core.Type and reports the target itself. Valid targets delegate to
the unchanged installed boot.typeassert, preserving the original value on
success and the actual asserted type/value on failed membership.
Necessary for source751 and dynamically applied UnionAll assertions in copy.
Core exports both builtins at boot.jl:252; runtime jl_f_typeassert performs
JL_TYPECHK before its jl_isa check. Source: base/broadcast.jl:751. -/
-- Source: base/broadcast.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- /Source
def checkedAssert {W L : Type} (ops : CoreOps W L) (value type : Value L) :
    CoreM W L (Value L) :=
  if ops.isa type (JuliaLean.base.boot.coreV ops "Type") then
    JuliaLean.base.boot.typeassert ops value type
  else JuliaLean.base.boot.throwTypeError ops "typeassert" ""
    (JuliaLean.base.boot.coreV ops "Type") type

end JuliaLean.base.broadcast.Models2Group5.RuntimeTypes


namespace JuliaLean.base.broadcast.Models2Group5.EltypeSampling

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed runtime function identities for source744-754. Property reads,
indexing and sampling retain the existing CoreOps dispatch boundary; the
tuple constructor is the actual Core.tuple binding used by Julia's splat
lowering. No field contains a precomputed sampling result. 
Source reference: base/broadcast.jl:744-754.
-/
-- Source: base/broadcast.jl:744-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- # Numbers must broadcast as scalars even if they override eltype
-- # Tuples may have heterogenous eltypes across indices
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- # since this method only exists to be inferred, indexing x is never actually executed. the
-- # inference barrier prevents recursion limiting, and ::eltype gives the desired result
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- 
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- _bc_eltypes(::Tuple{}, i) = ()
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  getindex : Value L
  tail : Value L
  bcEltype : Value L
  bcEltypes : Value L
  broadcastGetindex : Value L
  eltype : Value L
  iterate : Value L

/-- Runtime type-directed selection for _bc_eltype. The source fixes only a
UnionAll Broadcasted, Number, Tuple, or unconstrained value at these entries.
custom names a genuinely selected additional method. 
Source reference: base/broadcast.jl:744-751.
-/
-- Source: base/broadcast.jl:744-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- # Numbers must broadcast as scalars even if they override eltype
-- # Tuples may have heterogenous eltypes across indices
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- # since this method only exists to be inferred, indexing x is never actually executed. the
-- # inference barrier prevents recursion limiting, and ::eltype gives the desired result
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- /Source
inductive SampleMethod where
  | broadcasted
  | number
  | tuple
  | fallback
  | custom

/-- Selected _bc_eltypes method. The known empty method is explicit, and
selected nonempty source753 retains its own actual recursive body. A custom
tail method remains open on the unfixed tuple/intermediate type. 
Source reference: base/broadcast.jl:753-754.
-/
-- Source: base/broadcast.jl:753-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- _bc_eltypes(::Tuple{}, i) = ()
-- /Source
inductive SamplesMethod where
  | empty
  | recursive
  | custom

/-- Existing runtime operations plus pure current-world dispatch metadata.
The selectors receive original runtime values and the actual current world;
they select method bodies, not their answers. No callee correctness law is
assumed. 
Source reference: base/broadcast.jl:744-754.
-/
-- Source: base/broadcast.jl:744-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- # Numbers must broadcast as scalars even if they override eltype
-- # Tuples may have heterogenous eltypes across indices
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- # since this method only exists to be inferred, indexing x is never actually executed. the
-- # inference barrier prevents recursion limiting, and ::eltype gives the desired result
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- 
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- _bc_eltypes(::Tuple{}, i) = ()
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedSample : Value L → Value L → W → SampleMethod
  selectedSamples : Value L → Value L → W → SamplesMethod

/-- Work item for the mutually recursive selected source methods. This is
model control state, not an additional Julia value or public argument. 
Source reference: base/broadcast.jl:744-754.
-/
-- Source: base/broadcast.jl:744-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- # Numbers must broadcast as scalars even if they override eltype
-- # Tuples may have heterogenous eltypes across indices
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- # since this method only exists to be inferred, indexing x is never actually executed. the
-- # inference barrier prevents recursion limiting, and ::eltype gives the desired result
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- 
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- _bc_eltypes(::Tuple{}, i) = ()
-- /Source
inductive Request (L : Type) where
  | sample (method : SampleMethod) (value index : Value L)
  | samples (method : SamplesMethod) (arguments index : Value L)

/-- Number sampling forwards the original value and index to the selected
_broadcast_getindex method. Number subtypes and index types are unfixed, so
the call preserves arbitrary custom outcomes through CoreM. 
Source reference: base/broadcast.jl:747-747.
-/
-- Source: base/broadcast.jl:747-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- /Source
def sampleNumber {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value index : Value L) : CoreM W L (Value L) :=
  ops.call bindings.broadcastGetindex [value, index]

/-- Tuple sampling has the same forwarding body, with unrestricted tuple
parameters and index types. The tuple remains an opaque constructible runtime
value; no unbounded mathematical coordinate list replaces it. 
Source reference: base/broadcast.jl:748-748.
-/
-- Source: base/broadcast.jl:748-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- /Source
def sampleTuple {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value index : Value L) : CoreM W L (Value L) :=
  ops.call bindings.broadcastGetindex [value, index]

/-- Execute the installed inferencebarrier at its literal :type setting, then
sample before querying eltype and applying the installed builtin assertion.
The barrier's successful projection reduces definitionally in the installed
model; the proof is a representation fact, not a theorem about this method.
Return values, type objects (including UnionAll), mutations, custom dispatch,
errors and divergence all remain actual CoreM/Value outcomes. 
Source reference: base/broadcast.jl:751-751.
-/
-- Source: base/broadcast.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- /Source
def sampleFallback {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value index : Value L) : CoreM W L (Value L) := do
  let barrier := (JuliaLean.base.essentials.inferencebarrier value).toOption.get (by rfl)
  let sampled ← ops.call bindings.broadcastGetindex [barrier, index]
  let elementType ← ops.call bindings.eltype [value]
  RuntimeTypes.checkedAssert ops sampled elementType

/-- Explicit mutual source recursion. A Broadcasted sample captures bc.f
before bc.args, executes the selected argument sampler, then splats that exact
result into the captured callable. Recursive tuple sampling obtains args[1],
samples it, obtains tail(args), samples that exact tail and finally performs
the source tuple splat. Custom property/index/tail results are not assumed to
be canonical values or even tuples. If they cause the same selected method to
recur indefinitely, the installed CoreM partial fixed point diverges; no fuel
or fabricated sample terminates it. Only genuinely selected additional
sampling methods use the corresponding open whole-function call.

The empty branch reuses the installed Material.m754 and embeds its actual
empty tuple. All other tuples here are existing runtime values or the source's
literal singleton tuple, so no unbounded list is introduced as a Julia value.
Each open call has the caller's actual runtime context encoded by CoreOps;
these source methods have no @propagate_inbounds annotation. 
Source reference: base/broadcast.jl:744-754.
-/
-- Source: base/broadcast.jl:744-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- # Numbers must broadcast as scalars even if they override eltype
-- # Tuples may have heterogenous eltypes across indices
-- _bc_eltype(x::Number, i) = _broadcast_getindex(x, i)
-- _bc_eltype(x::Tuple, i) = _broadcast_getindex(x, i)
-- # since this method only exists to be inferred, indexing x is never actually executed. the
-- # inference barrier prevents recursion limiting, and ::eltype gives the desired result
-- _bc_eltype(x, i) = _broadcast_getindex(Base.inferencebarrier(x), i)::eltype(x)
-- 
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- _bc_eltypes(::Tuple{}, i) = ()
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L) :
    Request L → CoreM W L (Value L)
  | .sample .number value index => sampleNumber ops.toCoreOps bindings value index
  | .sample .tuple value index => sampleTuple ops.toCoreOps bindings value index
  | .sample .fallback value index => sampleFallback ops.toCoreOps bindings value index
  | .sample .custom value index => ops.call bindings.bcEltype [value, index]
  | .sample .broadcasted bc index => do
      let function ← ops.call bindings.getproperty [bc, .symbol "f"]
      let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
      let selected ← (show CoreM W L SamplesMethod from fun world =>
        some (.ok (ops.selectedSamples arguments index world, world)))
      let sampled ← run ops bindings (.samples selected arguments index)
      ops.applyIterate bindings.iterate [function, sampled]
  | .samples .empty _ index =>
      pure (JuliaLean.base.boot.tupleV ops.toCoreOps
        (Material.m754 (V := Value L) index))
  | .samples .custom arguments index => ops.call bindings.bcEltypes [arguments, index]
  | .samples .recursive arguments index => do
      let head ← ops.call bindings.getindex
        [arguments, JuliaLean.base.boot.intV ops.toCoreOps (JInt.lit .i64 1)]
      let headMethod ← (show CoreM W L SampleMethod from fun world =>
        some (.ok (ops.selectedSample head index world, world)))
      let sampled ← run ops bindings (.sample headMethod head index)
      let rest ← ops.call bindings.tail [arguments]
      let restMethod ← (show CoreM W L SamplesMethod from fun world =>
        some (.ok (ops.selectedSamples rest index world, world)))
      let suffix ← run ops bindings (.samples restMethod rest index)
      ops.applyIterate bindings.iterate
        [JuliaLean.base.boot.coreV ops.toCoreOps "tuple",
         JuliaLean.base.boot.tupleV ops.toCoreOps [sampled], suffix]
partial_fixpoint

/-- Selected source744 entry, with explicit nested argument recursion and
runtime property access retained by run. 
Source reference: base/broadcast.jl:744-744.
-/
-- Source: base/broadcast.jl:744-744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltype(bc::Broadcasted, i) = bc.f(_bc_eltypes(bc.args, i)...)
-- /Source
def sampleBroadcasted {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (bc index : Value L) : CoreM W L (Value L) :=
  run ops bindings (.sample .broadcasted bc index)

/-- Selected source753 body. In ordinary dispatch an empty input selects the
separate known empty case; an explicit invocation of this generic body on an
empty tuple still attempts its real first indexing operation. 
Source reference: base/broadcast.jl:753-753.
-/
-- Source: base/broadcast.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bc_eltypes(args::Tuple, i) = (_bc_eltype(args[1], i), _bc_eltypes(tail(args), i)...)
-- /Source
def sampleArguments {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (arguments index : Value L) : CoreM W L (Value L) :=
  run ops bindings (.samples .recursive arguments index)

end JuliaLean.base.broadcast.Models2Group5.EltypeSampling


namespace JuliaLean.base.broadcast.Models2Group5.EltypeInference

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed runtime bindings for the inference and retained legacy protocols.
emptyTupleType is the source's compiled Tuple{} constant, representing the
installed Material.m768 empty tuple-type result; it is not an inferred answer.
All other fields are the actual named function identities. 
Source reference: base/broadcast.jl:756-778.
-/
-- Source: base/broadcast.jl:756-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function result_eltype(bc::Broadcasted)
--     argtypes = Iterators.TupleOrBottom(typeof(bc), eltype(eachindex(bc)))
--     argtypes === Union{} && return Union{}
--     rettype = Base._return_type(_bc_eltype, argtypes)
--     return promote_typejoin_union(rettype)
-- end
-- 
-- ### this machinery is now dead code in Base, but several packages
-- ### reach into these internals so it's retained for convenience.
-- _broadcast_getindex_eltype(bc::Broadcasted) = combine_eltypes(bc.f, bc.args)
-- _broadcast_getindex_eltype(A) = eltype(A)  # Tuple, Array, etc.
-- 
-- eltypes(::Tuple{}) = Tuple{}
-- eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
-- eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
-- eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
-- 
-- # Inferred eltype of result of broadcast(f, args...)
-- function combine_eltypes(f, args::Tuple)
--     argT = eltypes(args)
--     argT === Union{} && return Union{}
--     return promote_typejoin_union(Base._return_type(f, argT))
-- end
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  getindex : Value L
  tail : Value L
  eltype : Value L
  eachindex : Value L
  tupleOrBottom : Value L
  returnType : Value L
  promoteUnion : Value L
  bcEltype : Value L
  broadcastGetindexEltype : Value L
  combineEltypes : Value L
  eltypes : Value L
  iterate : Value L
  emptyTupleType : Value L

/-- Full runtime-type result inference. Builtin typeof observes the original
Broadcasted object before the eachindex/eltype calls. TupleOrBottom dispatch
is open on its unfixed type arguments, including custom returned objects.
Only actual identity with Union{} skips reflection and promotion. The compiler
reflection primitive and promotion remain existing runtime calls on unfixed
argument/result types; neither a type oracle nor a PType/JType approximation
replaces their results, errors or worlds. 
Source reference: base/broadcast.jl:756-761.
-/
-- Source: base/broadcast.jl:756-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function result_eltype(bc::Broadcasted)
--     argtypes = Iterators.TupleOrBottom(typeof(bc), eltype(eachindex(bc)))
--     argtypes === Union{} && return Union{}
--     rettype = Base._return_type(_bc_eltype, argtypes)
--     return promote_typejoin_union(rettype)
-- end
-- /Source
def resultEltype {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let broadcastType : Value L := .leaf (ops.typeOf bc)
  let indices ← ops.call bindings.eachindex [bc]
  let indexType ← ops.call bindings.eltype [indices]
  let argumentTypes ← ops.call bindings.tupleOrBottom [broadcastType, indexType]
  if ops.same argumentTypes (JuliaLean.base.boot.coreV ops "Union{}") then
    pure (JuliaLean.base.boot.coreV ops "Union{}")
  else do
    let inferred ← ops.call bindings.returnType [bindings.bcEltype, argumentTypes]
    ops.call bindings.promoteUnion [inferred]

/-- The retained Broadcasted element-type wrapper reads f before args, then
passes those exact property results to combine_eltypes. Both Broadcasted
parameters and property result types are unfixed, so the actual selected
methods retain open dispatch and effects. 
Source reference: base/broadcast.jl:765-765.
-/
-- Source: base/broadcast.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _broadcast_getindex_eltype(bc::Broadcasted) = combine_eltypes(bc.f, bc.args)
-- /Source
def broadcastedEltype {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
  ops.call bindings.combineEltypes [function, arguments]

/-- The non-Broadcasted fallback is one generic eltype call on the original
value. The complete runtime type domain and arbitrary selected outcomes are
retained, including UnionAll and custom type-like return values. 
Source reference: base/broadcast.jl:766-766.
-/
-- Source: base/broadcast.jl:766-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _broadcast_getindex_eltype(A) = eltype(A)  # Tuple, Array, etc.
-- /Source
def otherEltype {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value : Value L) : CoreM W L (Value L) :=
  ops.call bindings.eltype [value]

/-- Full selected singleton body. Tuple element parameters and the queried
element type are unfixed; both real indexing and element-type dispatch stay
at CoreOps.call, followed by the actual TupleOrBottom call. 
Source reference: base/broadcast.jl:769-769.
-/
-- Source: base/broadcast.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
-- /Source
def oneEltype {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (tuple : Value L) : CoreM W L (Value L) := do
  let first ← ops.call bindings.getindex
    [tuple, JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
  let firstType ← ops.call bindings.broadcastGetindexEltype [first]
  ops.call bindings.tupleOrBottom [firstType]

/-- Full selected pair body. Julia evaluates the complete left query before
indexing/querying the right element. Even a bottom first reply does not skip
the right effects; only TupleOrBottom, called afterward, decides its result. 
Source reference: base/broadcast.jl:770-770.
-/
-- Source: base/broadcast.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
-- /Source
def twoEltypes {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (tuple : Value L) : CoreM W L (Value L) := do
  let first ← ops.call bindings.getindex
    [tuple, JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
  let firstType ← ops.call bindings.broadcastGetindexEltype [first]
  let second ← ops.call bindings.getindex
    [tuple, JuliaLean.base.boot.intV ops (JInt.lit .i64 2)]
  let secondType ← ops.call bindings.broadcastGetindexEltype [second]
  ops.call bindings.tupleOrBottom [firstType, secondType]

/-- Pure current-world method metadata for recursive eltypes calls. Canonical
empty, singleton, pair and generic methods are explicit; custom denotes an
actually selected different method on the unfixed tuple/intermediate type. 
Source reference: base/broadcast.jl:768-771.
-/
-- Source: base/broadcast.jl:768-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(::Tuple{}) = Tuple{}
-- eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
-- eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
-- eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
-- /Source
inductive Method where
  | empty
  | one
  | two
  | recursive
  | custom

/-- Existing runtime interface plus pure recursive dispatch metadata. No
result type, termination, tail decrease or canonical property law is imposed. 
Source reference: base/broadcast.jl:768-771.
-/
-- Source: base/broadcast.jl:768-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(::Tuple{}) = Tuple{}
-- eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
-- eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
-- eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedEltypes : Value L → W → Method

/-- Execute the selected eltypes body with its real tail-first recursion.
Source771's tail result is not assumed to be a shorter canonical tuple:
dispatch is selected in its actual returned world, and the explicit CoreM
partial fixed point admits repeated selection and divergence. A bottom tail
skips all head work. Otherwise the head's actual queried type precedes the
actual parameters property and runtime splat, with no assumption that TT is a
Tuple DataType. Only genuinely selected different eltypes methods remain open.
Other generic callees dispatch on types this method does not fix; they are
not callbacks replacing source771's own recursion. 
Source reference: base/broadcast.jl:768-771.
-/
-- Source: base/broadcast.jl:768-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(::Tuple{}) = Tuple{}
-- eltypes(t::Tuple{Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]))
-- eltypes(t::Tuple{Any,Any}) = Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), _broadcast_getindex_eltype(t[2]))
-- eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (tuple : Value L) : CoreM W L (Value L) := do
  match method with
  | .empty => pure bindings.emptyTupleType
  | .one => oneEltype ops.toCoreOps bindings tuple
  | .two => twoEltypes ops.toCoreOps bindings tuple
  | .custom => ops.call bindings.eltypes [tuple]
  | .recursive =>
      let rest ← ops.call bindings.tail [tuple]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedEltypes rest world, world)))
      let tailType ← run ops bindings selected rest
      if ops.same tailType (JuliaLean.base.boot.coreV ops.toCoreOps "Union{}") then
        pure (JuliaLean.base.boot.coreV ops.toCoreOps "Union{}")
      else do
        let first ← ops.call bindings.getindex
          [tuple, JuliaLean.base.boot.intV ops.toCoreOps (JInt.lit .i64 1)]
        let firstType ← ops.call bindings.broadcastGetindexEltype [first]
        let parameters ← ops.call bindings.getproperty [tailType, .symbol "parameters"]
        ops.applyIterate bindings.iterate
          [bindings.tupleOrBottom, JuliaLean.base.boot.tupleV ops.toCoreOps [firstType], parameters]
partial_fixpoint

/-- Selected generic source771 entry. Canonical zero/one/two overloads are
chosen only by recursive method metadata, not by silently changing this
explicitly selected source body. 
Source reference: base/broadcast.jl:771-771.
-/
-- Source: base/broadcast.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eltypes(t::Tuple) = (TT = eltypes(tail(t)); TT === Union{} ? Union{} : Iterators.TupleOrBottom(_broadcast_getindex_eltype(t[1]), TT.parameters...))
-- /Source
def tupleEltypes {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (tuple : Value L) : CoreM W L (Value L) :=
  run ops bindings .recursive tuple

/-- Full combine_eltypes body on the original supplied tuple and callable.
The eltypes call selects on unfixed tuple parameters, and its actual result
controls the bottom early return. Reflection and promotion occur only on the
nonbottom path and retain full runtime type identity, errors and effects.
The older JType-slot algorithm is not used as a substitute for these queries. 
Source reference: base/broadcast.jl:774-778.
-/
-- Source: base/broadcast.jl:774-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function combine_eltypes(f, args::Tuple)
--     argT = eltypes(args)
--     argT === Union{} && return Union{}
--     return promote_typejoin_union(Base._return_type(f, argT))
-- end
-- /Source
def combineEltypes {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function arguments : Value L) : CoreM W L (Value L) := do
  let argumentType ← ops.call bindings.eltypes [arguments]
  if ops.same argumentType (JuliaLean.base.boot.coreV ops "Union{}") then
    pure (JuliaLean.base.boot.coreV ops "Union{}")
  else do
    let inferred ← ops.call bindings.returnType [function, argumentType]
    ops.call bindings.promoteUnion [inferred]

end JuliaLean.base.broadcast.Models2Group5.EltypeInference


namespace JuliaLean.base.broadcast.Models2Group5.MaterialForward

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual fixed source bindings for the public materialization adapters.
indexValue is the nominal runtime encoding of the installed Index carrier,
not a constructor callback; it preserves the concrete empty CartesianIndex
already represented by Index.m631. All other fields are original function
identities, never supplied results or callee-correctness laws.
Source: base/broadcast.jl:859-942. -/
-- Source: base/broadcast.jl:908-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcast_preserving_zero_d(f, As...)
--     bc = broadcasted(f, As...)
--     r = materialize(bc)
--     return length(axes(bc)) == 0 ? fill!(similar(bc, typeof(r)), r) : r
-- end
-- @inline broadcast_preserving_zero_d(f) = fill(f())
-- @inline broadcast_preserving_zero_d(f, as::Number...) = fill(f(as...))
-- /Source
structure Bindings (L : Type) where
  broadcasted : Value L
  materialize : Value L
  materializeBang : Value L
  iterate : Value L
  map : Value L
  axes : Value L
  length : Value L
  equal : Value L
  similar : Value L
  fillBang : Value L
  fill : Value L
  instantiate : Value L
  copy : Value L
  getproperty : Value L
  broadcastedConstructor : Value L
  copytoBang : Value L
  getindex : Value L
  indexValue : Index.Index → Value L

/-- The source859 expression has two genuinely selected calls, with the
broadcasted result evaluated before materialize. The supplied vararg tuple
is native-sized and heterogeneous; the source splat uses the installed
_apply_iterate boundary. All returned object identities, mutations, errors
and divergence are retained, without the old pure-composition restriction.
Source reference: base/broadcast.jl:859. -/
-- Source: base/broadcast.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast(f::Tf, As::Vararg{Any,N}) where {Tf,N} = materialize(broadcasted(f, As...))
-- /Source
def broadcast {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function : Value L) (args : Constructors.ArgumentTuple L) : CoreM W L (Value L) := do
  let bc ← ops.applyIterate bindings.iterate
    [bindings.broadcasted, JuliaLean.base.boot.tupleV ops [function],
      JuliaLean.base.boot.tupleV ops args.values]
  ops.call bindings.materialize [bc]

/-- The entire source863 body is the selected map call, not a replacement
pure zip algorithm. The original first tuple and source vararg tuple retain
all element and callable types. Trusted source dispatch supplies the common
NTuple length; opaque runtime tuples cannot be oversized Lean lists. The
vararg container alone is represented by native-bounded immutable slots.
Map selection depends on the unfixed function/tuple types, so its complete
actual outcomes belong in the existing runtime interface.
Source reference: base/broadcast.jl:863. -/
-- Source: base/broadcast.jl:863-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline broadcast(f, t::NTuple{N,Any}, ts::Vararg{NTuple{N,Any}}) where {N} = map(f, t, ts...)
-- /Source
def tupleBroadcast {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function first : Value L) (rest : Constructors.ArgumentTuple L) :
    CoreM W L (Value L) :=
  ops.applyIterate bindings.iterate
    [bindings.map, JuliaLean.base.boot.tupleV ops [function, first],
      JuliaLean.base.boot.tupleV ops rest.values]

/-- Bind the unchanged effectful Material.m898 driver. The exact original
destination is returned after selected materialize! succeeds, independently
of that selected method's returned object. The destination is not inserted
among the source arguments unless it was already explicitly present there.
Errors/divergence stop before the destination return, retaining the actual
world. Source: base/broadcast.jl:898 and docstring865-896. -/
-- Source: base/broadcast.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast!(f::Tf, dest, As::Vararg{Any,N}) where {Tf,N} = (materialize!(dest, broadcasted(f, As...)); dest)
-- /Source
def broadcastBang {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function dest : Value L) (args : Constructors.ArgumentTuple L) :
    CoreM W L (Value L) :=
  Material.m898
    (fun function args => ops.applyIterate bindings.iterate
      [bindings.broadcasted, JuliaLean.base.boot.tupleV ops [function],
        JuliaLean.base.boot.tupleV ops args])
    (fun dest bc => do
      let _ ← ops.call bindings.materializeBang [dest, bc]
      pure ()) function dest args.values

/-- Full source908 body. The selected materialize result precedes axes,
length and equality; a custom axes object is never reduced to List.isEmpty.
Only a true Bool equality result invokes similar with the builtin typeof(r),
then fill! with that exact allocation and original r. False returns r after
all preceding effects; non-Bool fails at the actual conditional context.
The result of fill! itself is retained, without an allocation-identity law.
All callee choices depend on types the source leaves unfixed.
Source reference: base/broadcast.jl:908-912. -/
-- Source: base/broadcast.jl:908-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcast_preserving_zero_d(f, As...)
--     bc = broadcasted(f, As...)
--     r = materialize(bc)
--     return length(axes(bc)) == 0 ? fill!(similar(bc, typeof(r)), r) : r
-- end
-- /Source
def preservingZero {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function : Value L) (args : Constructors.ArgumentTuple L) : CoreM W L (Value L) := do
  let bc ← ops.applyIterate bindings.iterate
    [bindings.broadcasted, JuliaLean.base.boot.tupleV ops [function],
      JuliaLean.base.boot.tupleV ops args.values]
  let result ← ops.call bindings.materialize [bc]
  let axes ← ops.call bindings.axes [bc]
  let dimensions ← ops.call bindings.length [axes]
  let test ← ops.call bindings.equal
    [dimensions, JuliaLean.base.boot.intV ops (JInt.lit .i64 0)]
  if ← CheckedBounds.booleanContext ops test then
    let dest ← ops.call bindings.similar [bc, .leaf (ops.typeOf result)]
    ops.call bindings.fillBang [dest, result]
  else pure result

/-- Call the arbitrary zero-argument function before invoking actual fill
on its returned value. The source performs a mutable zero-dimensional
allocation through the selected fill method; no immutable ZeroD record or
stored exception is substituted. Since the returned type is unfixed, that
selected fill operation retains all custom outcomes. Source: base/broadcast.jl:913. -/
-- Source: base/broadcast.jl:913-913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline broadcast_preserving_zero_d(f) = fill(f())
-- /Source
def preservingNullary {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function : Value L) : CoreM W L (Value L) := do
  let value ← ops.call function []
  ops.call bindings.fill [value]

/-- The Number-vararg specialization preserves its actual heterogeneous,
native-sized arguments and callable dispatch, then invokes fill on the exact
returned value. Custom Number/function methods, non-Number results and all
allocation/call failures remain in scope. Source: base/broadcast.jl:914. -/
-- Source: base/broadcast.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline broadcast_preserving_zero_d(f, as::Number...) = fill(f(as...))
-- /Source
def preservingNumbers {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (function : Value L) (args : Constructors.ArgumentTuple L) : CoreM W L (Value L) := do
  let value ← ops.applyIterate bindings.iterate
    [function, JuliaLean.base.boot.tupleV ops args.values]
  ops.call bindings.fill [value]

/-- Bind unchanged Material.m921 to the full runtime-value domain. Its
single B type can be Value, allowing instantiate to return arbitrary types
before selecting copy. No concrete array, successful instantiation, or copy
identity assumption is imposed. Source: base/broadcast.jl:921. -/
-- Source: base/broadcast.jl:921-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline materialize(bc::Broadcasted) = copy(instantiate(bc))
-- /Source
def materialize {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) :=
  Material.m921 (fun bc => ops.call bindings.instantiate [bc])
    (fun ready => ops.call bindings.copy [ready]) bc

/-- Full source932 rebuild-and-copy sequence. The four Broadcasted parameters
are unfixed, so actual property dispatch can be effectful. Read style, f and
args in that order, then destination axes; pass all exact replies to the
selected four-argument constructor, instantiate its result and invoke copyto!
with the original destination. No record reconstruction silently bypasses
constructor/property effects. The separate style argument is unused.
Source reference: base/broadcast.jl:932-934. -/
-- Source: base/broadcast.jl:932-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(::BroadcastStyle, dest, bc::Broadcasted{<:Any})
--     return copyto!(dest, instantiate(Broadcasted(bc.style, bc.f, bc.args, axes(dest))))
-- end
-- /Source
def materializeStyled {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (_style dest bc : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.getproperty [bc, .symbol "style"]
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  let args ← ops.call bindings.getproperty [bc, .symbol "args"]
  let axes ← ops.call bindings.axes [dest]
  let rebuilt ← ops.call bindings.broadcastedConstructor [style, function, args, axes]
  let ready ← ops.call bindings.instantiate [rebuilt]
  ops.call bindings.copytoBang [dest, ready]

/-- Reuse the unchanged one-call Material.m942 driver, passing the concrete
empty CartesianIndex from the installed Index.m631 model through its nominal
runtime encoding. No arbitrary constructor callback or integer-zero index
replaces CartesianIndex(). The Broadcasted type parameters still select the
actual getindex method with all its outcomes. Source: base/broadcast.jl:942;
base/broadcast.jl:631 and base/multidimensional.jl:75-82. -/
-- Source: base/broadcast.jl:942-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copy(bc::Broadcasted{<:AbstractArrayStyle{0}}) = bc[CartesianIndex()]
-- /Source
def copyZero {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) :=
  Material.m942 (fun bc => ops.call bindings.getindex
    [bc, bindings.indexValue Index.m631]) bc

end JuliaLean.base.broadcast.Models2Group5.MaterialForward


namespace JuliaLean.base.broadcast.Models2Group5.MaterialRecursion

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed identities at the source two-argument materialize! methods.
The identity function is passed to Broadcasted; it is never executed by
this adapter itself. Source: base/broadcast.jl:924-930. -/
-- Source: base/broadcast.jl:924-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, x)
--     return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
-- end
-- 
-- @inline function materialize!(dest, bc::Broadcasted{<:Any})
--     return materialize!(combine_styles(dest, bc), dest, bc)
-- end
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  broadcastedConstructor : Value L
  instantiate : Value L
  materializeBang : Value L
  combineStyles : Value L
  identity : Value L

/-- Actual selected two-argument materialize! method. The two known source
bodies below are explicit; other denotes a genuinely selected different
method on unfixed input types, including dispatch failure. The tag supplies
no result or algorithm. Source: base/broadcast.jl:924-930. -/
-- Source: base/broadcast.jl:924-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, x)
--     return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
-- end
-- 
-- @inline function materialize!(dest, bc::Broadcasted{<:Any})
--     return materialize!(combine_styles(dest, bc), dest, bc)
-- end
-- /Source
inductive Method where
  | fallback
  | broadcasted
  | other

/-- Existing Core operations with pure current-world dispatch metadata.
The recursive target is selected only after axes, construction and
instantiation effects finish. Source: base/broadcast.jl:924-926. -/
-- Source: base/broadcast.jl:924-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, x)
--     return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
-- end
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedMaterialize : Value L → Value L → W → Method

/-- Complete source928 body with effectful style combination. The original
destination and Broadcasted object are passed unchanged to the three-argument
selected method, after the actual style value is obtained. That different
arity is a dispatch target on types this method does not fix; it does not
stand in for this two-argument body's recursion. Source: broadcast.jl:928-930. 
Source reference: base/broadcast.jl:928-930.
-/
-- Source: base/broadcast.jl:928-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, bc::Broadcasted{<:Any})
--     return materialize!(combine_styles(dest, bc), dest, bc)
-- end
-- /Source
def broadcastedBang {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.combineStyles [dest, bc]
  ops.call bindings.materializeBang [style, dest, bc]

/-- Execute the actual selected two-argument source bodies. A fallback
frame reads destination axes, calls the actual three-argument Broadcasted
constructor with identity and the singleton original value, instantiates the
exact result, then explicitly executes the next selected materialize! body.
Custom constructors/instantiate may return any type, so the fallback can be
selected repeatedly or forever. CoreM partial_fixpoint preserves that genuine
nontermination without caller fuel or a supplied own-body callback. Only a
genuinely different selected target goes through the open call boundary.
No destination allocation or alias copy is invented by the adapter.
Source reference: base/broadcast.jl:924-930. -/
-- Source: base/broadcast.jl:924-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, x)
--     return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
-- end
-- 
-- @inline function materialize!(dest, bc::Broadcasted{<:Any})
--     return materialize!(combine_styles(dest, bc), dest, bc)
-- end
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (dest value : Value L) : CoreM W L (Value L) := do
  match method with
  | .broadcasted => broadcastedBang ops.toCoreOps bindings dest value
  | .other => ops.call bindings.materializeBang [dest, value]
  | .fallback =>
      let axes ← ops.call bindings.axes [dest]
      let bc ← ops.call bindings.broadcastedConstructor
        [bindings.identity, JuliaLean.base.boot.tupleV ops.toCoreOps [value], axes]
      let ready ← ops.call bindings.instantiate [bc]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedMaterialize dest ready world, world)))
      run ops bindings selected dest ready
partial_fixpoint

/-- Enter the selected generic source924 body directly; only its recursive
calls consult dispatch metadata. Explicit invocation on a value ordinarily
handled by a more-specific method is therefore retained. Source924-926. 
Source reference: base/broadcast.jl:924-926.
-/
-- Source: base/broadcast.jl:924-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, x)
--     return materialize!(dest, instantiate(Broadcasted(identity, (x,), axes(dest))))
-- end
-- /Source
def fallbackBang {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest value : Value L) : CoreM W L (Value L) :=
  run ops bindings .fallback dest value

end JuliaLean.base.broadcast.Models2Group5.MaterialRecursion


namespace JuliaLean.base.broadcast.Models2Group5.CopyNarrowing

open JuliaLean
open JuliaLean.base.expr (Value Sym)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Source function/type identities for the selected default copy body.
boundName is the compiler-generated bound variable's fixed Symbol from this
method's lowering, not a callable result or user Julia argument. The installed
Material.m948 already fixes TypeVar, ndims, apply_type, UnionAll order; this
adapter retains that ordering and reuses the installed TypeVar/UnionAll bodies.
Source reference: base/broadcast.jl:948-975. -/
-- Source: base/broadcast.jl:948-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted)
--     ElType = result_eltype(bc)
--     if Base.isconcretetype(ElType)
--         # We can trust it and defer to the simpler `copyto!`
--         return copyto!(similar(bc, ElType), bc)
--     end
--     # When ElType is not concrete, use narrowing. Use the first output
--     # value to determine the starting output eltype; copyto_nonleaf!
--     # will widen `dest` as needed to accommodate later values.
--     bc′ = preprocess(nothing, bc)
--     iter = eachindex(bc′)
--     y = iterate(iter)
--     if y === nothing
--         # if empty, take the ElType at face value
--         return similar(bc′, ElType)
--     end
--     # Initialize using the first value
--     I, state = y
--     @inbounds val = bc′[I]
--     dest = similar(bc′, typeof(val))
--     @inbounds dest[I] = val
--     # Now handle the remaining values
--     # The typeassert gives inference a helping hand on the element type and dimensionality
--     # (work-around for #28382)
--     ElType′ = ElType === Union{} ? Any : ElType <: Type ? Type : ElType
--     RT = dest isa AbstractArray ? AbstractArray{<:ElType′, ndims(dest)} : Any
--     return copyto_nonleaf!(dest, bc′, iter, state, 1)::RT
-- end
-- /Source
structure Bindings (L : Type) where
  resultEltype : Value L
  isConcreteType : Value L
  similar : Value L
  copyTo : Value L
  preprocess : Value L
  eachindex : Value L
  iterate : Value L
  indexedIterate : Value L
  getindex : Value L
  setindex : Value L
  ndims : Value L
  abstractArray : Value L
  copyNonleaf : Value L
  boundName : Sym

/-- Actual constructor selection at anonymous-type lowering call sites.
The generated name is fixed, but the bound and preceding constructor results
are unfixed. Only canonical selection reuses the installed concrete body.
Source reference: base/broadcast.jl:973; base/boot.jl:369-374. -/
-- Source: base/boot.jl:369-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # n.b. the effects and model of these is refined in inference abstractinterpretation.jl
-- TypeVar(@nospecialize(n)) = _typevar(n::Symbol, Union{}, Any)
-- TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
-- TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub)) = _typevar(n::Symbol, lb, ub)
-- UnionAll(@nospecialize(v), @nospecialize(t)) = ccall(:jl_type_unionall, Any, (Any, Any), v::TypeVar, t)
-- 
-- /Source
inductive ConstructorMethod where
  | builtin
  | custom

/-- Contextual existing primitives and pure constructor-selection metadata.
Selectors run at each actual call world, after every preceding operation.
No assumption says a custom TypeVar constructor returns a TypeVar or that
an arbitrary selected UnionAll constructor preserves a particular body.
Source reference: base/broadcast.jl:973. -/
-- Source: base/broadcast.jl:973-973 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     RT = dest isa AbstractArray ? AbstractArray{<:ElType′, ndims(dest)} : Any
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedTypeVar : Sym → Value L → W → ConstructorMethod
  selectedUnionAll : Value L → Value L → W → ConstructorMethod

/-- Actual TypeVar(name,bound) call in the retained anonymous-bound lowering.
Canonical selection uses existing boot.TypeVar2; a genuinely selected method
on the unfixed bound type retains the original Core constructor and arguments.
Source reference: base/broadcast.jl:973; base/boot.jl:371. -/
-- Source: base/boot.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
-- /Source
def typeVariable {W L : Type} (ops : Ops W L) (core : CoreOps W L)
    (name : Sym) (bound : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedTypeVar name bound world with
  | .builtin => JuliaLean.base.boot.TypeVar2 core (.symbol name) bound world
  | .custom => core.call (JuliaLean.base.boot.coreV core "TypeVar") [.symbol name, bound] world

/-- Actual UnionAll call after type application. Canonical selection retains
the installed TypeVar assertion and jl_type_unionall primitive; only genuinely
selected extensions on unfixed constructor results remain open.
Source reference: base/broadcast.jl:973; base/boot.jl:373. -/
-- Source: base/boot.jl:373-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UnionAll(@nospecialize(v), @nospecialize(t)) = ccall(:jl_type_unionall, Any, (Any, Any), v::TypeVar, t)
-- /Source
def universalType {W L : Type} (ops : Ops W L) (core : CoreOps W L)
    (typeVariableValue body : Value L) : CoreM W L (Value L) := fun world =>
  match ops.selectedUnionAll typeVariableValue body world with
  | .builtin => JuliaLean.base.boot.UnionAll core typeVariableValue body world
  | .custom => core.call (JuliaLean.base.boot.coreV core "UnionAll") [typeVariableValue, body] world

/-- Source's first iterate result and exact two-target assignment lowering.
A result identical to nothing is the empty branch; every other value is
passed to actual indexed_iterate calls with native positions one/two and the
first returned state. Runtime getfield reads preserve failures on malformed
custom results. The internal Option/pair is created only after all these
source effects, so it does not restrict iterate to conventional tuple output.
The sequence is the installed flfrontend.destructure2 lowering; no extra
second destructuring state field is read. Julia source: base/broadcast.jl:958-964;
base/flfrontend.lean:destructure2; manual/functions.md:394-409. -/
-- Source: base/broadcast.jl:958-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     iter = eachindex(bc′)
--     y = iterate(iter)
--     if y === nothing
--         # if empty, take the ElType at face value
--         return similar(bc′, ElType)
--     end
--     # Initialize using the first value
-- /Source
def firstIteration {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (iterator : Value L) : CoreM W L (Option (Value L × Value L)) := do
  let result ← ops.call bindings.iterate [iterator]
  if ops.same result (JuliaLean.base.boot.nothingV ops) then pure none
  else do
    let one := JuliaLean.base.boot.intV ops (JInt.lit .i64 1)
    let two := JuliaLean.base.boot.intV ops (JInt.lit .i64 2)
    let firstPair ← ops.call bindings.indexedIterate [result, one]
    let index ← ops.getfield firstPair one
    let state ← ops.getfield firstPair two
    let secondPair ← ops.call bindings.indexedIterate [result, two, state]
    let nextState ← ops.getfield secondPair one
    pure (some (index, nextState))

/-- Full runtime binding of the unchanged Material.m948 source driver.
Every type/value, custom iterator result, array, coordinate and state is an
actual runtime Value. The isconcretetype answer is validated in Boolean
context, and firstIteration performs the actual effectful destructuring.
The explicit @inbounds element read/write use false-context operations; all
other selected calls retain their applicable caller context. CoreM preserves
all preceding mutation worlds even if later conversion/type construction or
copying throws. Native one, builtin typeof/identity/isa/subtyping and the final
runtime assertion retain their actual source meaning.

The return type is constructed from the original destination after its first
write and before copyto_nonleaf!, exactly as in the installed driver. Canonical constructor selection reuses existing boot.TypeVar2 and boot.UnionAll,
including bound validation and TypeVar assertion; genuinely selected extensions
on unfixed bound/result types retain their exact calls and outcomes. No new unknown
callee or callback replaces this method's algorithm. The remaining generic
calls select on types left unfixed by the source and have no correctness laws.
Source reference: base/broadcast.jl:948-975; base/boot.jl:369-374. -/
-- Source: base/broadcast.jl:948-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted)
--     ElType = result_eltype(bc)
--     if Base.isconcretetype(ElType)
--         # We can trust it and defer to the simpler `copyto!`
--         return copyto!(similar(bc, ElType), bc)
--     end
--     # When ElType is not concrete, use narrowing. Use the first output
--     # value to determine the starting output eltype; copyto_nonleaf!
--     # will widen `dest` as needed to accommodate later values.
--     bc′ = preprocess(nothing, bc)
--     iter = eachindex(bc′)
--     y = iterate(iter)
--     if y === nothing
--         # if empty, take the ElType at face value
--         return similar(bc′, ElType)
--     end
--     # Initialize using the first value
--     I, state = y
--     @inbounds val = bc′[I]
--     dest = similar(bc′, typeof(val))
--     @inbounds dest[I] = val
--     # Now handle the remaining values
--     # The typeassert gives inference a helping hand on the element type and dimensionality
--     # (work-around for #28382)
--     ElType′ = ElType === Union{} ? Any : ElType <: Type ? Type : ElType
--     RT = dest isa AbstractArray ? AbstractArray{<:ElType′, ndims(dest)} : Any
--     return copyto_nonleaf!(dest, bc′, iter, state, 1)::RT
-- end
-- /Source
def copy {W L : Type} (ops : Ops W L)
    (bindings : Bindings L) (bc : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  let core := ops.contexts.inContext boundscheck
  let inbounds := ops.contexts.inContext false
  Material.m948
    (fun value => core.call bindings.resultEltype [value])
    (fun type => do
      let test ← core.call bindings.isConcreteType [type]
      CheckedBounds.booleanContext core test)
    (fun value type => core.call bindings.similar [value, type])
    (fun dest source => core.call bindings.copyTo [dest, source])
    (fun value => core.call bindings.preprocess [JuliaLean.base.boot.nothingV core, value])
    (fun value => core.call bindings.eachindex [value])
    (firstIteration core bindings)
    (fun value index => inbounds.call bindings.getindex [value, index])
    (fun value => pure (.leaf (core.typeOf value)))
    (fun dest index value => do
      let _ ← inbounds.call bindings.setindex [dest, value, index]
      pure ())
    (fun first second => pure (core.same first second))
    core.subtype
    (JuliaLean.base.boot.coreV core "Union{}")
    (JuliaLean.base.boot.coreV core "Any")
    (JuliaLean.base.boot.coreV core "Type")
    (fun dest => pure (core.isa dest bindings.abstractArray))
    (fun bound => typeVariable ops core bindings.boundName bound)
    (fun dest => core.call bindings.ndims [dest])
    (fun typeVariableValue dimensions => core.applyType bindings.abstractArray [typeVariableValue, dimensions])
    (universalType ops core)
    (fun dest ready iterator state count => core.call bindings.copyNonleaf
      [dest, ready, iterator, state, JuliaLean.base.boot.intV core count])
    (fun result type => RuntimeTypes.checkedAssert core result type)
    bc

end JuliaLean.base.broadcast.Models2Group5.CopyNarrowing


namespace JuliaLean.base.broadcast.Models2Group5.CopyDispatch

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual source function/type identities. Property results, flatness tests,
conversions, scalar reads and destination types remain unfixed, so their
selected generic calls retain all runtime outcomes. Julia source980-993. 
Source reference: base/broadcast.jl:980-993.
-/
-- Source: base/broadcast.jl:980-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- 
-- # Performance optimization for the common identity scalar case: dest .= val
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
structure Bindings (L : Type) where
  broadcasted : Value L
  convert : Value L
  copyTo : Value L
  getproperty : Value L
  identity : Value L
  isFlat : Value L
  getindex : Value L
  fill : Value L

/-- Actual copyto! method selected after conversion. The two known recursive
bodies are explicit; other means a genuinely different selected method on
unfixed destination/result types, not an arbitrary replacement for either.
Source reference: base/broadcast.jl:980-993. -/
-- Source: base/broadcast.jl:980-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- 
-- # Performance optimization for the common identity scalar case: dest .= val
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
inductive Method where
  | generic
  | scalar
  | other

/-- Existing runtime interface with pure current-world copyto! selection.
The selector runs after the conversion's actual mutation/error effects.
Source reference: base/broadcast.jl:980-993. -/
-- Source: base/broadcast.jl:980-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- 
-- # Performance optimization for the common identity scalar case: dest .= val
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedCopy : Value L → Value L → W → Method

/-- Source's exact Broadcasted{Nothing} conversion expression. Type application
precedes convert, and no law forces a custom conversion to return the desired
wrapper/type. Subsequent copyto! redispatch therefore remains necessary.
Source reference: base/broadcast.jl:980,991. -/
-- Source: base/broadcast.jl:980-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- 
-- # Performance optimization for the common identity scalar case: dest .= val
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
def convertNothing {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let type ← ops.applyType bindings.broadcasted [JuliaLean.base.boot.coreV ops "Nothing"]
  ops.call bindings.convert [type, bc]

/-- Actual short-circuit scalar optimization. f is tested by builtin identity;
only then is args read and tested against Tuple{Any}, and only then does
isflat run in Boolean context. The successful route rereads args, indexes its
first element, performs zero-argument indexing on that exact object, and fills
the original destination. It may return an arbitrary fill result. None means
the source's fallback branch was reached, not a Julia value or an error.
The source parameters/property result types are unfixed, so actual selected
getters and scalar getindex/fill calls remain open. Julia source983-993. 
Source reference: base/broadcast.jl:983-993.
-/
-- Source: base/broadcast.jl:983-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
def scalarFast {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Option (Value L)) := do
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  if !(ops.same function bindings.identity) then pure none
  else do
    let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
    let singleType ← ops.applyType (JuliaLean.base.boot.coreV ops "Tuple")
      [JuliaLean.base.boot.coreV ops "Any"]
    if !(ops.isa arguments singleType) then pure none
    else do
      let test ← ops.call bindings.isFlat [bc]
      if !(← CheckedBounds.booleanContext ops test) then pure none
      else do
        let argumentsAgain ← ops.call bindings.getproperty [bc, .symbol "args"]
        let argument ← ops.call bindings.getindex
          [argumentsAgain, JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
        let value ← ops.call bindings.getindex [argument]
        let result ← ops.call bindings.fill [dest, value]
        pure (some result)

/-- Shared actual recursion of the generic and zero-dimensional copyto!
bodies. Custom conversion may return a value selecting either method again;
CoreM's least partial fixed point retains these cycles and all mutation worlds.
No caller provides the own recursive action, and no fuel or termination law
is imposed. A genuinely different selected destination method receives the
unchanged original destination and the exact converted source.
Source reference: base/broadcast.jl:980-993. -/
-- Source: base/broadcast.jl:980-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- 
-- # Performance optimization for the common identity scalar case: dest .= val
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (dest bc : Value L) : CoreM W L (Value L) := do
  match method with
  | .other => ops.call bindings.copyTo [dest, bc]
  | .generic =>
      let converted ← convertNothing ops.toCoreOps bindings bc
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedCopy dest converted world, world)))
      run ops bindings selected dest converted
  | .scalar =>
      match ← scalarFast ops.toCoreOps bindings dest bc with
      | some result => pure result
      | none =>
          let converted ← convertNothing ops.toCoreOps bindings bc
          let selected ← (show CoreM W L Method from fun world =>
            some (.ok (ops.selectedCopy dest converted world, world)))
          run ops bindings selected dest converted
partial_fixpoint

/-- Selected generic source980 entry; only recursive calls consult metadata.
The original destination survives every actual conversion/redispatch.
Source reference: base/broadcast.jl:980. -/
-- Source: base/broadcast.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- /Source
def generic {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Value L) := run ops bindings .generic dest bc

/-- Selected zero-dimensional source983 entry. The source shortcut and
fallback are both retained, including effects/errors and recursive redispatch.
Source reference: base/broadcast.jl:983-993. -/
-- Source: base/broadcast.jl:983-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{<:AbstractArrayStyle{0}})
--     # Typically, we must independently execute bc for every storage location in `dest`, but:
--     # IF we're in the common no-op identity case with no nested args (like `dest .= val`),
--     if bc.f === identity && bc.args isa Tuple{Any} && isflat(bc)
--         # THEN we can just extract the argument and `fill!` the destination with it
--         return fill!(dest, bc.args[1][])
--     else
--         # Otherwise, fall back to the default implementation like above
--         return copyto!(dest, convert(Broadcasted{Nothing}, bc))
--     end
-- end
-- /Source
def scalar {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Value L) := run ops bindings .scalar dest bc

end JuliaLean.base.broadcast.Models2Group5.CopyDispatch


namespace JuliaLean.base.broadcast.Models2Group5.Preprocessing

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed function/type identities for the preprocessing expressions. All
stored argument, destination and returned types remain actual runtime values;
selected property, alias, extrusion and constructor operations remain open
where the source types are unfixed. Julia source1001-1012. 
Source reference: base/broadcast.jl:1001-1012.
-/
-- Source: base/broadcast.jl:1001-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
-- broadcast_unalias(::Nothing, src) = src
-- 
-- # Preprocessing a `Broadcasted` does two things:
-- # * unaliases any arguments from `dest`
-- # * "extrudes" the arguments where it is advantageous to pre-compute the broadcasted indices
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- 
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
structure Bindings (L : Type) where
  unalias : Value L
  broadcastUnalias : Value L
  extrude : Value L
  preprocess : Value L
  preprocessArgs : Value L
  getproperty : Value L
  broadcasted : Value L
  getindex : Value L
  tail : Value L
  iterate : Value L

/-- Source1001's identity exception preserves the exact original source with
no preventative-copy action. Otherwise the selected unalias target receives
the actual destination/source and retains every effect, allocation, error or
divergence in CoreM. It is open on both types, rather than a pure copying law.
Source reference: base/broadcast.jl:995-1002. -/
-- Source: base/broadcast.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
-- /Source
def unalias {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (dest source : Value L) : CoreM W L (Value L) :=
  if ops.same dest source then pure source
  else ops.call bindings.unalias [dest, source]

/-- Actual preprocess method selection on destination/value types left
unfixed by the caller. Only custom denotes a genuinely different body.
Source reference: base/broadcast.jl:1007-1008. -/
-- Source: base/broadcast.jl:1007-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- /Source
inductive PreprocessMethod where
  | broadcasted
  | fallback
  | custom

/-- Actual tuple preprocessing selection, including the known singleton and
empty overloads. Custom can specialize the unfixed destination or tuple type.
Source reference: base/broadcast.jl:1010-1012. -/
-- Source: base/broadcast.jl:1010-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
inductive ArgumentsMethod where
  | generic
  | singleton
  | empty
  | custom

/-- Tags for the mutually recursive source bodies. These are internal control
metadata only, never Julia input values or computed preprocessing results.
Source reference: base/broadcast.jl:1007-1012. -/
-- Source: base/broadcast.jl:1007-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- 
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
inductive Method where
  | broadcasted
  | fallback
  | arguments
  | singleton
  | empty
  | customPreprocess
  | customArguments

/-- Existing runtime primitives with pure current-world selections. Nested
preprocessing and recursive tail selection occur only after the preceding
actual property/index/processing effects, including mutation.
Source reference: base/broadcast.jl:1007-1012. -/
-- Source: base/broadcast.jl:1007-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- 
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedPreprocess : Value L → Value L → W → PreprocessMethod
  selectedArguments : Value L → Value L → W → ArgumentsMethod

/-- The selected preprocess tag names its actual locally modelled body.
Source reference: base/broadcast.jl:1007-1008. -/
-- Source: base/broadcast.jl:1007-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- /Source
def preprocessMethod : PreprocessMethod → Method
  | .broadcasted => .broadcasted
  | .fallback => .fallback
  | .custom => .customPreprocess

/-- The selected tuple tag names its actual locally modelled body.
Source reference: base/broadcast.jl:1010-1012. -/
-- Source: base/broadcast.jl:1010-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
def argumentsMethod : ArgumentsMethod → Method
  | .generic => .arguments
  | .singleton => .singleton
  | .empty => .empty
  | .custom => .customArguments

/-- Full mutually recursive preprocessing. Broadcasted reconstruction reads
style, f and args, recursively preprocesses that exact args value, then reads
axes and invokes the actual constructor. A generic tuple reads/processes its
head before tail and recursively processes the returned tail; the final tuple
uses the installed runtime splat, allowing arbitrary custom returned iterables.
Singleton and empty branches use actual tuple packaging, reusing Material.m1012
for the concrete empty slots. Fallback preserves unalias-before-extrude order.

Actual getters and tail methods may introduce new trees or cycles, so runtime
Values and a least partial fixed point preserve the full domain without a list
restriction, recursive callback or fuel. Every exception carries its current
world. Only selected custom preprocessing methods use the open whole-call
boundary; generic property/index/alias/constructor targets remain open on
unfixed argument types. Julia source: base/broadcast.jl:1007-1012. -/
-- Source: base/broadcast.jl:1007-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- 
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (dest value : Value L) : CoreM W L (Value L) := do
  let one := JuliaLean.base.boot.intV ops.toCoreOps (JInt.lit .i64 1)
  match method with
  | .broadcasted =>
      let style ← ops.call bindings.getproperty [value, .symbol "style"]
      let function ← ops.call bindings.getproperty [value, .symbol "f"]
      let arguments ← ops.call bindings.getproperty [value, .symbol "args"]
      let selected ← (show CoreM W L ArgumentsMethod from fun world =>
        some (.ok (ops.selectedArguments dest arguments world, world)))
      let processed ← run ops bindings (argumentsMethod selected) dest arguments
      let axes ← ops.call bindings.getproperty [value, .symbol "axes"]
      ops.call bindings.broadcasted [style, function, processed, axes]
  | .fallback =>
      let unaliased ← ops.call bindings.broadcastUnalias [dest, value]
      ops.call bindings.extrude [unaliased]
  | .arguments =>
      let head ← ops.call bindings.getindex [value, one]
      let selectedHead ← (show CoreM W L PreprocessMethod from fun world =>
        some (.ok (ops.selectedPreprocess dest head world, world)))
      let processedHead ← run ops bindings (preprocessMethod selectedHead) dest head
      let tail ← ops.call bindings.tail [value]
      let selectedTail ← (show CoreM W L ArgumentsMethod from fun world =>
        some (.ok (ops.selectedArguments dest tail world, world)))
      let processedTail ← run ops bindings (argumentsMethod selectedTail) dest tail
      ops.applyIterate bindings.iterate
        [JuliaLean.base.boot.coreV ops.toCoreOps "tuple",
         JuliaLean.base.boot.tupleV ops.toCoreOps [processedHead], processedTail]
  | .singleton =>
      let head ← ops.call bindings.getindex [value, one]
      let selected ← (show CoreM W L PreprocessMethod from fun world =>
        some (.ok (ops.selectedPreprocess dest head world, world)))
      let processed ← run ops bindings (preprocessMethod selected) dest head
      pure (JuliaLean.base.boot.tupleV ops.toCoreOps [processed])
  | .empty =>
      pure (JuliaLean.base.boot.tupleV ops.toCoreOps
        (Material.m1012 (D := Value L) (B := Value L) dest))
  | .customPreprocess => ops.call bindings.preprocess [dest, value]
  | .customArguments => ops.call bindings.preprocessArgs [dest, value]
partial_fixpoint

/-- Selected source1007 entry; nested method selection is explicit in run.
Source reference: base/broadcast.jl:1007. -/
-- Source: base/broadcast.jl:1007-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- /Source
def broadcasted {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Value L) := run ops bindings .broadcasted dest bc

/-- Selected source1008 entry, preserving all selected unalias/extrude results.
Source reference: base/broadcast.jl:1008. -/
-- Source: base/broadcast.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- /Source
def fallback {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest value : Value L) : CoreM W L (Value L) := run ops bindings .fallback dest value

/-- Selected source1010 entry, including explicit-invoke empty/singleton tuples
and arbitrary custom tail behavior. No tuple is converted to a mathematical
list; its actual runtime indexing/splat operations remain visible.
Source reference: base/broadcast.jl:1010. -/
-- Source: base/broadcast.jl:1010-1010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- /Source
def arguments {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest args : Value L) : CoreM W L (Value L) := run ops bindings .arguments dest args

/-- Selected source1011 entry. Its actual processed head is stored in one
immutable tuple slot with no copy or coercion. Julia source1011. 
Source reference: base/broadcast.jl:1011-1011.
-/
-- Source: base/broadcast.jl:1011-1011 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- /Source
def singleton {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest args : Value L) : CoreM W L (Value L) := run ops bindings .singleton dest args

end JuliaLean.base.broadcast.Models2Group5.Preprocessing


namespace JuliaLean.base.broadcast.Models2Group5.SimdLoop

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual functions used by the pinned @simd expansion. Their selected
methods depend on the original range, outer index or actual numeric replies;
no native-only iterator or count assumption is imposed on this generic helper.
Source: base/simdloop.jl:66-86. -/
-- Source: base/simdloop.jl:66-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # i: Trip index for inner loop
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
-- /Source
structure Bindings (L : Type) where
  simd_outer_range : Value L
  simd_inner_length : Value L
  simd_index : Value L
  zero : Value L
  less : Value L
  add : Value L
  iterate : Value L

/-- The actual expanded inner while loop. Both the comparison and generated
index call remain at their source points. The body finishes before i+=1;
addition uses the original native Int literal1 and the actual current counter,
so arbitrary custom numeric results, effects and nontermination are retained.
S carries the caller's lexical mutable variables, not a Julia heap snapshot.
The supplied CoreOps is already selected for the call site's bounds context.
Source: base/simdloop.jl:73-80. -/
-- Source: base/simdloop.jl:73-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
-- /Source
def inner {W L S : Type} (core : CoreOps W L) (bindings : Bindings L)
    (range outer count counter : Value L) (state : S)
    (body : Value L → S → CoreM W L S) : CoreM W L S := do
  let test ← core.call bindings.less [counter, count]
  if ← CheckedBounds.booleanContext core test then
    let index ← core.call bindings.simd_index [range, outer, counter]
    let nextState ← body index state
    let nextCounter ← core.call bindings.add
      [counter, JuliaLean.base.boot.intV core (JInt.lit .i64 1)]
    inner core bindings range outer count nextCounter nextState body
  else pure state
partial_fixpoint

/-- The expanded outer for loop, using the compiler's iterator-result
getfield protocol. Both next fields are read before entering the body. The
initial zero(n)<n test is distinct from the inner i<n test, and zero(n) is
called a second time only after the first comparison succeeds. Outer iterator
advancement follows all inner/body effects. The primitive ===nothing test,
getfield failures, conditional TypeError and arbitrary numeric dispatch are
all retained. No list enumeration or bounded execution replaces the loops.
Source: base/simdloop.jl:69-83. -/
-- Source: base/simdloop.jl:69-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
-- /Source
def outer {W L S : Type} (core : CoreOps W L) (bindings : Bindings L)
    (range outerRange next : Value L) (state : S)
    (body : Value L → S → CoreM W L S) : CoreM W L S := do
  if core.same next (JuliaLean.base.boot.nothingV core) then pure state
  else
    let one := JuliaLean.base.boot.intV core (JInt.lit .i64 1)
    let two := JuliaLean.base.boot.intV core (JInt.lit .i64 2)
    let outerIndex ← core.getfield next one
    let iteratorState ← core.getfield next two
    let count ← core.call bindings.simd_inner_length [range, outerIndex]
    let zero ← core.call bindings.zero [count]
    let positive ← core.call bindings.less [zero, count]
    let updated ←
      if ← CheckedBounds.booleanContext core positive then do
        let counter ← core.call bindings.zero [count]
        inner core bindings range outerIndex count counter state body
      else pure state
    let following ← core.call bindings.iterate [outerRange, iteratorState]
    outer core bindings range outerRange following updated body
partial_fixpoint

/-- Run exactly the runtime expansion of @simd on one already evaluated range.
This helper is used only for a range whose selected SIMD methods remain open;
callers with a completely fixed concrete Base range bind its existing closed
operations instead. The callback is the source loop body with explicit caller
state, not a replacement for the loop or recursion. No compile-time AST or
new runtime primitive is introduced. Source: base/simdloop.jl:66-86. -/
-- Source: base/simdloop.jl:66-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # i: Trip index for inner loop
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
-- /Source
def fold {W L S : Type} (core : CoreOps W L) (bindings : Bindings L)
    (range : Value L) (initial : S) (body : Value L → S → CoreM W L S) : CoreM W L S := do
  let outerRange ← core.call bindings.simd_outer_range [range]
  let next ← core.call bindings.iterate [outerRange]
  outer core bindings range outerRange next initial body

end JuliaLean.base.broadcast.Models2Group5.SimdLoop


namespace JuliaLean.base.broadcast.Models2Group5.PlainCopy

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source bindings and the actual @simd expansion's generic functions.
Destination, Broadcasted parameters, axis values, property results and returned
iterators remain unfixed. Julia source: base/broadcast.jl:1015-1031. -/
-- Source: base/broadcast.jl:1015-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     # Performance optimization: broadcast!(identity, dest, A) is equivalent to copyto!(dest, A) if indices match
--     if bc.f === identity && bc.args isa Tuple{AbstractArray} # only a single input argument to broadcast!
--         A = bc.args[1]
--         if axes(dest) == axes(A)
--             return copyto!(dest, A)
--         end
--     end
--     bc′ = preprocess(dest, bc)
--     # Performance may vary depending on whether `@inbounds` is placed outside the
--     # for loop or not. (cf. https://github.com/JuliaLang/julia/issues/38086)
--     @inbounds @simd for I in eachindex(bc′)
--         dest[I] = bc′[I]
--     end
--     return dest
-- end
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  equal : Value L
  throwDimension : Value L
  getproperty : Value L
  identity : Value L
  abstractArray : Value L
  getindex : Value L
  copyTo : Value L
  preprocess : Value L
  eachindex : Value L
  setindex : Value L
  simd : SimdLoop.Bindings L

/-- Pure metadata for the copyto! selected on the fast path. true names this
exact source1015 body; false is a genuinely different selected method on the
unfixed actual source/destination types. Even after the earlier tuple isa
check, the repeated args getter may return a different object/type.
Source reference: base/broadcast.jl:1017-1023. -/
-- Source: base/broadcast.jl:1017-1023 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # Performance optimization: broadcast!(identity, dest, A) is equivalent to copyto!(dest, A) if indices match
--     if bc.f === identity && bc.args isa Tuple{AbstractArray} # only a single input argument to broadcast!
--         A = bc.args[1]
--         if axes(dest) == axes(A)
--             return copyto!(dest, A)
--         end
--     end
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedSelf : Value L → Value L → W → Bool

/-- Source's dimension guard. The first axis pair is used only for equality;
a false result triggers fresh destination then source axes for throwdm. The
right-hand call of || is not itself tested for Bool, and the expression result
is discarded. Thus a genuinely selected custom throwdm that returns allows
execution to continue; its actual error or mutation world is still preserved.
Source reference: base/broadcast.jl:1016. -/
-- Source: base/broadcast.jl:1016-1016 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
-- /Source
def checkAxes {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L Unit := do
  let destAxes ← core.call bindings.axes [dest]
  let sourceAxes ← core.call bindings.axes [bc]
  let equal ← core.call bindings.equal [destAxes, sourceAxes]
  if !(← CheckedBounds.booleanContext core equal) then
    let destAxesAgain ← core.call bindings.axes [dest]
    let sourceAxesAgain ← core.call bindings.axes [bc]
    let _ ← core.call bindings.throwDimension [destAxesAgain, sourceAxesAgain]
    pure ()
  else pure ()

/-- Exact identity/single-array shortcut tests. The f identity check precedes
args and Tuple{AbstractArray}; the successful type test then rereads args and
indexes the actual new property result. Fresh destination/source axes and
actual Boolean equality determine whether this source is returned as the
candidate. None is internal control metadata, not a fabricated Julia result.
Source reference: base/broadcast.jl:1017-1023. -/
-- Source: base/broadcast.jl:1017-1023 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # Performance optimization: broadcast!(identity, dest, A) is equivalent to copyto!(dest, A) if indices match
--     if bc.f === identity && bc.args isa Tuple{AbstractArray} # only a single input argument to broadcast!
--         A = bc.args[1]
--         if axes(dest) == axes(A)
--             return copyto!(dest, A)
--         end
--     end
-- /Source
def identitySource {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (dest bc : Value L) : CoreM W L (Option (Value L)) := do
  let function ← core.call bindings.getproperty [bc, .symbol "f"]
  if !(core.same function bindings.identity) then pure none
  else do
    let arguments ← core.call bindings.getproperty [bc, .symbol "args"]
    let oneArray ← core.applyType (JuliaLean.base.boot.coreV core "Tuple") [bindings.abstractArray]
    if !(core.isa arguments oneArray) then pure none
    else do
      let argumentsAgain ← core.call bindings.getproperty [bc, .symbol "args"]
      let source ← core.call bindings.getindex
        [argumentsAgain, JuliaLean.base.boot.intV core (JInt.lit .i64 1)]
      let destAxes ← core.call bindings.axes [dest]
      let sourceAxes ← core.call bindings.axes [source]
      let equal ← core.call bindings.equal [destAxes, sourceAxes]
      if ← CheckedBounds.booleanContext core equal then pure (some source)
      else pure none

/-- The concrete source loop body reads the actual preprocessed source
before writing the exact returned value into the original destination at the
same index. Its CoreOps is supplied in the enclosing false bounds context.
Source reference: base/broadcast.jl:1028. -/
-- Source: base/broadcast.jl:1028-1028 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         dest[I] = bc′[I]
-- /Source
def writeOne {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (dest ready index : Value L) : CoreM W L Unit := do
  let value ← core.call bindings.getindex [ready, index]
  let _ ← core.call bindings.setindex [dest, value, index]
  pure ()

/-- Actual fallback preprocessing and SIMD loop. The @inbounds macro encloses
both the eachindex range expression and the entire @simd expansion; all use
the false-context runtime operations. Every body reads the actual preprocessed
source at its generated index before writing that exact value at the same
index of the original destination. The shared explicit SIMD fold retains
custom range splitting/numeric/iterator behavior and genuine nontermination.
The body lambda is defined here from source, not supplied by the public caller.
Only after loop completion is the original destination returned.
Source reference: base/broadcast.jl:1024-1031; base/simdloop.jl:66-86. -/
-- Source: base/broadcast.jl:1024-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     bc′ = preprocess(dest, bc)
--     # Performance may vary depending on whether `@inbounds` is placed outside the
--     # for loop or not. (cf. https://github.com/JuliaLang/julia/issues/38086)
--     @inbounds @simd for I in eachindex(bc′)
--         dest[I] = bc′[I]
--     end
--     return dest
-- end
-- /Source
def copyLoop {W L : Type} (contexts : Iteration.ContextOps W L) (bindings : Bindings L)
    (dest bc : Value L) (boundscheck : Bool := true) : CoreM W L (Value L) := do
  let core := contexts.inContext boundscheck
  let inbounds := contexts.inContext false
  let ready ← core.call bindings.preprocess [dest, bc]
  let indices ← inbounds.call bindings.eachindex [ready]
  let _ ← SimdLoop.fold inbounds bindings.simd indices () (fun index _ =>
    writeOne inbounds bindings dest ready index)
  pure dest

/-- Complete source1015. Dimension checking always precedes shortcut tests;
the shortcut explicitly redispatches its actual source and recursively executes
this body when selected again. Custom property results can reselect it or
cycle, so the least partial fixed point is necessary. Other selected copy
methods stay open on unfixed types and may return arbitrary objects. The loop
path invokes real preprocessing/SIMD and returns dest only after completion.
Every operation error retains all prior writes and its actual runtime world.
Source reference: base/broadcast.jl:1015-1031. -/
-- Source: base/broadcast.jl:1015-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::AbstractArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     # Performance optimization: broadcast!(identity, dest, A) is equivalent to copyto!(dest, A) if indices match
--     if bc.f === identity && bc.args isa Tuple{AbstractArray} # only a single input argument to broadcast!
--         A = bc.args[1]
--         if axes(dest) == axes(A)
--             return copyto!(dest, A)
--         end
--     end
--     bc′ = preprocess(dest, bc)
--     # Performance may vary depending on whether `@inbounds` is placed outside the
--     # for loop or not. (cf. https://github.com/JuliaLang/julia/issues/38086)
--     @inbounds @simd for I in eachindex(bc′)
--         dest[I] = bc′[I]
--     end
--     return dest
-- end
-- /Source
def copy {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc : Value L) (boundscheck : Bool := true) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext boundscheck
  checkAxes core bindings dest bc
  match ← identitySource core bindings dest bc with
  | none => copyLoop ops.contexts bindings dest bc boundscheck
  | some source =>
      let self ← (show CoreM W L Bool from fun world =>
        some (.ok (ops.selectedSelf dest source world, world)))
      if self then copy ops bindings dest source boundscheck
      else core.call bindings.copyTo [dest, source]
partial_fixpoint

end JuliaLean.base.broadcast.Models2Group5.PlainCopy


namespace JuliaLean.base.broadcast.Models2Group5.BitCopy

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Native range failures and runtime-value failures are kept in separate existing
exception channels. `run` returns CoreM of an Except: `.ok` is the only method
success, `.error rangeError` is a native-range failure with the current world;
a CoreM error is an actual thrown runtime value with its own current world.
Neither channel is converted to a default or allowed to roll back earlier writes.
Source reference: base/broadcast.jl:1035-1073. -/
-- Source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
--     ndims(dest) == 0 && (dest[] = bc[]; return dest)
--     bc′ = preprocess(dest, bc)
--     # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
--     # to keep the index arithmetic below from wrapping.
--     ax = axes(dest)
--     ax1, out = ax[1], CartesianIndices(tail(ax))
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
--         destc[indc+1] = remain
--     end
--     return dest
-- end
-- /Source
abbrev M (W L A : Type) := ExceptT JuliaLean.base.range.Exc (CoreM W L) A

/-- Lift an actual call while retaining its exact value, exception, mutation world and divergence. This adapter is needed by source1035 inside the closed-range exception layer. Julia source: base/broadcast.jl:1035-1073. -/
-- Source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
--     ndims(dest) == 0 && (dest[] = bc[]; return dest)
--     bc′ = preprocess(dest, bc)
--     # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
--     # to keep the index arithmetic below from wrapping.
--     ax = axes(dest)
--     ax1, out = ax[1], CartesianIndices(tail(ax))
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
--         destc[indc+1] = remain
--     end
--     return dest
-- end
-- /Source

def liftRuntime {W L A : Type} (action : CoreM W L A) : M W L A :=
  ExceptT.mk (do return .ok (← action))

/-- Lift the existing concrete native range models without extracting success by a default or inventing runtime error payloads. The installed range exception remains an error of the outer ExceptT, with the current world. Julia source: base/broadcast.jl:1050-1063. -/
-- Source: base/broadcast.jl:1050-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
-- /Source

def liftNative {W L A : Type} (action : JuliaLean.base.range.JlX A) : M W L A :=
  ExceptT.mk (pure action)

/-- Fixed source bindings. The inherited axis guard is literally identical to source1016 and is reused. BitArray rank, Broadcasted parameters, returned axes/properties/iterators and scalar conversion results are not fixed by this method, so their selected operations remain full runtime calls. The simd field supplies the actual shared expansion for the final dynamically typed colon range. Julia source: base/broadcast.jl:1035-1073. -/
-- Source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
--     ndims(dest) == 0 && (dest[] = bc[]; return dest)
--     bc′ = preprocess(dest, bc)
--     # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
--     # to keep the index arithmetic below from wrapping.
--     ax = axes(dest)
--     ax1, out = ax[1], CartesianIndices(tail(ax))
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
--         destc[indc+1] = remain
--     end
--     return dest
-- end
-- /Source

structure Bindings (L : Type) extends PlainCopy.Bindings L where
  isChunked : Value L
  chunkedCopy : Value L
  ndims : Value L
  tail : Value L
  cartesianIndices : Value L
  first : Value L
  last : Value L
  length : Value L
  subtract : Value L
  greaterEqual : Value L
  greater : Value L
  lessEqual : Value L
  colon : Value L
  convert : Value L
  shiftLeft : Value L
  bitOr : Value L

/-- Source lexical registers. indc and bitst remain native Int64 under their known literal increments; remain stays a full runtime value because custom convert/UInt64/shift/or dispatch may return other objects. No storage is copied into a local heap: all actual writes stay in CoreM. Julia source: base/broadcast.jl:1044-1045. -/
-- Source: base/broadcast.jl:1044-1045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
-- /Source

structure State (L : Type) where
  indc : JInt .i64
  bitst : JInt .i64
  remain : Value L

/-- Closed native UnitRange length, reusing the installed range body and installed native arithmetic. First/last dispatch use their installed OrdinalRange models, and all conversion dictionaries are the existing native ones. Integer(Int64) is the source identity representation. Signed length wraps before the macro compares it with zero; it is never replaced by a mathematical Nat count. Julia source: base/range.jl:794-804. -/
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source

def nativeLength (range : JuliaLean.base.range.UnitRange (JInt .i64)) :
    JuliaLean.base.range.JlX (JInt .i64) :=
  letI : JuliaLean.base.range.JEltype
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨⟩
  letI : JuliaLean.base.range.JFieldStart
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.start⟩
  letI : JuliaLean.base.range.JFieldStop
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JFirst
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.first_OrdinalRange⟩
  letI : JuliaLean.base.range.JLast
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.last_OrdinalRange⟩
  letI : JuliaLean.base.range.JZero (JInt .i64) := ⟨JInt.lit .i64 0⟩
  letI : HSub (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.sub⟩
  letI : HAdd (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.add⟩
  letI : JuliaLean.base.range.JType (JInt .i64) :=
    JuliaLean.base.range.Models1Group7.oneToBitIntegerType .i64
  letI : JuliaLean.base.range.JInteger (JInt .i64) (JInt .i64) := ⟨fun value => pure value⟩
  JuliaLean.base.range.length_AbstractUnitRange range

/-- Closed native iteration for the macro outer 0:0 range, using the installed OrdinalRange entry and state methods. The dictionaries are actual Int64 field access, emptiness, step, comparison, increment and conversion; no iterator callback is accepted. Julia source: base/range.jl:935-943. -/
-- Source: base/range.jl:935-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))
-- 
-- function iterate(r::OrdinalRange{T}, i) where {T}
--     @inline
--     i == last(r) && return nothing
--     next = convert(T, i + step(r))
--     (next, next)
-- end
-- 
-- /Source

def nativeIterate (range : JuliaLean.base.range.UnitRange (JInt .i64))
    (state : Option (JInt .i64)) : JuliaLean.base.range.JlX
      (Option (JInt .i64 × JInt .i64)) :=
  letI : JuliaLean.base.range.JEltype
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨⟩
  letI : JuliaLean.base.range.JFieldStart
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.start⟩
  letI : JuliaLean.base.range.JFieldStop
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) := ⟨fun r => r.stop⟩
  letI : JuliaLean.base.range.JFirst
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.first_OrdinalRange⟩
  letI : JuliaLean.base.range.JLast
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨JuliaLean.base.range.last_OrdinalRange⟩
  letI : JuliaLean.base.range.JLt (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.lt⟩
  letI : JuliaLean.base.range.JIsempty
      (JuliaLean.base.range.UnitRange (JInt .i64)) :=
    ⟨JuliaLean.base.range.isempty_AbstractUnitRange⟩
  letI : JuliaLean.base.range.JZero (JInt .i64) := ⟨JInt.lit .i64 0⟩
  letI : HSub (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.sub⟩
  letI : HAdd (JInt .i64) (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.add⟩
  letI : JuliaLean.base.range.JEq (JInt .i64) (JInt .i64) := ⟨JuliaLean.base.int.eq⟩
  letI : JuliaLean.base.range.JStep
      (JuliaLean.base.range.UnitRange (JInt .i64)) (JInt .i64) :=
    ⟨fun r => pure (JuliaLean.base.range.step_AbstractUnitRange r)⟩
  match state with
  | none => JuliaLean.base.range.iterate_OrdinalRange range
  | some previous => JuliaLean.base.range.iterate_OrdinalRange_state range previous

/-- Closed native SIMD inner loop. Int64 zero, comparison and counter increments use installed wrapping arithmetic. simd_index adds the concrete UnitRange firstindex 1, then invokes installed getindexUnitRangeOverflowSafe with its bounds block elided by the macro inbounds context. Its remainder-to-Int64 is identity on the already Int64 result. The user body is invoked at the actual native index and may change the world, throw, or diverge. Julia source: base/simdloop.jl:52-54 and66-86. -/
-- Source: base/simdloop.jl:66-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # i: Trip index for inner loop
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
-- /Source

def nativeInner {W L S : Type}
    (range : JuliaLean.base.range.UnitRange (JInt .i64)) (count counter : JInt .i64)
    (state : S) (body : JInt .i64 → S → M W L S) : M W L S := do
  if JuliaLean.base.int.lt counter count then
    let index ← JuliaLean.base.range.getindexUnitRangeOverflowSafe
      (m := M W L) (fun _ => pure (JInt.lit .i64 1))
      (fun x y => pure (JuliaLean.base.int.sub x y))
      (fun x y => pure (JuliaLean.base.int.add x y))
      (fun _ _ _ => pure true)
      (fun _ _ => throw (JuliaLean.base.range.Exc.jl .boundsError))
      (fun value => pure value) range
      (JuliaLean.base.int.add counter (JInt.lit .i64 1))
    let next ← body index state
    nativeInner range count (JuliaLean.base.int.add counter (JInt.lit .i64 1)) next body
  else pure state
partial_fixpoint

/-- Closed native SIMD outer loop. The selected builtin simd_outer_range is 0:0, its actual iterator is executed through nativeIterate, and each inner length is the installed nativeLength. The positive test precedes the inner counter-zero initialization, as in the macro. There is no supplied callback replacing either loop. Julia source: base/simdloop.jl:66-86. -/
-- Source: base/simdloop.jl:66-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # i: Trip index for inner loop
--     return quote
--         # Evaluate range value once, to enhance type and data flow analysis by optimizers.
--         let r = $(esc(range))
--             for j in Base.simd_outer_range(r)
--                 let n = Base.simd_inner_length(r,j)
--                     if zero(n) < n
--                         # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
--                         let i = zero(n)
--                             while i < n
--                                 local $(esc(var)) = Base.simd_index(r,j,i)
--                                 $(esc(x.args[2]))        # Body of loop
--                                 i += 1
--                                 $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
--                             end
--                         end
--                     end
--                 end
--             end
--         end
--         nothing
-- /Source

def nativeOuter {W L S : Type}
    (range outer : JuliaLean.base.range.UnitRange (JInt .i64))
    (iteratorState : Option (JInt .i64)) (state : S)
    (body : JInt .i64 → S → M W L S) : M W L S := do
  match ← liftNative (nativeIterate outer iteratorState) with
  | none => pure state
  | some (_, nextIteratorState) =>
      let count ← liftNative (nativeLength range)
      let next ← if JuliaLean.base.int.lt (JInt.lit .i64 0) count then
          nativeInner range count (JInt.lit .i64 0) state body
        else pure state
      nativeOuter range outer (some nextIteratorState) next body
partial_fixpoint

/-- Complete concrete Int64 colon/SIMD composition for the two source ranges bitst:63 and0:63. Both colon constructors reuse the installed homogeneous Real colon model with existing native UnitRange dictionaries. Its loop and source getindex are explicit above; signed-length overflow is retained. This runtime composition is distinct from the installed simdloop syntax-construction model. Julia source: base/broadcast.jl:1050-1062; base/simdloop.jl:48-54 and66-86. -/
-- Source: base/broadcast.jl:1050-1062 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
-- /Source

def nativeFold {W L S : Type} (start stop : JInt .i64) (state : S)
    (body : JInt .i64 → S → M W L S) : M W L S := do
  let range ← liftNative (JuliaLean.base.range.colon_T_T_Real start stop)
  let outer ← liftNative (JuliaLean.base.range.colon_T_T_Real
    (JInt.lit .i64 0) (JInt.lit .i64 0))
  nativeOuter range outer none state body

/-- One source bit accumulation. Its five operations preserve the actual read, Bool conversion, UInt64 construction, shift and or result values without assuming their types. The shift count is the already computed native masked value. All operations are in the surrounding inbounds context. Julia source: base/broadcast.jl:1051. -/
-- Source: base/broadcast.jl:1051-1051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
-- /Source

def accumulate {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (ready outer index : Value L) (shift : JInt .i64) (previous : Value L) :
    CoreM W L (Value L) := do
  let value ← core.call bindings.getindex [ready, index, outer]
  let boolean ← core.call bindings.convert [JuliaLean.base.boot.coreV core "Bool", value]
  let word ← core.call (JuliaLean.base.boot.coreV core "UInt64") [boolean]
  let shifted ← core.call bindings.shiftLeft [word, JuliaLean.base.boot.intV core shift]
  core.call bindings.bitOr [previous, shifted]

/-- Native chunk-loop body updates the actual i by generic + before reading the broadcast, then applies the native j&63 mask and keeps the actual accumulated word. The updated lexical index is carried to the next loop iteration. Julia source: base/broadcast.jl:1050-1052 and1058-1060. -/
-- Source: base/broadcast.jl:1050-1052 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
-- /Source

def wordBody {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (ready outer : Value L) (j : JInt .i64) (current : Value L × Value L) :
    M W L (Value L × Value L) := do
  let index ← liftRuntime (core.call bindings.simd.add
    [current.1, JuliaLean.base.boot.intV core (JInt.lit .i64 1)])
  let word ← liftRuntime (accumulate core bindings ready outer index
    (JuliaLean.base.int.band j (JInt.lit .i64 63)) current.2)
  pure (index, word)

/-- Complete full-chunk while loop. It reevaluates last(ax1) and subtraction before every condition, initializes each chunk with concrete UInt64 zero, executes the fixed0:63 SIMD loop, increments the native output chunk index, and writes the actual returned accumulator. Open arithmetic or iterators may prevent progress, represented by the partial fixed point. Julia source: base/broadcast.jl:1056-1063. -/
-- Source: base/broadcast.jl:1056-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
-- /Source

def fullWords {W L : Type} (contexts : Iteration.ContextOps W L) (bindings : Bindings L)
    (ready outer axis chunks index : Value L) (state : State L)
    (boundscheck : Bool) : M W L (Value L × State L) := do
  let core := contexts.inContext boundscheck
  let inbounds := contexts.inContext false
  let last ← liftRuntime (core.call bindings.last [axis])
  let stop ← liftRuntime (core.call bindings.subtract
    [last, JuliaLean.base.boot.intV core (JInt.lit .i64 64)])
  let test ← liftRuntime (core.call bindings.lessEqual [index, stop])
  if ← liftRuntime (CheckedBounds.booleanContext core test) then
    let (nextIndex, word) ← nativeFold (JInt.lit .i64 0) (JInt.lit .i64 63)
      (index, JuliaLean.base.boot.intV core (JInt.lit .u64 0))
      (wordBody inbounds bindings ready outer)
    let nextChunk := JuliaLean.base.int.add state.indc (JInt.lit .i64 1)
    let _ ← liftRuntime (inbounds.call bindings.setindex
      [chunks, word, JuliaLean.base.boot.intV inbounds nextChunk])
    fullWords contexts bindings ready outer axis chunks nextIndex
      { state with indc := nextChunk } boundscheck
  else pure (index, state)
partial_fixpoint

/-- Final dynamic-range body. It uses the actual generated j directly, masks the native current bitst, and increments bitst only after the accumulated value has been returned. The chunk index is retained. Julia source: base/broadcast.jl:1065-1068. -/
-- Source: base/broadcast.jl:1065-1068 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
-- /Source

def remainingBody {W L : Type} (core : CoreOps W L) (bindings : Bindings L)
    (ready outer index : Value L) (state : State L) : CoreM W L (State L) := do
  let word ← accumulate core bindings ready outer index
    (JuliaLean.base.int.band state.bitst (JInt.lit .i64 63)) state.remain
  pure { state with bitst := JuliaLean.base.int.add state.bitst (JInt.lit .i64 1),
                    remain := word }

/-- Full outer-row body, retaining both short-circuit tests, the second ndims(bc) read, conditional pending-chunk flush, complete full-word while loop and final dynamic SIMD range. Every subexpression under @inbounds, including the last range construction, uses the false context. The final range type is unfixed by source, so the shared complete generic SIMD expansion applies there. Julia source: base/broadcast.jl:1047-1068. -/
-- Source: base/broadcast.jl:1047-1068 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
-- /Source

def row {W L : Type} (contexts : Iteration.ContextOps W L) (bindings : Bindings L)
    (bc ready axis chunks outer : Value L) (state : State L)
    (boundscheck : Bool) : M W L (State L) := do
  let core := contexts.inContext boundscheck
  let inbounds := contexts.inContext false
  let first ← liftRuntime (core.call bindings.first [axis])
  let start ← liftRuntime (core.call bindings.subtract
    [first, JuliaLean.base.boot.intV core (JInt.lit .i64 1)])
  let dimensions ← liftRuntime (core.call bindings.ndims [bc])
  let oneDimensional ← liftRuntime (core.call bindings.equal
    [dimensions, JuliaLean.base.boot.intV core (JInt.lit .i64 1)])
  let chunksPossible ← if ← liftRuntime (CheckedBounds.booleanContext core oneDimensional) then
      pure true
    else do
      let length ← liftRuntime (core.call bindings.length [axis])
      let available ← liftRuntime (core.call bindings.subtract
        [JuliaLean.base.boot.intV core (JInt.lit .i64 64), length])
      let test ← liftRuntime (core.call bindings.greaterEqual
        [JuliaLean.base.boot.intV core state.bitst, available])
      liftRuntime (CheckedBounds.booleanContext core test)
  let (index, current) ← if chunksPossible then do
      let dimensionsAgain ← liftRuntime (core.call bindings.ndims [bc])
      let moreThanOne ← liftRuntime (core.call bindings.greater
        [dimensionsAgain, JuliaLean.base.boot.intV core (JInt.lit .i64 1)])
      let flush ← liftRuntime (CheckedBounds.booleanContext core moreThanOne)
      let (index, current) ← if flush && !(JuliaLean.base.int.eq state.bitst (JInt.lit .i64 0)) then do
          let (nextIndex, word) ← nativeFold state.bitst (JInt.lit .i64 63)
            (start, state.remain) (wordBody inbounds bindings ready outer)
          let nextChunk := JuliaLean.base.int.add state.indc (JInt.lit .i64 1)
          let _ ← liftRuntime (inbounds.call bindings.setindex
            [chunks, word, JuliaLean.base.boot.intV inbounds nextChunk])
          pure (nextIndex, ({ indc := nextChunk, bitst := JInt.lit .i64 0, remain := JuliaLean.base.boot.intV core (JInt.lit .u64 0) } : State L))
        else pure (start, state)
      fullWords contexts bindings ready outer axis chunks index current boundscheck
    else pure (start, state)
  let rangeStart ← liftRuntime (inbounds.call bindings.simd.add
    [index, JuliaLean.base.boot.intV inbounds (JInt.lit .i64 1)])
  let rangeStop ← liftRuntime (inbounds.call bindings.last [axis])
  let range ← liftRuntime (inbounds.call bindings.colon [rangeStart, rangeStop])
  liftRuntime (SimdLoop.fold inbounds bindings.simd range current
    (remainingBody inbounds bindings ready outer))

/-- Explicit ordinary outer for loop on the actual CartesianIndices result. The iterate reply is tested against nothing before its value/state fields are read. Every row receives the state produced by the preceding row; the next iterate call uses the original outer object and actual returned iteration state. No tuple/list/fuel restriction is imposed on the selected custom iterator. Julia source: base/broadcast.jl:1046-1069. -/
-- Source: base/broadcast.jl:1046-1069 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
-- /Source

def outerLoop {W L : Type} (contexts : Iteration.ContextOps W L) (bindings : Bindings L)
    (bc ready axis chunks out next : Value L) (state : State L)
    (boundscheck : Bool) : M W L (State L) := do
  let core := contexts.inContext boundscheck
  if core.same next (JuliaLean.base.boot.nothingV core) then pure state
  else do
    let outer ← liftRuntime (core.getfield next
      (JuliaLean.base.boot.intV core (JInt.lit .i64 1)))
    let iteratorState ← liftRuntime (core.getfield next
      (JuliaLean.base.boot.intV core (JInt.lit .i64 2)))
    let current ← row contexts bindings bc ready axis chunks outer state boundscheck
    let following ← liftRuntime (core.call bindings.simd.iterate [out, iteratorState])
    outerLoop contexts bindings bc ready axis chunks out following current boundscheck
partial_fixpoint

/-- Full source1035, including fresh dimension-error axes, chunked and zero-dimensional exits, full setup/evaluation order, three nested explicit loop forms and final pending-chunk write. CoreM retains all partial writes on runtime error or divergence. The outer ExceptT retains the existing concrete range errors without altering their class or world. The source returns the original destination only on its explicit destination-return branches; the chunked branch returns the actual selected result. Julia source: base/broadcast.jl:1035-1073. -/
-- Source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
--     ndims(dest) == 0 && (dest[] = bc[]; return dest)
--     bc′ = preprocess(dest, bc)
--     # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
--     # to keep the index arithmetic below from wrapping.
--     ax = axes(dest)
--     ax1, out = ax[1], CartesianIndices(tail(ax))
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
--         destc[indc+1] = remain
--     end
--     return dest
-- end
-- /Source

def copy {W L : Type} (contexts : Iteration.ContextOps W L) (bindings : Bindings L)
    (dest bc : Value L) (boundscheck : Bool := true) : M W L (Value L) := do
  let core := contexts.inContext boundscheck
  let inbounds := contexts.inContext false
  liftRuntime (PlainCopy.checkAxes core bindings.toBindings dest bc)
  let chunked ← liftRuntime (core.call bindings.isChunked [dest, bc])
  if ← liftRuntime (CheckedBounds.booleanContext core chunked) then
    liftRuntime (core.call bindings.chunkedCopy [dest, bc])
  else do
    let dimensions ← liftRuntime (core.call bindings.ndims [dest])
    let scalar ← liftRuntime (core.call bindings.equal
      [dimensions, JuliaLean.base.boot.intV core (JInt.lit .i64 0)])
    if ← liftRuntime (CheckedBounds.booleanContext core scalar) then
      let value ← liftRuntime (core.call bindings.getindex [bc])
      let _ ← liftRuntime (core.call bindings.setindex [dest, value])
      pure dest
    else do
      let ready ← liftRuntime (core.call bindings.preprocess [dest, bc])
      let axes ← liftRuntime (core.call bindings.axes [dest])
      let axis ← liftRuntime (core.call bindings.getindex
        [axes, JuliaLean.base.boot.intV core (JInt.lit .i64 1)])
      let tail ← liftRuntime (core.call bindings.tail [axes])
      let out ← liftRuntime (core.call bindings.cartesianIndices [tail])
      let chunks ← liftRuntime (core.call bindings.getproperty [dest, .symbol "chunks"])
      let initial : State L := { indc := JInt.lit .i64 0, bitst := JInt.lit .i64 0, remain := JuliaLean.base.boot.intV core (JInt.lit .u64 0) }
      let next ← liftRuntime (core.call bindings.simd.iterate [out])
      let final ← outerLoop contexts bindings bc ready axis chunks out next initial boundscheck
      if !(JuliaLean.base.int.eq final.bitst (JInt.lit .i64 0)) then
        let _ ← liftRuntime (inbounds.call bindings.setindex
          [chunks, final.remain, JuliaLean.base.boot.intV inbounds
            (JuliaLean.base.int.add final.indc (JInt.lit .i64 1))])
        pure dest
      else pure dest

end JuliaLean.base.broadcast.Models2Group5.BitCopy


namespace JuliaLean.base.broadcast.Models2Group5.ChunkClosures

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)
open JuliaLean.base.broadcast.Models1Group12 (ChunkFunctionCode)

/-- Fixed bitwise generic functions and the nominal embedding of the already
installed first-class ChunkFunctionCode identities. The five capture-free
closure identities are distinct from each other and from global functions;
functionValue is their representation, not a callback implementing a closure.
Source: base/broadcast.jl:1091-1096. -/
-- Source: base/broadcast.jl:1091-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
structure Bindings (L : Type) where
  xor : Value L
  complement : Value L
  and : Value L
  or : Value L
  functionValue : ChunkFunctionCode → Value L

/-- Execute the actual selected binary closure bodies on unrestricted Julia
values. Reuse the installed Models1Group12.m1091/m1093/m1094/m1095/m1096 to
create their capture-free first-class identity codes; this interpreter fills
the old application's mixed/custom-type gap without changing those models.
Every bitwise dispatch target depends on untyped x/y or an arbitrary prior
result, so it uses the existing open CoreOps.call boundary. There is no
same-integer-type restriction or assumption that an operation returns a word.
The global-function codes use the corresponding actual generic function
identity and do not stand in for any anonymous closure's own body.
Source: base/broadcast.jl:1091-1096. -/
-- Source: base/broadcast.jl:1091-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
def applyBinary {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (code : ChunkFunctionCode) (left right : Value L) : CoreM W L (Value L) := do
  match code with
  | .equalClosure =>
      let value ← ops.call bindings.xor [left, right]
      ops.call bindings.complement [value]
  | .lessClosure =>
      let value ← ops.call bindings.complement [left]
      ops.call bindings.and [value, right]
  | .lessEqualClosure =>
      let value ← ops.call bindings.complement [left]
      ops.call bindings.or [value, right]
  | .greaterClosure =>
      let value ← ops.call bindings.complement [right]
      ops.call bindings.and [left, value]
  | .greaterEqualClosure =>
      let value ← ops.call bindings.complement [right]
      ops.call bindings.or [left, value]
  | _ => ops.call (bindings.functionValue code) [left, right]

/-- Complete selected canonical application of a returned anonymous closure.
Two arguments execute its explicit body above. Every other arity produces
the installed MethodError representation with the actual closure identity,
complete original argument tuple and current world age. This helper is an
application of the source-defined anonymous method, not dispatch selection
for additional methods a user might attach to its type; such genuinely other
selected methods remain ordinary CoreOps.call targets. The argument slots
are the caller's already supplied machine-bounded tuple; its native-size
representation invariant is carried by the model input. Source: base/broadcast.jl:1091-1096. -/
-- Source: base/broadcast.jl:1091-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _chunkop(::typeof(==), ::Tuple{Any,Any}) = (x, y) -> ~xor(x, y)
-- _chunkop(::typeof(!=), ::Tuple{Any,Any}) = xor
-- _chunkop(::typeof(<), ::Tuple{Any,Any}) = (x, y) -> ~x & y
-- _chunkop(::typeof(<=), ::Tuple{Any,Any}) = (x, y) -> ~x | y
-- _chunkop(::typeof(>), ::Tuple{Any,Any}) = (x, y) -> x & ~y
-- _chunkop(::typeof(>=), ::Tuple{Any,Any}) = (x, y) -> x | ~y
-- /Source
def invoke {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (code : ChunkFunctionCode) (arguments : Constructors.ArgumentTuple L) :
    CoreM W L (Value L) := do
  match code with
  | .equalClosure | .lessClosure | .lessEqualClosure | .greaterClosure | .greaterEqualClosure =>
      match arguments.values with
      | [left, right] => applyBinary ops bindings code left right
      | _ =>
          let age ← ops.worldAge
          JuliaLean.base.boot.throwObj ops (.methodError (bindings.functionValue code)
            (JuliaLean.base.boot.tupleV ops arguments.values) (JuliaLean.base.boot.intV ops age))
  | _ => ops.call (bindings.functionValue code) arguments.values

end JuliaLean.base.broadcast.Models2Group5.ChunkClosures


namespace JuliaLean.base.broadcast.Models2Group5.ChunkedCheck

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual selected source method. The first six tags are two-argument
methods, noFunction/withFunction are three-argument methods; customTwo and
customThree retain genuinely different dispatch or dispatch failure. Selectors
are trusted dispatch metadata, not supplied algorithms or results.
Source: base/broadcast.jl:1098-1105. -/
-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
inductive Method where
  | wrapper
  | fallback
  | bitHead
  | boolHead
  | wrapperHead
  | empty
  | noFunction
  | withFunction
  | customTwo
  | customThree

/-- Existing runtime and native/custom tuple-read interface, with pure
current-world dispatch metadata for both recursive arities. No Boolean
correctness law, shape law or successful-constructor premise is imposed.
Source: base/broadcast.jl:1098-1105. -/
-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
structure Ops (W L : Type) extends NewIndex.IntegerOps W L where
  selectedTwo : Value L → Value L → W → Method
  selectedThree : Value L → Value L → Value L → W → Method

/-- Actual fixed generic-function identities at base/broadcast.jl:1098-1105. -/
-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  getindex : Value L
  chunkop : Value L
  ischunked : Value L
  size : Value L
  equal : Value L
  tail : Value L

/-- Eliminate the impossible error branch of a pure installed Boolean model.
This only unwraps StateT Unit (Except Empty); it executes no Julia callback,
adds no error recovery and cannot drop a runtime effect. The source constant
methods below reuse Bits.m1099/m1101/m1105 through this adapter.
Source: base/broadcast.jl:1099-1105. -/
-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
def pureBoolean (action : StateT Unit (Except Empty) Bool) : Bool :=
  match action () with
  | .ok (value, _) => value
  | .error impossible => nomatch impossible

/-- All selected source bodies and their actual own recursion. Wrapper
methods read f before args, obtain the actual chunk operation, then select the
three-argument call. That call reads the current args property before
selecting its two-argument target. Tuple branches preserve source evaluation
order: size(R) precedes the bit-array head access; nested wrappers are fully
checked before their tail is touched; Bool heads are never read. Every &&
uses the installed Boolean-context lowering, including non-Bool TypeError.
A tail, property or custom method may return arbitrary values or cycles, so
CoreM partial_fixpoint admits nontermination without caller fuel. Canonical
native tuple reads use NewIndex.tupleGet, and the fixed false/true Base cases
reuse the unchanged installed constant models. The result argument is always
forwarded by original identity. Source: base/broadcast.jl:1098-1105. -/
-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (method : Method) (result value function : Value L) : CoreM W L (Value L) := do
  let core := ops.toIntegerOps.toOps.toCoreOps
  let absent := JuliaLean.base.boot.nothingV core
  match method with
  | .noFunction =>
      pure (JuliaLean.base.boot.boolV core
        (pureBoolean (Bits.m1099 (H := Unit) (ε := Empty) result value Bits.Nothing.nothing)))
  | .fallback =>
      pure (JuliaLean.base.boot.boolV core
        (pureBoolean (Bits.m1101 (H := Unit) (ε := Empty) result value)))
  | .empty =>
      pure (JuliaLean.base.boot.boolV core
        (pureBoolean (Bits.m1105 (H := Unit) (ε := Empty) result ())))
  | .customTwo => ops.call bindings.ischunked [result, value]
  | .customThree => ops.call bindings.ischunked [result, value, function]
  | .wrapper =>
      let originalFunction ← ops.call bindings.getproperty [value, .symbol "f"]
      let arguments ← ops.call bindings.getproperty [value, .symbol "args"]
      let chunkFunction ← ops.call bindings.chunkop [originalFunction, arguments]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedThree result value chunkFunction world, world)))
      run ops bindings selected result value chunkFunction
  | .withFunction =>
      let arguments ← ops.call bindings.getproperty [value, .symbol "args"]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedTwo result arguments world, world)))
      run ops bindings selected result arguments absent
  | .bitHead =>
      let resultSize ← ops.call bindings.size [result]
      let head ← NewIndex.tupleGet ops.toIntegerOps bindings.getindex value (JInt.lit .i64 1)
      let headSize ← ops.call bindings.size [head]
      let equal ← ops.call bindings.equal [resultSize, headSize]
      if ← CheckedBounds.booleanContext core equal then
        let tail ← ops.call bindings.tail [value]
        let selected ← (show CoreM W L Method from fun world =>
          some (.ok (ops.selectedTwo result tail world, world)))
        run ops bindings selected result tail absent
      else pure (JuliaLean.base.boot.boolV core false)
  | .boolHead =>
      let tail ← ops.call bindings.tail [value]
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedTwo result tail world, world)))
      run ops bindings selected result tail absent
  | .wrapperHead =>
      let head ← NewIndex.tupleGet ops.toIntegerOps bindings.getindex value (JInt.lit .i64 1)
      let selected ← (show CoreM W L Method from fun world =>
        some (.ok (ops.selectedTwo result head world, world)))
      let checked ← run ops bindings selected result head absent
      if ← CheckedBounds.booleanContext core checked then
        let tail ← ops.call bindings.tail [value]
        let tailMethod ← (show CoreM W L Method from fun world =>
          some (.ok (ops.selectedTwo result tail world, world)))
        run ops bindings tailMethod result tail absent
      else pure (JuliaLean.base.boot.boolV core false)
partial_fixpoint

/-- Enter the selected source1098 body directly; only subsequent recursive
calls consult dispatch metadata. Source: base/broadcast.jl:1098. -/
-- Source: base/broadcast.jl:1098-1098 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- /Source
def wrapper {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (result value : Value L) : CoreM W L (Value L) :=
  run ops bindings .wrapper result value (JuliaLean.base.boot.nothingV ops.toIntegerOps.toOps.toCoreOps)

/-- Enter the selected source1100 body directly; only subsequent recursive
calls consult dispatch metadata. Source: base/broadcast.jl:1100. -/
-- Source: base/broadcast.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- /Source
def withFunction {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (result value function : Value L) : CoreM W L (Value L) :=
  run ops bindings .withFunction result value function

/-- Enter the selected source1102 body directly; only subsequent recursive
calls consult dispatch metadata. Source: base/broadcast.jl:1102. -/
-- Source: base/broadcast.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- /Source
def bitHead {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (result value : Value L) : CoreM W L (Value L) :=
  run ops bindings .bitHead result value (JuliaLean.base.boot.nothingV ops.toIntegerOps.toOps.toCoreOps)

/-- Enter the selected source1103 body directly; only subsequent recursive
calls consult dispatch metadata. Source: base/broadcast.jl:1103. -/
-- Source: base/broadcast.jl:1103-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- /Source
def boolHead {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (result value : Value L) : CoreM W L (Value L) :=
  run ops bindings .boolHead result value (JuliaLean.base.boot.nothingV ops.toIntegerOps.toOps.toCoreOps)

/-- Enter the selected source1104 body directly; only subsequent recursive
calls consult dispatch metadata. Source: base/broadcast.jl:1104. -/
-- Source: base/broadcast.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- /Source
def wrapperHead {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (result value : Value L) : CoreM W L (Value L) :=
  run ops bindings .wrapperHead result value (JuliaLean.base.boot.nothingV ops.toIntegerOps.toOps.toCoreOps)

end JuliaLean.base.broadcast.Models2Group5.ChunkedCheck


namespace JuliaLean.base.broadcast.Models2Group5.LiftFunctions

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The selected two-argument liftfuncs method after chunkop has returned.
The two Base bodies are explicit; custom denotes genuinely different dispatch
on the unfixed Broadcasted/function types. Source: broadcast.jl:1108-1110. 
Source reference: base/broadcast.jl:1108-1110.
-/
-- Source: base/broadcast.jl:1108-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted{<:Any,<:Any,<:Any}) = liftfuncs(bc, _chunkop(bc.f, bc.args))
-- liftfuncs(bc::Broadcasted, ::Nothing) = Broadcasted(bc.style, bc.f, map(liftfuncs, bc.args), bc.axes)
-- liftfuncs(bc::Broadcasted, f) = Broadcasted(bc.style, f, map(liftfuncs, bc.args), bc.axes)
-- /Source
inductive Method where
  | preserve
  | replace
  | custom

/-- Existing runtime operations plus current-world method selection.
Selection supplies neither the constructor nor the map/body result.
Source: base/broadcast.jl:1108-1110. -/
-- Source: base/broadcast.jl:1108-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted{<:Any,<:Any,<:Any}) = liftfuncs(bc, _chunkop(bc.f, bc.args))
-- liftfuncs(bc::Broadcasted, ::Nothing) = Broadcasted(bc.style, bc.f, map(liftfuncs, bc.args), bc.axes)
-- liftfuncs(bc::Broadcasted, f) = Broadcasted(bc.style, f, map(liftfuncs, bc.args), bc.axes)
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedLift : Value L → Value L → W → Method

/-- Original global function identities. map receives the actual liftfuncs
function object, not a newly supplied recursive mapper or closure.
Source: base/broadcast.jl:1108-1110. -/
-- Source: base/broadcast.jl:1108-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted{<:Any,<:Any,<:Any}) = liftfuncs(bc, _chunkop(bc.f, bc.args))
-- liftfuncs(bc::Broadcasted, ::Nothing) = Broadcasted(bc.style, bc.f, map(liftfuncs, bc.args), bc.axes)
-- liftfuncs(bc::Broadcasted, f) = Broadcasted(bc.style, f, map(liftfuncs, bc.args), bc.axes)
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  chunkop : Value L
  liftfuncs : Value L
  map : Value L
  broadcasted : Value L

/-- Full Nothing-operator body. Read style, original f and args in source
order; map the exact args using the original liftfuncs function identity;
only after map completes read axes and call the four-argument constructor.
Unfixed tuple parameter/property-return types select map through existing
open dispatch. The map callback is an actual source callee, not this method's
body or its direct recursion. Every reference and operation outcome survives.
Source: base/broadcast.jl:1109. -/
-- Source: base/broadcast.jl:1109-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted, ::Nothing) = Broadcasted(bc.style, bc.f, map(liftfuncs, bc.args), bc.axes)
-- /Source
def preserve {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.getproperty [bc, .symbol "style"]
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
  let mapped ← ops.call bindings.map [bindings.liftfuncs, arguments]
  let axes ← ops.call bindings.getproperty [bc, .symbol "axes"]
  ops.call bindings.broadcasted [style, function, mapped, axes]

/-- Full replacement-operator body. It never reads bc.f: the exact supplied
function is used after style, map(liftfuncs,args), and axes have been evaluated.
Property reads and constructor dispatch remain effectful on unfixed type
parameters; no immutable simplified record bypasses them. Source1110. 
Source reference: base/broadcast.jl:1110-1110.
-/
-- Source: base/broadcast.jl:1110-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted, f) = Broadcasted(bc.style, f, map(liftfuncs, bc.args), bc.axes)
-- /Source
def replace {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (bc function : Value L) : CoreM W L (Value L) := do
  let style ← ops.call bindings.getproperty [bc, .symbol "style"]
  let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
  let mapped ← ops.call bindings.map [bindings.liftfuncs, arguments]
  let axes ← ops.call bindings.getproperty [bc, .symbol "axes"]
  ops.call bindings.broadcasted [style, function, mapped, axes]

/-- Full unary method: f and args precede chunkop; its actual result and the
current world select the direct two-argument call. Both known source bodies
are executed explicitly and only a genuinely different selected target uses
the open liftfuncs call. A custom chunk operator need not be a function or
return a conventional value. Source: base/broadcast.jl:1108-1110. -/
-- Source: base/broadcast.jl:1108-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- liftfuncs(bc::Broadcasted{<:Any,<:Any,<:Any}) = liftfuncs(bc, _chunkop(bc.f, bc.args))
-- /Source
def wrapper {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let function ← ops.call bindings.getproperty [bc, .symbol "f"]
  let arguments ← ops.call bindings.getproperty [bc, .symbol "args"]
  let operation ← ops.call bindings.chunkop [function, arguments]
  let selected ← (show CoreM W L Method from fun world =>
    some (.ok (ops.selectedLift bc operation world, world)))
  match selected with
  | .preserve => preserve ops.toCoreOps bindings bc
  | .replace => replace ops.toCoreOps bindings bc operation
  | .custom => ops.call bindings.liftfuncs [bc, operation]

end JuliaLean.base.broadcast.Models2Group5.LiftFunctions


namespace JuliaLean.base.broadcast.Models2Group5.IthChunk

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The source varargs after i and the mandatory vector/word. Native total
arity includes both mandatory arguments. Heterogeneous elements and all
mutable reference aliases remain their actual Values.
Source: base/broadcast.jl:1118-1119. The stored tuple field count also fits UInt32, matching the DataTypeLayout
representation invariant at base/runtime_internals.jl:624-626. -/
-- Source: base/broadcast.jl:1118-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
structure Tail (L : Type) where
  values : List (Value L)
  fieldCountFits : values.length ≤ IntTy.u32.max.toNat
  totalSize : JInt .i64
  totalSize_eq : totalSize.val = (values.length : Int) + 2

/-- Actual selected non-nullary ithchunk method; custom denotes a genuinely
different method on the unfixed index or tail types. Source1118-1119. 
Source reference: base/broadcast.jl:1118-1119.
-/
-- Source: base/broadcast.jl:1118-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
inductive ConsMethod where
  | vector
  | scalar
  | custom

/-- Even the terminal call can select an extension on an unfixed index type.
The builtin tag names the installed constant method at1117. 
Source reference: base/broadcast.jl:1117-1119.
-/
-- Source: base/broadcast.jl:1117-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ithchunk(i) = ()
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
inductive NilMethod where
  | builtin
  | custom

/-- Existing context-selected runtime operations and pure current-world
selected-method metadata. The Bool is propagated compiler context, never an
added Julia argument. Dispatch can depend on arbitrary prior getter effects.
Source: base/broadcast.jl:1117-1119. -/
-- Source: base/broadcast.jl:1117-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ithchunk(i) = ()
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedCons : Value L → Value L → List (Value L) → W → ConsMethod
  selectedNil : Value L → W → NilMethod

/-- Fixed source function identities at base/broadcast.jl:1118-1119. -/
-- Source: base/broadcast.jl:1118-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
structure Bindings (L : Type) where
  getindex : Value L
  ithchunk : Value L
  iterate : Value L

/-- Explicit recursive ithchunk application on the already supplied argument
tuple. Its immutable slot list is a suffix of the public native-bounded Tail;
structural recursion is representation traversal, never Julia integer
arithmetic or caller fuel. The index remains an arbitrary Julia value.
Although a vector is concretely Vector{UInt64}, its indexing target depends
on the unfixed index type: ranges, custom indices, arbitrary returns, errors
and effects all remain in the allowed CoreOps.call interface. A UInt64 head
is stored unchanged and performs no read or arithmetic. Canonical nullary
termination reuses Bits.m1117. Each source tuple splat executes after its
recursive suffix, through the existing _apply_iterate primitive. Only an
actually selected different method invokes the open ithchunk function.
forced is selected-entry metadata for the public source method, not fuel.
Source: base/broadcast.jl:1117-1119. -/
-- Source: base/broadcast.jl:1117-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ithchunk(i) = ()
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (boundscheck : Bool) (forced : Option ConsMethod) (index : Value L)
    (arguments : List (Value L)) : CoreM W L (Value L) :=
  let core := ops.contexts.inContext boundscheck
  match arguments with
  | [] => fun world =>
      match ops.selectedNil index world with
      | .custom => core.call bindings.ithchunk [index] world
      | .builtin =>
          let empty := match Bits.m1117 (H := Unit) (ε := Empty) index () () with
            | .ok (value, _) => value
            | .error impossible => nomatch impossible
          match empty with
          | () => some (.ok (JuliaLean.base.boot.tupleV core [], world))
  | head :: tail => do
      let method ← (show CoreM W L ConsMethod from fun world =>
        let method := match forced with
          | some method => method
          | none => ops.selectedCons index head tail world
        some (.ok (method, world)))
      match method with
      | .custom => core.call bindings.ithchunk (index :: head :: tail)
      | .vector =>
          let first ← core.call bindings.getindex [head, index]
          let suffix ← run ops bindings boundscheck none index tail
          core.applyIterate bindings.iterate
            [JuliaLean.base.boot.coreV core "tuple", JuliaLean.base.boot.tupleV core [first], suffix]
      | .scalar =>
          let suffix ← run ops bindings boundscheck none index tail
          core.applyIterate bindings.iterate
            [JuliaLean.base.boot.coreV core "tuple", JuliaLean.base.boot.tupleV core [head], suffix]

/-- Enter the selected vector method with the original unrestricted index.
All reads use the propagated compiler context and precede recursive suffix
work. Source: base/broadcast.jl:1118. -/
-- Source: base/broadcast.jl:1118-1118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds ithchunk(i, c::Vector{UInt64}, args...) = (c[i], ithchunk(i, args...)...)
-- /Source
def vector {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (index chunks : Value L) (tail : Tail L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  run ops bindings boundscheck (some .vector) index (chunks :: tail.values)

/-- Enter the selected UInt64 method with its actual machine word. Its bits
are embedded unchanged; no read, conversion or index inspection is added.
Source: base/broadcast.jl:1119. -/
-- Source: base/broadcast.jl:1119-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds ithchunk(i, b::UInt64, args...) = (b, ithchunk(i, args...)...)
-- /Source
def scalar {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (index : Value L) (word : JInt .u64) (tail : Tail L)
    (boundscheck : Bool := true) : CoreM W L (Value L) :=
  let core := ops.contexts.inContext boundscheck
  run ops bindings boundscheck (some .scalar) index
    (JuliaLean.base.boot.intV core word :: tail.values)

end JuliaLean.base.broadcast.Models2Group5.IthChunk


namespace JuliaLean.base.broadcast.Models2Group5.ChunkedCopy

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual selected final &: a canonical UInt64 pair carries both original
machine words, while custom covers genuinely selected other argument types
or methods. The payload is runtime operand metadata, never a supplied result.
Source: base/broadcast.jl:1128; base/int.jl:407. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
inductive AndMethod where
  | words (left right : JInt .u64)
  | custom

/-- Existing contextual runtime operations plus actual current-world bitwise
selection. Normal source operations use the incoming applicable context;
explicit @inbounds body/final-mask operations use context false. Type/rank
parameters and arbitrary property results remain open dispatch boundaries.
Source: base/broadcast.jl:1120-1130. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedAnd : Value L → Value L → W → AndMethod

/-- Actual source function identities, including those of the pinned SIMD
macro expansion. iterate is shared by ordinary iteration and source splats.
Source: base/broadcast.jl:1120-1130; base/simdloop.jl:66-86. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
structure Bindings (L : Type) where
  isempty : Value L
  liftfuncs : Value L
  flatten : Value L
  liftchunks : Value L
  getproperty : Value L
  eachindex : Value L
  ithchunk : Value L
  getindex : Value L
  setindexBang : Value L
  lastindex : Value L
  maskEnd : Value L
  and : Value L
  simd : SimdLoop.Bindings L

/-- Known UInt64 &: reuse the installed concrete bit-integer model. A custom
selected operator sees both exact values only after the final word and mask
have been evaluated. No mask or word is coerced by this caller.
Source: base/broadcast.jl:1128; base/int.jl:407. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
def bitAnd {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (left right : Value L) : CoreM W L (Value L) := fun world =>
  let core := ops.contexts.inContext false
  match ops.selectedAnd left right world with
  | .words first second => some (.ok
      (JuliaLean.base.boot.intV core (JuliaLean.base.int.band first second), world))
  | .custom => core.call bindings.and [left, right] world

/-- One source loop body. Its callee property f.f is evaluated before either
splat, the original i is included only in ithchunk's input, and actual returned
arguments are splatted into the selected function. setindex! then receives
its exact value, same chunk object and original index. Assignment yields its
RHS value, independently of a custom setter's return. Every operation is in
the explicit @inbounds context and retains alias effects and throw worlds.
Source: base/broadcast.jl:1126. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
def writeChunk {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (flat arguments chunks index : Value L) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext false
  let function ← core.call bindings.getproperty [flat, .symbol "f"]
  let values ← core.applyIterate bindings.simd.iterate
    [bindings.ithchunk, JuliaLean.base.boot.tupleV core [index], arguments]
  let value ← core.applyIterate bindings.simd.iterate [function, values]
  let _ ← core.call bindings.setindexBang [chunks, value, index]
  pure value

/-- The final indexed &= evaluates end once, reads the actual old word, then
obtains the actual selected end mask, combines them and writes the result.
The destination's unfixed BitArray rank permits selected _msk_end methods;
its exact result and errors remain open rather than an assumed masking law.
When &:UInt64×UInt64 is canonical, its concrete Base bits are closed above.
The successful setter's return is discarded before returning original dest.
Source: base/broadcast.jl:1128-1129. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
def finish {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest chunks : Value L) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext false
  let last ← core.call bindings.lastindex [chunks]
  let word ← core.call bindings.getindex [chunks, last]
  let mask ← core.call bindings.maskEnd [dest]
  let masked ← bitAnd ops bindings word mask
  let _ ← core.call bindings.setindexBang [chunks, masked, last]
  pure dest

/-- Full chunked-copy body. True emptiness returns the original destination
before preprocessing; non-Bool fails at the source conditional. Otherwise
liftfuncs, flatten, argument lifting, chunks and eachindex are evaluated once
in order. The actual pinned SIMD expansion executes all outer/inner numeric
and iterator calls, with an explicit stateful loop body. Its result is followed
by the final mask write, never a snapshot rewrite. Arbitrary custom indices,
functions, properties, results, mutations, errors and divergence remain in
scope. Only machine integer constants and canonical UInt64 & are fixed;
there are no unbounded native counts, List iterator restrictions or own-loop
callbacks. Source: base/broadcast.jl:1120-1130; simdloop.jl:66-86. -/
-- Source: base/broadcast.jl:1120-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function chunkedcopyto!(dest::BitArray, bc::Broadcasted)
--     isempty(dest) && return dest
--     f = flatten(liftfuncs(bc))
--     args = liftchunks(f.args)
--     dc = dest.chunks
--     @simd for i in eachindex(dc)
--         @inbounds dc[i] = f.f(ithchunk(i, args...)...)
--     end
--     @inbounds dc[end] &= Base._msk_end(dest)
--     return dest
-- end
-- /Source
def copy {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc : Value L) (boundscheck : Bool := true) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext boundscheck
  let empty ← core.call bindings.isempty [dest]
  if ← CheckedBounds.booleanContext core empty then pure dest
  else
    let lifted ← core.call bindings.liftfuncs [bc]
    let flat ← core.call bindings.flatten [lifted]
    let sourceArguments ← core.call bindings.getproperty [flat, .symbol "args"]
    let arguments ← core.call bindings.liftchunks [sourceArguments]
    let chunks ← core.call bindings.getproperty [dest, .symbol "chunks"]
    let indices ← core.call bindings.eachindex [chunks]
    let _ ← SimdLoop.fold core bindings.simd indices () (fun index _ => do
      let _ ← writeChunk ops bindings flat arguments chunks index
      pure ())
    finish ops bindings dest chunks

end JuliaLean.base.broadcast.Models2Group5.ChunkedCopy


namespace JuliaLean.base.broadcast.Models2Group5.NonleafCopy

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual lexical arguments of copyto_nonleaf!. Count is unrestricted because
the Julia method does not constrain its type; additions still use native Int1
and actual selected +, never Lean Nat arithmetic. Source1145-1163. 
Source reference: base/broadcast.jl:1145-1163.
-/
-- Source: base/broadcast.jl:1145-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
structure CopyInputs (L : Type) where
  dest : Value L
  bc : Value L
  iterator : Value L
  state : Value L
  count : Value L

/-- The eight actual restart arguments, retaining both allocation references
and every alias. These records only group source locals. Source1136-1143. 
Source reference: base/broadcast.jl:1136-1143.
-/
-- Source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- /Source
structure RestartInputs (L : Type) where
  newdest : Value L
  dest : Value L
  bc : Value L
  value : Value L
  index : Value L
  iterator : Value L
  state : Value L
  count : Value L

/-- Actual selected recursive method: the known source body or a genuinely
different method on unfixed argument types. Source1136-1163. 
Source reference: base/broadcast.jl:1136-1163.
-/
-- Source: base/broadcast.jl:1136-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- 
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
inductive Selection where
  | builtin
  | custom

/-- Explicit source control states for mutual copy/restart recursion. Cached
eltype is retained by loop frames and refreshed only at a new copy entry.
The iterator's next value is kept separately from its actual Julia state.
Source: base/broadcast.jl:1136-1163. -/
-- Source: base/broadcast.jl:1136-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- 
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
inductive Phase (L : Type) where
  | copy (inputs : CopyInputs L)
  | loop (inputs : CopyInputs L) (elementType : Value L)
  | restart (inputs : RestartInputs L)
  | priorReplies (inputs : RestartInputs L) (taken next : Value L)

/-- Existing contextual operations and pure live-world recursive selection.
Ordinary calls use the function's default context; the explicit @inbounds
read/write in source1145 uses false. No iterator, count, element or allocation
correctness law is imposed. Source1136-1163. 
Source reference: base/broadcast.jl:1136-1163.
-/
-- Source: base/broadcast.jl:1136-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- 
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedCopy : CopyInputs L → W → Selection
  selectedRestart : RestartInputs L → W → Selection

/-- Fixed functions used by the actual source bodies and their generic
assignment/iteration lowering. Source1136-1163. 
Source reference: base/broadcast.jl:1136-1163.
-/
-- Source: base/broadcast.jl:1136-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- 
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
structure Bindings (L : Type) where
  take : Value L
  iterate : Value L
  indexedIterate : Value L
  getindex : Value L
  setindexBang : Value L
  add : Value L
  eltype : Value L
  promoteTypejoin : Value L
  similar : Value L
  restart : Value L
  copy : Value L

/-- Complete own mutual recursion and iteration. Restart uses actual take and
for-loop iteration, copying each source element into the new destination
before writing the current value and incrementing count. Copy caches eltype,
iterates with its supplied state, destructures the explicit I,state assignment
by indexed_iterate, then reads bc inbounds. A checked dynamic isa rejects
non-type eltype replies; fitting values are written before count increments.
The non-fitting branch promotes from cached T and typeof(actual value),
allocates, then executes the actual selected restart body. Every count value,
iterator shape, property/result, error, mutation and divergence is retained.
The state machine merely makes source loops/mutual calls explicit; its least
partial fixed point has no fuel, list iterator or size-decrease premise.
Source: base/broadcast.jl:1136-1163; flfrontend.destructure2 lowering. -/
-- Source: base/broadcast.jl:1136-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- 
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
def run {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (phase : Phase L) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext true
  let unchecked := ops.contexts.inContext false
  let one := JuliaLean.base.boot.intV core (JInt.lit .i64 1)
  let two := JuliaLean.base.boot.intV core (JInt.lit .i64 2)
  match phase with
  | .copy inputs =>
      let elementType ← core.call bindings.eltype [inputs.dest]
      run ops bindings (.loop inputs elementType)
  | .loop inputs elementType =>
      let next ← core.call bindings.iterate [inputs.iterator, inputs.state]
      if core.same next (JuliaLean.base.boot.nothingV core) then pure inputs.dest
      else
        let firstPair ← core.call bindings.indexedIterate [next, one]
        let index ← core.getfield firstPair one
        let destructureState ← core.getfield firstPair two
        let secondPair ← core.call bindings.indexedIterate [next, two, destructureState]
        let nextState ← core.getfield secondPair one
        let value ← unchecked.call bindings.getindex [inputs.bc, index]
        if ← RuntimeTypes.checkedIsa core value elementType then
          let _ ← unchecked.call bindings.setindexBang [inputs.dest, value, index]
          let count ← core.call bindings.add [inputs.count, one]
          run ops bindings (.loop { inputs with state := nextState, count := count } elementType)
        else
          let widened ← core.call bindings.promoteTypejoin
            [elementType, .leaf (core.typeOf value)]
          let newdest ← core.call bindings.similar [inputs.bc, widened]
          let restart : RestartInputs L :=
            ⟨newdest, inputs.dest, inputs.bc, value, index, inputs.iterator,
              nextState, inputs.count⟩
          let method ← (show CoreM W L Selection from fun world =>
            some (.ok (ops.selectedRestart restart world, world)))
          return ← match method with
          | .builtin => run ops bindings (.restart restart)
          | .custom => core.call bindings.restart [restart.newdest, restart.dest, restart.bc, restart.value, restart.index, restart.iterator, restart.state, restart.count]
  | .restart inputs =>
      let taken ← core.call bindings.take [inputs.iterator, inputs.count]
      let next ← core.call bindings.iterate [taken]
      run ops bindings (.priorReplies inputs taken next)
  | .priorReplies inputs taken next =>
      if core.same next (JuliaLean.base.boot.nothingV core) then
        let _ ← core.call bindings.setindexBang [inputs.newdest, inputs.value, inputs.index]
        let count ← core.call bindings.add [inputs.count, one]
        let copied : CopyInputs L :=
          ⟨inputs.newdest, inputs.bc, inputs.iterator, inputs.state, count⟩
        let method ← (show CoreM W L Selection from fun world =>
          some (.ok (ops.selectedCopy copied world, world)))
        return ← match method with
        | .builtin => run ops bindings (.copy copied)
        | .custom => core.call bindings.copy [copied.dest, copied.bc, copied.iterator, copied.state, copied.count]
      else
        let index ← core.getfield next one
        let iteratorState ← core.getfield next two
        let value ← core.call bindings.getindex [inputs.dest, index]
        let _ ← core.call bindings.setindexBang [inputs.newdest, value, index]
        let following ← core.call bindings.iterate [taken, iteratorState]
        run ops bindings (.priorReplies inputs taken following)
partial_fixpoint

/-- Enter the selected restart body directly with all original arguments.
Only actual subsequent recursive calls consult selection metadata.
Source: base/broadcast.jl:1136-1143. -/
-- Source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--     # Function barrier that makes the copying to newdest type stable
--     for II in Iterators.take(iter, count)
--         newdest[II] = dest[II]
--     end
--     newdest[I] = val
--     return copyto_nonleaf!(newdest, bc, iter, state, count+1)
-- end
-- /Source
def restart {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (newdest dest bc value index iterator state count : Value L) : CoreM W L (Value L) :=
  run ops bindings (.restart ⟨newdest, dest, bc, value, index, iterator, state, count⟩)

/-- Enter the selected nonleaf-copy body directly; no type, count or iterator
representation is narrowed beyond trusted Julia source dispatch.
Source: base/broadcast.jl:1145-1163. -/
-- Source: base/broadcast.jl:1145-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto_nonleaf!(dest, bc::Broadcasted, iter, state, count)
--     T = eltype(dest)
--     while true
--         y = iterate(iter, state)
--         y === nothing && break
--         I, state = y
--         @inbounds val = bc[I]
--         if val isa T
--             @inbounds dest[I] = val
--         else
--             # This element type doesn't fit in dest. Allocate a new dest with wider eltype,
--             # copy over old values, and continue
--             newdest = Base.similar(bc, promote_typejoin(T, typeof(val)))
--             return restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
--         end
--         count += 1
--     end
--     return dest
-- end
-- /Source
def copy {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (dest bc iterator state count : Value L) : CoreM W L (Value L) :=
  run ops bindings (.copy ⟨dest, bc, iterator, state, count⟩)

end JuliaLean.base.broadcast.Models2Group5.NonleafCopy


namespace JuliaLean.base.broadcast.Models2Group5.TupleCopy

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Complete first-class representation of the generated unary callable at
base/broadcast.jl:1171. The original bc reference is retained, alongside its
nominal generated-function value and executable full positional application.
The runtime interfaces are interpretation data, not extra Julia captures. -/
-- Source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted{Style{Tuple}})
--     dim = axes(bc)
--     length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
--     N = length(dim[1])
--     return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
-- end
-- /Source
structure Closure (W L : Type) where
  capturedBc : Value L
  value : Value L
  invoke : Constructors.ArgumentTuple L → CoreM W L (Value L)

/-- Actual global bindings and the nominal representation of the generated
closure with its original bc capture, from base/broadcast.jl:1167-1172.
closureValue supplies identity/representation, never a callback or result. -/
-- Source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted{Style{Tuple}})
--     dim = axes(bc)
--     length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
--     N = length(dim[1])
--     return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
-- end
-- /Source
structure Bindings (L : Type) where
  axes : Value L
  length : Value L
  equal : Value L
  getindex : Value L
  broadcastGetindex : Value L
  val : Value L
  ntuple : Value L
  dimensionMismatch : Value L
  closureValue : Value L → Value L

/-- Existing primitive/dispatch operations in their actual compiler contexts,
and the selected ntuple callee on the still-unfixed Val(N) result type. That
callee receives the complete source callable so custom dispatch may inspect
its identity/capture or invoke its body. No ntuple correctness law is assumed.
Source: base/broadcast.jl:1171. -/
-- Source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted{Style{Tuple}})
--     dim = axes(bc)
--     length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
--     N = length(dim[1])
--     return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
-- end
-- /Source
structure Ops (W L : Type) where
  contexts : Iteration.ContextOps W L
  ntuple : Closure W L → Value L → CoreM W L (Value L)

/-- The generated source callable has exactly one argument. Its body passes
original bc and that argument to the selected _broadcast_getindex under the
explicit @inbounds context. Other native-bounded positional arities preserve
the actual function/argument identities and current world-age MethodError.
Nothing assumes that a custom ntuple supplies an integer or a valid index.
Source: base/broadcast.jl:1171. -/
-- Source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted{Style{Tuple}})
--     dim = axes(bc)
--     length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
--     N = length(dim[1])
--     return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
-- end
-- /Source
def closure {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (bc : Value L) : Closure W L where
  capturedBc := bc
  value := bindings.closureValue bc
  invoke := fun arguments =>
    match arguments.values with
    | [index] => (contexts.inContext false).call bindings.broadcastGetindex [bc, index]
    | _ => do
        let core := contexts.inContext true
        let age ← core.worldAge
        JuliaLean.base.boot.throwObj core (.methodError (bindings.closureValue bc)
          (JuliaLean.base.boot.tupleV core arguments.values)
          (JuliaLean.base.boot.intV core age))

/-- Necessary concrete default constructor for the fixed String literal in
base/broadcast.jl:1169. array.jl:11-13 declares msg::AbstractString; its typed
default constructor stores the already-AbstractString literal directly with
new. The constructors manual's typed/default pair and essentials.jl's new
lowering justify that no user conversion is executed on this typed branch.
Use the existing allocation primitive, retaining allocation errors/worlds and
the exact message/reference. This helper covers precisely this fixed call. -/
-- Source: base/array.jl:11-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct DimensionMismatch <: Exception
--     msg::AbstractString
-- end
-- /Source
def constructDimensionMismatch {W L : Type} (core : CoreOps W L)
    (bindings : Bindings L) : CoreM W L (Value L) :=
  core.new bindings.dimensionMismatch
    [JuliaLean.base.boot.strV core "tuple only supports one dimension"]

/-- Full tuple-style copy body from base/broadcast.jl:1167-1172. Runtime axes,
lengths and the Val result retain their complete Julia types and effects;
there is no List/Nat rank or length restriction. A failed comparison's Bool
context is checked before constructing/throwing the actual DimensionMismatch.
The generated callable captures the original bc before Val(N) is evaluated;
selected ntuple then receives that callable and the exact constructor result.
The closure's own body is explicit above and all failures retain their worlds. -/
-- Source: base/broadcast.jl:1167-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copy(bc::Broadcasted{Style{Tuple}})
--     dim = axes(bc)
--     length(dim) == 1 || throw(DimensionMismatch("tuple only supports one dimension"))
--     N = length(dim[1])
--     return ntuple(k -> @inbounds(_broadcast_getindex(bc, k)), Val(N))
-- end
-- /Source
def copy {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (bc : Value L) : CoreM W L (Value L) := do
  let core := ops.contexts.inContext true
  let dim ← core.call bindings.axes [bc]
  let rank ← core.call bindings.length [dim]
  let rankMatches ← core.call bindings.equal
    [rank, JuliaLean.base.boot.intV core (JInt.lit .i64 1)]
  if !(← CheckedBounds.booleanContext core rankMatches) then
    let exception ← constructDimensionMismatch core bindings
    throw exception
  else
    let axis ← core.call bindings.getindex
      [dim, JuliaLean.base.boot.intV core (JInt.lit .i64 1)]
    let count ← core.call bindings.length [axis]
    let function := closure ops.contexts bindings bc
    let countVal ← core.call bindings.val [count]
    ops.ntuple function countVal

end JuliaLean.base.broadcast.Models2Group5.TupleCopy


namespace JuliaLean.base.broadcast.Models2Group5.RangeRuntime

open JuliaLean.base.expr (Value Sym)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed Base/Broadcast function and type identities. Parameterized range
objects remain actual Julia Values; no getter, numeric result, length or
constructor outcome is pre-extracted into a RangeView. All selected targets
operate on types left unfixed by the corresponding method signature.
Source reference: base/broadcast.jl:1178-1242. -/
-- Source: base/broadcast.jl:1178-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange) = range(-first(r), step=negate(step(r)), length=length(r))
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange) = range(-first(r), -last(r), step=negate(step(r)))
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::StepRangeLen) = StepRangeLen(-r.ref, negate(r.step), length(r), r.offset)
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::LinRange) = LinRange(-r.start, -r.stop, length(r))
-- 
-- # For #18336 we need to prevent promotion of the step type:
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractRange, x::Number) = range(first(r) + x, step=step(r), length=length(r))
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::AbstractRange) = range(x + first(r), step=step(r), length=length(r))
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::OrdinalRange, x::Integer) = range(first(r) + x, last(r) + x, step=step(r))
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Integer, r::OrdinalRange) = range(x + first(r), x + last(r), step=step(r))
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  first : Value L
  last : Value L
  step : Value L
  length : Value L
  add : Value L
  subtract : Value L
  multiply : Value L
  divide : Value L
  leftDivide : Value L
  negate : Value L
  big : Value L
  colon : Value L
  range : Value L
  stepRangeLen : Value L
  linRange : Value L
  rangeStartStepLength : Value L

/-- Existing runtime operations plus the actual selected Base.range keyword
callee, carrying its positional arguments and explicit ordered keyword names.
This is a parameterized dispatch target on unfixed argument/keyword types,
not a new Core primitive, a constructor answer, or a replacement for any
range-broadcast method's own expression. All argument evaluation remains
explicit below. It includes the selected keyword call's errors, mutation and
divergence, without assuming conventional numeric results. Source-level
keyword dispatch is described by devdocs/functions.md:124-184; this boundary
does not invent compiler-generated function names or a NamedTuple lowering.
The argument/key lists below have at most two fixed slots, not unbounded
Julia containers. Source: base/broadcast.jl:1178,1184-1187,1190-1191,1200-1205,
1230,1235. -/
-- Source: base/broadcast.jl:1178-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange) = range(-first(r), step=negate(step(r)), length=length(r))
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  rangeKeyword : List (Value L) → List (Sym × Value L) → CoreM W L (Value L)

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1178-1178. -/
-- Source: base/broadcast.jl:1178-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange) = range(-first(r), step=negate(step(r)), length=length(r))
-- /Source
def method1178 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.negate [v2]
  let v4 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v3), ("length", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1180-1180. -/
-- Source: base/broadcast.jl:1180-1180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::StepRangeLen) = StepRangeLen(-r.ref, negate(r.step), length(r), r.offset)
-- /Source
def method1180 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call bindings.subtract [v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v3 ← ops.call bindings.negate [v2]
  let v4 ← ops.call bindings.length [range]
  let v5 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call bindings.stepRangeLen [v1, v3, v4, v5]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1181-1181. -/
-- Source: base/broadcast.jl:1181-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::LinRange) = LinRange(-r.start, -r.stop, length(r))
-- /Source
def method1181 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.subtract [v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.subtract [v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1184-1184. -/
-- Source: base/broadcast.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractRange, x::Number) = range(first(r) + x, step=step(r), length=length(r))
-- /Source
def method1184 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [v0, scalar]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v2), ("length", v3)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1185-1185. -/
-- Source: base/broadcast.jl:1185-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::AbstractRange) = range(x + first(r), step=step(r), length=length(r))
-- /Source
def method1185 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [scalar, v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v2), ("length", v3)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1186-1186. -/
-- Source: base/broadcast.jl:1186-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::OrdinalRange, x::Integer) = range(first(r) + x, last(r) + x, step=step(r))
-- /Source
def method1186 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [v0, scalar]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.add [v2, scalar]
  let v4 ← ops.call bindings.step [range]
  ops.rangeKeyword [v1, v3] [("step", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1187-1187. -/
-- Source: base/broadcast.jl:1187-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Integer, r::OrdinalRange) = range(x + first(r), x + last(r), step=step(r))
-- /Source
def method1187 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [scalar, v0]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.add [scalar, v2]
  let v4 ← ops.call bindings.step [range]
  ops.rangeKeyword [v1, v3] [("step", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1189-1189. -/
-- Source: base/broadcast.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Integer, r::AbstractUnitRange) = range(x + first(r), x + last(r))
-- /Source
def method1189 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [scalar, v0]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.add [scalar, v2]
  ops.call bindings.range [v1, v3]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1190-1190. -/
-- Source: base/broadcast.jl:1190-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::AbstractUnitRange, x::Real) = range(first(r) + x, length=length(r))
-- /Source
def method1190 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [v0, scalar]
  let v2 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("length", v2)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1191-1191. -/
-- Source: base/broadcast.jl:1191-1191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Real, r::AbstractUnitRange) = range(x + first(r), length=length(r))
-- /Source
def method1191 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.add [scalar, v0]
  let v2 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("length", v2)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The static T is supplied as
elementType metadata. T(r.ref) and arithmetic determine the constructor type
before the second, distinct r.ref read; no getter result is cached across
those effects and no extra T-return assertion is inserted. 
Source reference: base/broadcast.jl:1192-1193. -/
-- Source: base/broadcast.jl:1192-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r::StepRangeLen{T}, x::Number) where T =
--     StepRangeLen{typeof(T(r.ref)+x)}(r.ref + x, r.step, length(r), r.offset)
-- /Source
def method1192 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (elementType : Value L) (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call elementType [v0]
  let v2 ← ops.call bindings.add [v1, scalar]
  let v3 ← ops.applyType bindings.stepRangeLen [.leaf (ops.typeOf v2)]
  let v4 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v5 ← ops.call bindings.add [v4, scalar]
  let v6 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v7 ← ops.call bindings.length [range]
  let v8 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call v3 [v5, v6, v7, v8]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The static T is supplied as
elementType metadata. T(r.ref) and arithmetic determine the constructor type
before the second, distinct r.ref read; no getter result is cached across
those effects and no extra T-return assertion is inserted. 
Source reference: base/broadcast.jl:1194-1195. -/
-- Source: base/broadcast.jl:1194-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::StepRangeLen{T}) where T =
--     StepRangeLen{typeof(x+T(r.ref))}(x + r.ref, r.step, length(r), r.offset)
-- /Source
def method1194 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (elementType : Value L) (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call elementType [v0]
  let v2 ← ops.call bindings.add [scalar, v1]
  let v3 ← ops.applyType bindings.stepRangeLen [.leaf (ops.typeOf v2)]
  let v4 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v5 ← ops.call bindings.add [scalar, v4]
  let v6 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v7 ← ops.call bindings.length [range]
  let v8 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call v3 [v5, v6, v7, v8]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1197-1197. -/
-- Source: base/broadcast.jl:1197-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(+), x::Number, r::LinRange) = LinRange(x + r.start, x + r.stop, length(r))
-- /Source
def method1197 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.add [scalar, v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.add [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1200-1200. -/
-- Source: base/broadcast.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange, x::Number) = range(first(r) - x, step=step(r), length=length(r))
-- /Source
def method1200 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [v0, scalar]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v2), ("length", v3)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1201-1201. -/
-- Source: base/broadcast.jl:1201-1201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::AbstractRange) = range(x - first(r), step=negate(step(r)), length=length(r))
-- /Source
def method1201 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [scalar, v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.negate [v2]
  let v4 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v3), ("length", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1202-1202. -/
-- Source: base/broadcast.jl:1202-1202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange, x::Integer) = range(first(r) - x, last(r) - x, step=step(r))
-- /Source
def method1202 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [v0, scalar]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.subtract [v2, scalar]
  let v4 ← ops.call bindings.step [range]
  ops.rangeKeyword [v1, v3] [("step", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1203-1203. -/
-- Source: base/broadcast.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Integer, r::OrdinalRange) = range(x - first(r), x - last(r), step=negate(step(r)))
-- /Source
def method1203 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [scalar, v0]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.subtract [scalar, v2]
  let v4 ← ops.call bindings.step [range]
  let v5 ← ops.call bindings.negate [v4]
  ops.rangeKeyword [v1, v3] [("step", v5)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1204-1204. -/
-- Source: base/broadcast.jl:1204-1204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractUnitRange, x::Integer) = range(first(r) - x, last(r) - x)
-- /Source
def method1204 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [v0, scalar]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.subtract [v2, scalar]
  ops.call bindings.range [v1, v3]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1205-1205. -/
-- Source: base/broadcast.jl:1205-1205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractUnitRange, x::Real) = range(first(r) - x, length=length(r))
-- /Source
def method1205 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.subtract [v0, scalar]
  let v2 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("length", v2)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The static T is supplied as
elementType metadata. T(r.ref) and arithmetic determine the constructor type
before the second, distinct r.ref read; no getter result is cached across
those effects and no extra T-return assertion is inserted. 
Source reference: base/broadcast.jl:1206-1207. -/
-- Source: base/broadcast.jl:1206-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::StepRangeLen{T}, x::Number) where T =
--     StepRangeLen{typeof(T(r.ref)-x)}(r.ref - x, r.step, length(r), r.offset)
-- /Source
def method1206 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (elementType : Value L) (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call elementType [v0]
  let v2 ← ops.call bindings.subtract [v1, scalar]
  let v3 ← ops.applyType bindings.stepRangeLen [.leaf (ops.typeOf v2)]
  let v4 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v5 ← ops.call bindings.subtract [v4, scalar]
  let v6 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v7 ← ops.call bindings.length [range]
  let v8 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call v3 [v5, v6, v7, v8]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The static T is supplied as
elementType metadata. T(r.ref) and arithmetic determine the constructor type
before the second, distinct r.ref read; no getter result is cached across
those effects and no extra T-return assertion is inserted. 
Source reference: base/broadcast.jl:1208-1209. -/
-- Source: base/broadcast.jl:1208-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::StepRangeLen{T}) where T =
--     StepRangeLen{typeof(x-T(r.ref))}(x - r.ref, negate(r.step), length(r), r.offset)
-- /Source
def method1208 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (elementType : Value L) (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call elementType [v0]
  let v2 ← ops.call bindings.subtract [scalar, v1]
  let v3 ← ops.applyType bindings.stepRangeLen [.leaf (ops.typeOf v2)]
  let v4 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v5 ← ops.call bindings.subtract [scalar, v4]
  let v6 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v7 ← ops.call bindings.negate [v6]
  let v8 ← ops.call bindings.length [range]
  let v9 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call v3 [v5, v7, v8, v9]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1211-1211. -/
-- Source: base/broadcast.jl:1211-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), x::Number, r::LinRange) = LinRange(x - r.start, x - r.stop, length(r))
-- /Source
def method1211 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.subtract [scalar, v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.subtract [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1212-1212. -/
-- Source: base/broadcast.jl:1212-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r1::AbstractRange, r2::AbstractRange) = r1 - r2
-- /Source
def method1212 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  ops.call bindings.subtract [range, scalar]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1215-1215. -/
-- Source: base/broadcast.jl:1215-1215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::Number, r::AbstractRange) = StepRangeLen(x*first(r), x*step(r), length(r))
-- /Source
def method1215 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.multiply [scalar, v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.multiply [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.stepRangeLen [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1218-1218. -/
-- Source: base/broadcast.jl:1218-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::Number, r::LinRange) = LinRange(x * r.start, x * r.stop, r.len)
-- /Source
def method1218 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.multiply [scalar, v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.multiply [scalar, v2]
  let v4 ← ops.call bindings.getproperty [range, .symbol "len"]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1219-1220. -/
-- Source: base/broadcast.jl:1219-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), x::AbstractFloat, r::OrdinalRange) =
--     Base.range_start_step_length(x*first(r), x*step(r), length(r))  # 0.2 .* (-2:2) needs TwicePrecision
-- /Source
def method1219 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.multiply [scalar, v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.multiply [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.rangeStartStepLength [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The static T is supplied as
elementType metadata. T(r.ref) and arithmetic determine the constructor type
before the second, distinct r.ref read; no getter result is cached across
those effects and no extra T-return assertion is inserted. 
Source reference: base/broadcast.jl:1223-1224. -/
-- Source: base/broadcast.jl:1223-1224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::StepRangeLen{T}, x::Number) where {T} =
--     StepRangeLen{typeof(T(r.ref)*x)}(r.ref*x, r.step*x, length(r), r.offset)
-- /Source
def method1223 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (elementType : Value L) (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call elementType [v0]
  let v2 ← ops.call bindings.multiply [v1, scalar]
  let v3 ← ops.applyType bindings.stepRangeLen [.leaf (ops.typeOf v2)]
  let v4 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v5 ← ops.call bindings.multiply [v4, scalar]
  let v6 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v7 ← ops.call bindings.multiply [v6, scalar]
  let v8 ← ops.call bindings.length [range]
  let v9 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call v3 [v5, v7, v8, v9]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1225-1225. -/
-- Source: base/broadcast.jl:1225-1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::LinRange, x::Number) = LinRange(r.start * x, r.stop * x, r.len)
-- /Source
def method1225 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.multiply [v0, scalar]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.multiply [v2, scalar]
  let v4 ← ops.call bindings.getproperty [range, .symbol "len"]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1226-1227. -/
-- Source: base/broadcast.jl:1226-1227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(*), r::OrdinalRange, x::AbstractFloat) =
--     Base.range_start_step_length(first(r)*x, step(r)*x, length(r))
-- /Source
def method1226 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.multiply [v0, scalar]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.multiply [v2, scalar]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.rangeStartStepLength [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1230-1230. -/
-- Source: base/broadcast.jl:1230-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(/), r::AbstractRange, x::Number) = range(first(r)/x, step=step(r)/x, length=length(r))
-- /Source
def method1230 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.divide [v0, scalar]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.divide [v2, scalar]
  let v4 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v3), ("length", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1233-1233. -/
-- Source: base/broadcast.jl:1233-1233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(/), r::LinRange, x::Number) = LinRange(r.start / x, r.stop / x, r.len)
-- /Source
def method1233 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.divide [v0, scalar]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.divide [v2, scalar]
  let v4 ← ops.call bindings.getproperty [range, .symbol "len"]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. The final
selected range keyword call retains its exact keyword names, values and
source ordering after all positional/keyword expressions are evaluated. 
Source reference: base/broadcast.jl:1235-1235. -/
-- Source: base/broadcast.jl:1235-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::AbstractRange) = range(x\first(r), step=x\step(r), length=length(r))
-- /Source
def method1235 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.first [range]
  let v1 ← ops.call bindings.leftDivide [scalar, v0]
  let v2 ← ops.call bindings.step [range]
  let v3 ← ops.call bindings.leftDivide [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  ops.rangeKeyword [v1] [("step", v3), ("length", v4)]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1236-1236. -/
-- Source: base/broadcast.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) = StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)
-- /Source
def method1236 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call bindings.leftDivide [scalar, v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v3 ← ops.call bindings.leftDivide [scalar, v2]
  let v4 ← ops.call bindings.length [range]
  let v5 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call bindings.stepRangeLen [v1, v3, v4, v5]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1237-1237. -/
-- Source: base/broadcast.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::LinRange) = LinRange(x \ r.start, x \ r.stop, r.len)
-- /Source
def method1237 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range scalar : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.leftDivide [scalar, v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.leftDivide [scalar, v2]
  let v4 ← ops.call bindings.getproperty [range, .symbol "len"]
  ops.call bindings.linRange [v1, v3, v4]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1239-1239. -/
-- Source: base/broadcast.jl:1239-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::UnitRange) = big(r.start):big(last(r))
-- /Source
def method1239 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.big [v0]
  let v2 ← ops.call bindings.last [range]
  let v3 ← ops.call bindings.big [v2]
  ops.call bindings.colon [v1, v3]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1240-1240. -/
-- Source: base/broadcast.jl:1240-1240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::StepRange) = big(r.start):big(r.step):big(last(r))
-- /Source
def method1240 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.big [v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v3 ← ops.call bindings.big [v2]
  let v4 ← ops.call bindings.last [range]
  let v5 ← ops.call bindings.big [v4]
  ops.call bindings.colon [v1, v3, v5]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1241-1241. -/
-- Source: base/broadcast.jl:1241-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::StepRangeLen) = StepRangeLen(big(r.ref), big(r.step), length(r), r.offset)
-- /Source
def method1241 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "ref"]
  let v1 ← ops.call bindings.big [v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "step"]
  let v3 ← ops.call bindings.big [v2]
  let v4 ← ops.call bindings.length [range]
  let v5 ← ops.call bindings.getproperty [range, .symbol "offset"]
  ops.call bindings.stepRangeLen [v1, v3, v4, v5]

/-- Full runtime-value body for the selected source overload. Getters,
arithmetic and constructors run in their written source order with exact
operand orientation; no numeric type, axis convention, successful conversion
or immutable allocation restriction is imposed. Each selected call retains
its actual world, exception identity and divergence. Getter results may be
arbitrary and may depend on preceding effects. 
Source reference: base/broadcast.jl:1242-1242. -/
-- Source: base/broadcast.jl:1242-1242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::DefaultArrayStyle{1}, ::typeof(big), r::LinRange) = LinRange(big(r.start), big(r.stop), length(r))
-- /Source
def method1242 {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (range : Value L) : CoreM W L (Value L) := do
  let v0 ← ops.call bindings.getproperty [range, .symbol "start"]
  let v1 ← ops.call bindings.big [v0]
  let v2 ← ops.call bindings.getproperty [range, .symbol "stop"]
  let v3 ← ops.call bindings.big [v2]
  let v4 ← ops.call bindings.length [range]
  ops.call bindings.linRange [v1, v3, v4]

end JuliaLean.base.broadcast.Models2Group5.RangeRuntime


namespace JuliaLean.base.broadcast.Models2Group5.CartesianRanges

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Distinct nominal identities for the three capture-free source function
singletons: the plus lambda, minus lambda and local diffrange. Runtime
interfaces are meta-level interpretation data, not captured Julia state.
Source: base/broadcast.jl:1245-1254. -/
-- Source: base/broadcast.jl:1245-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
inductive ClosureName where
  | plus
  | minus
  | difference
  deriving DecidableEq

/-- A complete first-class callable passed to selected map dispatch. Its
nominal runtime value is available for type/identity observations and its
invoke operation includes both the actual two-argument body and wrong-arity
MethodError. Native-bounded varargs preserve all mutable references.
Source: base/broadcast.jl:1245-1254. -/
-- Source: base/broadcast.jl:1245-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
structure Closure (W L : Type) where
  name : ClosureName
  value : Value L
  invoke : Constructors.ArgumentTuple L → CoreM W L (Value L)

/-- Actual source bindings and nominal embeddings of the three generated
function singleton identities. No supplied function body or result is hidden
in these bindings. The range keyword target is inherited from RangeRuntime.
Source: base/broadcast.jl:1245-1254. -/
-- Source: base/broadcast.jl:1245-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
structure Bindings (L : Type) extends RangeRuntime.Bindings L where
  broadcasted : Value L
  materialize : Value L
  cartesianIndices : Value L
  reverse : Value L
  map : Value L
  closureValue : ClosureName → Value L

/-- The actual selected map callee on unfixed returned tuple/axis types. It
receives the complete callable, including identity and executable body, so
custom map implementations can inspect or invoke it. All property, conversion,
constructor and map outcomes stay arbitrary in the installed CoreM world.
Source: base/broadcast.jl:1245-1254. -/
-- Source: base/broadcast.jl:1245-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
structure Ops (W L : Type) extends RangeRuntime.Ops W L where
  map : Closure W L → Value L → Value L → CoreM W L (Value L)

/-- Actual plus lambda: dot syntax materializes the broadcasted result.
Both arguments are unrestricted, with no range/offset numerical assumption
or forced scalar arithmetic. Source: base/broadcast.jl:1246. -/
-- Source: base/broadcast.jl:1245-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- /Source
def plusBody {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (range offset : Value L) : CoreM W L (Value L) := do
  let bc ← ops.call bindings.broadcasted [bindings.add, range, offset]
  ops.call bindings.materialize [bc]

/-- Actual minus lambda, preserving range-minus-offset operand order and
both selected broadcasting stages. Source: base/broadcast.jl:1250. -/
-- Source: base/broadcast.jl:1249-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- /Source
def minusBody {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (range offset : Value L) : CoreM W L (Value L) := do
  let bc ← ops.call bindings.broadcasted [bindings.subtract, range, offset]
  ops.call bindings.materialize [bc]

/-- Full queued local diffrange method. Read last before offset subtraction,
then length and step in their source keyword order. The range keyword callee
gets one positional argument and exactly length followed by step; no range
metadata is pre-extracted and no negated step is substituted. All argument
and result types remain unfixed. Source: base/broadcast.jl:1252. -/
-- Source: base/broadcast.jl:1252-1252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
-- /Source
def differenceBody {W L : Type} (ops : RangeRuntime.Ops W L) (bindings : Bindings L)
    (offset range : Value L) : CoreM W L (Value L) := do
  let last ← ops.call bindings.last [range]
  let first ← ops.call bindings.subtract [offset, last]
  let length ← ops.call bindings.length [range]
  let step ← ops.call bindings.step [range]
  ops.rangeKeyword [first] [("length", length), ("step", step)]

/-- The actual generated callable, with no user-supplied implementation.
Exactly two arguments execute its source body. Other native-sized argument
lists fail dispatch with the actual function, entire argument tuple and
current world age, using the installed MethodError construction protocol.
No arbitrary-arity call is replaced by a silent value or coverage gap.
Source: base/broadcast.jl:1245-1254; installed boot.noMethod. -/
-- Source: base/broadcast.jl:1245-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
def closure {W L : Type} (ops : RangeRuntime.Ops W L) (bindings : Bindings L)
    (name : ClosureName) : Closure W L where
  name := name
  value := bindings.closureValue name
  invoke := fun args =>
    match args.values with
    | [left, right] =>
        match name with
        | .plus => plusBody ops.toCoreOps bindings left right
        | .minus => minusBody ops.toCoreOps bindings left right
        | .difference => differenceBody ops bindings left right
    | _ => do
        let age ← ops.worldAge
        JuliaLean.base.boot.throwObj ops.toCoreOps (.methodError
          (bindings.closureValue name) (JuliaLean.base.boot.tupleV ops.toCoreOps args.values)
          (JuliaLean.base.boot.intV ops.toCoreOps age))

/-- Full source1245: read actual I.indices, call Tuple on the original
CartesianIndex, then map the real plus callable before constructing
CartesianIndices from the exact map result. Unfixed rank/axis types allow
selected property, Tuple and map methods with arbitrary runtime outcomes.
Source: base/broadcast.jl:1245-1246. -/
-- Source: base/broadcast.jl:1245-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .+ offset, I.indices, Tuple(j)))
-- /Source
def plus {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (indices offset : Value L) : CoreM W L (Value L) := do
  let axes ← ops.call bindings.getproperty [indices, .symbol "indices"]
  let coordinates ← ops.call (JuliaLean.base.boot.coreV ops.toOps.toCoreOps "Tuple") [offset]
  let shifted ← ops.map (closure ops.toOps bindings .plus) axes coordinates
  ops.call bindings.cartesianIndices [shifted]

/-- Reverse operand adapter preserves I .+ j, including materialization of
the actual broadcasted result. It does not substitute scalar + or return an
unmaterialized wrapper. Its inner dispatch has CartesianIndices first, a
different argument category from this selected method. Source1247-1248. 
Source reference: base/broadcast.jl:1247-1248.
-/
-- Source: base/broadcast.jl:1247-1248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(+), j::CartesianIndex{N}, I::CartesianIndices{N}) where N =
--     I .+ j
-- /Source
def plusReversed {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (offset indices : Value L) : CoreM W L (Value L) := do
  let bc ← ops.call bindings.broadcasted [bindings.add, indices, offset]
  ops.call bindings.materialize [bc]

/-- Full source1249, with the actual minus callable and original coordinate
provenance. The selected map can observe or invoke the complete callable;
its returned type need not be a tuple or array. Source1249-1250. 
Source reference: base/broadcast.jl:1249-1250.
-/
-- Source: base/broadcast.jl:1249-1250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcasted(::typeof(-), I::CartesianIndices{N}, j::CartesianIndex{N}) where N =
--     CartesianIndices(map((rng, offset)->rng .- offset, I.indices, Tuple(j)))
-- /Source
def minus {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (indices offset : Value L) : CoreM W L (Value L) := do
  let axes ← ops.call bindings.getproperty [indices, .symbol "indices"]
  let coordinates ← ops.call (JuliaLean.base.boot.coreV ops.toOps.toCoreOps "Tuple") [offset]
  let shifted ← ops.map (closure ops.toOps bindings .minus) axes coordinates
  ops.call bindings.cartesianIndices [shifted]

/-- Full source1251: Tuple(j) precedes I.indices, map receives diffrange and
those exact objects in offset/range order, then CartesianIndices precedes
Iterators.reverse. The capture-free local function includes its executable
body and full invocation arity behavior. Source: base/broadcast.jl:1251-1254. -/
-- Source: base/broadcast.jl:1251-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function broadcasted(::typeof(-), j::CartesianIndex{N}, I::CartesianIndices{N}) where N
--     diffrange(offset, rng) = range(offset-last(rng), length=length(rng), step=step(rng))
--     Iterators.reverse(CartesianIndices(map(diffrange, Tuple(j), I.indices)))
-- end
-- /Source
def minusReversed {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (offset indices : Value L) : CoreM W L (Value L) := do
  let coordinates ← ops.call (JuliaLean.base.boot.coreV ops.toOps.toCoreOps "Tuple") [offset]
  let axes ← ops.call bindings.getproperty [indices, .symbol "indices"]
  let shifted ← ops.map (closure ops.toOps bindings .difference) coordinates axes
  let cartesian ← ops.call bindings.cartesianIndices [shifted]
  ops.call bindings.reverse [cartesian]

end JuliaLean.base.broadcast.Models2Group5.CartesianRanges


namespace JuliaLean.base.broadcast.Models2Group5.MaskedForward

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Fixed source identities for the masked-array forwarding methods.
Unfixed rank/type parameters and returned property types retain selected
runtime dispatch. No field supplies a constructor, view or fill result. 
Source reference: base/broadcast.jl:1263-1271.
-/
-- Source: base/broadcast.jl:1263-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function BitMaskedBitArray(parent::BitArray{N}, mask::BitArray{M}) where {N,M}
--     @boundscheck checkbounds(parent, mask)
--     BitMaskedBitArray{N,M}(parent, mask)
-- end
-- Base.@propagate_inbounds dotview(B::BitArray, i::BitArray) = BitMaskedBitArray(B, i)
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- # Override materialize! to prevent the BitMaskedBitArray from escaping to an overridable method
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any,<:Any,typeof(identity),Tuple{Bool}}) = fill!(B, bc.args[1])
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any}) = materialize!(@inbounds(view(B.parent, B.mask)), bc)
-- /Source
structure Bindings (L : Type) where
  bitMasked : Value L
  checkbounds : Value L
  getproperty : Value L
  getindex : Value L
  fill : Value L
  view : Value L
  materialize : Value L
  showFn : Value L

/-- Selected checked outer constructor. N and M are actual dispatch type
parameters, represented as full Julia values. Only the @boundscheck call is
elided in the unchecked context; target type application and the actual
constructor call remain at their source positions. Constructor dispatch can
specialize on the unfixed N/M and parent/mask types, so it remains an open
call rather than pretending the untyped inner new is a plain pair record. 
Source reference: base/broadcast.jl:1263-1266.
-/
-- Source: base/broadcast.jl:1263-1266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function BitMaskedBitArray(parent::BitArray{N}, mask::BitArray{M}) where {N,M}
--     @boundscheck checkbounds(parent, mask)
--     BitMaskedBitArray{N,M}(parent, mask)
-- end
-- /Source
def construct {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (n m parent mask : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let ops := contexts.inContext boundscheck
  if boundscheck then
    let _ ← ops.call bindings.checkbounds [parent, mask]
    pure ()
  let target ← ops.applyType bindings.bitMasked [n, m]
  ops.call target [parent, mask]

/-- The specialized dotview preserves the exact BitArray references and the
incoming propagated compiler context while invoking their selected masked
constructor. Its ranks remain unfixed; no detached copy or pair is returned
in place of the actual constructor outcome. 
Source reference: base/broadcast.jl:1267-1267.
-/
-- Source: base/broadcast.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds dotview(B::BitArray, i::BitArray) = BitMaskedBitArray(B, i)
-- /Source
def dotview {W L : Type} (contexts : Iteration.ContextOps W L)
    (bindings : Bindings L) (parent mask : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) :=
  (contexts.inContext boundscheck).call bindings.bitMasked [parent, mask]

/-- The source1268 callable's fixed code identity and captured IO reference.
Its executable body is callShowClosure below; a selected foreach receives this
actual represented callable, not a precomputed output or capture callback. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
inductive ShowCode where
  | source1268

/-- Nominal source callable and its complete capture environment. The pure
closureValue embedding in ShowOps exposes this exact code/capture identity to
custom foreach and to wrong-arity MethodError construction. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
structure ShowClosure (L : Type) where
  code : ShowCode
  io : Value L

/-- Actual body of arg -> show(io,arg). The captured IO subtype and argument
type remain unfixed, hence show uses the existing runtime dispatch boundary.
All stream mutation, exceptions and divergence stay in the same CoreM world. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
def callShowClosure {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (closure : ShowClosure L) (argument : Value L) : CoreM W L (Value L) :=
  ops.call bindings.showFn [closure.io, argument]

/-- Complete positional application of the generated unary callable. Exactly
one argument executes its actual body; every other native-bounded arity uses
the installed missing-method world-age/throw protocol with the exact callable
identity and original argument tuple. No arbitrary-arity call is silently
accepted by the unary lambda. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
def invokeShowClosure {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (closureValue : ShowClosure L → Value L) (closure : ShowClosure L)
    (arguments : Constructors.ArgumentTuple L) : CoreM W L (Value L) :=
  match arguments.values with
  | [argument] => callShowClosure ops bindings closure argument
  | _ => do
      let age ← ops.worldAge
      JuliaLean.base.boot.throwObj ops (.methodError (closureValue closure)
        (JuliaLean.base.boot.tupleV ops arguments.values) (JuliaLean.base.boot.intV ops age))

/-- Existing runtime primitives plus the selected foreach target on the
represented source closure and actual two-element tuple. The callable's
captured IO type and tuple element types are unfixed. This target may invoke
callShowClosure, mutate, throw, return arbitrary values or diverge; no law is
assumed. The known lambda body itself is not supplied as an interface field. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
structure ShowOps (W L : Type) extends CoreOps W L where
  closureValue : ShowClosure L → Value L
  foreach : ShowClosure L → Value L → CoreM W L (Value L)

/-- Source1268 evaluates typeof(B), B.parent and B.mask before foreach starts.
The actual pair is nested in the outer tuple with typeof(B), and the closure
retains the original IO identity. Property dispatch may change the world or
return arbitrary objects; no fixed render string or eager show is substituted. 
Source reference: base/broadcast.jl:1268-1268.
-/
-- Source: base/broadcast.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, B::BitMaskedBitArray) = foreach(arg->show(io, arg), (typeof(B), (B.parent, B.mask)))
-- /Source
def showMasked {W L : Type} (ops : ShowOps W L) (bindings : Bindings L)
    (io value : Value L) : CoreM W L (Value L) := do
  let type : Value L := .leaf (ops.typeOf value)
  let parent ← ops.call bindings.getproperty [value, .symbol "parent"]
  let mask ← ops.call bindings.getproperty [value, .symbol "mask"]
  ops.foreach ⟨.source1268, io⟩ (JuliaLean.base.boot.tupleV ops.toCoreOps
    [type, JuliaLean.base.boot.tupleV ops.toCoreOps [parent, mask]])

/-- The identity/Bool materializer reads the actual args property, indexes its
first slot, and invokes fill! with the original destination and exact result.
Unfixed wrapper parameters/property returns retain open dispatch, including
exceptions or noncanonical returned values. No caller function is evaluated
and no lazy wrapper field is overwritten. 
Source reference: base/broadcast.jl:1270-1270.
-/
-- Source: base/broadcast.jl:1270-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any,<:Any,typeof(identity),Tuple{Bool}}) = fill!(B, bc.args[1])
-- /Source
def materializeScalar {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (destination broadcast : Value L) : CoreM W L (Value L) := do
  let arguments ← ops.call bindings.getproperty [broadcast, .symbol "args"]
  let bit ← ops.call bindings.getindex
    [arguments, JuliaLean.base.boot.intV ops (JInt.lit .i64 1)]
  ops.call bindings.fill [destination, bit]

/-- Metadata for the source1271 recursive edge. same selects exactly the
current masked materializer; other selects a genuinely different method. 
Source reference: base/broadcast.jl:1271-1271.
-/
-- Source: base/broadcast.jl:1271-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any}) = materialize!(@inbounds(view(B.parent, B.mask)), bc)
-- /Source
inductive MaterializeMethod where
  | same
  | other

/-- Contextual runtime operations and pure current-world materialize!
selection after view returns. This preserves self-returning custom views and
does not require views to be canonical SubArrays or nonaliasing objects. 
Source reference: base/broadcast.jl:1271-1271.
-/
-- Source: base/broadcast.jl:1271-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any}) = materialize!(@inbounds(view(B.parent, B.mask)), bc)
-- /Source
structure MaterializeOps (W L : Type) where
  contexts : Iteration.ContextOps W L
  selectedMaterialize : Value L → Value L → W → MaterializeMethod

/-- Source1271's entire view expression, including both property reads, is
inside @inbounds. The subsequent materialize! uses the surrounding context.
The same selected method executes recursively rather than calling a supplied
replacement body; cycles remain actual CoreM divergence. Only a genuinely
different selected target uses the open materialize! call. 
Source reference: base/broadcast.jl:1271-1271.
-/
-- Source: base/broadcast.jl:1271-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline materialize!(B::BitMaskedBitArray, bc::Broadcasted{<:Any}) = materialize!(@inbounds(view(B.parent, B.mask)), bc)
-- /Source
def materializeView {W L : Type} (ops : MaterializeOps W L) (bindings : Bindings L)
    (destination broadcast : Value L) (boundscheck : Bool := true) :
    CoreM W L (Value L) := do
  let unchecked := ops.contexts.inContext false
  let parent ← unchecked.call bindings.getproperty [destination, .symbol "parent"]
  let mask ← unchecked.call bindings.getproperty [destination, .symbol "mask"]
  let viewed ← unchecked.call bindings.view [parent, mask]
  let selected ← (show CoreM W L MaterializeMethod from fun world =>
    some (.ok (ops.selectedMaterialize viewed broadcast world, world)))
  match selected with
  | .same => materializeView ops bindings viewed broadcast boundscheck
  | .other =>
      (ops.contexts.inContext boundscheck).call bindings.materialize [viewed, broadcast]
partial_fixpoint

end JuliaLean.base.broadcast.Models2Group5.MaskedForward


namespace JuliaLean.base.broadcast.Models2Group5.MaskedFill

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- The two source binary word operations. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
inductive Binary where
  | union
  | intersection

/-- Actual selected UInt64 builtin arguments or a genuinely different
operator method. Native words keep all 64 bits; no mathematical-Int substitute
or correctness law is supplied for a custom operation. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
inductive BinaryMethod where
  | native (left right : JInt .u64)
  | custom

/-- Actual UInt64 complement metadata or a selected different unary method. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
inductive UnaryMethod where
  | native (word : JInt .u64)
  | custom

/-- Existing runtime calls and pure current-world operator selection. Chunk
objects come from actual property results whose types remain unfixed, so their
length, indexing, setters and iteration use selected runtime calls. This
retains arbitrary shared/overlapping address aliases in W rather than imposing
the historical single-memory-handle heap restriction. Native UInt64 operators
are implemented below; they are never opaque generic callbacks. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
structure Ops (W L : Type) extends CoreOps W L where
  selectedBinary : Binary → Value L → Value L → W → BinaryMethod
  selectedUnary : Value L → W → UnaryMethod

/-- The initial property expressions have the surrounding checked context;
the complete if/loop region is explicitly @inbounds. These are compiler
contexts, not additional Julia arguments or memory-safety premises. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
structure ContextOps (W L : Type) where
  inContext : Bool → Ops W L

/-- Fixed source function identities; no loop, mask or mutation result is
stored in this record. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
structure Bindings (L : Type) where
  getproperty : Value L
  length : Value L
  colon : Value L
  iterate : Value L
  getindex : Value L
  setindex : Value L
  union : Value L
  intersection : Value L
  complement : Value L

/-- Concrete UInt64 operators reuse installed int.bor/int.band; only actual
selected different operand methods use the open call. Selection happens in
the world after both source operand reads and any earlier unary operation. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
def binary {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (operation : Binary) (left right : Value L) : CoreM W L (Value L) := do
  let selected ← (show CoreM W L BinaryMethod from fun world =>
    some (.ok (ops.selectedBinary operation left right world, world)))
  match selected with
  | .native a b =>
      let result := match operation with
        | .union => JuliaLean.base.int.bor a b
        | .intersection => JuliaLean.base.int.band a b
      pure (JuliaLean.base.boot.intV ops.toCoreOps result)
  | .custom =>
      let function := match operation with
        | .union => bindings.union
        | .intersection => bindings.intersection
      ops.call function [left, right]

/-- Concrete UInt64 complement reuses installed int.bnot. A different selected
operator keeps its exact returned value and effects for the following & call. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
def complement {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (word : Value L) : CoreM W L (Value L) := do
  let selected ← (show CoreM W L UnaryMethod from fun world =>
    some (.ok (ops.selectedUnary word world, world)))
  match selected with
  | .native value => pure (JuliaLean.base.boot.intV ops.toCoreOps (JuliaLean.base.int.bnot value))
  | .custom => ops.call bindings.complement [word]

/-- Explicit for-loop execution on the actual iterator protocol. Each
non-nothing iterate result supplies its value and state through the builtin
two-field tuple projection used by for lowering (manual/interfaces.md:29-54).
Invalid/undefined fields retain their actual getfield errors. The parent read
precedes the mask read; b=true unions their words, while b=false complements
the actual mask before intersecting. The setter occurs before the next
iterate call, so later aliased reads observe all earlier writes. Iterator
states and arrays remain original reference-valued runtime leaves. The least
partial fixed point admits arbitrary iteration/cycles with no fuel or native
length approximation. Every operation runs in the explicit false context. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
def loop {W L : Type} (ops : Ops W L) (bindings : Bindings L)
    (parent mask iterator next : Value L) (bit : Bool) : CoreM W L Unit := do
  let core := ops.toCoreOps
  if core.same next (JuliaLean.base.boot.nothingV core) then
    pure ()
  else do
    let index ← core.getfield next (JuliaLean.base.boot.intV core (JInt.lit .i64 1))
    let state ← core.getfield next (JuliaLean.base.boot.intV core (JInt.lit .i64 2))
    let old ← core.call bindings.getindex [parent, index]
    let selectedMask ← core.call bindings.getindex [mask, index]
    let word ← if bit then binary ops bindings .union old selectedMask else do
      let inverted ← complement ops bindings selectedMask
      binary ops bindings .intersection old inverted
    let _ ← core.call bindings.setindex [parent, word, index]
    let following ← core.call bindings.iterate [iterator, state]
    loop ops bindings parent mask iterator following bit
partial_fixpoint

/-- Full selected source1272 body. Both chained property reads occur before
the inbounds region, in parent/chunks then mask/chunks order. The original
parent chunks determine length and the actual 1:length(...) iterator. The
complete explicit loop preserves mutation worlds, failures and arbitrary
aliases, and successful completion returns the exact original B reference.
No copy, detached snapshot, zero-based indexing or native-only range is added. 
Source reference: base/broadcast.jl:1272-1285.
-/
-- Source: base/broadcast.jl:1272-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.fill!(B::BitMaskedBitArray, b::Bool)
--     Bc = B.parent.chunks
--     Ic = B.mask.chunks
--     @inbounds if b
--         for i = 1:length(Bc)
--             Bc[i] |= Ic[i]
--         end
--     else
--         for i = 1:length(Bc)
--             Bc[i] &= ~Ic[i]
--         end
--     end
--     return B
-- end
-- /Source
def fill {W L : Type} (contexts : ContextOps W L) (bindings : Bindings L)
    (value : Value L) (bit : Bool) : CoreM W L (Value L) := do
  let checked := (contexts.inContext true).toCoreOps
  let parent ← checked.call bindings.getproperty [value, .symbol "parent"]
  let parentChunks ← checked.call bindings.getproperty [parent, .symbol "chunks"]
  let mask ← checked.call bindings.getproperty [value, .symbol "mask"]
  let maskChunks ← checked.call bindings.getproperty [mask, .symbol "chunks"]
  let ops := contexts.inContext false
  let core := ops.toCoreOps
  let count ← core.call bindings.length [parentChunks]
  let iterator ← core.call bindings.colon [JuliaLean.base.boot.intV core (JInt.lit .i64 1), count]
  let next ← core.call bindings.iterate [iterator]
  loop ops bindings parentChunks maskChunks iterator next bit
  pure value

end JuliaLean.base.broadcast.Models2Group5.MaskedFill


namespace JuliaLean.base.broadcast.Models2Group5.SyntaxBoundary

open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreM)

/-- Reuse the installed generic forwarding body at base/broadcast.jl:1297
with its result instantiated to the actual effect/exception/divergence monad.
The native-sized heterogeneous vararg tuple preserves every Julia argument,
including zero arguments. Its source splat is the direct expansion of this
already assembled native tuple, not an arbitrary iterable. The target
maybeview dispatches on types the source leaves unfixed; its actual method
therefore stays in CoreOps.call with the caller's propagated bounds metadata.
No maybeview correctness or purity law is assumed. -/
-- Source: base/broadcast.jl:1297-1297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds dotview(args...) = Base.maybeview(args...)
-- /Source
def dotview {W L : Type} (contexts : Iteration.ContextOps W L)
    (maybeView : Value L) (arguments : Constructors.ArgumentTuple L)
    (boundscheck : Bool := true) : CoreM W L (Value L) :=
  Syntax.m1297
    (fun values => (contexts.inContext boundscheck).call maybeView values)
    arguments.values

end JuliaLean.base.broadcast.Models2Group5.SyntaxBoundary


namespace JuliaLean.base.broadcast.Models2Group5.KeywordBroadcast

open JuliaLean
open JuliaLean.base.expr (Value)
open JuliaLean.base.boot (CoreOps CoreM)

/-- Actual source function/type identities and compiled character literals.
The parentheses are the source Char values, not replacement render strings.
All arbitrary callable, keyword, IO and property values remain runtime values.
Source reference: base/broadcast.jl:1390-1404,1452-1460. -/
-- Source: base/broadcast.jl:1390-1392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __dot__(x)
--     esc(__dot__(x))
-- end
-- /Source
-- Source: base/broadcast.jl:1394-1404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- @inline function broadcasted(f::F, args...) where {F}
--     args′ = map(broadcastable, args)
--     broadcasted(combine_styles(args′...), f, args′...)
-- end
-- /Source
-- Source: base/broadcast.jl:1452-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BroadcastFunction)(x...; kwargs...) = op.f.(x...; kwargs...)
-- 
-- function Base.show(io::IO, op::BroadcastFunction)
--     print(io, BroadcastFunction, '(')
--     show(io, op.f)
--     print(io, ')')
--     nothing
-- end
-- Base.show(io::IO, ::MIME"text/plain", op::BroadcastFunction) = show(io, op)
-- /Source
structure Bindings (L : Type) where
  dotTransform : Value L
  esc : Value L
  isempty : Value L
  broadcasted : Value L
  broadcastedKeyword : Value L
  broadcastable : Value L
  map : Value L
  combineStyles : Value L
  defaultArrayStyle : Value L
  iterate : Value L
  getproperty : Value L
  materialize : Value L
  print : Value L
  showFn : Value L
  broadcastFunctionType : Value L
  leftParen : Value L
  rightParen : Value L

/-- The macro calls the separately dispatched transform on its original,
unfixed input, then passes the exact result to esc. Both remain actual source
calls on types the macro does not fix; no finite AST conversion, render tree,
or supplied replacement for the macro body is introduced.
Source reference: base/broadcast.jl:1390-1392. -/
-- Source: base/broadcast.jl:1390-1392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __dot__(x)
--     esc(__dot__(x))
-- end
-- /Source
def dotMacro {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (value : Value L) : CoreM W L (Value L) := do
  let transformed ← ops.call bindings.dotTransform [value]
  ops.call bindings.esc [transformed]

/-- Nominal code identity of the source1394 vararg keyword-forwarding lambda.
Source reference: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
inductive KeywordCode where
  | source1394

/-- Complete generated-callable identity and capture environment. The actual
function and collected Pairs/NamedTuple keyword object keep their identity,
types, names, order and values; they are not collapsed into strings or flags.
Source reference: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
structure KeywordClosure (L : Type) where
  code : KeywordCode
  function : Value L
  kwargs : Value L

/-- A complete represented callable supplied to a higher-order selected
broadcasted method: nominal captures, actual runtime identity, and executable
application at every native-bounded positional arity. Only keywordCallable
below constructs this record for the public entry, binding invoke to the
known source lambda body rather than accepting it as an input.
Source reference: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
structure KeywordCallable (W L : Type) where
  captures : KeywordClosure L
  identity : Value L
  invoke : Constructors.ArgumentTuple L → CoreM W L (Value L)

/-- Existing primitives plus the actual selected keyword-call boundary on an
unfixed function and keyword/argument types. The positional list is a compiler
call argument sequence, not a Julia array or a fabricated Tuple allocation;
below it comes only from a native-bounded source vararg tuple and a fixed
source prefix. This boundary retains ordinary implicit keyword dispatch,
argument/keyword expansion errors, exceptions, mutation and divergence, with
no law about a canonical keyword merger. The pure closureValue embedding
exposes exact nominal code/capture identity. broadcastClosure is the actual
selected broadcasted target on the represented callable and unfixed native
argument tuple; it receives the complete code/captures/identity/application
record constructed below. No parameter supplies the known lambda body.
Source reference: base/broadcast.jl:1394-1400,1452;
doc/src/devdocs/functions.md:124-184 (keyword calls). -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
-- Source: base/broadcast.jl:1452-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BroadcastFunction)(x...; kwargs...) = op.f.(x...; kwargs...)
-- /Source
structure KeywordOps (W L : Type) extends CoreOps W L where
  closureValue : KeywordClosure L → Value L
  keywordCall : Value L → List (Value L) → Value L → CoreM W L (Value L)
  broadcastClosure : Value L → KeywordCallable W L → CombineAxes.Tail L → CoreM W L (Value L)

/-- Complete all-arity application of (args...)->f(args...;kwargs...). Every
constructible positional arity, including zero, invokes the actual captured
function with its unchanged collected keyword object. No arity is discarded,
and no supplied callback replaces the lambda body. The sole selected callee
is precisely the source's user function, so every keyword-dispatch outcome
remains open. Julia source: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
def invokeKeywordClosure {W L : Type} (ops : KeywordOps W L)
    (closure : KeywordClosure L) (arguments : Constructors.ArgumentTuple L) :
    CoreM W L (Value L) :=
  ops.keywordCall closure.function arguments.values closure.kwargs

/-- The actual source lambda value with its executable body attached. Its
identity is the runtime embedding of these exact captures; its all-arity
application is the locally defined keyword-forwarding body. The selected
broadcasted target may inspect the callable, invoke it at arbitrary arities,
throw or diverge, with all effects kept in the same runtime world.
Source reference: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
def keywordCallable {W L : Type} (ops : KeywordOps W L) (function kwargs : Value L) :
    KeywordCallable W L :=
  let captures : KeywordClosure L := ⟨.source1394, function, kwargs⟩
  { captures := captures
    identity := ops.closureValue captures
    invoke := invokeKeywordClosure ops captures }

/-- Full keyword-syntax entry. The actual isempty result is checked as Bool;
the empty branch preserves the original f identity/type, while the nonempty
branch supplies the complete generated callable, including its runtime
identity and executable all-arity body, to the actual selected broadcasted
target. Both branches retain the original native argument tuple.
The native bound includes mandatory f in the full source argument list.
Source reference: base/broadcast.jl:1394-1400. -/
-- Source: base/broadcast.jl:1394-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted_kwsyntax(f, args...; kwargs...)
--     if isempty(kwargs) # some BroadcastStyles dispatch on `f`, so try to preserve its type
--         return broadcasted(f, args...)
--     else
--         return broadcasted((args...) -> f(args...; kwargs...), args...)
--     end
-- end
-- /Source
def keywordSyntax {W L : Type} (ops : KeywordOps W L) (bindings : Bindings L)
    (function : Value L) (arguments : CombineAxes.Tail L) (kwargs : Value L) :
    CoreM W L (Value L) := do
  let emptyReply ← ops.call bindings.isempty [kwargs]
  let empty ← CheckedBounds.booleanContext ops.toCoreOps emptyReply
  if empty then
    ops.applyIterate bindings.iterate
      [bindings.broadcasted, JuliaLean.base.boot.tupleV ops.toCoreOps [function],
        JuliaLean.base.boot.tupleV ops.toCoreOps arguments.values]
  else
    ops.broadcastClosure bindings.broadcasted (keywordCallable ops function kwargs) arguments

/-- Full source1401 body. The known empty Tuple map reuses installed
tuple.mapOneEmpty (whose actual callback is never evaluated), and nullary
combine_styles executes the already-modelled DefaultArrayStyle{0} constructor.
For a nonempty heterogeneous tuple, map's selected target remains open on
unfixed element parameters; the exact returned container then supplies both
source splats, retaining arbitrary iteration errors and non-tuple results.
The final call contains at least style and f, so ordinary dispatch selects a
more-specific method rather than reentering this one-argument vararg body.
Source reference: base/broadcast.jl:1401-1404; base/tuple.jl:358;
base/broadcast.jl:431. -/
-- Source: base/broadcast.jl:1401-1404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted(f::F, args...) where {F}
--     args′ = map(broadcastable, args)
--     broadcasted(combine_styles(args′...), f, args′...)
-- end
-- /Source
def broadcastedGeneric {W L : Type} (ops : DefaultStyle.Ops W L)
    (bindings : Bindings L) (function : Value L) (arguments : CombineAxes.Tail L) :
    CoreM W L (Value L) :=
  match arguments.values with
  | [] => do
      let actions := JuliaLean.base.tuple.mapOneEmpty
        (fun value : Value L => ops.call bindings.broadcastable [value])
      let _ ← actions.mapM id
      let style ← Constructors.combineEmpty ops bindings.defaultArrayStyle
      ops.call bindings.broadcasted [style, function]
  | _ :: _ => do
      let mapped ← ops.call bindings.map
        [bindings.broadcastable, JuliaLean.base.boot.tupleV ops.toCoreOps arguments.values]
      let style ← ops.applyIterate bindings.iterate [bindings.combineStyles, mapped]
      ops.applyIterate bindings.iterate
        [bindings.broadcasted, JuliaLean.base.boot.tupleV ops.toCoreOps [style, function], mapped]

/-- Dotted application reads the wrapper's actual f property, invokes the
actual selected broadcasted_kwsyntax keyword call with the original positional
arguments and complete keyword object, and materializes that exact result.
The BroadcastFunction parameter F and the property/argument/keyword types are
unfixed, so these are selected runtime calls with all outcomes retained.
No scalar-only shortcut or replacement broadcast result is supplied.
Source reference: base/broadcast.jl:1452; devdocs/functions.md:124-184. -/
-- Source: base/broadcast.jl:1452-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline (op::BroadcastFunction)(x...; kwargs...) = op.f.(x...; kwargs...)
-- /Source
def broadcastFunction {W L : Type} (ops : KeywordOps W L) (bindings : Bindings L)
    (operator : Value L) (arguments : Constructors.ArgumentTuple L) (kwargs : Value L) :
    CoreM W L (Value L) := do
  let function ← ops.call bindings.getproperty [operator, .symbol "f"]
  let lazyResult ← ops.keywordCall bindings.broadcastedKeyword (function :: arguments.values) kwargs
  ops.call bindings.materialize [lazyResult]

/-- Pure current-world dispatch for the inner show(io,op.f) call. A returned
BroadcastFunction may select the same method again, including nested wrappers
and self-returning custom properties; other selects an actually different
method on the unfixed IO/function type. Julia source: base/broadcast.jl:1454-1459. -/
-- Source: base/broadcast.jl:1454-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.show(io::IO, op::BroadcastFunction)
--     print(io, BroadcastFunction, '(')
--     show(io, op.f)
--     print(io, ')')
--     nothing
-- end
-- /Source
inductive ShowMethod where
  | same
  | other

/-- The known show body stays explicit when directly selected recursively.
Only genuinely different inner show targets remain open runtime calls; the
selector is metadata read after the source f property query's effects.
Source reference: base/broadcast.jl:1454-1459. -/
-- Source: base/broadcast.jl:1454-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.show(io::IO, op::BroadcastFunction)
--     print(io, BroadcastFunction, '(')
--     show(io, op.f)
--     print(io, ')')
--     nothing
-- end
-- /Source
structure ShowOps (W L : Type) extends CoreOps W L where
  selectedShow : Value L → Value L → W → ShowMethod

/-- Full two-argument display body. Print receives the actual
BroadcastFunction type and source Char literal before f is even read. Inner
display executes explicitly again when it selects this same method; after
its success the closing character is printed and the method returns nothing.
Errors preserve the exact partial stream world and prevent later output.
Unbounded recursive wrappers/cycles remain real partial-fixed-point behavior,
not a supplied renderer, bounded AST, or assumed nonrecursive callable.
Source reference: base/broadcast.jl:1454-1459. -/
-- Source: base/broadcast.jl:1454-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Base.show(io::IO, op::BroadcastFunction)
--     print(io, BroadcastFunction, '(')
--     show(io, op.f)
--     print(io, ')')
--     nothing
-- end
-- /Source
def showFunction {W L : Type} (ops : ShowOps W L) (bindings : Bindings L)
    (io operator : Value L) : CoreM W L (Value L) := do
  let _ ← ops.call bindings.print [io, bindings.broadcastFunctionType, bindings.leftParen]
  let function ← ops.call bindings.getproperty [operator, .symbol "f"]
  let selected ← (show CoreM W L ShowMethod from fun world =>
    some (.ok (ops.selectedShow io function world, world)))
  let _ ← match selected with
    | .same => showFunction ops bindings io function
    | .other => ops.call bindings.showFn [io, function]
  let _ ← ops.call bindings.print [io, bindings.rightParen]
  pure (JuliaLean.base.boot.nothingV ops.toCoreOps)
partial_fixpoint

/-- Text/plain display forwards the original IO and wrapper to their actual
two-argument show target, retaining that selected result and all stream
effects/errors. It makes no fixed rendering or forced-success assumption.
Source reference: base/broadcast.jl:1460. -/
-- Source: base/broadcast.jl:1460-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.show(io::IO, ::MIME"text/plain", op::BroadcastFunction) = show(io, op)
-- /Source
def showPlain {W L : Type} (ops : CoreOps W L) (bindings : Bindings L)
    (io operator : Value L) : CoreM W L (Value L) :=
  ops.call bindings.showFn [io, operator]

end JuliaLean.base.broadcast.Models2Group5.KeywordBroadcast

namespace JuliaLean.BroadcastCov.BitsSyntax

inductive ChunkOp where
  | unsupported
  | and
  | or
  | xor
  | nand
  | nor
  | not
  | identity
  | equal
  | unequal
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

/-- `_chunkop`, lines 1083-1096, as a word operation. -/
def applyChunkOp (op : ChunkOp) (x y : UInt64) : Option UInt64 :=
  match op with
  | .unsupported => none
  | .and => some (x &&& y)
  | .or => some (x ||| y)
  | .xor | .unequal => some (x ^^^ y)
  | .nand => some (~~~(x &&& y))
  | .nor => some (~~~(x ||| y))
  | .not => some (~~~x)
  | .identity => some x
  | .equal => some (~~~(x ^^^ y))
  | .less => some ((~~~x) &&& y)
  | .lessEqual => some ((~~~x) ||| y)
  | .greater => some (x &&& (~~~y))
  | .greaterEqual => some (x ||| (~~~y))

inductive ChunkArg where
  | bitarray (chunks : List UInt64)
  | scalar (value : Bool)
  | nested (supported : Bool) (args : List ChunkArg)
  | other
  deriving Repr

/-- `ischunkedbroadcast`, lines 1098-1105. -/
def chunkable (destinationChunks : Nat) : List ChunkArg → Bool
  | [] => true
  | .bitarray chunks :: rest => chunks.length == destinationChunks && chunkable destinationChunks rest
  | .scalar _ :: rest => chunkable destinationChunks rest
  | .nested supported args :: rest =>
      supported && chunkable destinationChunks args && chunkable destinationChunks rest
  | .other :: _ => false

/-- `liftchunks`, lines 1113-1116. Nested expressions are flattened by
`liftfuncs` before this function is called. -/
def liftChunks : List ChunkArg → List (List UInt64)
  | [] => []
  | .bitarray chunks :: rest => chunks :: liftChunks rest
  | .scalar value :: rest =>
      [if value then ~~~(0 : UInt64) else 0] :: liftChunks rest
  | _ :: rest => liftChunks rest

/-- `ithchunk`, lines 1117-1119. -/
def ithChunk (i : Nat) (chunks : List (List UInt64)) : List UInt64 :=
  chunks.map (fun c => c.getD i 0)

/-- `chunkedcopyto!`, lines 1120-1130. `lastMask` is `Base._msk_end(dest)`. -/
def chunkedCopy (op : UInt64 → UInt64 → UInt64) (left right : List UInt64)
    (lastMask : UInt64) : List UInt64 :=
  let result := (left.zip right).map fun p => op p.1 p.2
  match result.reverse with
  | [] => []
  | last :: rest => ((last &&& lastMask) :: rest).reverse

structure BitMasked where
  parent : List Bool
  mask : List Bool
  deriving Repr, DecidableEq

/-- `BitMaskedBitArray` constructors and `dotview`, lines 1261-1267. -/
def bitMasked (parent mask : List Bool) : Option BitMasked :=
  if parent.length == mask.length then some ⟨parent, mask⟩ else none

/-- `fill!(::BitMaskedBitArray)`, lines 1272-1285, expanded from chunks to
logical bits. -/
def fillMasked (b : BitMasked) (value : Bool) : BitMasked :=
  { b with parent := (b.parent.zip b.mask).map fun p => if p.2 then value else p.1 }

/-- The identity `materialize!` fast path at line 1270. -/
def materializeIdentity (b : BitMasked) (value : Bool) : BitMasked := fillMasked b value

/-- `show(::BitMaskedBitArray)`, line 1268, exposes the wrapper type and both fields. -/
def showBitMasked (b : BitMasked) : List (List Bool) := [b.parent, b.mask]

inductive Head where
  | call
  | comparison
  | dollar
  | letHead
  | forHead
  | generator
  | filter
  | assignment
  | functionHead
  | macroHead
  | subtype
  | supertype
  | block
  | other (name : String)
  deriving Repr, DecidableEq

inductive Syntax where
  | atom (name : String)
  | expr (head : Head) (args : List Syntax)
  deriving Repr

def dottable : Syntax → Bool
  | .atom name => name != ":" && (name == ".." || !name.startsWith ".")
  | .expr .dollar _ => false
  | .expr _ _ => true

/-- `undot`, lines 1308-1317. -/
def undot : Syntax → Syntax
  | .expr (.other ".=") args => .expr .assignment args
  | .expr .assignment args => .expr .assignment args
  | .expr .block args => .expr .block (args.map undot)
  | x => x

/-- `__dot__`, lines 1318-1348. -/
def dotSyntax : Syntax → Syntax
  | .atom name => .atom name
  | .expr head args =>
      let dotted := args.map dotSyntax
      match head with
      | .call =>
          match dotted with
          | f :: rest => if dottable f then .expr (.other ".") (f :: [.expr (.other "tuple") rest])
            else .expr .call dotted
          | [] => .expr .call []
      | .comparison => .expr .comparison dotted
      | .dollar => dotted.getD 0 (.atom "")
      | .letHead => .expr .letHead [undot (dotted.getD 0 (.atom "")), dotted.getD 1 (.atom "")]
      | .forHead => .expr .forHead [undot (dotted.getD 0 (.atom "")), dotted.getD 1 (.atom "")]
      | .generator => .expr .generator (dotted.take 1 ++ (dotted.drop 1).map undot)
      | .filter => .expr .filter (dotted.take 1 ++ (dotted.drop 1).map undot)
      | .functionHead | .macroHead =>
          .expr head [args.getD 0 (.atom ""), dotted.getD 1 (.atom "")]
      | .subtype => .expr .call (.atom ".<:" :: dotted)
      | .supertype => .expr .call (.atom ".>:" :: dotted)
      | .assignment => .expr (.other ".=") dotted
      | .other name =>
          if name = "&&" ∨ name = "||" ∨ (!name.startsWith "." && name.endsWith "=") then
            .expr (.other ("." ++ name)) dotted
          else .expr head dotted
      | .block => .expr .block dotted

/-- Macro wrapper at lines 1390-1392. -/
def macroDot (x : Syntax) : Syntax := dotSyntax x

/-- Generic `dotview(args...) = maybeview(args...)`, line 1297. -/
def dotviewResult (maybeViewResult : Syntax) : Syntax := maybeViewResult

/-- `liftfuncs`, lines 1108-1111, recursively transforms nested arguments and
retains whether `_chunkop` found a word operation. -/
def liftFunctions : ChunkArg → ChunkArg
  | .nested supported args => .nested supported (args.map liftFunctions)
  | x => x

inductive BroadcastedPath where
  | direct
  | keywordClosure
  | genericMapped (argumentCount : Nat)
  | explicitStyle
  deriving Repr, DecidableEq

/-- `broadcasted_kwsyntax` and generic `broadcasted` wrappers, lines 1394-1420. -/
def broadcastedPath (hasKeywords explicitStyle : Bool) (argumentCount : Nat) : BroadcastedPath :=
  if explicitStyle then .explicitStyle
  else if hasKeywords then .keywordClosure
  else if argumentCount = 0 then .direct
  else .genericMapped argumentCount

/-- `BroadcastFunction` call and show methods, lines 1452-1460. -/
def broadcastFunctionCall (f : List Int → Int) (args : List Int) : Int := f args
def broadcastFunctionShow (functionName : String) : String :=
  "BroadcastFunction(" ++ functionName ++ ")"

end JuliaLean.BroadcastCov.BitsSyntax

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

end JuliaLean.BroadcastCov.BroadcastCore

namespace JuliaLean.BroadcastCov.BroadcastRanges

inductive Kind where
  | abstractRange
  | ordinalRange
  | unitRange
  | stepRange
  | stepRangeLen
  | linRange
  deriving Repr, DecidableEq

structure RangeModel where
  kind : Kind
  first : Int
  step : Int
  stop : Int
  len : Nat
  offset : Nat
  deriving Repr, DecidableEq

inductive UnaryOp where
  | plus
  | minus
  | big
  deriving Repr, DecidableEq

/-- Unary `+`, unary `-`, and `big`, lines 1176-1181 and 1239-1242. -/
def unary (op : UnaryOp) (r : RangeModel) : RangeModel :=
  match op with
  | .plus => r
  | .minus =>
      match r.kind with
      | .ordinalRange =>
          { r with first := -r.first, stop := -r.stop, step := -r.step }
      | .stepRangeLen => { r with first := -r.first, step := -r.step }
      | .linRange => { r with first := -r.first, stop := -r.stop }
      | _ => { r with first := -r.first, step := -r.step, stop := -r.stop }
  | .big => r

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | ldiv
  deriving Repr, DecidableEq

inductive Side where
  | scalarLeft
  | scalarRight
  deriving Repr, DecidableEq

def applyScalar (op : BinaryOp) (side : Side) (x y : Int) : Int :=
  match op, side with
  | .add, _ => x + y
  | .sub, _ => x - y
  | .mul, _ => x * y
  | .div, _ => if y = 0 then 0 else x / y
  | .ldiv, _ => if x = 0 then 0 else y / x

/-- Scalar/range `+`, `-`, `*`, `/`, and `\`, lines 1184-1237. Division by
zero is outside this constructor observation because Julia performs it in the
scalar operation before constructing the range. -/
def scalarRange (op : BinaryOp) (side : Side) (x : Int) (r : RangeModel) : RangeModel :=
  let endpoint (y : Int) :=
    match side with
    | .scalarLeft => applyScalar op side x y
    | .scalarRight => applyScalar op side y x
  let newStep :=
    match op, side with
    | .sub, .scalarLeft => -r.step
    | .div, .scalarLeft => if r.step = 0 then 0 else x / r.step
    | .ldiv, .scalarLeft => if x = 0 then 0 else r.step / x
    | .div, .scalarRight => if x = 0 then 0 else r.step / x
    | .ldiv, .scalarRight => if r.step = 0 then 0 else x / r.step
    | .mul, _ => x * r.step
    | _, _ => r.step
  { r with first := endpoint r.first, stop := endpoint r.stop, step := newStep }

/-- Range/range addition and subtraction at lines 1198 and 1212, recording the
constructor fields used by `+(::AbstractRange, ::AbstractRange)` and its
subtraction counterpart. -/
def pairRange (subtract : Bool) (a b : RangeModel) : RangeModel :=
  { kind := .abstractRange
    first := if subtract then a.first - b.first else a.first + b.first
    step := if subtract then a.step - b.step else a.step + b.step
    stop := if subtract then a.stop - b.stop else a.stop + b.stop
    len := max a.len b.len
    offset := 1 }

structure CartesianRanges where
  ranges : List RangeModel
  deriving Repr, DecidableEq

/-- CartesianIndices `.+` and `.-` CartesianIndex, lines 1245-1254. -/
def shiftCartesian (subtract reverse : Bool) (ranges : CartesianRanges)
    (offsets : List Int) : CartesianRanges :=
  let shifted := (ranges.ranges.zip offsets).map fun p =>
    if reverse then
      { p.1 with first := p.2 - p.1.stop, stop := p.2 - p.1.first, step := p.1.step }
    else
      let s := if subtract then -p.2 else p.2
      { p.1 with first := p.1.first + s, stop := p.1.stop + s }
  ⟨if reverse then shifted.reverse else shifted⟩

/-- Nested `diffrange`, line 1252. -/
def diffrange (offset : Int) (r : RangeModel) : RangeModel :=
  { r with first := offset - r.stop, stop := offset - r.first }

end JuliaLean.BroadcastCov.BroadcastRanges


namespace JuliaLean.BroadcastViews

open JuliaLean


/-- `_bcs1(a::Integer, b::Integer)`, `base/broadcast.jl:531`:
`a == 1 ? b : (b == 1 ? a : (a == b ? a : throw(DimensionMismatch(...))))`. -/
def bcs1 (a b : I64) : R I64 :=
  if a.val = 1 then .ok b
  else if b.val = 1 then .ok a
  else if a.val = b.val then .ok a
  else .error .dimensionMismatch

/-- `_bcs(shape, newshape)`, `base/broadcast.jl:524-529`: combine two size tuples dimension by
dimension, copying the trailing dimensions of the longer one. -/
def bcs : List I64 → List I64 → R (List I64)
  | [], [] => .ok []
  | [], b :: bs => do let r ← bcs [] bs; pure (b :: r)
  | a :: as, [] => do let r ← bcs as []; pure (a :: r)
  | a :: as, b :: bs => do let x ← bcs1 a b; let r ← bcs as bs; pure (x :: r)

/-- `broadcast_shape(shape, shapes...)`, `base/broadcast.jl:521-522`:
`broadcast_shape(shape, shape1, shapes...) = broadcast_shape(_bcs(shape, shape1), shapes...)`. -/
def broadcastShape : List I64 → List (List I64) → R (List I64)
  | s, [] => .ok s
  | s, t :: ts => do let u ← bcs s t; broadcastShape u ts

/-- The extent of dimension `d` (0-based) of a size tuple; dimensions past its end have extent 1. -/
def ext (s : List I64) (d : Nat) : Int :=
  match s[d]? with
  | some x => x.val
  | none => 1

/-- Largest number of dimensions among the size tuples. -/
def maxLen (shapes : List (List I64)) : Nat := shapes.foldr (fun s m => max s.length m) 0

/-! ## Axes mixed with integer sizes

`_bcs1(a::Integer, b)` for an axis `b` (line 532) and `_bcs1(a, b::Integer) = _bcs1(b, a)`
(line 533). A one-based axis `OneTo(n)`/`1:n` is `Ax.oneTo n`; `first(b) == 1`, `last(b) == n`. -/

/-- A one-based `AbstractUnitRange{Int}` axis `1:n`. -/
structure Ax where
  n : I64
  deriving DecidableEq, Repr

/-- An entry of a shape tuple: an integer size or an axis. -/
inductive Dim where
  | size (n : I64)
  | axis (a : Ax)
  deriving DecidableEq, Repr

/-- The length of a shape entry. -/
def Dim.len : Dim → Int
  | .size n => n.val
  | .axis a => a.n.val

/-- `_bcs1` on one integer size and one axis, `base/broadcast.jl:532-533`:
`a == 1 ? b : (first(b) == 1 && last(b) == a ? b : throw(DimensionMismatch(...)))`. -/
def bcs1Mixed : Dim → Dim → R Dim
  | .size a, .axis b => if a.val = 1 then .ok (.axis b) else if b.n.val = a.val then .ok (.axis b) else .error .dimensionMismatch
  | .axis b, .size a => if a.val = 1 then .ok (.axis b) else if b.n.val = a.val then .ok (.axis b) else .error .dimensionMismatch
  | .size a, .size b => (bcs1 a b).map Dim.size
  | .axis a, .axis b =>
    -- `_bcs1(a, b) = _bcsm(b, a) ? axistype(b, a) : _bcsm(a, b) ? axistype(a, b) : throw(...)`,
    -- `_bcsm(a, b) = a == b || length(b) == 1` (lines 534-536); one-based axes are equal iff their lengths are.
    if b.n.val = a.n.val ∨ a.n.val = 1 then .ok (.axis b)
    else if a.n.val = b.n.val ∨ b.n.val = 1 then .ok (.axis a)
    else .error .dimensionMismatch

end JuliaLean.BroadcastViews

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `dest .= src` for two distinct view objects `dest = view(P, I...)`, `src = view(P, J...)` of
one parent with memory `mem` and size `dims`: `materialize!` → `copyto!(dest, bc)`
(`base/broadcast.jl:1015-1031`), whose identity fast path calls `copyto!(dest, src)` and otherwise
`preprocess`es the argument; both replace `src` by a copy exactly when `mightalias(dest, src)`.
The elements are then written in order. -/
def bcAssign (dims : List Nat) (mem : List Int) (I J : List Idx) : R (List Int) := do
  let copySrc ← mightaliasSame I J
  let dpos := (positions I).map (linIdx dims)
  let spos := (positions J).map (linIdx dims)
  pure <| (dpos.zip spos).foldl
    (fun m (p : Nat × Nat) => m.set p.1 ((if copySrc then mem else m).getD p.2 0)) mem

/-- `dest .= dest .+ c` (`dest .+= c`) for a view `dest = view(P, I...)`: `dest` is `===` the
destination, so `broadcast_unalias(dest, dest) = dest` (`base/broadcast.jl:1001`) does not copy it
and each element is read from the current memory just before its own write. -/
def bcSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  dpos.foldl (fun m p => m.set p (m.getD p 0 + c)) mem

end JuliaLean.BroadcastViews

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- Elementwise broadcast of `+` over two vectors (`collect(r1) .+ collect(r2)`): a length-1
argument is expanded (`base/broadcast.jl:531`, `_bcs1`), unequal non-singleton lengths throw. -/
def bcAddVectors (a b : List I64) : R (List I64) :=
  if a.length = b.length then .ok (List.zipWith (· + ·) a b)
  else if a.length = 1 then .ok (b.map (fun y => a.headD (i64 0) + y))
  else if b.length = 1 then .ok (a.map (fun x => x + b.headD (i64 0)))
  else .error .dimensionMismatch

/-- `x \ y` for a `Float64` `x` and a field value `y`: `\(x, y) = adjoint(adjoint(y)/adjoint(x))`
(`base/operators.jl:709`); `adjoint(x::Number) = conj(x)` (`base/number.jl:275`) has no method
for `TwicePrecision`, which is not a `Number`. -/
def ldivField : RefT → R RefT
  | .float => .ok .float
  | .twicePrecision => .error .methodError

/-- `broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) =
StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)`, `base/broadcast.jl:1236`; returns the
field type of the result. -/
def bcLdivRange (fieldT : RefT) : R RefT := do
  let ref ← ldivField fieldT
  let _step ← ldivField fieldT
  pure ref

/-- `r .- x` for `r = a:s:b::StepRange{UInt64,UInt64}` with `length(r) = n` and an integral
`x::Float64`: `range(first(r) - x, step=step(r), length=length(r))` (`base/broadcast.jl:1200`)
→ `range_start_step_length(a - x, Float64(s), n::UInt64)` (`base/twiceprecision.jl:450-465`,
with `rat` giving `(a - x, 1)` and `(s, 1)`) → `floatrange(Float64, a - x, s, n, 1)`.
Returns the exact value of element `i`. -/
def bcSubFloatElem (a s n : U64) (x : Int) (i : Nat) : R Int := do
  let (ref, off) ← floatrangeU (a.val - x) s.val n
  pure (srlElemU ref off s.val i)

/-- `.-(lo:hi)` for `lo:hi::UnitRange{UInt8}` (`last = hi` when `hi ≥ lo`, else `lo - 1`):
`broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange) =
range(-first(r), -last(r), step=negate(step(r)))`, `base/broadcast.jl:1179`, with `-x` on `UInt8`
wrapping; `range(a, b; step)` is `a:step:b`. -/
def bcNegU8 (lo hi : U8) : R (List U8) := do
  let last : U8 := if hi.val ≥ lo.val then hi else JInt.wrap .u8 (lo.val - 1)
  let r ← mkSRange8 (-lo) negateOne8 (-last)
  pure r.elems

end JuliaLean.BroadcastViews

namespace JuliaLean.Ranges

open JuliaLean

/-- Ordinal integer scalar addition specialization, base/broadcast.jl:1199-1205.
OneTo uses the AbstractUnitRange method and returns a UnitRange. -/
def broadcastAdd (r : Rng) (x : Num) : Jl ResultRng := do
  let a := Num.add (first r) x
  let b := Num.add (last r) x
  if r.kind = .step then
    return .ordinal (← colon3 a (step r) b)
  else
    return .ordinal (← colon2 a b)

/-- Integer scalar multiplication specialization, base/broadcast.jl:1241-1253. -/
def broadcastMul (r : Rng) (x : Num) : Jl ResultRng := do
  let a := Num.mul (first r) x
  let s := Num.mul (step r) x
  let n ← length r
  countedRange (Num.add a (Num.zero s.ty)).ty a s n

/-- `base/broadcast.jl:1208-1211`: scalar addition converts the reference before inferring element type. -/
def countedBroadcastAdd (r : RngLen) (x : Num) (scalarLeft : Bool := false) : Jl RngLen := do
  let refT ← Num.cast r.elementTy r.ref
  let element := if scalarLeft then Num.add x refT else Num.add refT x
  let ref := if scalarLeft then Num.add x r.ref else Num.add r.ref x
  countedNew element.ty ref r.stride r.len r.offset

/-- `base/broadcast.jl:1243-1244,1251-1252`: multiplication preserves offset and wraps every product separately. -/
def countedBroadcastMul (r : RngLen) (x : Num) (scalarLeft : Bool := false) : Jl RngLen := do
  let refT ← Num.cast r.elementTy r.ref
  let element := if scalarLeft then Num.mul x refT else Num.mul refT x
  let ref := if scalarLeft then Num.mul x r.ref else Num.mul r.ref x
  let stride := if scalarLeft then Num.mul x r.stride else Num.mul r.stride x
  countedNew element.ty ref stride r.len r.offset

end JuliaLean.Ranges
