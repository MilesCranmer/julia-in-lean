import JuliaLean.Core
import JuliaLean.base.tuple
import JuliaLean.Ranges.Keywords
import JuliaLean.FloatRanges.StepRangeLen
import JuliaLean.FloatRanges.LinRange
import JuliaLean.BroadcastViews.Alias

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




def convertInt (value : Int) : Jl JInt64 := JInt.convert .i64 value


structure Extruded (A : Type) where
  x : A
  keeps : List Bool
  defaults : List Int
  deriving Repr, DecidableEq

structure EvalBroadcasted (A V : Type) where
  f : List V → V
  args : List A

def gather {A I V : Type} (getindex : A → I → V) : List A → I → List V
  | [], _ => []
  | head :: tail, index => getindex head index :: gather getindex tail index

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

structure MaterializedExpr (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

inductive Inferred where | bottom | concrete | abstract deriving Repr, DecidableEq

structure Expr (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

def preprocessArgs {D A B : Type} (preprocess : D → A → B) (dest : D) : List A → List B
  | [] => []
  | head :: tail => preprocess dest head :: preprocessArgs preprocess dest tail

def copyLoop {H ε D B I V : Type}
    (getindex : B → I → StateT H (Except ε) V)
    (setindex : D → I → V → StateT H (Except ε) Unit)
    (dest : D) (bc : B) : List I → StateT H (Except ε) D
  | [] => pure dest
  | i :: rest => do
    let value ← getindex bc i
    setindex dest i value
    copyLoop getindex setindex dest bc rest

def copyPrefix {D I V : Type} (getindex : D → I → V) (setindex : D → I → V → D)
    (source target : D) : List I → D
  | [] => target
  | index :: rest => copyPrefix getindex setindex source (setindex target index (getindex source index)) rest

def copyNonleaf {D I V State : Type} (fits : V → Bool) (getvalue : I → V)
    (setindex : D → I → V → D) (widen : D → V → I → State → Nat → D) :
    D → List (I × State) → Nat → D
  | dest, [], _ => dest
  | dest, (index, state) :: rest, count =>
      let value := getvalue index
      if fits value then
        copyNonleaf fits getvalue setindex widen (setindex dest index value) rest (count + 1)
      else
        widen dest value index state count

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
def m229 {S F A X T R : Type} (axes : Broadcasted S F A X → R)
    (similar : Broadcasted S F A X → T → R → R) (bc : Broadcasted S F A X) (Tval : T) : R :=
  similar bc Tval (axes bc)
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
def m242 {E A Axis : Type} (combineAxes : A → Except E (List Axis)) (args : A) :
    Except E (List Axis) := combineAxes args
end Lazy

namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_axes(bc::Broadcasted{<:AbstractArrayStyle{0}}, ::Nothing) = ()
```
-/
def m243 {E A Axis : Type} (_args : A) : Except E (List Axis) := .ok []
end Lazy
namespace Lazy
open Style
/--
Julia source: base/broadcast.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline Base.axes(bc::Broadcasted) = _axes(bc, bc.axes)
```
-/
def m240 {E S F A Axis : Type} (unsetAxes : A → Except E (List Axis))
    (bc : Broadcasted S F A (Option (List Axis))) : Except E (List Axis) :=
  match bc.axes with | some axes => .ok (m241 axes) | none => unsetAxes bc.args
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
def m310 {E S F A Axis : Type} (combineAxes : A → Except E (List Axis))
    (checkAxes : List Axis → A → Except E Unit)
    (bc : Broadcasted S F A (Option (List Axis))) : Except E (Broadcasted S F A (Option (List Axis))) := do
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
def m322 {E S F A Axis : Type} (checkAxes : List Axis → A → Except E Unit)
    (bc : Broadcasted S F A (List Axis)) : Except E (Broadcasted S F A (List Axis)) := do
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
Julia source: base/broadcast.jl:459-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function result_style(s1::S, s2::S) where S<:BroadcastStyle
    s1 ≡ s2 ? s1 : error("inconsistent broadcast styles, custom rule needed")
end
```
-/
def m459 (identical : Style → Style → Bool) (left right : Style) :
    Except StyleError Style :=
  if identical left right then .ok left else .error .inconsistent
end Style

namespace Style
/--
Julia source: base/broadcast.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
result_style(s1, s2) = result_join(s1, s2, BroadcastStyle(s1, s2), BroadcastStyle(s2, s1))
```
-/
def m463 {σ : Type} (pairRule : Style → Style → StateT σ (Except StyleError) Style)
    (left right : Style) : StateT σ (Except StyleError) Style := fun state =>
  match pairRule left right state with
  | .error error => .error error
  | .ok (forward, stateAfterForward) =>
      match pairRule right left stateAfterForward with
      | .error error => .error error
      | .ok (reverse, stateAfterReverse) =>
          match resultJoin left right forward reverse with
          | .ok style => .ok (style, stateAfterReverse)
          | .error error => .error error
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
def m477 {α β : Type} (identical : Style → Style → Bool)
    (_left : α) (_right : β) (forward reverse : Style) : Except StyleError Style :=
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
def m502 {E A Args AxesA AxesRest Out : Type}
    (axes : A → Except E AxesA) (combineAxes : Args → Except E AxesRest)
    (broadcastShape : AxesA → AxesRest → Except E Out) (first : A) (rest : Args) : Except E Out := do
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
def m503 {E A B AxesA AxesB Out : Type}
    (axesA : A → Except E AxesA) (axesB : B → Except E AxesB)
    (broadcastShape : AxesA → AxesB → Except E Out) (left : A) (right : B) : Except E Out := do
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
def m504 {E A Axis : Type} (axes : A → Except E (List Axis)) (value : A) : Except E (List Axis) :=
  axes value
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
def m536 {A B : Type} {t : IntTy} (equal : A → B → Bool) (length : B → JInt t)
    (a : A) (b : B) : Bool := equal a b || (length b).val == 1
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
def m548 {S : Type} (_shape : S) : Result Unit := .ok ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(shp, ::Tuple{}) = nothing
```
-/
def m549 {S : Type} (_shape : S) : Result Unit := .ok ()
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:550-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_broadcast_shape(::Tuple{}, ::Tuple{}) = nothing
```
-/
def m550 : Result Unit := .ok ()
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
def m551 {Axis : Type} {t : IntTy} (length : Axis → JInt t) (axes : List Axis) : Result Unit :=
  if axes.any (fun axis => (length axis).val ≠ 1) then .error .dimensionMismatch else .ok ()
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
def m557 {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool) (length : Axis → JInt t)
    (head : D) (tail : List D) (axis : Axis) (axes : List Axis) : Result Unit :=
  if !m536 equal length head axis then .error .dimensionMismatch
  else match tail, axes with
    | [], [] => m550
    | _, [] => m549 tail
    | [], remaining => m551 length remaining
    | next :: rest, nextAxis :: restAxes => m557 equal length next rest nextAxis restAxes
termination_by tail.length

-- Tuple-arity dispatch selects the source check_broadcast_shape overload.
def checkShape {D Axis : Type} {t : IntTy} (equal : D → Axis → Bool) (length : Axis → JInt t) :
    List D → List Axis → Result Unit
  | [], [] => m550
  | [], axes => m551 length axes
  | shape, [] => m549 shape
  | head :: tail, axis :: axes => m557 equal length head tail axis axes
end Shape

namespace Shape
/--
Julia source: base/broadcast.jl:561-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline check_broadcast_axes(shp, A) = check_broadcast_shape(shp, axes(A))
```
-/
def m561 {A D Axis : Type} {t : IntTy} (axes : A → Result (List Axis))
    (equal : D → Axis → Bool) (length : Axis → JInt t) (shape : List D) (array : A) : Result Unit := do
  checkShape equal length shape (← axes array)
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
def m563 {A D Axis : Type} {t : IntTy} (axes : A → Result (List Axis))
    (equal : D → Axis → Bool) (length : Axis → JInt t)
    (shape : List D) (first second : A) (rest : List A) : Result Unit := do
  m561 axes equal length shape first
  match rest with
  | [] => m561 axes equal length shape second
  | next :: tail => m563 axes equal length shape second next tail
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
def m588 {I : Type} (_indices : I) : List Int := []
end Index
namespace Index
/--
Julia source: base/broadcast.jl:590-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple{}, I::Tuple{}) = ()
```
-/
def m590 : List Int := []
end Index
namespace Index
/--
Julia source: base/broadcast.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple{}) = (ax[1][begin], _newindex(tail(ax), ())...)
```
-/
def m589 (axis : Axis) (axes : List Axis) : Result (List Int) := do
  let rest ← match axes with
    | [] => pure m590
    | next :: tail => m589 next tail
  pure (axisFirst axis :: rest)
termination_by axes.length
end Index
namespace Index
/--
Julia source: base/broadcast.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _newindex(ax::Tuple, I::Tuple) = (ifelse(length(ax[1]) == 1, ax[1][begin], I[1]), _newindex(tail(ax), tail(I))...)
```
-/
def m587 (axis : Axis) (axes : List Axis) (index : Int) (indices : List Int) : Result (List Int) := do
  let first := axisFirst axis
  let chosen := if axis.values.length = 1 then first else index
  let rest ← match axes, indices with
    | [], [] => pure m590
    | [], remaining => pure (m588 remaining)
    | next :: tail, [] => m589 next tail
    | next :: tail, coordinate :: remaining => m587 next tail coordinate remaining
  pure (chosen :: rest)
termination_by axes.length

def remapAxes : List Axis → List Int → Result (List Int)
  | [], [] => pure m590
  | [], indices => pure (m588 indices)
  | axis :: axes, [] => m589 axis axes
  | axis :: axes, index :: indices => m587 axis axes index indices
end Index
namespace Index
/--
Julia source: base/broadcast.jl:585-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds newindex(arg, I::CartesianIndex) = to_index(_newindex(axes(arg), I.I))
```
-/
def m585 {A : Type} (axes : A → List Axis) (arg : A) (index : List Int) : Result Index :=
  toIndex <$> remapAxes (axes arg) index
end Index
namespace Index
/--
Julia source: base/broadcast.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds newindex(arg, I::Integer) = to_index(_newindex(axes(arg), (I,)))
```
-/
def m586 {A : Type} (axes : A → List Axis) (arg : A) (index : Int) : Result Index :=
  toIndex <$> remapAxes (axes arg) [index]
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
def m608 : List Bool × List Int := ([], [])
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
def m609 (axis : Axis) (axes : List Axis) : Result (List Bool × List Int) := do
  let rest ← match axes with
    | [] => pure m608
    | next :: remaining => m609 next remaining
  pure ((axis.values.length ≠ 1) :: rest.1, axisFirst axis :: rest.2)
termination_by axes.length

def newIndexer : List Axis → Result (List Bool × List Int)
  | [] => pure m608
  | axis :: axes => m609 axis axes
end Index
namespace Index
/--
Julia source: base/broadcast.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline shapeindexer(ax) = _newindexer(ax)
```
-/
def m607 (axes : List Axis) : Result (List Bool × List Int) := newIndexer axes
end Index
namespace Index
/--
Julia source: base/broadcast.jl:606-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline newindexer(A) = shapeindexer(axes(A))
```
-/
def m606 {A : Type} (axes : A → List Axis) (array : A) : Result (List Bool × List Int) :=
  m607 (axes array)
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
def m615 {BC Raw Flat R : Type} (flatten : Raw → Flat) (toIndexFn : Flat → Index)
    (indexStyle : BC → Bool) (getindex : Bool → BC → Index → R)
    (bc : BC) (indices : Raw) : R :=
  let index := toIndexFn (flatten indices)
  getindex (indexStyle bc) bc index
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
def m619 {BC I V : Type} (checkbounds : BC → I → Result Unit)
    (uncheckedGet : BC → I → Result V) (_style : Bool) (bc : BC) (index : I) : Result V := do
  checkbounds bc index
  uncheckedGet bc index
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
def m623 {BC CI V : Type} (axes : BC → List Axis) (cartesianIndices : List Axis → Int → Result CI)
    (getindex : Bool → BC → CI → Result V) (style : Bool) (bc : BC) (index : Int) : Result V := do
  let converted ← cartesianIndices (axes bc) index
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
def m627 {BC CI V : Type} (axes : BC → List Axis) (linearIndices : List Axis → CI → Result Int)
    (getindex : Bool → BC → Int → Result V) (style : Bool) (bc : BC) (index : CI) : Result V := do
  let converted ← linearIndices (axes bc) index
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
def m635 {BC CI : Type} (axes : BC → List Axis)
    (checkboundsIndices : List Axis → CI → Bool) (bc : BC) (index : CI) : Result Unit :=
  if checkboundsIndices (axes bc) index then .ok () else .error (.julia .boundsError)
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
def m640 {BC : Type} (eachindex : BC → List Int) (bc : BC) (index : Int) : Result Unit :=
  if (eachindex bc).contains index then .ok () else .error (.julia .boundsError)
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
def m657 {A I V : Type} (newindex : A → I → Result I) (getindex : A → I → Result V)
    (array : A) (index : I) : Result V := do
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
/--
Julia source: base/broadcast.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Any}, I)
    args = _getindex(bc.args, I)
    return _broadcast_getindex_evalf(bc.f, args...)
end
```
-/
def m675 {A I V : Type} (getindex : A → I → V) (bc : EvalBroadcasted A V) (index : I) : V :=
  bc.f (gather getindex bc.args index)
end Index

namespace Index
/--
Julia source: base/broadcast.jl:685-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Vararg{Any}}}, I) where {T}
    args = _getindex(tail(bc.args), I)
    return _broadcast_getindex_evalf(bc.f, T, args...)
end
```
-/
def m685 {A I T V : Type} (getindex : A → I → V) (f : T → List V → V)
    (typeValue : T) (tail : List A) (index : I) : V := f typeValue (gather getindex tail index)
end Index

namespace Index
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
def m689 {A I T V : Type} (getindex : A → I → V) (f : V → T → List V → V)
    (first : A) (typeValue : T) (tail : List A) (index : I) : V :=
  let firstValue := getindex first index
  f firstValue typeValue (gather getindex tail index)
end Index

namespace Index
/--
Julia source: base/broadcast.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Tuple{Ref{Type{T}},Ref{Type{S}},Vararg{Any}}}, I) where {T,S}
    args = _getindex(tail(tail(bc.args)), I)
    return _broadcast_getindex_evalf(bc.f, T, S, args...)
end
```
-/
def m694 {A I T S V : Type} (getindex : A → I → V) (f : T → S → List V → V)
    (firstType : T) (secondType : S) (tail : List A) (index : I) : V :=
  f firstType secondType (gather getindex tail index)
end Index

namespace Index
/--
Julia source: base/broadcast.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
```
-/
def m700 {A I V : Type} (getindex : A → I → V) (head : A) (tail : List A) (index : I) : List V :=
  getindex head index :: gather getindex tail index
end Index

namespace Index
/--
Julia source: base/broadcast.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
```
-/
def m701 {A I V : Type} (getindex : A → I → V) (head : A) (index : I) : List V := [getindex head index]
end Index

namespace Index
/--
Julia source: base/broadcast.jl:702-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
```
-/
def m702 {I V : Type} (_index : I) : List V := []
end Index

namespace Index
/--
Julia source: base/broadcast.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _broadcast_getindex_evalf(f::Tf, args::Vararg{Any,N}) where {Tf,N} = f(args...)  # not propagate_inbounds
```
-/
def m704 {A V : Type} (f : List A → V) (args : List A) : V := f args
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
def m740 {I V : Type} (collect : I → Result (List V)) (iterable : I) : Result (List V) := collect iterable
end Material

namespace Material
/--
Julia source: base/broadcast.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcastable(::Union{AbstractDict, NamedTuple}) = throw(ArgumentError("broadcasting over dictionaries and `NamedTuple`s is reserved"))
```
-/
def m741 {D : Type} (_dict : D) : Result Unit := .error .argument
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
def m756 {B A : Type} (argtypes : B → A) (returnType : A → JType)
    (promoteUnion : JType → JType) (bc : B) : JType :=
  let args := argtypes bc
  match returnType args with | .bottom => .bottom | result => promoteUnion result
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
def m898 {F D A B : Type} (broadcasted : F → A → Result B)
    (materializeBang : D → B → Result Unit) (f : F) (dest : D) (args : A) : Result D := do
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
def m908 {F A B R C T : Type} (broadcasted : F → A → B) (materialize : B → R)
    (axes : B → List C) (similarFill : B → R → T) (f : F) (args : A) : Sum T R :=
  let bc := broadcasted f args
  let result := materialize bc
  if (axes bc).isEmpty then .inl (similarFill bc result) else .inr result
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
def m921 {B R : Type} (instantiate : B → B) (copy : B → R) (bc : B) : R := copy (instantiate bc)
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
def m924 {D X I A B R : Type} (axes : D → X)
    (make : I → List A → X → B) (identity : I) (x : A)
    (instantiate : B → B) (materializeBang : D → B → R) (dest : D) : R :=
  materializeBang dest (instantiate (make identity [x] (axes dest)))
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
def m932 {S D F A X R : Type} (axes : D → X)
    (instantiate : MaterializedExpr S F A X → MaterializedExpr S F A X)
    (copyto : D → MaterializedExpr S F A X → R) (_style : S) (dest : D)
    (bc : MaterializedExpr S F A X) : R :=
  copyto dest (instantiate ⟨bc.style, bc.f, bc.args, axes dest⟩)
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
def m948 {B Iter I State V D : Type} (resultEltype : B → Result Inferred)
    (similar : B → Inferred → Result D) (copyto : D → B → Result D)
    (preprocess : B → Result B) (eachindex : B → Result Iter)
    (iterate : Iter → Result (Option (I × State))) (getindex : B → I → Result V)
    (typeOf : V → Inferred) (setindex : D → I → V → Result D)
    (normalize : Inferred → Inferred)
    (copyNonleaf : D → B → Iter → State → Nat → Result D)
    (assertReturn : Inferred → D → Result D) (bc : B) : Result D := do
  let elementType ← resultEltype bc
  if elementType = .concrete then
    let dest ← similar bc elementType
    copyto dest bc
  else
    let ready ← preprocess bc
    let iter ← eachindex ready
    match ← iterate iter with
    | none => similar ready elementType
    | some (index, state) => do
        let value ← getindex ready index
        let dest ← similar ready (typeOf value)
        let dest ← setindex dest index value
        let result ← copyNonleaf dest ready iter state 1
        assertReturn (normalize elementType) result
end Material

namespace Material
/--
Julia source: base/broadcast.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
```
-/
def m980 {D B : Type} (convertNothing : B → B) (copyto : D → B → D) (dest : D) (bc : B) : D :=
  copyto dest (convertNothing bc)
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
def m1007 {S F A X D : Type} (preprocessArgs : D → A → A) (dest : D) (bc : Expr S F A X) : Expr S F A X :=
  ⟨bc.style, bc.f, preprocessArgs dest bc.args, bc.axes⟩
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
```
-/
def m1008 {D A B : Type} (unalias : D → A → B) (extrude : B → B) (dest : D) (value : A) : B :=
  extrude (unalias dest value)
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1010-1010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
```
-/
def m1010 {D A B : Type} (preprocess : D → A → B) (dest : D) (head : A) (tail : List A) : List B :=
  preprocess dest head :: preprocessArgs preprocess dest tail
end Material

namespace Material
/--
Julia source: base/broadcast.jl:1011-1011 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
```
-/
def m1011 {D A B : Type} (preprocess : D → A → B) (dest : D) (value : A) : List B := [preprocess dest value]
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
def m1015 {H ε D S F Args Axes X I V : Type}
    (axesDest : D → StateT H (Except ε) X)
    (axesExpr : Expr S F Args Axes → StateT H (Except ε) X)
    (sameAxes : X → X → Bool) (isIdentity : F → Bool) (singleArray : Args → Option D)
    (throwdm : X → X → StateT H (Except ε) D)
    (copyto : D → D → StateT H (Except ε) D)
    (preprocess : D → Expr S F Args Axes → StateT H (Except ε) (Expr S F Args Axes))
    (eachindex : Expr S F Args Axes → StateT H (Except ε) (List I))
    (getindex : Expr S F Args Axes → I → StateT H (Except ε) V)
    (setindex : D → I → V → StateT H (Except ε) Unit)
    (dest : D) (bc : Expr S F Args Axes) : StateT H (Except ε) D := do
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
def m1133 {H ε A B Message Out : Type}
    (lazyString : String → A → String → B → StateT H (Except ε) Message)
    (dimensionMismatch : Message → StateT H (Except ε) ε)
    (destAxes : A) (sourceAxes : B) : StateT H (Except ε) Out := do
  let message ← lazyString "destination axes " destAxes
    " are not compatible with source axes " sourceAxes
  throw (← dimensionMismatch message)
end Material

namespace Material
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
def m1136 {D B I V State : Type} (getindex : D → I → V) (setindex : D → I → V → D)
    (continueCopy : D → B → List I → State → Nat → D) (newdest dest : D) (bc : B)
    (value : V) (index : I) (iter : List I) (state : State) (count : Nat) : D :=
  let copied := copyPrefix getindex setindex dest newdest (iter.take count)
  continueCopy (setindex copied index value) bc iter state (count + 1)
end Material

namespace Material
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
def m1145 {D I V State : Type} (fits : V → Bool) (getvalue : I → V)
    (setindex : D → I → V → D) (widen : D → V → I → State → Nat → D)
    (dest : D) (iterations : List (I × State)) (count : Nat) : D :=
  copyNonleaf fits getvalue setindex widen dest iterations count
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
        (Shape.m536 (· = ·) Ax.n) (Shape.m536 (· = ·) Ax.n)
        Shape.m542 Shape.m542 a b).map Dim.axis


end Sizes


namespace RangeExamples
open Sizes
structure URange where
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

def URange.len (r : URange) : Nat := (r.hi.val - r.lo.val + 1).toNat

def URange.elems (r : URange) : List I64 := (List.range r.len).map (fun k : Nat => r.lo + i64 k)


def bcAddVectors (a b : List I64) : R (List I64) :=
  if a.length = b.length then .ok (List.zipWith (· + ·) a b)
  else if a.length = 1 then .ok (b.map (fun y => a.headD (i64 0) + y))
  else if b.length = 1 then .ok (a.map (fun x => x + b.headD (i64 0)))
  else .error .dimensionMismatch

inductive RefT where
  | float
  | twicePrecision
  deriving DecidableEq, Repr

inductive FloatT where
  | f32
  | f64
  deriving DecidableEq, Repr

def colonRefT : FloatT → RefT
  | .f64 => .twicePrecision
  | .f32 => .float

def ldivField : RefT → R RefT
  | .float => .ok .float
  | .twicePrecision => .error .methodError

/--
Julia source: base/broadcast.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) = StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)
```
-/
def bcLdivRange (fieldT : RefT) : R RefT := do
  let ref ← ldivField fieldT
  let _step ← ldivField fieldT
  pure ref

abbrev U64 := JInt .u64

def roundHalfEven (n d : Int) : Int :=
  let n' := if d < 0 then -n else n
  let d' := if d < 0 then -d else d
  let q := n'.fdiv d'
  let r := n' - q * d'
  if 2 * r < d' then q else if 2 * r > d' then q + 1 else if q % 2 = 0 then q else q + 1

def floatrangeU (startN stepN : Int) (len : U64) : R (Int × U64) :=
  if len.val < 2 ∨ stepN = 0 then .ok (startN, JInt.lit .u64 1)
  else
    let k := roundHalfEven (stepN - startN) stepN
    if k < 0 then .error .inexactError
    else
      let imin : U64 := JInt.wrap .u64 (max 1 (min k len.val))
      let refN : U64 := JInt.wrap .u64 (startN + (imin.val - 1) * stepN)
      if refN.val ≥ 2 ^ 64 - 2 ^ 10 then .error .inexactError
      else .ok (refN.val, imin)

def srlElemU (ref : Int) (offset : U64) (stepN : Int) (i : Nat) : Int :=
  ref + (JInt.wrap .u64 ((i : Int) - offset.val)).val * stepN

/--
Julia source: base/broadcast.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange, x::Number) = range(first(r) - x, step=step(r), length=length(r))
```
-/
def bcSubFloatElem (a s n : U64) (x : Int) (i : Nat) : R Int := do
  let (ref, off) ← floatrangeU (a.val - x) s.val n
  pure (srlElemU ref off s.val i)

abbrev U8 := JInt .u8

def observeIntegerRange {t : IntTy} (r : JuliaLean.Ranges.Rng) : Jl (List (JInt t)) := do
  let n ← JuliaLean.Ranges.length r
  (List.range n.val.toNat).mapM fun (k : Nat) => do
    let value ← JuliaLean.Ranges.getindex r
      (JuliaLean.Ranges.Num.lit (.bit .i64) ((k : Int) + 1))
    JInt.convert t value.val

def observeResultRange {t : IntTy} (r : JuliaLean.Ranges.ResultRng) : Jl (List (JInt t)) := do
  let n ← JuliaLean.Ranges.resultLength r
  (List.range n.val.toNat).mapM fun (k : Nat) => do
    let value ← JuliaLean.Ranges.resultGetindex r
      (JuliaLean.Ranges.Num.lit (.bit .i64) ((k : Int) + 1))
    JInt.convert t value.val

def urange8Elems (lo hi : U8) : List U8 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun k : Nat => JInt.wrap .u8 (lo.val + (k : Int)))


end RangeExamples

namespace AliasExamples
open JuliaLean.BroadcastViews
/--
Julia source: base/broadcast.jl:1001-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
broadcast_unalias(::Nothing, src) = src
```
-/
def bcSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  let src := Material.m1001 (fun a b : List Nat => a == b) (fun _ src => src) dpos dpos
  let result : Except Empty (Unit × List Int) :=
    Material.copyLoop
      (fun (_ : Unit) p memory => .ok (memory.getD p 0 + c, memory))
      (fun (_ : Unit) p value memory => .ok ((), memory.set p value))
      () () src mem
  match result with
  | .ok (_, memory) => memory
  | .error impossible => nomatch impossible
end AliasExamples
end JuliaLean.base.broadcast
