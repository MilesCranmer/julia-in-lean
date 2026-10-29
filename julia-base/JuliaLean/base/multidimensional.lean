import JuliaLean.Core
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.subarray

/-!
# Model of `base/multidimensional.jl`

Julia target `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, 64-bit `Int`.
Coordinates are typed `JInt .i64`. Lists represent tuples; Julia dispatch supplies their
matching ranks. `Rng` is the earlier range interface, with first, step and length fields.
Operations on abstract arrays, IO, later-loaded functions and user-extensible types
are explicit typed parameters. Array mutation threads the destination value.
-/

namespace JuliaLean.base.multidimensional

open JuliaLean

/-- Julia exceptions used by this file, including exceptions not present in Core. -/
inductive Error where
  | overflowError (message : String)
  | argumentError (message : String)
  | boundsError
  | inexactError (functionName : String)
  | divideError
  | domainError (message : String)
  | methodError (functionName : String)
  | dimensionMismatch (message : String := "")
  | typeError
  | undefRefError
  | assertionError
  | errorException (message : String)
  | array (error : JuliaLean.base.array.Error)
  deriving Repr, DecidableEq, Inhabited

abbrev Result (A : Type) := Except Error A

abbrev I64 := JInt .i64
structure Rng where
  start : I64
  step : I64
  len : Nat
  deriving DecidableEq, Repr

/-- The exact value of the `j`-th element (0-based). -/
def Rng.elem (r : Rng) (j : Int) : Int := r.start.val + j * r.step.val

/-- `last(r)`: the normalised `stop` field, `start + (len-1)*step` (for an empty range
`start - step`, as `steprange_last_empty` produces), `base/range.jl`. -/
def Rng.last (r : Rng) : I64 := JInt.wrap .i64 (r.elem ((r.len : Int) - 1))

/-- The elements of `r`, in iteration order. -/
def Rng.elems (r : Rng) : List I64 :=
  (List.range r.len).map fun (j : Nat) => JInt.wrap .i64 (r.elem j)

/-- A range that Julia can construct: nonzero step and every element representable. -/
def Rng.WF (r : Rng) : Prop :=
  r.step.val ≠ 0 ∧ ∀ j : Nat, j < r.len → IntTy.min .i64 ≤ r.elem j ∧ r.elem j ≤ IntTy.max .i64

instance (r : Rng) : Decidable r.WF := by
  unfold Rng.WF; exact inferInstance

/-- `in(x, r)` for an integer range: `x` is one of its elements. -/
def Rng.contains (r : Rng) (x : I64) : Bool := r.elems.contains x

/-- 0-based position of the exact integer `x` in `r`, if it is an element. -/
def Rng.pos (r : Rng) (x : Int) : Option Nat :=
  if r.step.val ≠ 0 ∧ (x - r.start.val) % r.step.val = 0 ∧ 0 ≤ (x - r.start.val) / r.step.val ∧
      (x - r.start.val) / r.step.val < r.len
  then some ((x - r.start.val) / r.step.val).toNat else none
abbrev CI := List I64
abbrev CIs := List Rng

def int (x : Int) : I64 := JInt.wrap .i64 x

def fromCoreError : JlError → Error
  | .overflowError message => .overflowError message
  | .argumentError message => .argumentError message
  | .boundsError => .boundsError
  | .inexactError functionName => .inexactError functionName
  | .divideError => .divideError
  | .domainError message => .domainError message
  | .methodError functionName => .methodError functionName

/-- Standard fully assigned vector indexing, with only the exception channel adapted. -/
def vectorRead {A : Type} (values : List A) (index : I64) : Result A :=
  (JuliaLean.base.array.vectorGet values index).mapError Error.array


def mapTupleM {α β γ : Type} (f : α → β → Result γ) : List α → List β → Result (List γ)
  | [], [] => .ok []
  | x :: xs, y :: ys => do return (← f x y) :: (← mapTupleM f xs ys)
  | _, _ => .error (.argumentError "tuple dimensions differ")

def tupleGet {α : Type} (xs : List α) (i : I64) : Result α :=
  if 1 ≤ i.val then
    match xs[i.val.toNat - 1]? with
    | some x => .ok x
    | none => .error .boundsError
  else .error .boundsError


structure LogicalIndex (M : Type) where
  mask : M
  sum : I64

abbrev LR (α : Type) := Result α


/-- The nested-loop expansion used by Base.Cartesian: dimension one is innermost.
`post` runs after each completed iteration at its dimension. -/
def nestedLoops {S : Type} (body : CI → S → Result S) (post : Nat → S → Result S) :
    List (CI × Nat) → CI → S → Result S
  | [], coordinates, state => body coordinates state
  | (axis, dimension) :: rest, coordinates, state =>
    axis.foldlM (fun state i => do
      let state ← nestedLoops body post rest (i :: coordinates) state
      post dimension state) state

def forCartesian {S : Type} (axes : List CI) (body : CI → S → Result S) (state : S) : Result S :=
  nestedLoops body (fun _ s => .ok s) axes.zipIdx.reverse [] state

structure ChunkState (C : Type) where
  chunks : C
  index : I64
  otherIndex : I64


/-- Julia loops may diverge. `none` is divergence;
`some (.error e)` and `some (.ok a)` are terminating Julia outcomes. -/
def whileLoop {S A : Type} (step : S → Result (Sum A S)) (state : S) : Option (Result A) :=
  match step state with
  | .error e => some (.error e)
  | .ok (.inl value) => some (.ok value)
  | .ok (.inr next) => whileLoop step next
partial_fixpoint

structure HashStreamState where
  streams : List (JInt .u64)
  index : I64

structure FibState (K : Type) where
  key : K
  linearIndex : I64
  skip : I64
  previousSkip : I64
  streams : List (JInt .u64)
  count : I64


structure UniqueState (R D M : Type) where
  rowMap : R
  firstRows : D
  uniqueRows : CI
  collided : M
  nowCollided : M


/-- The first coordinate varies fastest in the Cartesian macro expansion. -/
def columnMajor {Index : Type} : List (List Index) → List (List Index)
  | [] => [[]]
  | axis :: rest => (columnMajor rest).flatMap fun tail => axis.map fun i => i :: tail


namespace AliasData
/-- An element of an index: an `Int` or a `CartesianIndex` with the given subscripts. -/
inductive Elem where
  | int (i : Int)
  | cart (is : List Int)
  deriving DecidableEq, Repr

/-- `x == y` between index elements. `CartesianIndex == Int` has no method of its own and falls
back to `===`, which is false. -/
def Elem.eqb : Elem → Elem → Bool
  | .int a, .int b => a == b
  | .cart a, .cart b => a == b
  | _, _ => false

/-- A parent index of a `SubArray`. -/
inductive Idx where
  /-- An `Int` (`Real` scalar index). -/
  | scalar (i : Int)
  /-- An `AbstractUnitRange{Int}` `lo:hi` (`UnitRange`, `OneTo`, `Slice(OneTo(n))`). -/
  | urange (lo hi : Int)
  /-- A non-unit `StepRange{Int,Int}` with `len` elements. -/
  | srange (start step : Int) (len : Nat)
  /-- A `Vector{Int}`. -/
  | ints (xs : List Int)
  /-- A `Vector{CartesianIndex{n}}` (each element has `n` subscripts). -/
  | carts (n : Nat) (xs : List (List Int))
  /-- Any other index type (conservative fallback). -/
  | other (subs : List (List Int))
  deriving DecidableEq, Repr

/-- The elements of an index, in order. -/
def Idx.elems : Idx → List Elem
  | .scalar i => [.int i]
  | .urange lo hi => ((List.range (hi - lo + 1).toNat).map (fun k : Nat => lo + (k : Int))).map .int
  | .srange a s n => ((List.range n).map (fun k : Nat => a + (k : Int) * s)).map .int
  | .ints xs => xs.map .int
  | .carts _ xs => xs.map .cart
  | .other _ => []
/-- `x in A` for an index array `A`: `any(y -> y == x, A)` (the range methods of `in` agree on
`Int`s; a `CartesianIndex` is never `==` to a range element). -/
def inIdx (x : Elem) (A : Idx) : Bool := A.elems.any (fun y => y.eqb x)

/-- The parent subscripts an index contributes per selected element. -/
def Idx.subs : Idx → List (List Int)
  | .carts _ xs => xs
  | .other subs => subs
  | i => i.elems.filterMap (fun | .int k => some [k] | .cart _ => none)
/-- The parent subscript tuples selected by a view's index tuple, in the view's column-major
element order (first index varies fastest). -/
def positions : List Idx → List (List Int)
  | [] => [[]]
  | i :: is => (positions is).flatMap (fun q => i.subs.map (fun p => p ++ q))

/-- Column-major linear index (0-based) of 1-based subscripts in a parent of size `dims`. -/
def linIdx : List Nat → List Int → Nat
  | n :: ns, i :: is => (i - 1).toNat + n * linIdx ns is
  | _, _ => 0

inductive IdxZ (Z : Type) where
  | scalar (i : Z)
  | urange (lo hi : Z)
  | srange (start step : Z) (len : Nat)
  | ints (xs : List Z)
  | carts (n : Nat) (xs : List (List Z))
  | other (subs : List (List Z))

def IdxZ.toIdx {Z : Type} (val : Z → Int) : IdxZ Z → Idx
  | .scalar i => .scalar (val i)
  | .urange lo hi => .urange (val lo) (val hi)
  | .srange a s n => .srange (val a) (val s) n
  | .ints xs => .ints (xs.map val)
  | .carts n xs => .carts n (xs.map (·.map val))
  | .other subs => .other (subs.map (·.map val))

end AliasData


def takeN {α : Type} (xs : List α) (n : Nat) : List α :=
  match xs with
  | [] => []
  | x :: rest =>
    match n with
    | 0 => []
    | m + 1 => x :: takeN rest m

/-- Structural execution of the generated gather loop, including the final
prechecked iterator advance performed after each write. -/
def gatherLoop {m : Type → Type} [Monad m] {Dest Src V K S Index : Type} (D : List K)
    (precheckedNext : List K → S → m (K × S))
    (getindex : Src → List Index → m V) (setindex : Dest → V → K → m Dest) (src : Src) :
    List (List Index) → Dest → K × S → m Dest
  | [], dest, _ => pure dest
  | j :: rest, dest, (idx, state) => do
    let dest ← setindex dest (← getindex src j) idx
    let next ← precheckedNext D state
    gatherLoop D precheckedNext getindex setindex src rest dest next

/--
Julia source: base/multidimensional.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        CartesianIndex{N}(index::NTuple{N,Integer}) where {N} = new(index)
```
-/
def cartesianInner {μ : Type → Type} [Monad μ] {Z : Type}
    (convertInt : Z → μ I64) (index : List Z) : μ CI :=
  index.mapM convertInt

/--
Julia source: base/multidimensional.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex(index::NTuple{N,Integer}) where {N} = CartesianIndex{N}(index)
```
-/
def cartesianTuple {μ : Type → Type} [Monad μ] {Z : Type}
    (construct : List Z → μ CI) (index : List Z) : μ CI := construct index

/--
Julia source: base/multidimensional.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex(index::Integer...) = CartesianIndex(index)
```
-/
def cartesianVarargs {μ : Type → Type} [Monad μ] {Z : Type}
    (construct : List Z → μ CI) (index : List Z) : μ CI := construct index

/--
Julia source: base/multidimensional.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex{N}(index::Vararg{Integer,N}) where {N} = CartesianIndex{N}(index)
```
-/
def cartesianSizedVarargs {Z : Type} (construct : List Z → Result CI) (index : List Z) : Result CI := construct index

/--
Julia source: base/multidimensional.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex{N}(index::Tuple) where {N} = CartesianIndex{N}(fill_to_length(index, 1, Val(N)))
```
-/
def cartesianPad {Z : Type} (fillToLength : List Z → Z → Nat → Result (List Z))
    (construct : List Z → Result CI) (one : Z) (N : Nat) (index : List Z) : Result CI := do
  construct (← fillToLength index one N)

/--
Julia source: base/multidimensional.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex{N}(index::Integer...) where {N} = CartesianIndex{N}(index)
```
-/
def cartesianSizedIntegers {Z : Type} (construct : List Z → Result CI) (index : List Z) : Result CI := construct index

/--
Julia source: base/multidimensional.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex{N}() where {N} = CartesianIndex{N}(())
```
-/
def cartesianDefault (construct : CI → Result CI) : Result CI := construct []

/--
Julia source: base/multidimensional.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex{N}(index::CartesianIndex{N}) where {N} = index
```
-/
def cartesianIdentity (index : CI) : CI := index

/--
Julia source: base/multidimensional.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex(index::Union{Integer, CartesianIndex}...) = CartesianIndex(flatten(index))
```
-/
def cartesianMixed {Z P : Type} (flatten : List Z → Result (List P)) (construct : List P → Result CI)
    (index : List Z) : Result CI := do construct (← flatten index)

/--
Julia source: base/multidimensional.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    flatten(::Tuple{}) = ()
```
-/
def flattenEmpty : CI := []

/--
Julia source: base/multidimensional.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    flatten(I::Tuple{Any}) = Tuple(I[1])
```
-/
def flattenSingle {A P : Type} (toTuple : A → Result (List P)) (x : A) : Result (List P) := toTuple x

/--
Julia source: base/multidimensional.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline flatten(I::Tuple) = (Tuple(I[1])..., flatten(tail(I))...)
```
-/
def flattenCons {A P : Type} (toTuple : A → Result (List P)) (flatten : List A → Result (List P))
    (head : A) (tail : List A) : Result (List P) := do return (← toTuple head) ++ (← flatten tail)

/--
Julia source: base/multidimensional.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndex(index::Tuple{Vararg{Union{Integer, CartesianIndex}}}) = CartesianIndex(index...)
```
-/
def cartesianMixedTuple {Z : Type} (construct : List Z → Result CI) (index : List Z) : Result CI := construct index

/--
Julia source: base/multidimensional.jl:94-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function show(io::IO, i::CartesianIndex)
        print(io, "CartesianIndex(")
        join(io, i.I, ", ")
        print(io, ")")
    end
```
-/
def showCartesian {IO : Type} (print : IO → String → Result IO)
    (join : IO → CI → String → Result IO) (io : IO) (index : CI) : Result IO := do
  let io ← print io "CartesianIndex("
  let io ← join io index ", "
  print io ")"

/--
Julia source: base/multidimensional.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(::CartesianIndex{N}) where {N} = N
```
-/
def cartesianLength (index : CI) : I64 := int index.length

/--
Julia source: base/multidimensional.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(::Type{CartesianIndex{N}}) where {N} = N
```
-/
def cartesianTypeLength (N : Nat) : I64 := int N

/--
Julia source: base/multidimensional.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    getindex(index::CartesianIndex, i::Integer) = index.I[i]
```
-/
def cartesianGetindex {Z : Type} (getindex : CI → Z → Result I64) (index : CI) (i : Z) : Result I64 :=
  getindex index i

/--
Julia source: base/multidimensional.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    firstindex(index::CartesianIndex) = firstindex(index.I)
```
-/
def cartesianFirstindex (firstindex : CI → I64) (index : CI) : I64 := firstindex index

/--
Julia source: base/multidimensional.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    lastindex(index::CartesianIndex) = lastindex(index.I)
```
-/
def cartesianLastindex (lastindex : CI → I64) (index : CI) : I64 := lastindex index

/--
Julia source: base/multidimensional.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.get(A::AbstractArray, I::CartesianIndex, default) = get(A, I.I, default)
```
-/
def arrayGetCartesian {A V : Type} (get : A → CI → V → Result V) (array : A) (index : CI) (default : V) : Result V :=
  get array index default

/--
Julia source: base/multidimensional.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eltype(::Type{T}) where {T<:CartesianIndex} = eltype(fieldtype(T, :I))
```
-/
def cartesianEltype {T F E : Type} (fieldtype : T → String → F) (eltype : F → E) (t : T) : E :=
  eltype (fieldtype t "I")

/--
Julia source: base/multidimensional.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Tuple(index::CartesianIndex) = index.I
```
-/
def cartesianToTuple (index : CI) : CI := index

/--
Julia source: base/multidimensional.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.setindex(x::CartesianIndex,i,j) = CartesianIndex(Base.setindex(Tuple(x),i,j))
```
-/
def cartesianSetindex {Z : Type} (setindex : CI → Z → I64 → Result CI)
    (construct : CI → Result CI) (x : CI) (value : Z) (j : I64) : Result CI := do
  construct (← setindex (cartesianToTuple x) value j)

/--
Julia source: base/multidimensional.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.:(==)(a::CartesianIndex{N}, b::CartesianIndex{N}) where N = a.I == b.I
```
-/
def cartesianEq (a b : CI) : Bool := a == b

/--
Julia source: base/multidimensional.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    zero(::CartesianIndex{N}) where {N} = zero(CartesianIndex{N})
```
-/
def cartesianZeroValue (zeroType : Nat → CI) (index : CI) : CI := zeroType index.length

/--
Julia source: base/multidimensional.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    zero(::Type{CartesianIndex{N}}) where {N} = CartesianIndex(ntuple(Returns(0), Val(N)))
```
-/
def cartesianZeroType (N : Nat) : CI := (List.range N).map fun _ => int 0

/--
Julia source: base/multidimensional.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    oneunit(::CartesianIndex{N}) where {N} = oneunit(CartesianIndex{N})
```
-/
def cartesianOneValue (oneType : Nat → CI) (index : CI) : CI := oneType index.length

/--
Julia source: base/multidimensional.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    oneunit(::Type{CartesianIndex{N}}) where {N} = CartesianIndex(ntuple(Returns(1), Val(N)))
```
-/
def cartesianOneType (N : Nat) : CI := (List.range N).map fun _ => int 1

/--
Julia source: base/multidimensional.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (+)(index::CartesianIndex) = index
```
-/
def cartesianPos (index : CI) : CI := index

/--
Julia source: base/multidimensional.jl:127-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (-)(index::CartesianIndex{N}) where {N} =
        CartesianIndex{N}(map(-, index.I))
```
-/
def cartesianNeg (index : CI) : CI := index.map (fun x => -x)

/--
Julia source: base/multidimensional.jl:129-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (+)(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =
        CartesianIndex{N}(map(+, index1.I, index2.I))
```
-/
def cartesianAdd (a b : CI) : CI := List.zipWith (· + ·) a b

/--
Julia source: base/multidimensional.jl:131-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (-)(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =
        CartesianIndex{N}(map(-, index1.I, index2.I))
```
-/
def cartesianSub (a b : CI) : CI := List.zipWith (· - ·) a b

/--
Julia source: base/multidimensional.jl:133-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline min(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =
        CartesianIndex{N}(map(min, index1.I, index2.I))
```
-/
def cartesianMin (a b : CI) : CI := List.zipWith (fun x y => if x.val ≤ y.val then x else y) a b

/--
Julia source: base/multidimensional.jl:135-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline max(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =
        CartesianIndex{N}(map(max, index1.I, index2.I))
```
-/
def cartesianMax (a b : CI) : CI := List.zipWith (fun x y => if x.val ≤ y.val then y else x) a b

/--
Julia source: base/multidimensional.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (*)(a::Integer, index::CartesianIndex{N}) where {N} = CartesianIndex{N}(map(x->a*x, index.I))
```
-/
def cartesianScaleLeft {Z X P : Type} (multiply : Z → X → Result P)
    (construct : List P → Result CI) (a : Z) (index : List X) : Result CI := do
  construct (← index.mapM (multiply a))

/--
Julia source: base/multidimensional.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline (*)(index::CartesianIndex, a::Integer) = *(a,index)
```
-/
def cartesianScaleRight {Z : Type} (multiply : Z → CI → Result CI) (index : CI) (a : Z) : Result CI := multiply a index

/--
Julia source: base/multidimensional.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    isless(I1::CartesianIndex{N}, I2::CartesianIndex{N}) where {N} = isless(reverse(I1.I), reverse(I2.I))
```
-/
def cartesianIsless (tupleIsless : CI → CI → Bool) (a b : CI) : Bool :=
  tupleIsless a.reverse b.reverse

/--
Julia source: base/multidimensional.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{T}, index::CartesianIndex{1}) where {T<:Number} = convert(T, index[1])
```
-/
def cartesianConvertNumber {T : Type} (getindex : CI → I64 → Result I64) (convert : I64 → Result T)
    (index : CI) : Result T := do
  convert (← getindex index (int 1))

/--
Julia source: base/multidimensional.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{T}, index::CartesianIndex) where {T<:Tuple} = convert(T, index.I)
```
-/
def cartesianConvertTuple {T : Type} (convert : CI → Result T) (index : CI) : Result T := convert index

/--
Julia source: base/multidimensional.jl:150-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.hash(ci::CartesianIndex, h::UInt)
        h ⊻= cartindexhash_seed
        for i in ci.I
            h = hash(i, h)
        end
        return h
    end
```
-/
def cartesianHash (hash : I64 → JInt .u64 → JInt .u64) (index : CI) (h : JInt .u64) : JInt .u64 :=
  let h := JInt.wrap .u64 (Int.ofNat (Nat.xor h.val.toNat 0xd60ca92f8284b8b0))
  index.foldl (fun h i => hash i h) h

/--
Julia source: base/multidimensional.jl:159-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.nextind(a::AbstractArray{<:Any,N}, i::CartesianIndex{N}) where {N}
        iter = CartesianIndices(axes(a))
        # might overflow
        I = inc(i.I, iter.indices)
        return I
    end
```
-/
def nextindCartesian {A : Type} (axes : A → CIs) (inc : CI → CIs → CI) (a : A) (i : CI) : CI :=
  let iter := axes a
  let I := inc i iter
  I

/--
Julia source: base/multidimensional.jl:165-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.prevind(a::AbstractArray{<:Any,N}, i::CartesianIndex{N}) where {N}
        iter = CartesianIndices(axes(a))
        # might underflow
        I = dec(i.I, iter.indices)
        return I
    end
```
-/
def previndCartesian {A : Type} (axes : A → CIs) (dec : CI → CIs → CI) (a : A) (i : CI) : CI :=
  let iter := axes a
  let I := dec i iter
  I

/--
Julia source: base/multidimensional.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base._ind2sub(t::Tuple, ind::CartesianIndex) = Tuple(ind)
```
-/
def ind2subCartesian {T : Type} (_t : T) (index : CI) : CI := cartesianToTuple index

/--
Julia source: base/multidimensional.jl:176-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.iterate(::CartesianIndex) =
        error("iteration is deliberately unsupported for CartesianIndex. Use `I` rather than `I...`, or use `Tuple(I)...`")
```
-/
def cartesianIterateDisabled (error : String → Result α) (_index : CI) : Result α :=
  error "iteration is deliberately unsupported for CartesianIndex. Use `I` rather than `I...`, or use `Tuple(I)...`"

/--
Julia source: base/multidimensional.jl:180-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.range_start_step_length(start::CartesianIndex, step::CartesianIndex, len::Integer) =
        error("range with a specified length is deliberately unsupported for CartesianIndex arguments."*
            " Use StepRangeLen($start, $step, $len) to construct this range")
```
-/
def cartesianRangeLengthDisabled {Z : Type} (start step : CI) (len : Z)
    (showIndex : CI → String := fun _ => "") (showLen : Z → String := fun _ => "") : Result α :=
  .error (.errorException ("range with a specified length is deliberately unsupported for CartesianIndex arguments. Use StepRangeLen(" ++
    showIndex start ++ ", " ++ showIndex step ++ ", " ++ showLen len ++ ") to construct this range"))

/--
Julia source: base/multidimensional.jl:187-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function show(io::IO, r::StepRangeLen{<:CartesianIndex})
        print(io, "StepRangeLen(", first(r), ", ",
                    step(r), ", ", length(r), ")")
    end
```
-/
def showCartesianStepRange {IO R : Type}
    (print : IO → String → CI → String → CI → String → I64 → String → Result IO)
    (first step : R → CI) (length : R → I64) (io : IO) (r : R) : Result IO :=
  print io "StepRangeLen(" (first r) ", " (step r) ", " (length r) ")"

/--
Julia source: base/multidimensional.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.in(x::CartesianIndex, r::AbstractRange{<:CartesianIndex}) = false
```
-/
def cartesianRangeContainsWrongRank {R : Type} (_x : CI) (_r : R) : Bool := false

/--
Julia source: base/multidimensional.jl:193-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.in(x::CartesianIndex{N}, r::AbstractRange{CartesianIndex{N}}) where {N}
        isempty(r) && return false
        f, st, l = first(r), step(r), last(r)
        # The n-th element of the range is a CartesianIndex
        # whose elements are the n-th along each dimension
        # Find the first dimension along which the index is changing,
        # so that n may be uniquely determined
        for i in 1:N
            iszero(st[i]) && continue
            n = findfirst(==(x[i]), f[i]:st[i]:l[i])
            isnothing(n) && return false
            return r[n] == x
        end
        # if the step is zero, the elements are identical, so compare with the first
        return x == f
    end
```
-/
def cartesianRangeContains {R : Type} (isempty : R → Bool) (first step last : R → CI)
    (findfirst : I64 → I64 → I64 → I64 → Result (Option I64)) (getindex : R → I64 → Result CI)
    (x : CI) (r : R) : Result Bool := do
  if isempty r then return false
  let f := first r
  let st := step r
  let l := last r
  for i in List.range x.length do
    let si ← tupleGet st (int (i + 1))
    if si.val != 0 then
      let xi ← tupleGet x (int (i + 1))
      let fi ← tupleGet f (int (i + 1))
      let li ← tupleGet l (int (i + 1))
      let n ← findfirst xi fi si li
      match n with
      | none => return false
      | some n => return (← getindex r n) == x
  return x == f

/--
Julia source: base/multidimensional.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndices(::Tuple{}) = CartesianIndices{0,typeof(())}(())
```
-/
def cartesianIndicesEmpty : CIs := []

/--
Julia source: base/multidimensional.jl:299-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function CartesianIndices(inds::NTuple{N,OrdinalRange{<:Integer, <:Integer}}) where {N}
        indices = map(r->convert(OrdinalRangeInt, r), inds)
        CartesianIndices{N, typeof(indices)}(indices)
    end
```
-/
def cartesianIndicesRanges {R : Type} (convert : R → Result Rng) (inds : List R) : Result CIs := do
  let indices ← inds.mapM convert
  return indices

/--
Julia source: base/multidimensional.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndices(index::CartesianIndex) = CartesianIndices(index.I)
```
-/
def cartesianIndicesIndex (construct : CI → Result CIs) (index : CI) : Result CIs := construct index

/--
Julia source: base/multidimensional.jl:305-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndices(inds::NTuple{N,Union{<:Integer,OrdinalRange{<:Integer}}}) where {N} =
        CartesianIndices(map(_convert2ind, inds))
```
-/
def cartesianIndicesMixed {I : Type} (convert2ind : I → Result Rng) (construct : CIs → Result CIs)
    (inds : List I) : Result CIs := do construct (← inds.mapM convert2ind)

/--
Julia source: base/multidimensional.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CartesianIndices(A::AbstractArray) = CartesianIndices(axes(A))
```
-/
def cartesianIndicesArray {A AX : Type} (axes : A → AX) (construct : AX → Result CIs) (a : A) : Result CIs := construct (axes a)

/--
Julia source: base/multidimensional.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _convert2ind(sz::Bool) = Base.OneTo(Int8(sz))
```
-/
def convert2indBool {R : Type} (oneTo : JInt .i8 → R) (sz : Bool) : R :=
  oneTo (JInt.wrap .i8 (if sz then 1 else 0))

/--
Julia source: base/multidimensional.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _convert2ind(sz::Integer) = Base.oneto(sz)
```
-/
def convert2indInteger {Z R : Type} (oneto : Z → Result R) (sz : Z) : Result R := oneto sz

/--
Julia source: base/multidimensional.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _convert2ind(sz::AbstractUnitRange) = first(sz):last(sz)
```
-/
def convert2indUnitRange {R Z O : Type} (first last : R → Z) (colon : Z → Z → Result O) (sz : R) : Result O :=
  colon (first sz) (last sz)

/--
Julia source: base/multidimensional.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _convert2ind(sz::OrdinalRange) = first(sz):step(sz):last(sz)
```
-/
def convert2indOrdinal {R Z S O : Type} (first last : R → Z) (step : R → S)
    (colon : Z → S → Z → Result O) (sz : R) : Result O := colon (first sz) (step sz) (last sz)

/--
Julia source: base/multidimensional.jl:315-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function show(io::IO, iter::CartesianIndices)
        print(io, "CartesianIndices(")
        show(io, map(_xform_index, iter.indices))
        print(io, ")")
    end
```
-/
def showCartesianIndices {IO R : Type} (print : IO → String → Result IO)
    (showIO : IO → List R → Result IO) (xform : Rng → R) (io : IO) (iter : CIs) : Result IO := do
  let io ← print io "CartesianIndices("
  let io ← showIO io (iter.map xform)
  print io ")"

/--
Julia source: base/multidimensional.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _xform_index(i) = i
```
-/
def xformIndex {R : Type} (i : R) : R := i

/--
Julia source: base/multidimensional.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _xform_index(i::OneTo) = i.stop
```
-/
def xformOneTo {R Z : Type} (stop : R → Z) (i : R) : Z := stop i

/--
Julia source: base/multidimensional.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    show(io::IO, ::MIME"text/plain", iter::CartesianIndices) = show(io, iter)
```
-/
def showCartesianIndicesPlain {IO : Type} (showIO : IO → CIs → Result IO) (io : IO) (iter : CIs) : Result IO := showIO io iter

/--
Julia source: base/multidimensional.jl:350-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    (:)(I::CartesianIndex{N}, J::CartesianIndex{N}) where N =
        CartesianIndices(map((i,j) -> i:j, Tuple(I), Tuple(J)))
```
-/
def cartesianColon (colon : I64 → I64 → Result Rng) (I J : CI) : Result CIs :=
  mapTupleM colon I J

/--
Julia source: base/multidimensional.jl:352-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    (:)(I::CartesianIndex{N}, S::CartesianIndex{N}, J::CartesianIndex{N}) where N =
        CartesianIndices(map((i,s,j) -> i:s:j, Tuple(I), Tuple(S), Tuple(J)))
```
-/
def cartesianStepColon (colon : I64 → I64 → I64 → Result Rng) (I S J : CI) : Result CIs :=
  mapTupleM (fun pair j => colon pair.1 pair.2 j) (I.zip S) J

/--
Julia source: base/multidimensional.jl:355-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    promote_rule(::Type{CartesianIndices{N,R1}}, ::Type{CartesianIndices{N,R2}}) where {N,R1,R2} =
        CartesianIndices{N,Base.indices_promote_type(R1,R2)}
```
-/
def cartesianIndicesPromote {R T : Type} (indicesPromoteType : R → R → T) (r1 r2 : R) : T :=
  indicesPromoteType r1 r2

/--
Julia source: base/multidimensional.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{Tuple{}}, R::CartesianIndices{0}) = ()
```
-/
def cartesianIndicesConvertEmpty (_R : CIs) : List Rng := []

/--
Julia source: base/multidimensional.jl:360-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @eval convert(::Type{NTuple{N,$RT}}, R::CartesianIndices{N}) where {N} =
            map(x->convert($RT, x), R.indices)
```
-/
def cartesianIndicesConvertRanges {R : Type} (convert : Rng → Result R) (indices : CIs) : Result (List R) :=
  indices.mapM convert

/--
Julia source: base/multidimensional.jl:363-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{NTuple{N,AbstractUnitRange}}, R::CartesianIndices{N}) where {N} =
        convert(NTuple{N,AbstractUnitRange{Int}}, R)
```
-/
def cartesianIndicesConvertAbstractUnit {R : Type} (convert : CIs → Result R) (indices : CIs) : Result R := convert indices

/--
Julia source: base/multidimensional.jl:365-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{NTuple{N,UnitRange{Int}}}, R::CartesianIndices{N}) where {N} =
        UnitRange{Int}.(convert(NTuple{N,AbstractUnitRange}, R))
```
-/
def cartesianIndicesConvertUnitInt {R U : Type} (convert : CIs → Result (List R)) (unitRange : R → Result U)
    (indices : CIs) : Result (List U) := do (← convert indices).mapM unitRange

/--
Julia source: base/multidimensional.jl:367-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{NTuple{N,UnitRange}}, R::CartesianIndices{N}) where {N} =
        UnitRange.(convert(NTuple{N,AbstractUnitRange}, R))
```
-/
def cartesianIndicesConvertUnit {R U : Type} (convert : CIs → Result (List R)) (unitRange : R → Result U)
    (indices : CIs) : Result (List U) := do (← convert indices).mapM unitRange

/--
Julia source: base/multidimensional.jl:369-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{Tuple{Vararg{AbstractUnitRange{Int}}}}, R::CartesianIndices{N}) where {N} =
        convert(NTuple{N,AbstractUnitRange{Int}}, R)
```
-/
def cartesianIndicesConvertVarargAbstractUnitInt {R : Type} (convert : CIs → Result R) (indices : CIs) : Result R := convert indices

/--
Julia source: base/multidimensional.jl:371-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{Tuple{Vararg{AbstractUnitRange}}}, R::CartesianIndices) =
        convert(Tuple{Vararg{AbstractUnitRange{Int}}}, R)
```
-/
def cartesianIndicesConvertVarargAbstractUnit {R : Type} (convert : CIs → Result R) (indices : CIs) : Result R := convert indices

/--
Julia source: base/multidimensional.jl:373-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{Tuple{Vararg{UnitRange{Int}}}}, R::CartesianIndices{N}) where {N} =
        convert(NTuple{N,UnitRange{Int}}, R)
```
-/
def cartesianIndicesConvertVarargUnitInt {R : Type} (convert : CIs → Result R) (indices : CIs) : Result R := convert indices

/--
Julia source: base/multidimensional.jl:375-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{Tuple{Vararg{UnitRange}}}, R::CartesianIndices) =
        convert(Tuple{Vararg{UnitRange{Int}}}, R)
```
-/
def cartesianIndicesConvertVarargUnit {R : Type} (convert : CIs → Result R) (indices : CIs) : Result R := convert indices

/--
Julia source: base/multidimensional.jl:378-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    convert(::Type{CartesianIndices{N,R}}, inds::CartesianIndices{N}) where {N,R} =
        CartesianIndices(convert(R, inds.indices))::CartesianIndices{N,R}
```
-/
def cartesianIndicesConvert {R : Type} (convert : CIs → Result R) (construct : R → Result CIs) (indices : CIs) : Result CIs := do
  construct (← convert indices)

/--
Julia source: base/multidimensional.jl:382-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.:(==)(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =
        all(map(==, a.indices, b.indices))
```
-/
def cartesianIndicesEq (rangeEq : Rng → Rng → Bool) (a b : CIs) : Bool :=
  (List.zipWith rangeEq a b).all id

/--
Julia source: base/multidimensional.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.:(==)(a::CartesianIndices, b::CartesianIndices) = false
```
-/
def cartesianIndicesEqWrongRank (_a _b : CIs) : Bool := false

/--
Julia source: base/multidimensional.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.axes(iter::CartesianIndices{N,R}) where {N,R} = map(Base.axes1, iter.indices)
```
-/
def cartesianIndicesAxes {AX : Type} (axes1 : Rng → AX) (iter : CIs) : List AX := iter.map axes1

/--
Julia source: base/multidimensional.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.has_offset_axes(iter::CartesianIndices) = Base.has_offset_axes(iter.indices...)
```
-/
def cartesianIndicesHasOffset (hasOffsetAxes : CIs → Bool) (iter : CIs) : Bool := hasOffsetAxes iter

/--
Julia source: base/multidimensional.jl:389-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds function isassigned(iter::CartesianIndices{N,R}, I::Vararg{Int, N}) where {N,R}
        for i in 1:N
            isassigned(iter.indices[i], I[i]) || return false
        end
        return true
    end
```
-/
def cartesianIndicesIsassigned (isassigned : Rng → I64 → Bool) (iter : CIs) (I : CI) : Bool :=
  (iter.zip I).all fun (range, index) => isassigned range index

/--
Julia source: base/multidimensional.jl:397-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Base.getindex(iter::CartesianIndices{0,R}) where {R}
        CartesianIndex()
    end
```
-/
def cartesianIndicesGetindexZero (_iter : CIs) : CI := []

/--
Julia source: base/multidimensional.jl:400-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Base.getindex(iter::CartesianIndices{N,R}, I::Vararg{Int, N}) where {N,R}
        # Eagerly do boundscheck before calculating each item of the CartesianIndex so that
        # we can pass `@inbounds` hint to inside the map and generates more efficient SIMD codes (#42115)
        @boundscheck checkbounds(iter, I...)
        index = map(iter.indices, I) do r, i
            @inbounds getindex(r, i)
        end
        CartesianIndex(index)
    end
```
-/
def cartesianIndicesGetindex (checkbounds : CIs → CI → Result Unit)
    (getindex : Rng → I64 → Result I64) (iter : CIs) (I : CI) : Result CI := do
  checkbounds iter I
  let index ← mapTupleM getindex iter I
  return index

/--
Julia source: base/multidimensional.jl:413-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Base.getindex(iter::CartesianIndices{N,R},
        I::Vararg{Union{OrdinalRange{<:Integer, <:Integer}, Colon}, N}) where {N,R}
        @boundscheck checkbounds(iter, I...)
        indices = map(iter.indices, I) do r, i
            @inbounds getindex(r, i)
        end
        CartesianIndices(indices)
    end
```
-/
def cartesianIndicesGetindexRanges {I : Type} (checkbounds : CIs → List I → Result Unit)
    (getindex : Rng → I → Result Rng) (iter : CIs) (I : List I) : Result CIs := do
  checkbounds iter I
  let indices ← mapTupleM getindex iter I
  return indices

/--
Julia source: base/multidimensional.jl:421-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds function Base.getindex(iter::CartesianIndices{N},
        C::CartesianIndices{N}) where {N}
        getindex(iter, C.indices...)
    end
```
-/
def cartesianIndicesGetindexRegion (getindex : CIs → CIs → Result CIs) (iter C : CIs) : Result CIs := getindex iter C

/--
Julia source: base/multidimensional.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline Base.getindex(iter::CartesianIndices{0}, ::CartesianIndices{0}) = iter
```
-/
def cartesianIndicesGetindexZeroRegion (iter _C : CIs) : CIs := iter

/--
Julia source: base/multidimensional.jl:428-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds function Base.view(c::CartesianIndices{N}, r::Vararg{Union{OrdinalRange{<:Integer, <:Integer}, Colon},N}) where {N}
        getindex(c, r...)
    end
```
-/
def cartesianIndicesViewRanges {I : Type} (getindex : CIs → List I → Result CIs) (c : CIs) (r : List I) : Result CIs := getindex c r

/--
Julia source: base/multidimensional.jl:431-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds function Base.view(c::CartesianIndices{N}, C::CartesianIndices{N}) where {N}
        getindex(c, C)
    end
```
-/
def cartesianIndicesViewRegion (getindex : CIs → CIs → Result CIs) (c C : CIs) : Result CIs := getindex c C

/--
Julia source: base/multidimensional.jl:435-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eachindex(::IndexCartesian, A::AbstractArray) = CartesianIndices(axes(A))
```
-/
def eachindexCartesian {A : Type} (axes : A → CIs) (a : A) : CIs := axes a

/--
Julia source: base/multidimensional.jl:437-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function eachindex(::IndexCartesian, A::AbstractArray, B::AbstractArray...)
        axsA = axes(A)
        axsBs = map(axes, B)
        all(==(axsA), axsBs) ||
            Base.throw_eachindex_mismatch_indices("axes", axsA, axsBs...)
        CartesianIndices(axsA)
    end
```
-/
def eachindexCartesianMany {A AX : Type} [BEq AX] (axes : A → AX)
    (construct : AX → Result CIs) (mismatch : AX → List AX → Result Unit) (a : A) (b : List A) : Result CIs := do
  let axsA := axes a
  let axsBs := b.map axes
  if !(axsBs.all (· == axsA)) then mismatch axsA axsBs
  construct axsA

/--
Julia source: base/multidimensional.jl:445-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(iter::CartesianIndices)
        iterfirst = first(iter)
        if !all(map(in, iterfirst.I, iter.indices))
            return nothing
        end
        iterfirst, iterfirst
    end
```
-/
def cartesianIterateFirst (iter : CIs) : Option (CI × CI) :=
  let iterfirst := iter.map (·.start)
  if !(List.zipWith (fun i r => r.contains i) iterfirst iter).all id then none
  else some (iterfirst, iterfirst)

/--
Julia source: base/multidimensional.jl:452-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(iter::CartesianIndices, state::CartesianIndex)
        valid, I = __inc(state.I, iter.indices)
        valid || return nothing
        return CartesianIndex(I...), CartesianIndex(I...)
    end
```
-/
def cartesianIterateNext (inc : CI → CIs → Bool × CI) (iter : CIs) (state : CI) : Option (CI × CI) :=
  let (valid, I) := inc state iter
  if !valid then none else some (I, I)

/--
Julia source: base/multidimensional.jl:459-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function inc(state, indices)
        _, I = __inc(state, indices)
        return CartesianIndex(I...)
    end
```
-/
def cartesianInc (inc : CI → CIs → Bool × CI) (state : CI) (indices : CIs) : CI :=
  let (_, I) := inc state indices
  I

/--
Julia source: base/multidimensional.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    __inc(::Tuple{}, ::Tuple{}) = false, ()
```
-/
def incEmpty : Bool × CI := (false, [])

/--
Julia source: base/multidimensional.jl:469-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function __inc(state::Tuple{Int}, indices::Tuple{OrdinalRangeInt})
        rng = indices[1]
        I = state[1] +% step(rng)
        valid = state[1] != last(rng)
        return valid, (I,)
    end
```
-/
def incSingle (state : I64) (rng : Rng) : Bool × CI :=
  let I := state + rng.step
  let valid := state != rng.last
  (valid, [I])

/--
Julia source: base/multidimensional.jl:475-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function __inc(state::Tuple{Int,Int,Vararg{Int}}, indices::Tuple{OrdinalRangeInt,OrdinalRangeInt,Vararg{OrdinalRangeInt}})
        rng = indices[1]
        if state[1] != last(rng)
            I = state[1] + step(rng)
            return true, (I, tail(state)...)
        end
        valid, Itail = __inc(tail(state), tail(indices))
        return valid, (first(rng), Itail...)
    end
```
-/
def incCons (inc : CI → CIs → Bool × CI) (state : I64) (tail : CI) (rng : Rng) (ranges : CIs) : Bool × CI :=
  if state != rng.last then
    let I := state + rng.step
    (true, I :: tail)
  else
    let (valid, Itail) := inc tail ranges
    (valid, rng.start :: Itail)

/--
Julia source: base/multidimensional.jl:486-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    iterate(iter::CartesianIndices{0}, done::Bool=false) = done ? nothing : (CartesianIndex(), true)
```
-/
def cartesianIterateZero (done : Bool := false) : Option (CI × Bool) :=
  if done then none else some ([], true)

/--
Julia source: base/multidimensional.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    size(iter::CartesianIndices) = map(length, iter.indices)
```
-/
def cartesianIndicesSize (length : Rng → I64) (iter : CIs) : CI := iter.map length

/--
Julia source: base/multidimensional.jl:491-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.step(iter::CartesianIndices) = CartesianIndex(map(step, iter.indices))
```
-/
def cartesianIndicesStep (iter : CIs) : CI := iter.map (·.step)

/--
Julia source: base/multidimensional.jl:493-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    first(iter::CartesianIndices) = CartesianIndex(map(first, iter.indices))
```
-/
def cartesianIndicesFirst (iter : CIs) : CI := iter.map (·.start)

/--
Julia source: base/multidimensional.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    last(iter::CartesianIndices)  = CartesianIndex(map(last, iter.indices))
```
-/
def cartesianIndicesLast (iter : CIs) : CI := iter.map (·.last)

/--
Julia source: base/multidimensional.jl:497-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function to_indices(A, inds, I::Tuple{CartesianIndices{N}, Vararg}) where N
        _, indstail = split(inds, Val(N))
        (map(Fix1(to_index, A), I[1].indices)..., to_indices(A, indstail, tail(I))...)
    end
```
-/
def toIndicesCartesianRegion {A AX I O : Type} (split : List AX → Nat → List AX × List AX)
    (toIndex : A → Rng → Result O) (toIndices : A → List AX → List I → Result (List O))
    (a : A) (inds : List AX) (head : CIs) (tail : List I) : Result (List O) := do
  let (_, indstail) := split inds head.length
  return (← head.mapM (toIndex a)) ++ (← toIndices a indstail tail)

/--
Julia source: base/multidimensional.jl:502-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline to_indices(A, inds, I::Tuple{CartesianIndices{0}, Vararg}) =
        (first(I), to_indices(A, inds, tail(I))...)
```
-/
def toIndicesCartesianRegionZero {A AX I O : Type} (toIndices : A → List AX → List I → Result (List O))
    (a : A) (inds : List AX) (head : O) (tail : List I) : Result (List O) := do
  return head :: (← toIndices a inds tail)

/--
Julia source: base/multidimensional.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline in(i::CartesianIndex, r::CartesianIndices) = false
```
-/
def cartesianIndicesContainsWrongRank (_i : CI) (_r : CIs) : Bool := false

/--
Julia source: base/multidimensional.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline in(i::CartesianIndex{N}, r::CartesianIndices{N}) where {N} = all(map(in, i.I, r.indices))
```
-/
def cartesianIndicesContains (i : CI) (r : CIs) : Bool :=
  (List.zipWith (fun i r => r.contains i) i r).all id

/--
Julia source: base/multidimensional.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    copy(iter::CartesianIndices) = iter
```
-/
def cartesianIndicesCopy (iter : CIs) : CIs := iter

/--
Julia source: base/multidimensional.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    simd_outer_range(iter::CartesianIndices{0}) = iter
```
-/
def simdOuterZero (iter : CIs) : CIs := iter

/--
Julia source: base/multidimensional.jl:511-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function simd_outer_range(iter::CartesianIndices)
        CartesianIndices(tail(iter.indices))
    end
```
-/
def simdOuter (iter : CIs) : CIs := iter.tail

/--
Julia source: base/multidimensional.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    simd_inner_length(iter::CartesianIndices{0}, ::CartesianIndex) = 1
```
-/
def simdInnerZero (_iter : CIs) (_I : CI) : I64 := int 1

/--
Julia source: base/multidimensional.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    simd_inner_length(iter::CartesianIndices, I::CartesianIndex) = Base.length(iter.indices[1])
```
-/
def simdInner (length : Rng → I64) (range : Rng) (_tail : CIs) (_I : CI) : I64 := length range

/--
Julia source: base/multidimensional.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    simd_index(iter::CartesianIndices{0}, ::CartesianIndex, I1::Int) = first(iter)
```
-/
def simdIndexZero (iter : CIs) (_I : CI) (_I1 : I64) : CI := cartesianIndicesFirst iter

/--
Julia source: base/multidimensional.jl:519-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds simd_index(iter::CartesianIndices, Ilast::CartesianIndex, I1::Int) =
        CartesianIndex(iter.indices[1][I1+firstindex(iter.indices[1])], Ilast)
```
-/
def simdIndex (getindex : Rng → I64 → Result I64) (firstindex : Rng → I64)
    (range : Rng) (_ranges : CIs) (Ilast : CI) (I1 : I64) : Result CI := do
  return (← getindex range (I1 + firstindex range)) :: Ilast

/--
Julia source: base/multidimensional.jl:523-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function split(t, V::Val)
        ref = ntuple(Returns(true), V)  # create a reference tuple of length N
        _split1(t, ref), _splitrest(t, ref)
    end
```
-/
def splitTuple {A : Type} (split1 splitrest : List A → List Bool → List A)
    (t : List A) (N : Nat) : List A × List A :=
  let ref := List.replicate N true
  (split1 t ref, splitrest t ref)

/--
Julia source: base/multidimensional.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline _split1(t, ref) = (t[1], _split1(tail(t), tail(ref))...)
```
-/
def split1Cons {A : Type} (split1 : List A → List Bool → List A)
    (head : A) (tail : List A) (refTail : List Bool) : List A := head :: split1 tail refTail

/--
Julia source: base/multidimensional.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))
```
-/
def splitrestCons {A : Type} (splitrest : List A → List Bool → List A)
    (tail : List A) (refTail : List Bool) : List A := splitrest tail refTail

/--
Julia source: base/multidimensional.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(::Tuple{}, ::Tuple{}) = ()
```
-/
def split1EmptyEmpty {A : Type}  : List A := []

/--
Julia source: base/multidimensional.jl:531-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(::Tuple{}, ref) = ()
```
-/
def split1EmptyRef {A : Type} (_ref : List Bool) : List A := []

/--
Julia source: base/multidimensional.jl:532-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(t, ::Tuple{}) = ()
```
-/
def split1TupleEmpty {A : Type} (_t : List A) : List A := []

/--
Julia source: base/multidimensional.jl:533-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(::Tuple{}, ::Tuple{}) = ()
```
-/
def splitrestEmptyEmpty {A : Type}  : List A := []

/--
Julia source: base/multidimensional.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(t, ::Tuple{}) = t
```
-/
def splitrestTupleEmpty {A : Type} (t : List A) : List A := t

/--
Julia source: base/multidimensional.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(::Tuple{}, ref) = ()
```
-/
def splitrestEmptyRef {A : Type} (_ref : List Bool) : List A := []

/--
Julia source: base/multidimensional.jl:537-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function split(I::CartesianIndex, V::Val)
        i, j = split(I.I, V)
        CartesianIndex(i), CartesianIndex(j)
    end
```
-/
def splitCartesian (split : CI → Nat → CI × CI) (I : CI) (N : Nat) : CI × CI :=
  let (i, j) := split I N
  (i, j)

/--
Julia source: base/multidimensional.jl:541-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function split(R::CartesianIndices, V::Val)
        i, j = split(R.indices, V)
        CartesianIndices(i), CartesianIndices(j)
    end
```
-/
def splitCartesianIndices (split : CIs → Nat → CIs × CIs) (R : CIs) (N : Nat) : CIs × CIs :=
  let (i, j) := split R N
  (i, j)

/--
Julia source: base/multidimensional.jl:547-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Base._reverse(iter::CartesianIndices, ::Colon)
        CartesianIndices(reverse.(iter.indices))
    end
```
-/
def reverseCartesianAll (reverse : Rng → Rng) (iter : CIs) : CIs := iter.map reverse

/--
Julia source: base/multidimensional.jl:551-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.@constprop :aggressive function Base._reverse(iter::CartesianIndices, dim::Integer)
        1 <= dim <= ndims(iter) || throw(ArgumentError(Base.LazyString("invalid dimension ", dim, " in reverse")))
        ndims(iter) == 1 && return Base._reverse(iter, :)
        indices = iter.indices
        return CartesianIndices(Base.setindex(indices, reverse(indices[dim]), dim))
    end
```
-/
def reverseCartesianDimension {Z : Type} (value : Z → Int) (reverse : Rng → Rng)
    (iter : CIs) (dim : Z) (ndims : CIs → Nat := List.length)
    (showDim : Z → String := fun d => toString (value d)) : Result CIs := do
  if !(1 ≤ value dim ∧ value dim ≤ ndims iter) then
    throw (.argumentError ("invalid dimension " ++ showDim dim ++ " in reverse"))
  if ndims iter == 1 then return reverseCartesianAll reverse iter
  let indices := iter
  let range ← tupleGet indices (int (value dim))
  return indices.set (value dim).toNat.pred (reverse range)

/--
Julia source: base/multidimensional.jl:558-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.@constprop :aggressive function Base._reverse(iter::CartesianIndices, dims::Tuple{Vararg{Integer}})
        indices = iter.indices
        # use `sum` to force const fold
        dimrev = ntuple(i -> sum(==(i), dims; init = 0) == 1, Val(length(indices)))
        length(dims) == sum(dimrev) || throw(ArgumentError(Base.LazyString("invalid dimensions ", dims, " in reverse")))
        length(dims) == length(indices) && return Base._reverse(iter, :)
        indices′ = map((i, f) -> f ? (@noinline reverse(i)) : i, indices, dimrev)
        return CartesianIndices(indices′)
    end
```
-/
def reverseCartesianDimensions {Z : Type} (value : Z → Int) (reverse : Rng → Rng)
    (iter : CIs) (dims : List Z)
    (showDims : List Z → String := fun ds => toString (ds.map value)) : Result CIs := do
  let indices := iter
  let dimrev := (List.range indices.length).map fun (i : Nat) =>
    ((dims.foldl (fun acc d => acc + if value d == (Int.ofNat i) + 1 then 1 else 0) (0 : Nat)) == 1)
  let sumDimrev := dimrev.foldl (fun acc b => acc + if b then 1 else 0) (0 : Nat)
  if dims.length != sumDimrev then
    throw (.argumentError ("invalid dimensions " ++ showDims dims ++ " in reverse"))
  if dims.length == indices.length then return reverseCartesianAll reverse iter
  let indices' := List.zipWith (fun i f => if f then reverse i else i) indices dimrev
  return indices'

/--
Julia source: base/multidimensional.jl:569-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base._reverse(iter::CartesianIndices{1}, dims::Tuple{Integer}) =
        Base._reverse(iter, first(dims))
```
-/
def reverseCartesianOneDimension {Z : Type} (reverse : CIs → Z → Result CIs) (iter : CIs) (dim : Z) : Result CIs :=
  reverse iter dim

/--
Julia source: base/multidimensional.jl:572-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(r::Reverse{<:CartesianIndices})
        iterfirst = last(r.itr)
        if !all(map(in, iterfirst.I, r.itr.indices))
            return nothing
        end
        iterfirst, iterfirst
    end
```
-/
def reverseIterateFirst (iter : CIs) : Option (CI × CI) :=
  let iterfirst := cartesianIndicesLast iter
  if !(List.zipWith (fun i r => r.contains i) iterfirst iter).all id then none
  else some (iterfirst, iterfirst)

/--
Julia source: base/multidimensional.jl:579-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(r::Reverse{<:CartesianIndices}, state)
        valid, I = __dec(state.I, r.itr.indices)
        valid || return nothing
        return CartesianIndex(I...), CartesianIndex(I...)
    end
```
-/
def reverseIterateNext (dec : CI → CIs → Bool × CI) (iter : CIs) (state : CI) : Option (CI × CI) :=
  let (valid, I) := dec state iter
  if !valid then none else some (I, I)

/--
Julia source: base/multidimensional.jl:586-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function dec(state, indices)
        _, I = __dec(state, indices)
        return CartesianIndex(I...)
    end
```
-/
def cartesianDec (dec : CI → CIs → Bool × CI) (state : CI) (indices : CIs) : CI :=
  let (_, I) := dec state indices
  I

/--
Julia source: base/multidimensional.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline __dec(::Tuple{}, ::Tuple{}) = false, ()
```
-/
def decEmpty : Bool × CI := (false, [])

/--
Julia source: base/multidimensional.jl:593-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function __dec(state::Tuple{Int}, indices::Tuple{OrdinalRangeInt})
        rng = indices[1]
        I = state[1] -% step(rng)
        valid = state[1] != first(rng)
        return valid, (I,)
    end
```
-/
def decSingle (state : I64) (rng : Rng) : Bool × CI :=
  let I := state - rng.step
  let valid := state != rng.start
  (valid, [I])

/--
Julia source: base/multidimensional.jl:599-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function __dec(state::Tuple{Int,Int,Vararg{Int}}, indices::Tuple{OrdinalRangeInt,OrdinalRangeInt,Vararg{OrdinalRangeInt}})
        rng = indices[1]
        I = state[1] -% step(rng)
        if state[1] != first(rng)
            return true, (I, tail(state)...)
        end
        valid, I = __dec(tail(state), tail(indices))
        return valid, (last(rng), I...)
    end
```
-/
def decCons (dec : CI → CIs → Bool × CI) (state : I64) (tail : CI) (rng : Rng) (ranges : CIs) : Bool × CI :=
  let I := state - rng.step
  if state != rng.start then (true, I :: tail)
  else
    let (valid, I) := dec tail ranges
    (valid, rng.last :: I)

/--
Julia source: base/multidimensional.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    iterate(iter::Reverse{<:CartesianIndices{0}}, state=false) = state ? nothing : (CartesianIndex(), true)
```
-/
def reverseIterateZero (state : Bool := false) : Option (CI × Bool) :=
  if state then none else some ([], true)

/--
Julia source: base/multidimensional.jl:612-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.LinearIndices(inds::CartesianIndices{N,R}) where {N,R<:NTuple{N, AbstractUnitRange}}
        LinearIndices{N,R}(inds.indices)
    end
```
-/
def linearIndicesUnit {L : Type} (construct : CIs → Result L) (inds : CIs) : Result L := construct inds

/--
Julia source: base/multidimensional.jl:615-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.LinearIndices(inds::CartesianIndices)
        indices = inds.indices
        if all(x->step(x)==1, indices)
            indices = map(rng->first(rng):last(rng), indices)
            LinearIndices{length(indices), typeof(indices)}(indices)
        else
            # Given the fact that StepRange 1:2:4 === 1:2:3, we lost the original size information
            # and thus cannot calculate the correct linear indices when the steps are not 1.
            throw(ArgumentError(LazyString("LinearIndices for ", typeof(inds), " with non-1 step size is not yet supported.")))
        end
    end
```
-/
def linearIndices {L : Type} (unitRange : I64 → I64 → Rng) (construct : CIs → Result L)
    (inds : CIs) (typeofInds : CIs → String := fun _ => "CartesianIndices") : Result L := do
  let indices := inds
  if indices.all (fun r => r.step.val == 1) then
    let indices := indices.map fun rng => unitRange rng.start rng.last
    construct indices
  else
    throw (.argumentError ("LinearIndices for " ++ typeofInds inds ++ " with non-1 step size is not yet supported."))

/--
Julia source: base/multidimensional.jl:631-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.collect(inds::CartesianIndices{N, R}) where {N,R<:NTuple{N, AbstractUnitRange}}
        Base._collect_indices(axes(inds), inds)
    end
```
-/
def collectCartesianUnit {AX A : Type} (axes : CIs → AX) (collectIndices : AX → CIs → Result A)
    (inds : CIs) : Result A := collectIndices (axes inds) inds

/--
Julia source: base/multidimensional.jl:634-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.collect(inds::CartesianIndices)
        dest = Array{eltype(inds), ndims(inds)}(undef, size(inds))
        i = 0
        @inbounds for a in inds
            dest[i+=1] = a
        end
        dest
    end
```
-/
def collectCartesian {A : Type} (allocate : CI → Result A) (size : CIs → CI)
    (elements : CIs → List CI) (setindex : A → CI → I64 → Result A) (inds : CIs) : Result A := do
  let mut dest ← allocate (size inds)
  let mut i := int 0
  for a in elements inds do
    i := i + int 1
    dest ← setindex dest a i
  return dest

/--
Julia source: base/multidimensional.jl:644-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.intersect(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =
        CartesianIndices(intersect.(a.indices, b.indices))
```
-/
def intersectCartesian (intersect : Rng → Rng → Result Rng) (a b : CIs) : Result CIs := mapTupleM intersect a b

/--
Julia source: base/multidimensional.jl:646-647 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Base.issubset(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =
        isempty(a) || all(map(issubset, a.indices, b.indices))
```
-/
def subsetCartesian (isempty : CIs → Bool) (issubset : Rng → Rng → Bool) (a b : CIs) : Bool :=
  isempty a || (List.zipWith issubset a b).all id

/--
Julia source: base/multidimensional.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eltype(::Type{PartitionIterator{T}}) where {T<:ReshapedArrayLF} = SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, true}
```
-/
def partitionEltypeLinear {T E S : Type} (eltype : T → E) (subArrayType : E → T → Bool → S) (t : T) : S :=
  subArrayType (eltype t) t true

/--
Julia source: base/multidimensional.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eltype(::Type{PartitionIterator{T}}) where {T<:ReshapedArray} = SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, false}
```
-/
def partitionEltypeCartesian {T E S : Type} (eltype : T → E) (subArrayType : E → T → Bool → S) (t : T) : S :=
  subArrayType (eltype t) t false

/--
Julia source: base/multidimensional.jl:653-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Iterators.IteratorEltype(::Type{<:PartitionIterator{T}}) where {T<:ReshapedArray} = Iterators.IteratorEltype(T)
```
-/
def partitionIteratorEltype {T E : Type} (iteratorEltype : T → E) (t : T) : E := iteratorEltype t

/--
Julia source: base/multidimensional.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eltype(::Type{PartitionIterator{T}}) where {T<:OneTo} = UnitRange{eltype(T)}
```
-/
def partitionEltypeOneTo {T E R : Type} (eltype : T → E) (unitRangeType : E → R) (t : T) : R := unitRangeType (eltype t)

/--
Julia source: base/multidimensional.jl:656-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eltype(::Type{PartitionIterator{T}}) where {T<:Union{UnitRange, StepRange, StepRangeLen, LinRange}} = T
```
-/
def partitionEltypeRange {T : Type} (t : T) : T := t

/--
Julia source: base/multidimensional.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Iterators.IteratorEltype(::Type{<:PartitionIterator{T}}) where {T<:Union{OneTo, UnitRange, StepRange, StepRangeLen, LinRange}} = Iterators.IteratorEltype(T)
```
-/
def partitionRangeIteratorEltype {T E : Type} (iteratorEltype : T → E) (t : T) : E := iteratorEltype t

/--
Julia source: base/multidimensional.jl:659-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(iter::CartesianPartition)
        isempty(iter) && return nothing
        f = first(iter)
        return (f, (f, 1))
    end
```
-/
def partitionIterateFirst {P : Type} (isempty : P → Bool) (first : P → CI) (iter : P) : Option (CI × (CI × I64)) :=
  if isempty iter then none else
    let f := first iter
    some (f, (f, int 1))

/--
Julia source: base/multidimensional.jl:664-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function iterate(iter::CartesianPartition, (state, n))
        n >= length(iter) && return nothing
        I = IteratorsMD.inc(state.I, iter.parent.parent.indices)
        return I, (I, n+1)
    end
```
-/
def partitionIterateNext {P : Type} (length : P → I64) (indices : P → CIs)
    (inc : CI → CIs → CI) (iter : P) (state : CI) (n : I64) : Option (CI × (CI × I64)) :=
  if n ≥ length iter then none else
    let I := inc state (indices iter)
    some (I, (I, n + int 1))

/--
Julia source: base/multidimensional.jl:670-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function simd_outer_range(iter::CartesianPartition)
        # In general, the Cartesian Partition might start and stop in the middle of the outer
        # dimensions — thus the outer range of a CartesianPartition is itself a
        # CartesianPartition.
        mi = iter.parent.mi
        ci = iter.parent.parent
        ax1 = Base.axes1(ci)
        function splitdim1(i, mi)
            d, r = divrem(i - 1, mi)
            d + 1, r + first(ax1)
        end
        vl, fl = splitdim1(first(iter.indices[1]), mi[1])
        vr, fr = splitdim1(last(iter.indices[1]), mi[1])
        # form the iterator for outer dimensions, equivalent to vec(oci), but mi is reused
        oci = CartesianIndices(tail(ci.indices))
        roci = ReshapedArray(oci, (length(oci),), tail(mi))
        outer = @inbounds view(roci, vl:vr)
        # Use Generator to make inner loop branchless
        @inline function skip_len_I(i::Int, I::CartesianIndex)
            l = i == 1 ? fl : first(ax1)
            r = i == length(outer) ? fr : last(ax1)
            l - first(ax1), r - l + 1, I
        end
        (skip_len_I(i, I) for (i, I) in Iterators.enumerate(outer))
    end
```
-/
def partitionSimdOuter {P AX R V MI : Type} (mi : P → List MI) (indices : P → CIs)
    (axes1 : CIs → AX) (firstAxis lastAxis : AX → I64) (partitionFirst partitionLast : P → I64)
    (divrem : I64 → MI → Result (I64 × I64)) (length : CIs → I64)
    (reshape : CIs → I64 → List MI → Result R) (view : R → I64 → I64 → Result V)
    (enumerate : V → List (I64 × CI)) (outerLength : V → I64) (iter : P) : Result (List (I64 × I64 × CI)) := do
  let splitdim1 := fun i mi => do
    let (d, r) ← divrem (i - int 1) mi
    return (d + int 1, r + firstAxis (axes1 (indices iter)))
  let inverses := mi iter
  let ci := indices iter
  let ax1 := axes1 ci
  let mi1 ← tupleGet inverses (int 1)
  let (vl, fl) ← splitdim1 (partitionFirst iter) mi1
  let (vr, fr) ← splitdim1 (partitionLast iter) mi1
  let oci := ci.tail
  let roci ← reshape oci (length oci) inverses.tail
  let outer ← view roci vl vr
  return (enumerate outer).map fun (i, I) =>
    let l := if i == int 1 then fl else firstAxis ax1
    let r := if i == outerLength outer then fr else lastAxis ax1
    (l - firstAxis ax1, r - l + int 1, I)

/--
Julia source: base/multidimensional.jl:677-680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function splitdim1(i, mi)
            d, r = divrem(i - 1, mi)
            d + 1, r + first(ax1)
        end
```
-/
def partitionSplitdim1 {MI : Type} (divrem : I64 → MI → Result (I64 × I64)) (axisFirst i : I64) (mi : MI) : Result (I64 × I64) := do
  let (d, r) ← divrem (i - int 1) mi
  return (d + int 1, r + axisFirst)

/--
Julia source: base/multidimensional.jl:688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline function skip_len_I(i::Int, I::CartesianIndex)
            l = i == 1 ? fl : first(ax1)
            r = i == length(outer) ? fr : last(ax1)
            l - first(ax1), r - l + 1, I
        end
```
-/
def partitionSkipLength (axisFirst axisLast fl fr outerLength i : I64) (I : CI) : I64 × I64 × CI :=
  let l := if i == int 1 then fl else axisFirst
  let r := if i == outerLength then fr else axisLast
  (l - axisFirst, r - l + int 1, I)

/--
Julia source: base/multidimensional.jl:695-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function simd_outer_range(iter::CartesianPartition{CartesianIndex{2}})
        # But for two-dimensional Partitions the above is just a simple one-dimensional range
        # over the second dimension; we don't need to worry about non-rectangular staggers in
        # higher dimensions.
        mi = iter.parent.mi
        ci = iter.parent.parent
        ax, ax1 = axes(ci), Base.axes1(ci)
        fl, vl = Base.ind2sub_rs(ax, mi, first(iter.indices[1]))
        fr, vr = Base.ind2sub_rs(ax, mi, last(iter.indices[1]))
        outer = @inbounds CartesianIndices((ci.indices[2][vl:vr],))
        # Use Generator to make inner loop branchless
        @inline function skip_len_I(I::CartesianIndex{1})
            l = I == first(outer) ? fl : first(ax1)
            r = I == last(outer) ? fr : last(ax1)
            l - first(ax1), r - l + 1, I
        end
        (skip_len_I(I) for I in outer)
    end
```
-/
def partitionSimdOuter2 {P AX MI : Type} (mi : P → List MI) (indices : P → CIs)
    (axes : CIs → List AX) (axes1 : CIs → AX) (firstAxis lastAxis : AX → I64)
    (partitionFirst partitionLast : P → I64) (ind2sub : List AX → List MI → I64 → Result (I64 × I64))
    (getrange : Rng → I64 → I64 → Result Rng) (elements : CIs → List CI) (iter : P) : Result (List (I64 × I64 × CI)) := do
  let inverses := mi iter
  let ci := indices iter
  let ax := axes ci
  let ax1 := axes1 ci
  let (fl, vl) ← ind2sub ax inverses (partitionFirst iter)
  let (fr, vr) ← ind2sub ax inverses (partitionLast iter)
  let range ← tupleGet ci (int 2)
  let outer := [← getrange range vl vr]
  return (elements outer).map fun I => let l := if I == cartesianIndicesFirst outer then fl else firstAxis ax1
    let r := if I == cartesianIndicesLast outer then fr else lastAxis ax1
    (l - firstAxis ax1, r - l + int 1, I)

/--
Julia source: base/multidimensional.jl:706-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @inline function skip_len_I(I::CartesianIndex{1})
            l = I == first(outer) ? fl : first(ax1)
            r = I == last(outer) ? fr : last(ax1)
            l - first(ax1), r - l + 1, I
        end
```
-/
def partitionSkipLength2 (axisFirst axisLast fl fr : I64) (firstOuter lastOuter I : CI) : I64 × I64 × CI :=
  let l := if I == firstOuter then fl else axisFirst
  let r := if I == lastOuter then fr else axisLast
  (l - axisFirst, r - l + int 1, I)

/--
Julia source: base/multidimensional.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline simd_inner_length(iter::CartesianPartition, (_, len, _)::Tuple{Int,Int,CartesianIndex}) = len
```
-/
def partitionSimdInner {P : Type} (_iter : P) (state : I64 × I64 × CI) : I64 := state.2.1

/--
Julia source: base/multidimensional.jl:714-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @propagate_inbounds simd_index(iter::CartesianPartition, (skip, _, I)::Tuple{Int,Int,CartesianIndex}, n::Int) =
        simd_index(iter.parent.parent, I, n + skip)
```
-/
def partitionSimdIndex {P : Type} (parentIndices : P → CIs) (simdIndex : CIs → CI → I64 → Result CI)
    (iter : P) (state : I64 × I64 × CI) (n : I64) : Result CI :=
  simdIndex (parentIndices iter) state.2.2 (n + state.1)

/--
Julia source: base/multidimensional.jl:735-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fn($(args...), i::Union{Integer,CartesianIndex}...)
            return $fn($(args...), CartesianIndex(to_indices($(args[1]), i)))
        end
```
-/
def atomicMixed {M Args I O : Type} (toIndices : M → List I → Result CI)
    (call : M → Args → CI → Result O) (mem : M) (args : Args) (i : List I) : Result O := do
  call mem args (← toIndices mem i)

/--
Julia source: base/multidimensional.jl:739-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fn($(args...), i::CartesianIndex)
            return $fn($(args...), Tuple(i)...)
        end
```
-/
def atomicCartesian {M Args O : Type} (call : M → Args → CI → Result O)
    (mem : M) (args : Args) (i : CI) : Result O := call mem args (cartesianToTuple i)

/--
Julia source: base/multidimensional.jl:743-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function $fn($(args...), i::Integer...)
            idcs = to_indices($(args[1]), i)
            S = IndexStyle($(args[1]))
            if isa(S, IndexLinear)
                return $fn($(args...), _to_linear_index($(args[1]), idcs...))
            else
                return $fn($(args...), _to_subscript_indices($(args[1]), idcs...))
            end
        end
```
-/
def atomicIntegers {M Args I O : Type} (toIndices : M → List I → Result CI) (isLinear : M → Bool)
    (toLinear : M → CI → Result I64) (toSubscripts : M → CI → Result CI)
    (callLinear : M → Args → I64 → Result O) (callCartesian : M → Args → CI → Result O)
    (mem : M) (args : Args) (i : List I) : Result O := do
  let idcs ← toIndices mem i
  let S := isLinear mem
  if S then callLinear mem args (← toLinear mem idcs)
  else callCartesian mem args (← toSubscripts mem idcs)

/--
Julia source: base/multidimensional.jl:757-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline checkbounds(::Type{Bool}, A::AbstractArray, i::CartesianIndex) =
    checkbounds_indices(Bool, axes(A), (i,))
```
-/
def checkboundsCartesian {A AX : Type} (axes : A → List AX)
    (checkboundsIndices : List AX → List CI → Bool) (a : A) (i : CI) : Bool :=
  checkboundsIndices (axes a) [i]

/--
Julia source: base/multidimensional.jl:760-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{CartesianIndex,Vararg})
    inds1, rest = IteratorsMD.split(inds, Val(length(I[1])))
    checkindex(Bool, inds1, I[1]) && checkbounds_indices(Bool, rest, tail(I))
end
```
-/
def checkboundsIndicesCartesian {AX I : Type} (checkindex : List AX → CI → Bool)
    (checkboundsIndices : List AX → List I → Bool) (inds : List AX) (head : CI) (tail : List I) : Bool :=
  let inds1 := inds.take head.length
  let rest := inds.drop head.length
  checkindex inds1 head && checkboundsIndices rest tail

/--
Julia source: base/multidimensional.jl:764-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline checkindex(::Type{Bool}, inds::Tuple, I::CartesianIndex) =
    checkbounds_indices(Bool, inds, I.I)
```
-/
def checkindexCartesian {AX : Type} (checkboundsIndices : List AX → CI → Bool) (inds : List AX) (I : CI) : Bool :=
  checkboundsIndices inds I

/--
Julia source: base/multidimensional.jl:766-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline checkindex(::Type{Bool}, inds::Tuple, i::AbstractRange{<:CartesianIndex}) =
    isempty(i) | (checkindex(Bool, inds, first(i)) && checkindex(Bool, inds, last(i)))
```
-/
def checkindexCartesianRange {AX R : Type} (isempty : R → Bool) (first last : R → CI)
    (checkindex : List AX → CI → Bool) (inds : List AX) (i : R) : Bool :=
  Bool.or (isempty i) (checkindex inds (first i) && checkindex inds (last i))

/--
Julia source: base/multidimensional.jl:772-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(A::Array, i1::Union{Integer, CartesianIndex}, I::Union{Integer, CartesianIndex}...) =
    A[to_indices(A, (i1, I...))...]
```
-/
def arrayGetMixed {A I V : Type} (toIndices : A → List I → Result CI) (getindex : A → CI → Result V)
    (a : A) (head : I) (tail : List I) : Result V := do getindex a (← toIndices a (head :: tail))

/--
Julia source: base/multidimensional.jl:774-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds setindex!(A::Array, v, i1::Union{Integer, CartesianIndex}, I::Union{Integer, CartesianIndex}...) =
    (A[to_indices(A, (i1, I...))...] = v; A)
```
-/
def arraySetMixed {A I V : Type} (toIndices : A → List I → Result CI) (setindex : A → V → CI → Result A)
    (a : A) (v : V) (head : I) (tail : List I) : Result A := do
  setindex a v (← toIndices a (head :: tail))

/--
Julia source: base/multidimensional.jl:779-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractArray{CartesianIndex{N}}) where {N} =
    checkbounds_indices(Bool, axes(A), (i,))
```
-/
def checkboundsCartesianArray {A AX I : Type} (axes : A → List AX)
    (checkboundsIndices : List AX → List I → Bool) (a : A) (i : I) : Bool := checkboundsIndices (axes a) [i]

/--
Julia source: base/multidimensional.jl:782-785 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{AbstractArray{CartesianIndex{N}},Vararg}) where N
    inds1, rest = IteratorsMD.split(inds, Val(N))
    checkindex(Bool, inds1, I[1]) && checkbounds_indices(Bool, rest, tail(I))
end
```
-/
def checkboundsIndicesCartesianArray {AX I R : Type} (checkindex : List AX → I → Bool)
    (checkboundsIndices : List AX → List R → Bool) (N : Nat) (inds : List AX) (head : I) (tail : List R) : Bool :=
  let inds1 := inds.take N
  let rest := inds.drop N
  checkindex inds1 head && checkboundsIndices rest tail

/--
Julia source: base/multidimensional.jl:786-787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline checkindex(::Type{Bool}, inds::Tuple, I::CartesianIndices) =
    checkbounds_indices(Bool, inds, I.indices)
```
-/
def checkindexCartesianIndices {AX : Type} (checkboundsIndices : List AX → CIs → Bool)
    (inds : List AX) (I : CIs) : Bool := checkboundsIndices inds I

/--
Julia source: base/multidimensional.jl:792-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_ndims(i1, I...) = (true, index_ndims(I...)...)
```
-/
def indexNdimsScalar {I : Type} (indexNdims : List I → List Bool) (_head : I) (tail : List I) : List Bool :=
  true :: indexNdims tail

/--
Julia source: base/multidimensional.jl:793-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function index_ndims(i1::CartesianIndex, I...)
    (map(Returns(true), i1.I)..., index_ndims(I...)...)
end
```
-/
def indexNdimsCartesian {I : Type} (indexNdims : List I → List Bool) (head : CI) (tail : List I) : List Bool :=
  head.map (fun _ => true) ++ indexNdims tail

/--
Julia source: base/multidimensional.jl:796-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function index_ndims(i1::AbstractArray{CartesianIndex{N}}, I...) where N
    (ntuple(Returns(true), Val(N))..., index_ndims(I...)...)
end
```
-/
def indexNdimsCartesianArray {I A : Type} (indexNdims : List I → List Bool) (N : Nat) (_head : A) (tail : List I) : List Bool :=
  List.replicate N true ++ indexNdims tail

/--
Julia source: base/multidimensional.jl:799-799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
index_ndims() = ()
```
-/
def indexNdimsEmpty : List Bool := []

/--
Julia source: base/multidimensional.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_dimsum(i1, I...) = (index_dimsum(I...)...,)
```
-/
def indexDimsumScalar {I : Type} (indexDimsum : List I → List Bool) (_head : I) (tail : List I) : List Bool := indexDimsum tail

/--
Julia source: base/multidimensional.jl:804-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_dimsum(::Colon, I...) = (true, index_dimsum(I...)...)
```
-/
def indexDimsumColon {I : Type} (indexDimsum : List I → List Bool) (tail : List I) : List Bool := true :: indexDimsum tail

/--
Julia source: base/multidimensional.jl:805-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_dimsum(::AbstractArray{Bool}, I...) = (true, index_dimsum(I...)...)
```
-/
def indexDimsumMask {I A : Type} (indexDimsum : List I → List Bool) (_mask : A) (tail : List I) : List Bool := true :: indexDimsum tail

/--
Julia source: base/multidimensional.jl:806-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function index_dimsum(::AbstractArray{<:Any,N}, I...) where N
    (ntuple(Returns(true), Val(N))..., index_dimsum(I...)...)
end
```
-/
def indexDimsumArray {I A : Type} (indexDimsum : List I → List Bool) (N : Nat) (_a : A) (tail : List I) : List Bool :=
  List.replicate N true ++ indexDimsum tail

/--
Julia source: base/multidimensional.jl:809-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
index_dimsum() = ()
```
-/
def indexDimsumEmpty : List Bool := []

/--
Julia source: base/multidimensional.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
index_lengths() = ()
```
-/
def indexLengthsEmpty {A : Type} : List A := []

/--
Julia source: base/multidimensional.jl:813-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_lengths(::Real, rest...) = (1, index_lengths(rest...)...)
```
-/
def indexLengthsScalar {Z I : Type} (indexLengths : List I → CI) (_head : Z) (rest : List I) : CI := int 1 :: indexLengths rest

/--
Julia source: base/multidimensional.jl:814-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_lengths(A::AbstractArray, rest...) = (length(A), index_lengths(rest...)...)
```
-/
def indexLengthsArray {A I : Type} (length : A → I64) (indexLengths : List I → CI) (a : A) (rest : List I) : CI :=
  length a :: indexLengths rest

/--
Julia source: base/multidimensional.jl:818-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
index_shape() = ()
```
-/
def indexShapeEmpty {A : Type} : List A := []

/--
Julia source: base/multidimensional.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_shape(::Real, rest...) = index_shape(rest...)
```
-/
def indexShapeScalar {Z I AX : Type} (indexShape : List I → List AX) (_head : Z) (rest : List I) : List AX := indexShape rest

/--
Julia source: base/multidimensional.jl:820-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_shape(A::AbstractArray, rest...) = (axes(A)..., index_shape(rest...)...)
```
-/
def indexShapeArray {A I AX : Type} (axes : A → List AX) (indexShape : List I → List AX) (a : A) (rest : List I) : List AX :=
  axes a ++ indexShape rest

/--
Julia source: base/multidimensional.jl:822-822 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
index_sizes() = ()
```
-/
def indexSizesEmpty {A : Type} : List A := []

/--
Julia source: base/multidimensional.jl:823-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_sizes(::Real, rest...) = index_sizes(rest...)
```
-/
def indexSizesScalar {Z I : Type} (indexSizes : List I → CI) (_head : Z) (rest : List I) : CI := indexSizes rest

/--
Julia source: base/multidimensional.jl:824-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline index_sizes(A::AbstractArray, rest...) = (size(A)..., index_sizes(rest...)...)
```
-/
def indexSizesArray {A I : Type} (size : A → CI) (indexSizes : List I → CI) (a : A) (rest : List I) : CI := size a ++ indexSizes rest

/--
Julia source: base/multidimensional.jl:837-837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    LogicalIndex{T,A}(mask::A) where {T,A<:AbstractArray{Bool}} = new(mask, count(mask))
```
-/
def logicalInner {M : Type} (count : M → Result I64) (mask : M) : Result (LogicalIndex M) := do
  return ⟨mask, ← count mask⟩

/--
Julia source: base/multidimensional.jl:839-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogicalIndex(mask::AbstractVector{Bool}) = LogicalIndex{Int, typeof(mask)}(mask)
```
-/
def logicalVector {M : Type} (construct : M → Result (LogicalIndex M)) (mask : M) : Result (LogicalIndex M) := construct mask

/--
Julia source: base/multidimensional.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogicalIndex(mask::AbstractArray{Bool, N}) where {N} = LogicalIndex{CartesianIndex{N}, typeof(mask)}(mask)
```
-/
def logicalArray {M : Type} (construct : M → Result (LogicalIndex M)) (mask : M) : Result (LogicalIndex M) := construct mask

/--
Julia source: base/multidimensional.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogicalIndex{Int}(mask::AbstractArray) = LogicalIndex{Int, typeof(mask)}(mask)
```
-/
def logicalExplicitInt {M : Type} (construct : M → Result (LogicalIndex M)) (mask : M) : Result (LogicalIndex M) := construct mask

/--
Julia source: base/multidimensional.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(L::LogicalIndex) = (L.sum,)
```
-/
def logicalSize {M : Type} (L : LogicalIndex M) : CI := [L.sum]

/--
Julia source: base/multidimensional.jl:843-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
collect(L::LogicalIndex) = [i for i in L]
```
-/
def logicalCollect {M K : Type} (iterate : LogicalIndex M → LR (List K)) (L : LogicalIndex M) : LR (List K) := do
  let mut result := []
  for i in (← iterate L) do result := result ++ [i]
  return result

/--
Julia source: base/multidimensional.jl:844-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, r::LogicalIndex) = print(io,collect(r))
```
-/
def logicalShow {IO M K : Type} (collect : LogicalIndex M → LR (List K))
    (print : IO → List K → LR IO) (io : IO) (r : LogicalIndex M) : LR IO := do print io (← collect r)

/--
Julia source: base/multidimensional.jl:845-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_array(io::IO, X::LogicalIndex) = print_array(io, collect(X))
```
-/
def logicalPrintArray {IO M K : Type} (collect : LogicalIndex M → LR (List K))
    (printArray : IO → List K → LR IO) (io : IO) (X : LogicalIndex M) : LR IO := do printArray io (← collect X)

/--
Julia source: base/multidimensional.jl:851-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(L::LogicalIndex{Int})
    r = LinearIndices(L.mask)
    iterate(L, (1, r))
end
```
-/
def logicalIterateIntFirst {M R O : Type} (linearIndices : M → LR R)
    (iterate : LogicalIndex M → I64 × R → LR O) (L : LogicalIndex M) : LR O := do
  let r ← linearIndices L.mask
  iterate L (int 1, r)

/--
Julia source: base/multidimensional.jl:855-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(L::LogicalIndex{<:CartesianIndex})
    r = CartesianIndices(axes(L.mask))
    iterate(L, (1, r))
end
```
-/
def logicalIterateCartesianFirst {M AX R O : Type} (axes : M → AX) (cartesianIndices : AX → LR R)
    (iterate : LogicalIndex M → I64 × R → LR O) (L : LogicalIndex M) : LR O := do
  let r ← cartesianIndices (axes L.mask)
  iterate L (int 1, r)

/--
Julia source: base/multidimensional.jl:859-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(L::LogicalIndex, s)
    # We're looking for the n-th true element, using iterator r at state i
    n = s[1]
    n > length(L) && return nothing
    #unroll once to help inference, cf issue #29418
    idx, i = iterate(tail(s)...)::Tuple{Any,Any}
    s = (n+1, s[2], i)
    L.mask[idx] && return (idx, s)
    while true
        idx, i = iterate(tail(s)...)::Tuple{Any,Any}
        s = (n+1, s[2], i)
        L.mask[idx] && return (idx, s)
    end
end
```
-/
def logicalIterate {M K S : Type} (readMask : M → K → LR Bool) (L : LogicalIndex M)
    (n : I64) (trace : List (K × S)) : LR (Option (K × (I64 × S))) :=
  if n > L.sum then .ok none else scan trace
where
  scan : List (K × S) → LR (Option (K × (I64 × S)))
    | [] => .error .typeError
    | (idx, i) :: rest => do
      let s := (n + int 1, i)
      if ← readMask L.mask idx then return some (idx, s)
      else scan rest

/--
Julia source: base/multidimensional.jl:874-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(L::LogicalIndex{Int,<:BitArray})
    L.sum == 0 && return nothing
    Bc = L.mask.chunks
    return iterate(L, (1, 1, (), @inbounds Bc[1]))
end
```
-/
def logicalBitIntFirst {M C O : Type} (chunks : M → List C)
    (iterate : LogicalIndex M → I64 × I64 × CI × C → Result O) (L : LogicalIndex M) : Result (Option O) := do
  if L.sum == int 0 then return none
  let Bc := chunks L.mask
  return some (← iterate L (int 1, int 1, [], ← tupleGet Bc (int 1)))

/--
Julia source: base/multidimensional.jl:879-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(L::LogicalIndex{<:CartesianIndex,<:BitArray})
    L.sum == 0 && return nothing
    Bc = L.mask.chunks
    irest = ntuple(one, ndims(L.mask)-1)
    return iterate(L, (1, 1, irest, @inbounds Bc[1]))
end
```
-/
def logicalBitCartesianFirst {M C O : Type} (chunks : M → List C) (ndims : M → I64)
    (iterate : LogicalIndex M → I64 × I64 × CI × C → Result O) (L : LogicalIndex M) : Result (Option O) := do
  if L.sum == int 0 then return none
  let Bc := chunks L.mask
  let irest := List.replicate ((ndims L.mask - int 1).val.toNat) (int 1)
  return some (← iterate L (int 1, int 1, irest, ← tupleGet Bc (int 1)))

/--
Julia source: base/multidimensional.jl:885-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(L::LogicalIndex{<:Any,<:BitArray}, (i1, Bi, irest, c))
    Bc = L.mask.chunks
    while c == 0
        Bi >= length(Bc) && return nothing
        i1 += 64
        @inbounds c = Bc[Bi+=1]
    end
    tz = trailing_zeros(c)
    c = _blsr(c)
    i1, irest = _overflowind(i1 + tz, irest, size(L.mask))
    return eltype(L)(i1, irest...), (i1 - tz, Bi, irest, c)
end
```
-/
def logicalBitIterate {M K C : Type} [BEq C] (zero : C) (chunks : M → List C)
    (trailingZeros : C → I64) (clearLowBit : C → C) (size : M → CI)
    (overflowind : I64 → CI → CI → Result (I64 × CI)) (construct : I64 → CI → Result K)
    (L : LogicalIndex M) (i1 Bi : I64) (irest : CI) (c : C) : Result (Option (K × (I64 × I64 × CI × C))) := do
  let Bc := chunks L.mask
  match ← scan Bc (Bc.drop Bi.val.toNat) i1 Bi c with
  | none => return none
  | some (i1, Bi, c) =>
    let tz := trailingZeros c
    let c := clearLowBit c
    let (i1, irest) ← overflowind (i1 + tz) irest (size L.mask)
    return some (← construct i1 irest, (i1 - tz, Bi, irest, c))
where
  scan (Bc : List C) : List C → I64 → I64 → C → Result (Option (I64 × I64 × C))
    | rest, i1, Bi, c =>
      if c != zero then .ok (some (i1, Bi, c))
      else if Bi.val ≥ Bc.length then .ok none
      else match rest with
      | [] => .error .boundsError
      | c :: rest => scan Bc rest (i1 + int 64) (Bi + int 1) c

/--
Julia source: base/multidimensional.jl:900-900 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, A::AbstractArray, i::LogicalIndex) = checkbounds(Bool, A, i.mask)
```
-/
def checkboundsLogical {A M : Type} (checkbounds : A → M → Bool) (a : A) (i : LogicalIndex M) : Bool :=
  checkbounds a i.mask

/--
Julia source: base/multidimensional.jl:902-902 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, i::LogicalIndex) = checkindex(Bool, inds, i.mask)
```
-/
def checkindexLogicalAxis {AX M : Type} (checkindex : AX → M → Bool) (inds : AX) (i : LogicalIndex M) : Bool := checkindex inds i.mask

/--
Julia source: base/multidimensional.jl:903-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::Tuple, i::LogicalIndex) = checkindex(Bool, inds, i.mask)
```
-/
def checkindexLogicalTuple {AX M : Type} (checkindex : AX → M → Bool) (inds : AX) (i : LogicalIndex M) : Bool := checkindex inds i.mask

/--
Julia source: base/multidimensional.jl:907-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractArray{Bool}) =
    checkbounds_indices(Bool, axes(A), (i,))
```
-/
def checkboundsMask {A AX M : Type} (axes : A → AX) (checkboundsIndices : AX → List M → Bool)
    (a : A) (i : M) : Bool := checkboundsIndices (axes a) [i]

/--
Julia source: base/multidimensional.jl:910-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractVector{Bool}) =
    checkindex(Bool, eachindex(IndexLinear(), A), i)
```
-/
def checkboundsVectorMask {A AX M : Type} (eachindexLinear : A → AX) (checkindex : AX → M → Bool)
    (a : A) (i : M) : Bool := checkindex (eachindexLinear a) i

/--
Julia source: base/multidimensional.jl:912-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{AbstractArray{Bool},Vararg})
    inds1, rest = IteratorsMD.split(inds, Val(ndims(I[1])))
    checkindex(Bool, inds1, I[1]) && checkbounds_indices(Bool, rest, tail(I))
end
```
-/
def checkboundsIndicesMask {AX M I : Type} (ndims : M → Nat) (checkindex : List AX → M → Bool)
    (checkboundsIndices : List AX → List I → Bool) (inds : List AX) (head : M) (tail : List I) : Bool :=
  let inds1 := inds.take (ndims head)
  let rest := inds.drop (ndims head)
  checkindex inds1 head && checkboundsIndices rest tail

/--
Julia source: base/multidimensional.jl:916-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, I::AbstractVector{Bool}) = axes1(I) == inds
```
-/
def checkindexVectorMask {AX M : Type} [BEq AX] (axes1 : M → AX) (inds : AX) (mask : M) : Bool := axes1 mask == inds

/--
Julia source: base/multidimensional.jl:917-917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::AbstractUnitRange, I::AbstractRange{Bool}) = axes1(I) == inds
```
-/
def checkindexRangeMask {AX M : Type} [BEq AX] (axes1 : M → AX) (inds : AX) (mask : M) : Bool := axes1 mask == inds

/--
Julia source: base/multidimensional.jl:918-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkindex(::Type{Bool}, inds::Tuple, I::AbstractArray{Bool}) = _check_boolean_axes(inds, axes(I))
```
-/
def checkindexMaskTuple {AX M : Type} (axes : M → List AX)
    (checkBooleanAxes : List AX → List AX → Bool) (inds : List AX) (mask : M) : Bool := checkBooleanAxes inds (axes mask)

/--
Julia source: base/multidimensional.jl:919-919 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_check_boolean_axes(inds::Tuple, axes::Tuple) = (inds[1] == axes[1]) && _check_boolean_axes(tail(inds), tail(axes))
```
-/
def checkBooleanAxesCons {AX : Type} [BEq AX] (recurse : List AX → List AX → Bool)
    (ih ah : AX) (it leftTail : List AX) : Bool := ih == ah && recurse it leftTail

/--
Julia source: base/multidimensional.jl:920-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_check_boolean_axes(::Tuple{}, axes::Tuple) = all(==(OneTo(1)), axes)
```
-/
def checkBooleanAxesEmpty {AX : Type} [BEq AX] (oneToOne : AX) (axes : List AX) : Bool := axes.all (· == oneToOne)

/--
Julia source: base/multidimensional.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ensure_indexable(I::Tuple{}) = ()
```
-/
def ensureIndexableEmpty {I : Type} : List I := []

/--
Julia source: base/multidimensional.jl:923-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ensure_indexable(I::Tuple{Any, Vararg{Any}}) = (I[1], ensure_indexable(tail(I))...)
```
-/
def ensureIndexableCons {I : Type} (ensure : List I → List I) (head : I) (tail : List I) : List I := head :: ensure tail

/--
Julia source: base/multidimensional.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ensure_indexable(I::Tuple{LogicalIndex, Vararg{Any}}) = (collect(I[1]), ensure_indexable(tail(I))...)
```
-/
def ensureIndexableLogical {M C I O : Type} (collect : LogicalIndex M → Result C)
    (ensure : List I → Result (List O)) (head : LogicalIndex M) (tail : List I) : Result (C × List O) := do
  return (← collect head, ← ensure tail)

/--
Julia source: base/multidimensional.jl:928-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline to_indices(A, I::Tuple{Vararg{Union{Integer, CartesianIndex}}}) = to_indices(A, (), I)
```
-/
def toIndicesMixed {A I O AX : Type} (toIndices : A → List AX → List I → Result O) (a : A) (I : List I) : Result O :=
  toIndices a [] I

/--
Julia source: base/multidimensional.jl:929-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(I::Tuple{CartesianIndex{0}, Vararg}) = (@inline; _drop_zerodim(tail(I)))
```
-/
def dropZeroDim {I O : Type} (drop : List I → O) (_head : CI) (tail : List I) : O := drop tail

/--
Julia source: base/multidimensional.jl:932-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function to_indices(A, inds, I::Tuple{CartesianIndex{N}, Vararg}) where N
    _, indstail = IteratorsMD.split(inds, Val(N))
    (map(Fix1(to_index, A), I[1].I)..., to_indices(A, indstail, tail(I))...)
end
```
-/
def toIndicesCartesian {A AX I O : Type} (toIndex : A → I64 → Result O)
    (toIndices : A → List AX → List I → Result (List O))
    (a : A) (inds : List AX) (head : CI) (tail : List I) : Result (List O) := do
  let indstail := inds.drop head.length
  return (← head.mapM (toIndex a)) ++ (← toIndices a indstail tail)

/--
Julia source: base/multidimensional.jl:937-940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function to_indices(A, inds, I::Tuple{AbstractArray{CartesianIndex{N}}, Vararg}) where N
    _, indstail = IteratorsMD.split(inds, Val(N))
    (to_index(A, I[1]), to_indices(A, indstail, tail(I))...)
end
```
-/
def toIndicesCartesianArray {A AX H I O : Type} (toIndex : A → H → Result O)
    (toIndices : A → List AX → List I → Result (List O)) (N : Nat)
    (a : A) (inds : List AX) (head : H) (tail : List I) : Result (List O) := do
  let indstail := inds.drop N
  return (← toIndex a head) :: (← toIndices a indstail tail)

/--
Julia source: base/multidimensional.jl:942-945 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function to_indices(A, inds, I::Tuple{AbstractArray{Bool, N}, Vararg}) where N
    _, indstail = IteratorsMD.split(inds, Val(N))
    (to_index(A, I[1]), to_indices(A, indstail, tail(I))...)
end
```
-/
def toIndicesMask {A AX H I O : Type} (toIndex : A → H → Result O)
    (toIndices : A → List AX → List I → Result (List O)) (N : Nat)
    (a : A) (inds : List AX) (head : H) (tail : List I) : Result (List O) := do
  let indstail := inds.drop N
  return (← toIndex a head) :: (← toIndices a indstail tail)

/--
Julia source: base/multidimensional.jl:947-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline to_indices(A, I::Tuple{AbstractArray{Bool}}) = (_maybe_linear_logical_index(IndexStyle(A), A, I[1]),)
```
-/
def toIndicesSingleMask {S A M O : Type} (indexStyle : A → S) (maybeLinear : S → A → M → Result O)
    (a : A) (mask : M) : Result (List O) := do return [← maybeLinear (indexStyle a) a mask]

/--
Julia source: base/multidimensional.jl:948-948 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_linear_logical_index(::IndexStyle, A, i) = to_index(A, i)
```
-/
def maybeLinearLogicalDefault {A I O : Type} (toIndex : A → I → Result O) (a : A) (i : I) : Result O := toIndex a i

/--
Julia source: base/multidimensional.jl:949-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_linear_logical_index(::IndexLinear, A, i) = LogicalIndex{Int}(i)
```
-/
def maybeLinearLogicalLinear {A M : Type} (construct : M → Result (LogicalIndex M)) (_a : A) (i : M) : Result (LogicalIndex M) := construct i

/--
Julia source: base/multidimensional.jl:952-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline to_indices(A, inds, I::Tuple{Colon, Vararg}) =
    (uncolon(inds), to_indices(A, Base.safe_tail(inds), tail(I))...)
```
-/
def toIndicesColon {A AX I O : Type} (uncolon : List AX → O)
    (toIndices : A → List AX → List I → Result (List O)) (a : A) (inds : List AX) (tail : List I) : Result (List O) := do
  return uncolon inds :: (← toIndices a inds.tail tail)

/--
Julia source: base/multidimensional.jl:955-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uncolon(::Tuple{}) = Slice(OneTo(1))
```
-/
def uncolonEmpty {AX S : Type} (oneTo : I64 → AX) (slice : AX → S) : S := slice (oneTo (int 1))

/--
Julia source: base/multidimensional.jl:956-956 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uncolon(inds::Tuple) = Slice(inds[1])
```
-/
def uncolonCons {AX S : Type} (slice : AX → S) (head : AX) (_tail : List AX) : S := slice head

/--
Julia source: base/multidimensional.jl:964-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds _prechecked_iterate(iter) = iterate(iter)
```
-/
def precheckedFirst {R O : Type} (iterate : R → Result O) (iter : R) : Result O := iterate iter

/--
Julia source: base/multidimensional.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds _prechecked_iterate(iter, state) = iterate(iter, state)
```
-/
def precheckedNext {R S O : Type} (iterate : R → S → Result O) (iter : R) (state : S) : Result O := iterate iter state

/--
Julia source: base/multidimensional.jl:967-967 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prechecked_iterate(iter::AbstractUnitRange) = first(iter), first(iter)
```
-/
def precheckedUnitFirst {R Z : Type} (first : R → Z) (iter : R) : Z × Z := (first iter, first iter)

/--
Julia source: base/multidimensional.jl:968-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prechecked_iterate(iter::AbstractUnitRange, i)
    i′ = convert(eltype(iter), i + step(iter))
    return i′, i′
end
```
-/
def precheckedUnitNext {R Z S : Type} (step : R → S) (add : Z → S → Result Z)
    (convert : Z → Result Z) (iter : R) (i : Z) : Result (Z × Z) := do
  let i' ← convert (← add i (step iter))
  return (i', i')

/--
Julia source: base/multidimensional.jl:972-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prechecked_iterate(iter::LinearIndices) = first(iter), first(iter)
```
-/
def precheckedLinearFirst {R : Type} (first : R → I64) (iter : R) : I64 × I64 := (first iter, first iter)

/--
Julia source: base/multidimensional.jl:973-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prechecked_iterate(iter::LinearIndices, i)
    i′ = i + 1
    return i′, i′
end
```
-/
def precheckedLinearNext {R : Type} (_iter : R) (i : I64) : I64 × I64 :=
  let i' := i + int 1
  (i', i')

/--
Julia source: base/multidimensional.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prechecked_iterate(iter::CartesianIndices) = first(iter), first(iter)
```
-/
def precheckedCartesianFirst (iter : CIs) : CI × CI :=
  (cartesianIndicesFirst iter, cartesianIndicesFirst iter)

/--
Julia source: base/multidimensional.jl:978-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prechecked_iterate(iter::CartesianIndices, i::CartesianIndex)
    i′ = IteratorsMD.inc(i.I, iter.indices)
    return i′, i′
end
```
-/
def precheckedCartesianNext (inc : CI → CIs → CI) (iter : CIs) (i : CI) : CI × CI :=
  let i' := inc i iter
  (i', i')

/--
Julia source: base/multidimensional.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prechecked_iterate(iter::SCartesianIndices2) = first(iter), first(iter)
```
-/
def precheckedSpecialFirst {R Z : Type} (first : R → Z) (iter : R) : Z × Z := (first iter, first iter)

/--
Julia source: base/multidimensional.jl:983-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prechecked_iterate(iter::SCartesianIndices2{K}, (;i, j)) where {K}
    I = i < K ? SCartesianIndex2{K}(i + 1, j) : SCartesianIndex2{K}(1, j + 1)
    return I, I
end
```
-/
def precheckedSpecialNext {S : Type} (construct : I64 → I64 → S) (K i j : I64) : S × S :=
  let I := if i < K then construct (i + int 1) j else construct (int 1) (j + int 1)
  (I, I)

/--
Julia source: base/multidimensional.jl:989-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(x::Union{Number,AbstractChar}, ::CartesianIndex{0}) = x
```
-/
def getindexScalarZero {V : Type} (x : V) : V := x

/--
Julia source: base/multidimensional.jl:990-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::Tuple,  i::CartesianIndex{1}) = getindex(t, i.I[1])
```
-/
def getindexTupleCartesian {T V : Type} (getindex : T → I64 → Result V) (t : T) (i : I64) : Result V := getindex t i

/--
Julia source: base/multidimensional.jl:995-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _getindex(l::IndexStyle, A::AbstractArray, I::Union{Real, AbstractArray}...)
    @boundscheck checkbounds(A, I...)
    return _unsafe_getindex(l, _maybe_reshape(l, A, I...), I...)
end
```
-/
def getindexAbstract {m : Type → Type} [Monad m] {S A I V : Type} (checkbounds : A → List I → m Unit)
    (maybeReshape : S → A → List I → m A) (unsafeGetindex : S → A → List I → m V)
    (style : S) (a : A) (I : List I) : m V := do
  checkbounds a I
  unsafeGetindex style (← maybeReshape style a I) I

/--
Julia source: base/multidimensional.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexLinear, A::AbstractArray, I...) = A
```
-/
def maybeReshapeLinear {A I : Type} (a : A) (_I : List I) : A := a

/--
Julia source: base/multidimensional.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_maybe_reshape(::IndexCartesian, A::AbstractVector, I...) = A
```
-/
def maybeReshapeVector {A I : Type} (a : A) (_I : List I) : A := a

/--
Julia source: base/multidimensional.jl:1002-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _maybe_reshape(::IndexCartesian, A::AbstractArray, I...) = __maybe_reshape(A, index_ndims(I...))
```
-/
def maybeReshapeCartesian {m : Type → Type} [Monad m] {A I : Type} (indexNdims : List I → List Bool)
    (reshape : A → List Bool → m A) (a : A) (I : List I) : m A := reshape a (indexNdims I)

/--
Julia source: base/multidimensional.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline __maybe_reshape(A::AbstractArray{T,N}, ::NTuple{N,Any}) where {T,N} = A
```
-/
def reshapeMatchingRank {A : Type} (a : A) (_ndims : Nat) : A := a

/--
Julia source: base/multidimensional.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline __maybe_reshape(A::AbstractArray, ::NTuple{N,Any}) where {N} = reshape(A, Val(N))
```
-/
def reshapeDifferentRank {m : Type → Type} [Monad m] {A : Type} (reshape : A → Nat → m A) (a : A) (N : Nat) : m A := reshape a N

/--
Julia source: base/multidimensional.jl:1006-1013 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unsafe_getindex(::IndexStyle, A::AbstractArray, I::Vararg{Union{Real, AbstractArray}, N}) where N
    # This is specifically not inlined to prevent excessive allocations in type unstable code
    shape = index_shape(I...)
    dest = similar(A, shape)
    map(length, axes(dest)) == map(length, shape) || throw_checksize_error(dest, shape)
    _unsafe_getindex!(dest, A, I...) # usually a generated function, don't allow it to impact inference result
    return dest
end
```
-/
def unsafeGetindex {m : Type → Type} [Monad m] {S A D I AX : Type} [BEq AX] (indexShape : List I → List AX)
    (similar : A → List AX → m D) (axes : D → List AX) (length : AX → I64)
    (throwChecksize : D → List AX → m Unit) (unsafeGetindexBang : D → A → List I → m D)
    (_style : S) (a : A) (I : List I) : m D := do
  let shape := indexShape I
  let dest ← similar a shape
  if (axes dest).map length != shape.map length then throwChecksize dest shape
  unsafeGetindexBang dest a I

/--
Julia source: base/multidimensional.jl:1015-1027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _generate_unsafe_getindex!_body(N::Int)
    quote
        @inline
        D = eachindex(dest)
        Dy = _prechecked_iterate(D)
        @inbounds @nloops $N j d->I[d] begin
            (idx, state) = Dy::NTuple{2,Any}
            dest[idx] = @ncall $N getindex src j
            Dy = _prechecked_iterate(D, state)
        end
        return dest
    end
end
```
-/
def generateUnsafeGetindexBody {m : Type → Type} [Monad m] {Dest Src I V K S Index : Type}
    (eachindex : Dest → List K)
    (precheckedFirst : List K → m (K × S)) (precheckedNext : List K → S → m (K × S))
    (indexElements : I → List Index) (getindex : Src → List Index → m V) (setindex : Dest → V → K → m Dest)
    (N : I64) (dest : Dest) (src : Src) (I : List I) : m Dest := do
  let D := eachindex dest
  let Dy ← precheckedFirst D
  gatherLoop D precheckedNext getindex setindex src (columnMajor ((takeN I N.val.toNat).map indexElements)) dest Dy
/--
Julia source: base/multidimensional.jl:1030-1032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray}, N}) where N
    _generate_unsafe_getindex!_body(N)
end
```
-/
def unsafeGetindexBang {m : Type → Type} [Monad m] {Dest Src I : Type}
    (generate : I64 → Dest → Src → List I → m Dest)
    (N : I64) (dest : Dest) (src : Src) (I : List I) : m Dest := generate N dest src I

/--
Julia source: base/multidimensional.jl:1035-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray},1})
    $(_generate_unsafe_getindex!_body(1))
end
```
-/
def unsafeGetindexBangOne {m : Type → Type} [Monad m] {Dest Src I : Type}
    (generate : I64 → Dest → Src → List I → m Dest)
    (dest : Dest) (src : Src) (I : List I) : m Dest := generate (int 1) dest src I

/--
Julia source: base/multidimensional.jl:1039-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray},2})
    $(_generate_unsafe_getindex!_body(2))
end
```
-/
def unsafeGetindexBangTwo {m : Type → Type} [Monad m] {Dest Src I : Type}
    (generate : I64 → Dest → Src → List I → m Dest)
    (dest : Dest) (src : Src) (I : List I) : m Dest := generate (int 2) dest src I

/--
Julia source: base/multidimensional.jl:1043-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_checksize_error(A, sz) = throw(DimensionMismatch("output array is the wrong size; expected $sz, got $(size(A))"))
```
-/
def throwChecksizeError {A SZ : Type} (a : A) (sz : SZ)
    (size : A → String := fun _ => "") (showSz : SZ → String := fun _ => "") : Result α :=
  .error (.dimensionMismatch ("output array is the wrong size; expected " ++ showSz sz ++ ", got " ++ size a))

/--
Julia source: base/multidimensional.jl:1046-1051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _setindex!(l::IndexStyle, A::AbstractArray, x, I::Union{Real, AbstractArray}...)
    @inline
    @boundscheck checkbounds(A, I...)
    _unsafe_setindex!(l, _maybe_reshape(l, A, I...), x, I...)
    A
end
```
-/
def setindexAbstract {m : Type → Type} [Monad m] {S A X I : Type} (checkbounds : A → List I → m Unit)
    (maybeReshape : S → A → List I → m A) (unsafeSetindex : S → A → X → List I → m A)
    (style : S) (a : A) (x : X) (I : List I) : m A := do
  checkbounds a I
  let _ ← unsafeSetindex style (← maybeReshape style a I) x I
  return a

/--
Julia source: base/multidimensional.jl:1053-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _generate_unsafe_setindex!_body(N::Int)
    quote
        x′ = unalias(A, x)
        @nexprs $N d->(I_d = unalias(A, I[d]))
        setindex_shape_check(x′, @ncall $N index_sizes I)
        X = eachindex(x′)
        Xy = _prechecked_iterate(X)
        @inbounds @nloops $N i d->I_d begin
            (idx, state) = Xy::NTuple{2,Any}
            @ncall $N setindex! A x′[idx] i
            Xy = _prechecked_iterate(X, state)
        end
        A
    end
end
```
-/
def generateUnsafeSetindexBody {m : Type → Type} [Monad m] {A X I V K S Index : Type} (unaliasValue : A → X → m X)
    (unaliasIndex : A → I → m I) (indexSizes : List I → CI) (shapeCheck : X → CI → m Unit)
    (eachindex : X → List K) (precheckedFirst : List K → m (K × S))
    (precheckedNext : List K → S → m (K × S)) (indexElements : I → List Index)
    (getindex : X → K → m V) (setindex : A → V → List Index → m A)
    (_N : I64) (a : A) (x : X) (I : List I) : m A := do
  let x' ← unaliasValue a x
  let I' ← I.mapM (unaliasIndex a)
  shapeCheck x' (indexSizes I')
  let X := eachindex x'
  let mut Xy ← precheckedFirst X
  let mut a := a
  for i in columnMajor (I'.map indexElements) do
    let (idx, state) := Xy
    a ← setindex a (← getindex x' idx) i
    Xy ← precheckedNext X state
  return a

/--
Julia source: base/multidimensional.jl:1069-1071 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray}, N}) where N
    _generate_unsafe_setindex!_body(N)
end
```
-/
def unsafeSetindexBang {m : Type → Type} [Monad m] {A X I S : Type} (generate : I64 → A → X → List I → m A)
    (N : I64) (_style : S) (a : A) (x : X) (I : List I) : m A := generate (N) a x I

/--
Julia source: base/multidimensional.jl:1073-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray},1})
    $(_generate_unsafe_setindex!_body(1))
end
```
-/
def unsafeSetindexBangOne {m : Type → Type} [Monad m] {A X I S : Type} (generate : I64 → A → X → List I → m A)
    (_style : S) (a : A) (x : X) (I : List I) : m A := generate (int 1) a x I

/--
Julia source: base/multidimensional.jl:1077-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray},2})
    $(_generate_unsafe_setindex!_body(2))
end
```
-/
def unsafeSetindexBangTwo {m : Type → Type} [Monad m] {A X I S : Type} (generate : I64 → A → X → List I → m A)
    (_style : S) (a : A) (x : X) (I : List I) : m A := generate (int 2) a x I

/--
Julia source: base/multidimensional.jl:1081-1081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
diff(a::AbstractVector) = diff(a, dims=1)
```
-/
def diffVector {A O : Type} (diff : A → I64 → Result O) (a : A) : Result O := diff a (int 1)

/--
Julia source: base/multidimensional.jl:1113-1122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function diff(a::AbstractArray{T,N}; dims::Integer) where {T,N}
    require_one_based_indexing(a)
    1 <= dims <= N || throw(ArgumentError("dimension $dims out of range (1:$N)"))

    r = axes(a)
    r0 = ntuple(i -> i == dims ? UnitRange(1, last(r[i]) - 1) : UnitRange(r[i]), N)
    r1 = ntuple(i -> i == dims ? UnitRange(2, last(r[i])) : UnitRange(r[i]), N)

    return view(a, r1...) .- view(a, r0...)
end
```
-/
def diffArray {A AX V O Z : Type} (requireOneBased : A → Result Unit) (axes : A → List AX)
    (last : AX → I64) (unitRange : I64 → I64 → AX) (toUnitRange : AX → AX)
    (view : A → List AX → Result V) (subtract : V → V → Result O) (value : Z → Int)
    (N : Nat) (a : A) (dims : Z) : Result O := do
  requireOneBased a
  if !(1 ≤ value dims ∧ value dims ≤ N) then
    throw (.argumentError ("dimension " ++ toString (value dims) ++ " out of range (1:" ++ toString N ++ ")"))
  let r := axes a
  let r0 := r.zipIdx |>.map fun (range, i) =>
    if (Int.ofNat i) + 1 == value dims then unitRange (int 1) (last range - int 1) else toUnitRange range
  let r1 := r.zipIdx |>.map fun (range, i) =>
    if (Int.ofNat i) + 1 == value dims then unitRange (int 2) (last range) else toUnitRange range
  let high ← view a r1
  let low ← view a r0
  subtract high low

/--
Julia source: base/multidimensional.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function diff(r::AbstractRange{T}; dims::Integer=1) where {T}
    dims == 1 || throw(ArgumentError("dimension $dims out of range (1:1)"))
    return [@inbounds r[i+1] - r[i] for i in firstindex(r):lastindex(r)-1]
end
```
-/
def diffRange {R Z V : Type} (value : Z → Int) (firstindex lastindex : R → I64)
    (getindex : R → I64 → Result V) (subtract : V → V → Result V)
    (unitRangeElements : I64 → I64 → CI) (r : R) (dims : Z) : Result (List V) := do
  if value dims != 1 then
    throw (.argumentError ("dimension " ++ toString (value dims) ++ " out of range (1:1)"))
  (unitRangeElements (firstindex r) (lastindex r - int 1)).mapM fun i => do
    let high ← getindex r (i + int 1)
    let low ← getindex r i
    subtract high low

/--
Julia source: base/multidimensional.jl:1130-1151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mightalias(A::SubArray, B::SubArray)
    # There are three ways that SubArrays might _problematically_ alias one another:
    #   1. The parents are the same we can conservatively check if the indices might overlap OR
    #   2. The parents alias each other in a more complicated manner (and we can't trace indices) OR
    #   3. One's parent is used in the other's indices
    # Note that it's ok for just the indices to alias each other as those should not be mutated,
    # so we can always do better than the default !_isdisjoint(dataids(A), dataids(B))
    if isbits(A.parent) || isbits(B.parent)
        return false # Quick out for immutables
    elseif _parentsmatch(A.parent, B.parent)
        # Each SubArray unaliases its own parent from its own indices upon construction, so if
        # the two parents are the same, then by construction one cannot alias the other's indices
        # and therefore this is the only test we need to perform:
        return _indicesmightoverlap(A.indices, B.indices)
    else
        A_parent_ids = dataids(A.parent)
        B_parent_ids = dataids(B.parent)
        return !_isdisjoint(A_parent_ids, B_parent_ids) ||
            !_isdisjoint(A_parent_ids, _splatmap(dataids, B.indices)) ||
            !_isdisjoint(B_parent_ids, _splatmap(dataids, A.indices))
    end
end
```
-/
def mightaliasSubarray {A P I ID : Type} (parent : A → P) (indices : A → I) (isbits : P → Bool)
    (parentsMatch : P → P → Bool) (indicesMightOverlap : I → I → Result Bool)
    (dataids : P → ID) (splatmapDataids : I → ID) (isdisjoint : ID → ID → Bool) (a b : A) : Result Bool :=
  if isbits (parent a) || isbits (parent b) then .ok false
  else if parentsMatch (parent a) (parent b) then indicesMightOverlap (indices a) (indices b)
  else
    let Aids := dataids (parent a)
    let Bids := dataids (parent b)
    .ok (!isdisjoint Aids Bids || !isdisjoint Aids (splatmapDataids (indices b)) ||
      !isdisjoint Bids (splatmapDataids (indices a)))

/--
Julia source: base/multidimensional.jl:1153-1153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_parentsmatch(A::AbstractArray, B::AbstractArray) = A === B
```
-/
def parentsMatchAbstract {A : Type} (identical : A → A → Bool) (a b : A) : Bool := identical a b

/--
Julia source: base/multidimensional.jl:1154-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_parentsmatch(A::DenseArray, B::DenseArray) = elsize(A) == elsize(B) && pointer(A) == pointer(B) && size(A) == size(B)
```
-/
def parentsMatchDense {A Ptr SZ : Type} [BEq Ptr] [BEq SZ] (elsize : A → I64)
    (pointer : A → Ptr) (size : A → SZ) (a b : A) : Bool :=
  elsize a == elsize b && pointer a == pointer b && size a == size b

/--
Julia source: base/multidimensional.jl:1155-1155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_parentsmatch(A::StridedArray, B::StridedArray) = elsize(A) == elsize(B) && pointer(A) == pointer(B) && strides(A) == strides(B)
```
-/
def parentsMatchStrided {A Ptr ST : Type} [BEq Ptr] [BEq ST] (elsize : A → I64)
    (pointer : A → Ptr) (strides : A → ST) (a b : A) : Bool :=
  elsize a == elsize b && pointer a == pointer b && strides a == strides b

/--
Julia source: base/multidimensional.jl:1158-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indicesmightoverlap(A::Tuple{}, B::Tuple{}) = true
```
-/
def indicesOverlapEmpty : Bool := true

/--
Julia source: base/multidimensional.jl:1159-1159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indicesmightoverlap(A::Tuple{}, B::Tuple) = error("malformed subarray")
```
-/
def indicesOverlapLeftEmpty {I : Type} (error : String → Result Bool) (_other : List I) : Result Bool := error "malformed subarray"

/--
Julia source: base/multidimensional.jl:1160-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indicesmightoverlap(A::Tuple, B::Tuple{}) = error("malformed subarray")
```
-/
def indicesOverlapRightEmpty {I : Type} (error : String → Result Bool) (_other : List I) : Result Bool := error "malformed subarray"

/--
Julia source: base/multidimensional.jl:1162-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _indicesmightoverlap(A::Tuple{AbstractRange, Vararg{Any}}, B::Tuple{AbstractRange, Vararg{Any}})
    !isempty(intersect(A[1], B[1])) ? _indicesmightoverlap(tail(A), tail(B)) : false
end
```
-/
def indicesOverlapRanges {R I : Type} (intersect : R → R → Result R) (isempty : R → Bool)
    (recurse : List I → List I → Result Bool) (a b : R) (leftTail bt : List I) : Result Bool := do
  if !isempty (← intersect a b) then recurse leftTail bt else return false

/--
Julia source: base/multidimensional.jl:1166-1168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _indicesmightoverlap(A::Tuple{AbstractUnitRange, Vararg{Any}}, B::Tuple{AbstractUnitRange, Vararg{Any}})
    max(first(A[1]),first(B[1])) <= min(last(A[1]),last(B[1])) ? _indicesmightoverlap(tail(A), tail(B)) : false
end
```
-/
def indicesOverlapUnitRanges {R I Z : Type}  (first last : R → Z) (max min : Z → Z → Z) (le : Z → Z → Bool)
    (recurse : List I → List I → Result Bool) (a b : R) (leftTail bt : List I) : Result Bool :=
  if le (max (first a) (first b)) (min (last a) (last b)) then recurse leftTail bt else .ok false

/--
Julia source: base/multidimensional.jl:1170-1171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _indicesmightoverlap(A::Tuple{Real, Vararg{Any}}, B::Tuple{Real, Vararg{Any}}) =
    A[1] == B[1] ? _indicesmightoverlap(tail(A), tail(B)) : false
```
-/
def indicesOverlapScalars {Z I : Type} (eq : Z → Z → Bool) (recurse : List I → List I → Result Bool)
    (a b : Z) (leftTail bt : List I) : Result Bool := if eq a b then recurse leftTail bt else .ok false

/--
Julia source: base/multidimensional.jl:1172-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _indicesmightoverlap(A::Tuple{Real, Vararg{Any}}, B::Tuple{AbstractArray, Vararg{Any}}) =
    A[1] in B[1] ? _indicesmightoverlap(tail(A), tail(B)) : false
```
-/
def indicesOverlapScalarArray {Z A I : Type} (contains : Z → A → Bool) (recurse : List I → List I → Result Bool)
    (a : Z) (b : A) (leftTail bt : List I) : Result Bool := if contains a b then recurse leftTail bt else .ok false

/--
Julia source: base/multidimensional.jl:1174-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _indicesmightoverlap(A::Tuple{AbstractArray, Vararg{Any}}, B::Tuple{Real, Vararg{Any}}) =
    B[1] in A[1] ? _indicesmightoverlap(tail(A), tail(B)) : false
```
-/
def indicesOverlapArrayScalar {Z A I : Type} (contains : Z → A → Bool) (recurse : List I → List I → Result Bool)
    (a : A) (b : Z) (leftTail bt : List I) : Result Bool := if contains b a then recurse leftTail bt else .ok false

/--
Julia source: base/multidimensional.jl:1177-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _indicesmightoverlap(A::Tuple{AbstractArray, Vararg{Any}}, B::Tuple{AbstractArray, Vararg{Any}})
    if length(A[1]) == 1
        return A[1][1] in B[1] ? _indicesmightoverlap(tail(A), tail(B)) : false
    elseif length(B[1]) == 1
        return B[1][1] in A[1] ? _indicesmightoverlap(tail(A), tail(B)) : false
    else
        # But checking larger arrays requires O(m*n) and is too much work
        return true
    end
end
```
-/
def indicesOverlapArrays {A Z I : Type} (length : A → Nat) (getindex : A → I64 → Result Z)
    (contains : Z → A → Bool) (recurse : List I → List I → Result Bool)
    (a b : A) (leftTail bt : List I) : Result Bool := do
  if length a == 1 then
    if contains (← getindex a (int 1)) b then recurse leftTail bt else return false
  else if length b == 1 then
    if contains (← getindex b (int 1)) a then recurse leftTail bt else return false
  else return true

/--
Julia source: base/multidimensional.jl:1188-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_indicesmightoverlap(A::Tuple{Any, Vararg{Any}}, B::Tuple{Any, Vararg{Any}}) = true
```
-/
def indicesOverlapFallback {A B : Type} (_a : A) (_b : B) : Bool := true

/--
Julia source: base/multidimensional.jl:1190-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::AbstractArray{T1,N}, Rdest::CartesianIndices{N},
                  src::AbstractArray{T2,N}, Rsrc::CartesianIndices{N}) where {T1,T2,N}
    isempty(Rdest) && return dest
    if size(Rdest) != size(Rsrc)
        throw(ArgumentError("source and destination must have same size (got $(size(Rsrc)) and $(size(Rdest)))"))
    end
    checkbounds(dest, first(Rdest))
    checkbounds(dest, last(Rdest))
    checkbounds(src, first(Rsrc))
    checkbounds(src, last(Rsrc))
    src′ = unalias(dest, src)
    CRdest = CartesianIndices(Rdest)
    CRsrc = CartesianIndices(Rsrc)
    ΔI = first(CRdest) - first(CRsrc)
    if @generated
        quote
            @nloops $N i (n->CRsrc.indices[n]) begin
                @inbounds @nref($N,dest,n->Rdest.indices[n][i_n+ΔI[n]]) = @nref($N,src′,n->Rsrc.indices[n][i_n])
            end
        end
    else
        for I in CRsrc
            @inbounds dest[Rdest[I + ΔI]] = src′[Rsrc[I]]
        end
    end
    dest
end
```
-/
def copytoCartesian {Dest Src V : Type} (isempty : CIs → Bool) (size : CIs → CI)
    (checkboundsDest : Dest → CI → Result Unit) (checkboundsSrc : Src → CI → Result Unit)
    (unalias : Dest → Src → Result Src)
    (cartesianIndices : CIs → CIs) (elements : CIs → List CI)
    (regionGetindex : CIs → CI → Result CI) (getindex : Src → CI → Result V)
    (setindex : Dest → V → CI → Result Dest)
    (dest : Dest) (Rdest : CIs) (src : Src) (Rsrc : CIs)
    (generated : Bool := false)
    (showSize : CI → String := fun _ => "") : Result Dest := do
  if isempty Rdest then return dest
  if size Rdest != size Rsrc then
    throw (.argumentError ("source and destination must have same size (got " ++
      showSize (size Rsrc) ++ " and " ++ showSize (size Rdest) ++ ")"))
  checkboundsDest dest (cartesianIndicesFirst Rdest)
  checkboundsDest dest (cartesianIndicesLast Rdest)
  checkboundsSrc src (cartesianIndicesFirst Rsrc)
  checkboundsSrc src (cartesianIndicesLast Rsrc)
  let src' ← unalias dest src
  let CRdest := cartesianIndices Rdest
  let CRsrc := cartesianIndices Rsrc
  let delta := cartesianSub (cartesianIndicesFirst CRdest) (cartesianIndicesFirst CRsrc)
  let mut dest := dest
  if generated then
    for I in columnMajor (CRsrc.map Rng.elems) do
      let srcIdx ← mapTupleM (fun r i => tupleGet r.elems i) Rsrc I
      let dstIdx ← mapTupleM (fun r i => tupleGet r.elems i) Rdest (cartesianAdd I delta)
      let value ← getindex src' srcIdx
      dest ← setindex dest value dstIdx
  else
    for I in elements CRsrc do
      let value ← getindex src' (← regionGetindex Rsrc I)
      dest ← setindex dest value (← regionGetindex Rdest (cartesianAdd I delta))
  return dest

/--
Julia source: base/multidimensional.jl:1246-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift!(dest::AbstractArray, src, ::Tuple{}) = copyto!(dest, src)
```
-/
def circshiftEmpty {Dest Src : Type} (copyto : Dest → Src → Result Dest)
    (dest : Dest) (src : Src) : Result Dest := copyto dest src

/--
Julia source: base/multidimensional.jl:1257-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function circshift!(dest::AbstractArray{T,N}, src, shiftamt::DimsInteger) where {T,N}
    dest === src && throw(ArgumentError("dest and src must be separate arrays"))
    inds = axes(src)
    axes(dest) == inds || throw(ArgumentError("indices of src and dest must match (got $inds and $(axes(dest)))"))
    isempty(src) && return dest
    _circshift!(dest, (), src, (), inds, fill_to_length(shiftamt, 0, Val(N)))
end
```
-/
def circshift {Dest Src Z : Type} (identical : Dest → Src → Bool)
    (axesDest : Dest → CIs) (axesSrc : Src → CIs) (axesEq : CIs → CIs → Bool)
    (isempty : Src → Bool) (fillToLength : List Z → Nat → Result (List Z))
    (recurse : Dest → CIs → Src → CIs → CIs → List Z → Result Dest)
    (N : Nat) (dest : Dest) (src : Src) (shiftamt : List Z)
    (showAxes : CIs → String := fun _ => "") : Result Dest := do
  if identical dest src then throw (.argumentError "dest and src must be separate arrays")
  let inds := axesSrc src
  if !axesEq (axesDest dest) inds then
    throw (.argumentError ("indices of src and dest must match (got " ++
      showAxes inds ++ " and " ++ showAxes (axesDest dest) ++ ")"))
  if isempty src then return dest
  recurse dest [] src [] inds (← fillToLength shiftamt N)

/--
Julia source: base/multidimensional.jl:1265-1266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift!(dest::AbstractArray, src, shiftamt) =
    circshift!(dest, src, map(Integer, (shiftamt...,)))
```
-/
def circshiftConvert {Dest Src S Z : Type} (integer : S → Result Z)
    (circshift : Dest → Src → List Z → Result Dest)
    (dest : Dest) (src : Src) (shiftamt : List S) : Result Dest := do
  circshift dest src (← shiftamt.mapM integer)

/--
Julia source: base/multidimensional.jl:1284-1295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _circshift!(dest, rdest, src, rsrc,
                             inds::Tuple{AbstractUnitRange,Vararg{Any}},
                             shiftamt::Tuple{Integer,Vararg{Any}})::typeof(dest)
    ind1, d = inds[1], shiftamt[1]
    s = mod(d, length(ind1))
    sf, sl = first(ind1)+s, last(ind1)-s
    r1, r2 = first(ind1):sf-1, sf:last(ind1)
    r3, r4 = first(ind1):sl, sl+1:last(ind1)
    tinds, tshiftamt = tail(inds), tail(shiftamt)
    _circshift!(dest, (rdest..., r1), src, (rsrc..., r4), tinds, tshiftamt)
    _circshift!(dest, (rdest..., r2), src, (rsrc..., r3), tinds, tshiftamt)
end
```
-/
def circshiftCons {Dest Src Z : Type} (mod : Z → I64 → Result I64) (length : Rng → I64)
    (unitRange : I64 → I64 → Rng) (recurse : Dest → CIs → Src → CIs → CIs → List Z → Result Dest)
    (dest : Dest) (rdest : CIs) (src : Src) (rsrc : CIs) (ind1 : Rng) (tinds : CIs)
    (d : Z) (tshiftamt : List Z) : Result Dest := do
  let s ← mod d (length ind1)
  let sf := ind1.start + s
  let sl := ind1.last - s
  let r1 := unitRange ind1.start (sf - int 1)
  let r2 := unitRange sf ind1.last
  let r3 := unitRange ind1.start sl
  let r4 := unitRange (sl + int 1) ind1.last
  let dest ← recurse dest (rdest ++ [r1]) src (rsrc ++ [r4]) tinds tshiftamt
  recurse dest (rdest ++ [r2]) src (rsrc ++ [r3]) tinds tshiftamt

/--
Julia source: base/multidimensional.jl:1297-1299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _circshift!(dest, rdest, src, rsrc, inds, shiftamt)
    copyto!(dest, CartesianIndices(rdest), src, CartesianIndices(rsrc))
end
```
-/
def circshiftBase {Dest Src I S : Type} (copyto : Dest → CIs → Src → CIs → Result Dest)
    (dest : Dest) (rdest : CIs) (src : Src) (rsrc : CIs) (_inds : I) (_shiftamt : S) : Result Dest :=
  copyto dest rdest src rsrc

/--
Julia source: base/multidimensional.jl:1337-1346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function circcopy!(dest, src)
    dest === src && throw(ArgumentError("dest and src must be separate arrays"))
    indssrc, indsdest = axes(src), axes(dest)
    if (szsrc = map(length, indssrc)) != (szdest = map(length, indsdest))
        throw(DimensionMismatch("src and dest must have the same sizes (got $szsrc and $szdest)"))
    end
    shift = map((isrc, idest)->first(isrc)-first(idest), indssrc, indsdest)
    all(x->x==0, shift) && return copyto!(dest, src)
    _circcopy!(dest, (), indsdest, src, (), indssrc)
end
```
-/
def circcopy {Dest Src : Type} (identical : Dest → Src → Bool)
    (axesDest : Dest → CIs) (axesSrc : Src → CIs) (length : Rng → I64)
    (copyto : Dest → Src → Result Dest)
    (recurse : Dest → CIs → CIs → Src → CIs → CIs → Result Dest)
    (dest : Dest) (src : Src)
    (showSize : CI → String := fun _ => "") : Result Dest := do
  if identical dest src then throw (.argumentError "dest and src must be separate arrays")
  let indssrc := axesSrc src
  let indsdest := axesDest dest
  let szsrc := indssrc.map length
  let szdest := indsdest.map length
  if szsrc != szdest then
    throw (.dimensionMismatch ("src and dest must have the same sizes (got " ++
      showSize szsrc ++ " and " ++ showSize szdest ++ ")"))
  let shift := List.zipWith (fun isrc idest => isrc.start - idest.start) indssrc indsdest
  if shift.all (fun x => x == int 0) then return ← copyto dest src
  recurse dest [] indsdest src [] indssrc

/--
Julia source: base/multidimensional.jl:1349-1361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _circcopy!(dest, rdest, indsdest::Tuple{AbstractUnitRange,Vararg{Any}},
                            src,  rsrc,  indssrc::Tuple{AbstractUnitRange,Vararg{Any}})::typeof(dest)
    indd1, inds1 = indsdest[1], indssrc[1]
    l = length(indd1)
    s = mod(first(inds1)-first(indd1), l)
    sdf = first(indd1)+s
    rd1, rd2 = first(indd1):sdf-1, sdf:last(indd1)
    ssf = last(inds1)-s
    rs1, rs2 = first(inds1):ssf, ssf+1:last(inds1)
    tindsd, tindss = tail(indsdest), tail(indssrc)
    _circcopy!(dest, (rdest..., rd1), tindsd, src, (rsrc..., rs2), tindss)
    _circcopy!(dest, (rdest..., rd2), tindsd, src, (rsrc..., rs1), tindss)
end
```
-/
def circcopyCons {Dest Src : Type} (length : Rng → I64) (mod : I64 → I64 → Result I64)
    (unitRange : I64 → I64 → Rng) (recurse : Dest → CIs → CIs → Src → CIs → CIs → Result Dest)
    (dest : Dest) (rdest : CIs) (indd1 : Rng) (tindsd : CIs)
    (src : Src) (rsrc : CIs) (inds1 : Rng) (tindss : CIs) : Result Dest := do
  let l := length indd1
  let s ← mod (inds1.start - indd1.start) l
  let sdf := indd1.start + s
  let rd1 := unitRange indd1.start (sdf - int 1)
  let rd2 := unitRange sdf indd1.last
  let ssf := inds1.last - s
  let rs1 := unitRange inds1.start ssf
  let rs2 := unitRange (ssf + int 1) inds1.last
  let dest ← recurse dest (rdest ++ [rd1]) tindsd src (rsrc ++ [rs2]) tindss
  recurse dest (rdest ++ [rd2]) tindsd src (rsrc ++ [rs1]) tindss

/--
Julia source: base/multidimensional.jl:1364-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _circcopy!(dest, rdest, indsdest, src, rsrc, indssrc)
    copyto!(dest, CartesianIndices(rdest), src, CartesianIndices(rsrc))
end
```
-/
def circcopyBase {Dest Src I : Type} (copyto : Dest → CIs → Src → CIs → Result Dest)
    (dest : Dest) (rdest : CIs) (_indsdest : I) (src : Src) (rsrc : CIs) (_indssrc : I) : Result Dest :=
  copyto dest rdest src rsrc

/--
Julia source: base/multidimensional.jl:1374-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_getindex!(X::BitArray, B::BitArray, I0::Union{AbstractUnitRange{Int},Slice})
    copy_chunks!(X.chunks, 1, B.chunks, indexoffset(I0)+1, length(I0))
    return X
end
```
-/
def bitGetindexContiguous {A C I : Type} (chunks : A → C) (setChunks : A → C → A)
    (copyChunks : C → I64 → C → I64 → I64 → Result C) (indexoffset length : I → I64)
    (X B : A) (I0 : I) : Result A := do
  let copied ← copyChunks (chunks X) (int 1) (chunks B) (indexoffset I0 + int 1) (length I0)
  return setChunks X copied

/--
Julia source: base/multidimensional.jl:1380-1414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_getindex!(X::BitArray, B::BitArray,
        I0::Union{Slice,UnitRange{Int}}, I::Union{Int,AbstractUnitRange{Int},Slice}...)
    N = length(I)
    quote
        $(Expr(:meta, :inline))
        @nexprs $N d->(I_d = I[d])

        idxlens = @ncall $N index_lengths I0 I

        f0 = indexoffset(I0)+1
        l0 = idxlens[1]

        gap_lst_1 = 0
        @nexprs $N d->(gap_lst_{d+1} = idxlens[d+1])
        stride = 1
        ind = f0
        @nexprs $N d->begin
            stride *= size(B, d)
            stride_lst_d = stride
            ind += stride * indexoffset(I_d)
            gap_lst_{d+1} *= stride
        end

        storeind = 1
        Xc, Bc = X.chunks, B.chunks
        @nloops($N, i, d->(1:idxlens[d+1]),
                d->nothing, # PRE
                d->(ind += stride_lst_d - gap_lst_d), # POST
                begin # BODY
                    copy_chunks!(Xc, storeind, Bc, ind, l0)
                    storeind += l0
                end)
        return X
    end
end
```
-/
def bitGetindexRanges {A C I : Type} (chunks : A → C) (setChunks : A → C → A)
    (indexLengths : List I → CI) (indexoffset : I → I64) (size : A → I64 → I64)
    (unitRangeElements : I64 → I64 → CI) (copyChunks : C → I64 → C → I64 → I64 → Result C)
    (X B : A) (I0 : I) (I : List I) : Result A := do
  let idxlens := indexLengths (I0 :: I)
  let f0 := indexoffset I0 + int 1
  let l0 ← tupleGet idxlens (int 1)
  let mut gap := [int 0] ++ idxlens.tail
  let mut strides := []
  let mut stride := int 1
  let mut ind := f0
  for (selector, d) in I.zipIdx do
    stride := stride * size B (int (d + 1))
    strides := strides ++ [stride]
    ind := ind + stride * indexoffset selector
    let old ← tupleGet gap (int (d + 2))
    gap := gap.set (d + 1) (old * stride)
  let axes := idxlens.tail.map fun n => unitRangeElements (int 1) n
  let state ← nestedLoops (fun _ state => do
      let copied ← copyChunks state.chunks state.otherIndex (chunks B) state.index l0
      return { state with chunks := copied, otherIndex := state.otherIndex + l0 })
    (fun d state => do
      let delta := (← tupleGet strides (int (d + 1))) - (← tupleGet gap (int (d + 1)))
      return { state with index := state.index + delta })
    axes.zipIdx.reverse [] (⟨chunks X, ind, int 1⟩ : ChunkState C)
  return setChunks X state.chunks

/--
Julia source: base/multidimensional.jl:1419-1434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_getindex!(X::BitArray, B::BitArray, I::Union{Int,AbstractArray{Int}}...)
    N = length(I)
    quote
        $(Expr(:meta, :inline))
        stride_1 = 1
        @nexprs $N d->(stride_{d+1} = stride_d*size(B, d))
        $(Symbol(:offset_, N)) = 1
        ind = 0
        Xc, Bc = X.chunks, B.chunks
        @nloops $N i d->I[d] d->(@inbounds offset_{d-1} = offset_d + (i_d-1)*stride_d) begin
            ind += 1
            unsafe_bitsetindex!(Xc, unsafe_bitgetindex(Bc, offset_0), ind)
        end
        return X
    end
end
```
-/
def bitGetindexGeneral {A C I : Type} (chunks : A → C) (setChunks : A → C → A)
    (size : A → I64 → I64) (indexElements : I → CI)
    (bitgetindex : C → I64 → Result Bool) (bitsetindex : C → Bool → I64 → Result C)
    (X B : A) (I : List I) : Result A := do
  let mut strides := [int 1]
  let mut stride := int 1
  for d in List.range I.length do
    stride := stride * size B (int (d + 1))
    strides := strides ++ [stride]
  let state ← forCartesian (I.map indexElements) (fun coordinates state => do
    let mut offset := int 1
    for (i, stride) in coordinates.zip strides do offset := offset + (i - int 1) * stride
    let ind := state.index + int 1
    let copied ← bitsetindex state.chunks (← bitgetindex (chunks B) offset) ind
    return { state with chunks := copied, index := ind })
    (⟨chunks X, int 0, int 0⟩ : ChunkState C)
  return setChunks X state.chunks

/--
Julia source: base/multidimensional.jl:1438-1447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::StridedArray, pos_s::Int, numbits::Int)
    bind = pos_d
    cind = pos_s
    lastind = pos_d + numbits - 1
    @inbounds while bind ≤ lastind
        unsafe_bitsetindex!(Bc, convert(Bool, C[cind]), bind)
        bind += 1
        cind += 1
    end
end
```
-/
def copyToBitarrayChunks {C A V : Type} (getindex : A → I64 → Result V) (convertBool : V → Result Bool)
    (bitsetindex : C → Bool → I64 → Result C)
    (Bc : C) (pos_d : I64) (source : A) (pos_s numbits : I64) : Option (Result C) :=
  let lastind := pos_d + numbits - int 1
  whileLoop (fun state => do
    if state.index ≤ lastind then
      let chunks ← bitsetindex state.chunks (← convertBool (← getindex source state.otherIndex)) state.index
      return .inr (⟨chunks, state.index + int 1, state.otherIndex + int 1⟩ : ChunkState C)
    else return .inl state.chunks) (⟨Bc, pos_d, pos_s⟩ : ChunkState C)

/--
Julia source: base/multidimensional.jl:1455-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline try_bool_conversion(x::Real) =
    x == 0 || x == 1 || throw(InexactError(:try_bool_conversion, Bool, x))
```
-/
def tryBoolConversion {R : Type} (eqZero eqOne : R → Bool) (x : R) : Result Unit :=
  if eqZero x || eqOne x then .ok () else .error (.inexactError "try_bool_conversion")

/--
Julia source: base/multidimensional.jl:1457-1457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline unchecked_bool_convert(x::Real) = x == 1
```
-/
def uncheckedBoolConvert {R : Type} (eqOne : R → Bool) (x : R) : Bool := eqOne x

/--
Julia source: base/multidimensional.jl:1459-1511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::StridedArray{<:Real}, pos_s::Int, numbits::Int)
    @inbounds for i = (1:numbits) .+ (pos_s - 1)
        try_bool_conversion(C[i])
    end

    kd0, ld0 = get_chunks_id(pos_d)
    kd1, ld1 = get_chunks_id(pos_d + numbits - 1)

    delta_kd = kd1 - kd0

    u = _msk64
    if delta_kd == 0
        msk_d0 = msk_d1 = ~(u << ld0) | (u << (ld1+1))
        lt0 = ld1
    else
        msk_d0 = ~(u << ld0)
        msk_d1 = (u << (ld1+1))
        lt0 = 63
    end

    bind = kd0
    ind = pos_s
    @inbounds if ld0 > 0
        c = UInt64(0)
        for j = ld0:lt0
            c |= (UInt64(unchecked_bool_convert(C[ind])) << j)
            ind += 1
        end
        Bc[kd0] = (Bc[kd0] & msk_d0) | (c & ~msk_d0)
        bind += 1
    end

    nc = _div64(numbits - ind + pos_s)
    @inbounds for i = 1:nc
        c = UInt64(0)
        for j = 0:63
            c |= (UInt64(unchecked_bool_convert(C[ind])) << j)
            ind += 1
        end
        Bc[bind] = c
        bind += 1
    end

    @inbounds if bind ≤ kd1
        @assert bind == kd1 "bind != kd1"
        c = UInt64(0)
        for j = 0:ld1
            c |= (UInt64(unchecked_bool_convert(C[ind])) << j)
            ind += 1
        end
        Bc[kd1] = (Bc[kd1] & msk_d1) | (c & ~msk_d1)
    end
end
```
-/
def copyToBitarrayChunksReal {C A V : Type} (getindex : A → I64 → Result V) (tryBool : V → Result Unit)
    (uncheckedBool : V → Bool) (getChunksId : I64 → I64 × I64)
    (readChunk : C → I64 → Result (JInt .u64)) (writeChunk : C → I64 → JInt .u64 → Result C)
    (bitAnd bitOr : JInt .u64 → JInt .u64 → JInt .u64) (bitNot : JInt .u64 → JInt .u64)
    (shl : JInt .u64 → I64 → JInt .u64) (div64 : I64 → I64)
    (elements : I64 → I64 → CI)
    (Bc : C) (pos_d : I64) (source : A) (pos_s numbits : I64) : Result C := do
  for i in (elements (int 1) numbits).map (fun i => i + (pos_s - int 1)) do
    tryBool (← getindex source i)
  let (kd0, ld0) := getChunksId pos_d
  let (kd1, ld1) := getChunksId (pos_d + numbits - int 1)
  let delta_kd := kd1 - kd0
  let u := JInt.wrap .u64 (-1)
  let (msk_d0, msk_d1, lt0) := if delta_kd == int 0 then
      let mask := bitOr (bitNot (shl u ld0)) (shl u (ld1 + int 1))
      (mask, mask, ld1)
    else (bitNot (shl u ld0), shl u (ld1 + int 1), int 63)
  let mut bind := kd0
  let mut ind := pos_s
  let mut Bc := Bc
  if ld0 > int 0 then
    let mut c := JInt.wrap .u64 0
    for j in elements ld0 lt0 do
      c := bitOr c (shl (JInt.wrap .u64 (if uncheckedBool (← getindex source ind) then 1 else 0)) j)
      ind := ind + int 1
    Bc ← writeChunk Bc kd0 (bitOr (bitAnd (← readChunk Bc kd0) msk_d0) (bitAnd c (bitNot msk_d0)))
    bind := bind + int 1
  let nc := div64 (numbits - ind + pos_s)
  for _ in elements (int 1) nc do
    let mut c := JInt.wrap .u64 0
    for j in elements (int 0) (int 63) do
      c := bitOr c (shl (JInt.wrap .u64 (if uncheckedBool (← getindex source ind) then 1 else 0)) j)
      ind := ind + int 1
    Bc ← writeChunk Bc bind c
    bind := bind + int 1
  if bind ≤ kd1 then
    if bind != kd1 then throw .assertionError
    let mut c := JInt.wrap .u64 0
    for j in elements (int 0) ld1 do
      c := bitOr c (shl (JInt.wrap .u64 (if uncheckedBool (← getindex source ind) then 1 else 0)) j)
      ind := ind + int 1
    Bc ← writeChunk Bc kd1 (bitOr (bitAnd (← readChunk Bc kd1) msk_d1) (bitAnd c (bitNot msk_d1)))
  return Bc

/--
Julia source: base/multidimensional.jl:1516-1525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(B::BitArray, X::Union{StridedArray,BitArray}, J0::D) where {D<:Union{Colon,AbstractUnitRange{Int}}}
    I0 = to_indices(B, (J0,))[1]
    @boundscheck checkbounds(B, I0)
    l0 = length(I0)
    setindex_shape_check(X, l0)
    l0 == 0 && return B
    f0 = indexoffset(I0)+1
    copy_to_bitarray_chunks!(B.chunks, f0, X, 1, l0)
    return B
end
```
-/
def bitSetindexContiguous {A X I J C : Type} (toIndices : A → List J → Result (List I))
    (checkbounds : A → I → Result Unit) (length indexoffset : I → I64) (shapeCheck : X → I64 → Result Unit)
    (chunks : A → C) (copyChunks : C → I64 → X → I64 → I64 → Result C) (setChunks : A → C → A)
    (B : A) (X : X) (J0 : J) : Result A := do
  let I0 ← tupleGet (← toIndices B [J0]) (int 1)
  checkbounds B I0
  let l0 := length I0
  shapeCheck X l0
  if l0 == int 0 then return B
  let f0 := indexoffset I0 + int 1
  return setChunks B (← copyChunks (chunks B) f0 X (int 1) l0)

/--
Julia source: base/multidimensional.jl:1527-1532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(B::BitArray, X::Union{StridedArray,BitArray},
        I0::DI0, I::Union{Int,AbstractUnitRange{Int},Colon}...) where {DI0<:Union{Colon,AbstractUnitRange{Int}}, }
    J = to_indices(B, (I0, I...))
    @boundscheck checkbounds(B, J...)
    _unsafe_setindex!(B, X, J...)
end
```
-/
def bitSetindexRanges {A X I J : Type} (toIndices : A → List J → Result (List I))
    (checkbounds : A → List I → Result Unit) (unsafeSetindex : A → X → List I → Result A)
    (B : A) (X : X) (I0 : J) (I : List J) : Result A := do
  let J ← toIndices B (I0 :: I)
  checkbounds B J
  unsafeSetindex B X J

/--
Julia source: base/multidimensional.jl:1533-1566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_setindex!(B::BitArray, X::Union{StridedArray,BitArray},
        I0::Union{Slice,AbstractUnitRange{Int}}, I::Union{Int,AbstractUnitRange{Int},Slice}...)
    N = length(I)
    quote
        idxlens = @ncall $N index_lengths I0 d->I[d]
        setindex_shape_check(X, @ncall $N index_sizes I0 d->I[d])
        isempty(X) && return B
        f0 = indexoffset(I0)+1
        l0 = idxlens[1]

        gap_lst_1 = 0
        @nexprs $N d->(gap_lst_{d+1} = idxlens[d+1])
        stride = 1
        ind = f0
        @nexprs $N d->begin
            stride *= size(B, d)
            stride_lst_d = stride
            ind += stride * indexoffset(I[d])
            gap_lst_{d+1} *= stride
        end

        refind = 1
        Bc = B.chunks
        @nloops($N, i, d->I[d],
                d->nothing, # PRE
                d->(ind += stride_lst_d - gap_lst_d), # POST
                begin # BODY
                    copy_to_bitarray_chunks!(Bc, ind, X, refind, l0)
                    refind += l0
                end)

        return B
    end
end
```
-/
def bitUnsafeSetindexRanges {A X C I : Type} (chunks : A → C) (setChunks : A → C → A)
    (indexLengths indexSizes : List I → CI) (shapeCheck : X → CI → Result Unit) (isempty : X → Bool)
    (indexoffset : I → I64) (size : A → I64 → I64) (indexElements : I → CI)
    (copyChunks : C → I64 → X → I64 → I64 → Result C)
    (B : A) (X : X) (I0 : I) (I : List I) : Result A := do
  let idxlens := indexLengths (I0 :: I)
  shapeCheck X (indexSizes (I0 :: I))
  if isempty X then return B
  let f0 := indexoffset I0 + int 1
  let l0 ← tupleGet idxlens (int 1)
  let mut gap := [int 0] ++ idxlens.tail
  let mut strides := []
  let mut stride := int 1
  let mut ind := f0
  for (selector, d) in I.zipIdx do
    stride := stride * size B (int (d + 1))
    strides := strides ++ [stride]
    ind := ind + stride * indexoffset selector
    let old ← tupleGet gap (int (d + 2))
    gap := gap.set (d + 1) (old * stride)
  let state ← nestedLoops (fun _ state => do
      let copied ← copyChunks state.chunks state.index X state.otherIndex l0
      return { state with chunks := copied, otherIndex := state.otherIndex + l0 })
    (fun d state => do
      let delta := (← tupleGet strides (int (d + 1))) - (← tupleGet gap (int (d + 1)))
      return { state with index := state.index + delta })
    ((I.map indexElements).zipIdx.reverse) [] (⟨chunks B, ind, int 1⟩ : ChunkState C)
  return setChunks B state.chunks

/--
Julia source: base/multidimensional.jl:1568-1571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(B::BitArray, X::AbstractArray,
        I0::DI0, I::Union{Int,AbstractUnitRange{Int},Colon}...) where {DI0<:Union{Colon,AbstractUnitRange{Int}}}
    _setindex!(IndexStyle(B), B, X, to_indices(B, (I0, I...))...)
end
```
-/
def bitSetindexAbstract {S A X I J : Type} (indexStyle : A → S)
    (toIndices : A → List J → Result (List I)) (setindex : S → A → X → List I → Result A)
    (B : A) (X : X) (I0 : J) (I : List J) : Result A := do
  setindex (indexStyle B) B X (← toIndices B (I0 :: I))

/--
Julia source: base/multidimensional.jl:1574-1581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill!(V::SubArray{Bool, <:Any, <:BitArray, <:Tuple{AbstractUnitRange{Int}}}, x)
    B = V.parent
    I0 = V.indices[1]
    l0 = length(I0)
    l0 == 0 && return V
    fill_chunks!(B.chunks, convert(Bool, x), first(I0), l0)
    return V
end
```
-/
def bitFillContiguous {V A I X C : Type} (parent : V → A) (indices : V → List I)
    (length first : I → I64) (chunks : A → C) (convertBool : X → Result Bool)
    (fillChunks : C → Bool → I64 → I64 → Result C) (updateParentChunks : V → C → V) (viewData : V) (x : X) : Result V := do
  let B := parent viewData
  let I0 ← tupleGet (indices viewData) (int 1)
  let l0 := length I0
  if l0 == int 0 then return viewData
  let copied ← fillChunks (chunks B) (← convertBool x) (first I0) l0
  return updateParentChunks viewData copied

/--
Julia source: base/multidimensional.jl:1583-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fill!(V::SubArray{Bool, <:Any, <:BitArray, <:Tuple{AbstractUnitRange{Int}, Vararg{Union{Int,AbstractUnitRange{Int}}}}}, x) =
    (_unsafe_fill_indices!(V.parent, x, V.indices...); V)
```
-/
def bitFillRanges {V A I X : Type} (parent : V → A) (indices : V → List I)
    (unsafeFill : A → X → List I → Result A) (updateParent : V → A → V) (viewData : V) (x : X) : Result V := do
  return updateParent viewData (← unsafeFill (parent viewData) x (indices viewData))

/--
Julia source: base/multidimensional.jl:1586-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unsafe_fill_indices!(B::BitArray, x,
        I0::AbstractUnitRange{Int}, I::Union{Int,AbstractUnitRange{Int}}...)
    N = length(I)
    quote
        y = convert(Bool, x)
        idxlens = @ncall $N index_lengths I0 d->I[d]

        f0 = indexoffset(I0)+1
        l0 = idxlens[1]
        l0 == 0 && return B
        @nexprs $N d->(isempty(I[d]) && return B)

        gap_lst_1 = 0
        @nexprs $N d->(gap_lst_{d+1} = idxlens[d+1])
        stride = 1
        ind = f0
        @nexprs $N d->begin
            stride *= size(B, d)
            stride_lst_d = stride
            ind += stride * indexoffset(I[d])
            gap_lst_{d+1} *= stride
        end

        @nloops($N, i, d->I[d],
                d->nothing, # PRE
                d->(ind += stride_lst_d - gap_lst_d), # POST
                fill_chunks!(B.chunks, y, ind, l0) # BODY
                )

        return B
    end
end
```
-/
def bitUnsafeFillIndices {A X C I : Type} (chunks : A → C) (setChunks : A → C → A)
    (convertBool : X → Result Bool) (indexLengths : List I → CI) (indexoffset : I → I64)
    (isempty : I → Bool) (size : A → I64 → I64) (indexElements : I → CI)
    (fillChunks : C → Bool → I64 → I64 → Result C) (B : A) (x : X) (I0 : I) (I : List I) : Result A := do
  let y ← convertBool x
  let idxlens := indexLengths (I0 :: I)
  let f0 := indexoffset I0 + int 1
  let l0 ← tupleGet idxlens (int 1)
  if l0 == int 0 then return B
  for selector in I do if isempty selector then return B
  let mut gap := [int 0] ++ idxlens.tail
  let mut strides := []
  let mut stride := int 1
  let mut ind := f0
  for (selector, d) in I.zipIdx do
    stride := stride * size B (int (d + 1))
    strides := strides ++ [stride]
    ind := ind + stride * indexoffset selector
    let old ← tupleGet gap (int (d + 2))
    gap := gap.set (d + 1) (old * stride)
  let state ← nestedLoops (fun _ state => do
      return { state with chunks := ← fillChunks state.chunks y state.index l0 })
    (fun d state => do
      let delta := (← tupleGet strides (int (d + 1))) - (← tupleGet gap (int (d + 1)))
      return { state with index := state.index + delta })
    ((I.map indexElements).zipIdx.reverse) [] (⟨chunks B, ind, int 0⟩ : ChunkState C)
  return setChunks B state.chunks

/--
Julia source: base/multidimensional.jl:1621-1635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function isassigned(B::BitArray, I_0::Int, I::Int...)
    N = length(I)
    quote
        @nexprs $N d->(I_d = I[d])
        stride = 1
        index = I_0
        @nexprs $N d->begin
            l = size(B,d)
            stride *= l
            @boundscheck 1 <= I_{d-1} <= l || return false
            index += (I_d - 1) * stride
        end
        return isassigned(B, index)
    end
end
```
-/
def bitIsassigned {A : Type} (size : A → I64 → I64) (isassigned : A → I64 → Bool)
    (B : A) (I0 : I64) (I : CI) : Bool := Id.run do
  let mut stride := int 1
  let mut index := I0
  let mut previous := I0
  for (next, d) in I.zipIdx do
    let l := size B (int (d + 1))
    stride := stride * l
    if !(int 1 ≤ previous ∧ previous ≤ l) then return false
    index := index + (next - int 1) * stride
    previous := next
  return isassigned B index

/--
Julia source: base/multidimensional.jl:1637-1637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isassigned(A::AbstractArray, i::CartesianIndex) = isassigned(A, Tuple(i)...)
```
-/
def isassignedCartesian {A : Type} (isassigned : A → CI → Result Bool) (a : A) (i : CI) : Result Bool :=
  isassigned a (cartesianToTuple i)

/--
Julia source: base/multidimensional.jl:1638-1640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function isassigned(A::AbstractArray, i::Union{Integer, CartesianIndex}...)
    return isassigned(A, CartesianIndex(to_indices(A, i)))
end
```
-/
def isassignedMixed {A I : Type} (toIndices : A → List I → Result CI)
    (isassigned : A → CI → Result Bool) (a : A) (i : List I) : Result Bool := do isassigned a (← toIndices a i)

/--
Julia source: base/multidimensional.jl:1641-1663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function isassigned(A::AbstractArray, i::Integer...)
    # convert to valid indices, checking for Bool
    inds = to_indices(A, i)
    @boundscheck checkbounds(Bool, A, inds...) || return false
    S = IndexStyle(A)
    ninds = length(inds)
    if (isa(S, IndexLinear) && ninds != 1)
        return @inbounds isassigned(A, _to_linear_index(A, inds...))
    elseif (!isa(S, IndexLinear) && ninds != ndims(A))
        return @inbounds isassigned(A, _to_subscript_indices(A, inds...)...)
    else
       try
            A[inds...]
            true
        catch e
            if isa(e, BoundsError) || isa(e, UndefRefError)
                return false
            else
                rethrow()
            end
        end
    end
end
```
-/
def isassignedIntegers {A I V E : Type} (toIndices : A → List I → Except E CI)
    (checkbounds : A → CI → Bool) (isLinear : A → Bool) (ndims : A → Nat)
    (toLinear : A → CI → Except E I64) (toSubscripts : A → CI → Except E CI)
    (isassignedLinear : A → I64 → Except E Bool) (isassignedCartesian : A → CI → Except E Bool)
    (getindex : A → CI → Except E V) (isBoundsError isUndefRefError : E → Bool)
    (a : A) (i : List I) : Except E Bool := do
  let inds ← toIndices a i
  if !checkbounds a inds then return false
  let S := isLinear a
  let ninds := inds.length
  if S && ninds != 1 then isassignedLinear a (← toLinear a inds)
  else if !S && ninds != ndims a then isassignedCartesian a (← toSubscripts a inds)
  else
    match getindex a inds with
    | .ok _ => return true
    | .error e => if isBoundsError e || isUndefRefError e then return false else throw e

/--
Julia source: base/multidimensional.jl:1669-1676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function permutedims(B::StridedArray, perm)
    dimsB = size(B)
    ndimsB = length(dimsB)
    (ndimsB == length(perm) && isperm(perm)) || throw(ArgumentError("no valid permutation of dimensions"))
    dimsP = ntuple(i->dimsB[perm[i]], ndimsB)::typeof(dimsB)
    P = similar(B, dimsP)
    permutedims!(P, B, perm)
end
```
-/
def permutedims {BType PType P : Type} (size : BType → CI) (length : P → Nat) (isperm : P → Bool)
    (getPerm : P → I64 → Result I64) (similar : BType → CI → Result PType)
    (permutedimsBang : PType → BType → P → Result PType)
    (B : BType) (perm : P) : Result PType := do
  let dimsB := size B
  let ndimsB := dimsB.length
  if !(ndimsB == length perm && isperm perm) then throw (.argumentError "no valid permutation of dimensions")
  let dimsP ← (List.range ndimsB).mapM fun (i : Nat) => do tupleGet dimsB (← getPerm perm (int (Int.ofNat (i + 1))))
  let P ← similar B dimsP
  permutedimsBang P B perm

/--
Julia source: base/multidimensional.jl:1678-1678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkdims_perm(P::AbstractArray{TP,N}, B::AbstractArray{TB,N}, perm) where {TP,TB,N} = checkdims_perm(axes(P), axes(B), perm)
```
-/
def checkdimsPermArrays {PType BType AX P : Type} (axesP : PType → List AX) (axesB : BType → List AX)
    (checkdimsPerm : List AX → List AX → P → Result Unit)
    (destination : PType) (B : BType) (perm : P) : Result Unit :=
  checkdimsPerm (axesP destination) (axesB B) perm

/--
Julia source: base/multidimensional.jl:1679-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkdims_perm(indsP::NTuple{N, AbstractUnitRange}, indsB::NTuple{N, AbstractUnitRange}, perm) where {N}
    length(perm) == N || throw(ArgumentError(LazyString("expected permutation of size ", N, ", but length(perm)=", length(perm))))
    isperm(perm) || throw(ArgumentError("input is not a permutation"))
    for i in eachindex(perm)
        indsP[i] == indsB[perm[i]] || throw(DimensionMismatch("destination tensor of incorrect size"))
    end
    nothing
end
```
-/
def checkdimsPerm {AX P : Type} [BEq AX] (length : P → Nat) (isperm : P → Bool)
    (eachindex : P → CI) (getPerm : P → I64 → Result I64)
    (indsP indsB : List AX) (perm : P) : Result Unit := do
  let N := indsB.length
  if length perm != N then
    throw (.argumentError ("expected permutation of size " ++ toString N ++
      ", but length(perm)=" ++ toString (length perm)))
  if !isperm perm then throw (.argumentError "input is not a permutation")
  for i in eachindex perm do
    if (← tupleGet indsP i) != (← tupleGet indsB (← getPerm perm i)) then
      throw (.dimensionMismatch "destination tensor of incorrect size")
  return ()

/--
Julia source: base/multidimensional.jl:1689-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval @generated function permutedims!(P::$PT{$(V...)}, B::$BT{$(V...)}, perm) where $(V...)
        quote
            checkdims_perm(axes(P), axes(B), perm)

            #calculates all the strides
            native_strides = size_to_strides(1, size(B)...)
            strides = @ntuple $N d->native_strides[perm[d]]
            strides::NTuple{$N,Integer}

            #Creates offset, because indexing starts at 1
            offset = 1 - reduce(+, strides, init = 0)

            sumc = 0
            ind = 1
            @nloops($N, i, P,
                    d->(sumc += i_d*strides[d]), # PRE
                    d->(sumc -= i_d*strides[d]), # POST
                    begin # BODY
                        @inbounds P[ind] = B[sumc+offset]
                        ind += 1
                    end)

            return P
        end
    end
```
-/
def permuteLoops {PType : Type} (body : I64 → PType × I64 × I64 → Result (PType × I64 × I64)) :
    List (CI × I64) → PType × I64 × I64 → Result (PType × I64 × I64)
  | [], state => body state.2.1 state
  | (axis, stride) :: rest, state =>
    axis.foldlM (fun (P, sumc, ind) i_d => do
      let sumc := sumc + i_d * stride
      let (P, sumc, ind) ← permuteLoops body rest (P, sumc, ind)
      let sumc := sumc - i_d * stride
      return (P, sumc, ind)) state

def permutedimsBang {PType BType AX P V : Type}
    (axesP : PType → AX) (axesB : BType → AX) (checkdimsPerm : AX → AX → P → Result Unit)
    (size : BType → CI) (sizeToStrides : I64 → CI → CI) (getPerm : P → I64 → Result I64)
    (indexAxes : PType → List CI) (getindex : BType → I64 → Result V)
    (setindex : PType → V → I64 → Result PType)
    (destination : PType) (B : BType) (perm : P) : Result PType := do
  checkdimsPerm (axesP destination) (axesB B) perm
  let nativeStrides := sizeToStrides (int 1) (size B)
  let strides ← (List.range (size B).length).mapM fun (d : Nat) => do
    tupleGet nativeStrides (← getPerm perm (int (Int.ofNat (d + 1))))
  let offset := int 1 - strides.foldl (· + ·) (int 0)
  let (destination, _, _) ← permuteLoops
    (fun sumc (P, sumcState, ind) => do
      let copied ← setindex P (← getindex B (sumc + offset)) ind
      return (copied, sumcState, ind + int 1))
    (((indexAxes destination).zip strides).reverse)
    (destination, int 0, int 1)
  return destination

/--
Julia source: base/multidimensional.jl:1723-1723 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Prehashed) = x.hash
```
-/
def prehashedHash (storedHash : JInt .u64) : JInt .u64 := storedHash

/--
Julia source: base/multidimensional.jl:1764-1764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unique(A::AbstractArray; dims::D = :) where {D<:Union{Colon,Integer}} = _unique_dims(A, dims)
```
-/
def unique {A D O : Type} (uniqueDims : A → D → O) (A : A) (dims : D) : O := uniqueDims A dims
/--
Julia source: base/multidimensional.jl:1766-1766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unique_dims(A::AbstractArray, dims::Colon) = invoke(unique, Tuple{Any}, A)
```
-/
def uniqueDimsColon {A O : Type} (invokeUnique : A → O) (A : A) : O := invokeUnique A
/--
Julia source: base/multidimensional.jl:1768-1836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@generated function _unique_dims(A::AbstractArray{T,N}, dim::Integer) where {T,N}
    quote
        1 <= dim <= $N || return copy(A)
        hashes = zeros(UInt, axes(A, dim))

        # Compute hash for each row
        k = 0
        @nloops $N i A d->(if d == dim; k = i_d; end) begin
            @inbounds hashes[k] = hash(hashes[k], hash((@nref $N A i)))
        end

        # Collect index of first row for each hash
        uniquerow = similar(Array{Int}, axes(A, dim))
        firstrow = Dict{Prehashed,Int}()
        for k = axes(A, dim)
            uniquerow[k] = get!(firstrow, Prehashed(hashes[k]), k)
        end
        uniquerows = collect(values(firstrow))

        # Check for collisions
        collided = falses(axes(A, dim))
        @inbounds begin
            @nloops $N i A d->(if d == dim
                k = i_d
                j_d = uniquerow[k]
            else
                j_d = i_d
            end) begin
                if !isequal((@nref $N A j), (@nref $N A i))
                    collided[k] = true
                end
            end
        end

        if any(collided)
            nowcollided = similar(BitArray, axes(A, dim))
            while any(collided)
                # Collect index of first row for each collided hash
                empty!(firstrow)
                for j = axes(A, dim)
                    collided[j] || continue
                    uniquerow[j] = get!(firstrow, Prehashed(hashes[j]), j)
                end
                for v in values(firstrow)
                    push!(uniquerows, v)
                end

                # Check for collisions
                fill!(nowcollided, false)
                @nloops $N i A d->begin
                    if d == dim
                        k = i_d
                        j_d = uniquerow[k]
                        (!collided[k] || j_d == k) && continue
                    else
                        j_d = i_d
                    end
                end begin
                    if !isequal((@nref $N A j), (@nref $N A i))
                        nowcollided[k] = true
                    end
                end
                (collided, nowcollided) = (nowcollided, collided)
            end
        end

        @nref $N A d->d == dim ? sort!(uniquerows) : (axes(A, d))
    end
end
```
-/
def uniqueDims {A H R D M V Z : Type} (dimVal : Z → Int) (ndims : A → Nat) (copy : A → Result A)
    (axis : A → Z → CI) (loopIndices : A → List CI) (zeros : CI → Result H)
    (hashGet : H → I64 → Result (JInt .u64)) (hashSet : H → I64 → JInt .u64 → Result H)
    (getindex : A → CI → Result V) (hashValue : V → Result (JInt .u64))
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64)
    (similarRows : CI → Result R) (rowGet : R → I64 → Result I64) (rowSet : R → I64 → I64 → Result R)
    (emptyDict : Result D) (clearDict : D → Result D) (dictGetOrInsert : D → JInt .u64 → I64 → Result (D × I64))
    (dictValues : D → CI) (falses similarMask : CI → Result M) (maskGet : M → I64 → Result Bool)
    (maskSet : M → I64 → Bool → Result M) (any : M → Bool) (fillFalse : M → Result M)
    (isequal : V → V → Bool) (sort : CI → Result CI) (select : A → Z → CI → Result A)
    (array : A) (dim : Z) : Option (Result A) :=
  if !(1 ≤ dimVal dim ∧ dimVal dim ≤ ndims array) then some (copy array)
  else match initialState with
  | .error e => some (.error e)
  | .ok (.inl result) => some (.ok result)
  | .ok (.inr (hashes, state)) => whileLoop (step hashes) state
where
  initialState : Result (Sum A (H × UniqueState R D M)) := do
    let ax := axis array dim
    let dI64 := int (dimVal dim)
    let dIdx := (dimVal dim).toNat - 1
    let mut hashes ← zeros ax
    let mut k := int 0
    for i in loopIndices array do
      k ← tupleGet i dI64
      let old ← hashGet hashes k
      let valuehash ← hashValue (← getindex array i)
      hashes ← hashSet hashes k (hashUInt old valuehash)
    let mut uniquerow ← similarRows ax
    let mut firstrow ← emptyDict
    for rowKey in ax do
      let (dict, representative) ← dictGetOrInsert firstrow (← hashGet hashes rowKey) rowKey
      firstrow := dict
      uniquerow ← rowSet uniquerow rowKey representative
    let uniquerows := dictValues firstrow
    let mut collided ← falses ax
    for i in loopIndices array do
      k ← tupleGet i dI64
      let j := i.set dIdx (← rowGet uniquerow k)
      if !isequal (← getindex array j) (← getindex array i) then collided ← maskSet collided k true
    if !any collided then return .inl (← select array dim (← sort uniquerows))
    let nowcollided ← similarMask ax
    return .inr (hashes, ⟨uniquerow, firstrow, uniquerows, collided, nowcollided⟩)
  step (hashes : H) (state : UniqueState R D M) : Result (Sum A (UniqueState R D M)) := do
    let dI64 := int (dimVal dim)
    let dIdx := (dimVal dim).toNat - 1
    if !any state.collided then return .inl (← select array dim (← sort state.uniqueRows))
    let mut firstrow ← clearDict state.firstRows
    let mut uniquerow := state.rowMap
    let mut uniquerows := state.uniqueRows
    for j in axis array dim do
      if ← maskGet state.collided j then
        let (dict, representative) ← dictGetOrInsert firstrow (← hashGet hashes j) j
        firstrow := dict
        uniquerow ← rowSet uniquerow j representative
    for v in dictValues firstrow do uniquerows := uniquerows ++ [v]
    let mut nowcollided ← fillFalse state.nowCollided
    for i in loopIndices array do
      let k ← tupleGet i dI64
      let jd ← rowGet uniquerow k
      if (← maskGet state.collided k) && jd != k then
        let j := i.set dIdx jd
        if !isequal (← getindex array j) (← getindex array i) then nowcollided ← maskSet nowcollided k true
    return .inr ⟨uniquerow, firstrow, uniquerows, nowcollided, state.collided⟩

/--
Julia source: base/multidimensional.jl:1839-1841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T <: Union{AbstractVector, Tuple}
    print(io, "pairs(::$T)")
end
```
-/
def showargPairsInteger {IO T R : Type} (print : IO → String → T → String → Result IO)
    (io : IO) (_r : R) (t : T) (_toplevel : Bool) : Result IO := print io "pairs(::" t ")"

/--
Julia source: base/multidimensional.jl:1842-1844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, r::Iterators.Pairs{<:CartesianIndex, <:Any, <:Any, T}, toplevel) where T <: AbstractArray
    print(io, "pairs(::$T)")
end
```
-/
def showargPairsCartesian {IO T R : Type} (print : IO → String → T → String → Result IO)
    (io : IO) (_r : R) (t : T) (_toplevel : Bool) : Result IO := print io "pairs(::" t ")"

/--
Julia source: base/multidimensional.jl:1846-1848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, r::Iterators.Pairs{<:CartesianIndex, <:Any, <:Any, T}, toplevel) where T<:AbstractVector
    print(io, "pairs(IndexCartesian(), ::$T)")
end
```
-/
def showargPairsVector {IO T R : Type} (print : IO → String → T → String → Result IO)
    (io : IO) (_r : R) (t : T) (_toplevel : Bool) : Result IO := print io "pairs(IndexCartesian(), ::" t ")"

/--
Julia source: base/multidimensional.jl:1969-1979 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sortslices(A::AbstractArray; dims::Union{Integer, Tuple{Vararg{Integer}}}, kws...)
    if A isa Matrix && dims isa Integer && dims == 1
        # TODO: remove once the generic version becomes as fast or faster
        perm = sortperm(eachslice(A; dims); kws...)
        return A[perm, :]
    end

    B = similar(A)
    _sortslices!(B, A, Val{dims}(); kws...)
    B
end
```
-/
def sortslices {m : Type → Type} [Monad m] {AType BType D K S P : Type}
    (isMatrix : AType → Bool) (dimsIsOneInteger : D → Bool)
    (eachslice : AType → D → m S) (sortperm : S → K → m P) (getRows : AType → P → m BType)
    (similar : AType → m BType) (sortslicesBang : BType → AType → D → K → m Unit)
    (array : AType) (dims : D) (kws : K) : m BType := do
  if isMatrix array && dimsIsOneInteger dims then
    let perm ← sortperm (← eachslice array dims) kws
    return ← getRows array perm
  let B ← similar array
  sortslicesBang B array dims kws
  return B

/--
Julia source: base/multidimensional.jl:1981-1990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sortslices!(B, A, ::Val{dims}; kws...) where dims
    ves = vec(eachslice(A; dims))
    perm = sortperm(ves; kws...)
    bes = eachslice(B; dims)

    # TODO for further optimization: traverse in memory order
    for (slice, i) in zip(eachslice(B; dims), perm)
        slice .= ves[i]
    end
end
```
-/
def sortslicesBang {m : Type → Type} [Monad m] {BType AType D K SA SB V P I : Type}
    (eachsliceA : AType → D → m SA) (eachsliceB : BType → D → m SB)
    (vec : SA → V) (sortperm : V → K → m P)
    (sliceList : SB → List I) (permutationList : P → CI)
    (getindex : V → I64 → m I) (broadcastAssign : I → I → m Unit)
    (B : BType) (array : AType) (dims : D) (kws : K) : m Unit := do
  let ves := vec (← eachsliceA array dims)
  let perm ← sortperm ves kws
  let _bes ← eachsliceB B dims
  for (slice, i) in (sliceList (← eachsliceB B dims)).zip (permutationList perm) do
    broadcastAssign slice (← getindex ves i)

/--
Julia source: base/multidimensional.jl:1992-1992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(b::Ref, ::CartesianIndex{0}) = getindex(b)
```
-/
def refGetindexZero {R V : Type} (getindex : R → Result V) (b : R) : Result V := getindex b

/--
Julia source: base/multidimensional.jl:1993-1993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(b::Ref, x, ::CartesianIndex{0}) = setindex!(b, x)
```
-/
def refSetindexZero {R V : Type} (setindex : R → V → Result R) (b : R) (x : V) : Result R := setindex b x

/--
Julia source: base/multidimensional.jl:1997-2058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hash_fib(A, h::UInt)
    # Goal: Hash approximately log(N) entries with a higher density of hashed elements
    # weighted towards the end and special consideration for repeated values. Colliding
    # hashes will often subsequently be compared by equality -- and equality between arrays
    # works elementwise forwards and is short-circuiting. This means that a collision
    # between arrays that differ by elements at the beginning is cheaper than one where the
    # difference is towards the end. Furthermore, choosing `log(N)` arbitrary entries from a
    # sparse array will likely only choose the same element repeatedly (zero in this case).

    # To achieve this, we work backwards, starting by hashing the last element of the
    # array. After hashing each element, we skip `fibskip` elements, where `fibskip`
    # is pulled from the Fibonacci sequence -- Fibonacci was chosen as a simple
    # ~O(log(N)) algorithm that ensures we don't hit a common divisor of a dimension
    # and only end up hashing one slice of the array (as might happen with powers of
    # two). Finally, we find the next distinct value from the one we just hashed.

    # This is a little tricky since skipping an integer number of values inherently works
    # with linear indices, but `findprev` uses `keys`. Hoist out the conversion "maps":
    ks = keys(A)
    key_to_linear = LinearIndices(ks) # Index into this map to compute the linear index
    linear_to_key = vec(ks)           # And vice-versa

    # Start at the last index
    keyidx = last(ks)
    linidx = key_to_linear[keyidx]
    fibskip = prevfibskip = oneunit(linidx)
    first_linear = first(LinearIndices(linear_to_key))
    @nexprs 4 i -> p_i = h

    n = 0
    while true
        n += 1
        # Hash the element
        elt = A[keyidx]

        stream_idx = mod1(n, 4)
        @nexprs 4 i -> stream_idx == i && (p_i = hash_mix_linear(hash(keyidx, p_i), hash(elt, p_i)))

        # Skip backwards a Fibonacci number of indices -- this is a linear index operation
        linidx = key_to_linear[keyidx]
        linidx < fibskip + first_linear && break
        linidx -= fibskip
        keyidx = linear_to_key[linidx]

        # Only increase the Fibonacci skip once every N iterations. This was chosen
        # to be big enough that all elements of small arrays get hashed while
        # obscenely large arrays are still tractable. With a choice of N=4096, an
        # entirely-distinct 8000-element array will have ~75% of its elements hashed,
        # with every other element hashed in the first half of the array. At the same
        # time, hashing a `typemax(Int64)`-length Float64 range takes about a second.
        if rem(n, 4096) == 0
            fibskip, prevfibskip = fibskip + prevfibskip, fibskip
        end

        # Find a key index with a value distinct from `elt` -- might be `keyidx` itself
        keyidx = findprev(!isequal(elt), A, keyidx)
        keyidx === nothing && break
    end

    @nexprs 4 i -> h = hash_mix_linear(p_i, h)
    return hash_uint(h)
end
```
-/
def hashFib {A K KS LM V : Type} (keys : A → Result KS) (linearIndices : KS → Result LM)
    (vec : KS → Result KS) (lastKey : KS → Result K) (keyToLinear : LM → K → Result I64)
    (linearToKey : KS → I64 → Result K) (oneunit : I64 → I64)
    (firstLinear : KS → Result I64) (getindex : A → K → Result V) (mod1 rem : I64 → I64 → Result I64)
    (hashKey : K → JInt .u64 → Result (JInt .u64)) (hashValue : V → JInt .u64 → Result (JInt .u64))
    (hashMix : JInt .u64 → JInt .u64 → JInt .u64) (hashUInt : JInt .u64 → JInt .u64)
    (findprevDistinct : V → A → K → Result (Option K)) (A : A) (h : JInt .u64) : Option (Result (JInt .u64)) :=
  match initialState with
  | .error e => some (.error e)
  | .ok (ks, map, first, state) => whileLoop (step ks map first) state
where
  initialState : Result (KS × LM × I64 × FibState K) := do
    let ks ← keys A
    let map ← linearIndices ks
    let linearToKeys ← vec ks
    let keyidx ← lastKey ks
    let linidx ← keyToLinear map keyidx
    let fibskip := oneunit linidx
    let first ← firstLinear linearToKeys
    return (linearToKeys, map, first, ⟨keyidx, linidx, fibskip, fibskip, List.replicate 4 h, int 0⟩)
  step (ks : KS) (map : LM) (first : I64) (state : FibState K) : Result (Sum (JInt .u64) (FibState K)) := do
    let n := state.count + int 1
    let elt ← getindex A state.key
    let streamIndex ← mod1 n (int 4)
    let mut streams := state.streams
    for i in List.range 4 do
      if streamIndex == int (i + 1) then
        let old ← tupleGet streams (int (i + 1))
        let keyhash ← hashKey state.key old
        let elementhash ← hashValue elt old
        streams := streams.set i (hashMix keyhash elementhash)
    let linidx ← keyToLinear map state.key
    if linidx < state.skip + first then return .inl (hashUInt (streams.foldl (fun h p => hashMix p h) h))
    let linidx := linidx - state.skip
    let keyidx ← linearToKey ks linidx
    let (fibskip, prevfibskip) := if (← rem n (int 4096)) == int 0 then
      (state.skip + state.previousSkip, state.skip) else (state.skip, state.previousSkip)
    match ← findprevDistinct elt A keyidx with
    | none => return .inl (hashUInt (streams.foldl (fun h p => hashMix p h) h))
    | some keyidx => return .inr ⟨keyidx, linidx, fibskip, prevfibskip, streams, n⟩

/--
Julia source: base/multidimensional.jl:2077-2083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function union_split(f, @nospecialize(x), ts::Tuple{Val{T}, Vararg{Val,N}}, args...) where {T, N}
    if x isa T
        f(x, args...)
    else
        union_split(f, x, Base.tail(ts), args...)
    end
end
```
-/
def unionSplitCons {F X T Args O : Type} (isa : X → T → Bool) (call : F → X → Args → Result O)
    (unionSplit : F → X → List T → Args → Result O) (f : F) (x : X) (head : T) (tail : List T) (args : Args) : Result O :=
  if isa x head then call f x args else unionSplit f x tail args

/--
Julia source: base/multidimensional.jl:2084-2084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline union_split(f, x, ::Tuple{}, args::Vararg{Any, N}) where {N} = f(x, args...)
```
-/
def unionSplitEmpty {F X Args O : Type} (call : F → X → Args → Result O)
    (f : F) (x : X) (args : Args) : Result O := call f x args

/--
Julia source: base/multidimensional.jl:2086-2120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash_shaped(A, h0::UInt, eltype_hint=())
    h::UInt = h0
    # Axes are themselves AbstractArrays, so hashing them directly would stack overflow
    # Instead hash the tuple of firsts and lasts along each dimension
    h = hash(map(first, axes(A)), h)
    h = hash(map(last, axes(A)), h)
    len = length(A)

    if len < 8
        # for the shortest arrays we chain directly
        for elt in A
            h = union_split(hash, elt, eltype_hint, h)
        end
        return h
    elseif len < 32768
        # separate accumulator streams, unrolled
        @nexprs 8 i -> p_i::UInt = h
        off = firstindex(A) - 1
        n  = 1
        limit = len - 7
        while n <= limit
            @nexprs 8 i -> p_i = union_split(hash, A[off + n + i - 1], eltype_hint, p_i)
            n += 8
        end
        while n <= len
            p_1 = union_split(hash, A[off + n], eltype_hint, p_1)
            n += 1
        end
        # fold all streams back together
        @nexprs 8 i -> h = hash_mix_linear(p_i, h)
        return hash_uint(h)
    else
        return _hash_fib(A, h)
    end
end
```
-/
def hashShaped {A V H AX AxisValue Len FirstIndex Offset IndexN IndexNI Index Limit : Type}
    [ForIn Result A V]
    (axes : A → List AX) (first last : AX → AxisValue)
    (hashAxes : List AxisValue → JInt .u64 → Result (JInt .u64))
    (length : A → Len) (lessLength : Len → I64 → Bool) (subtractLength : Len → I64 → Result Limit)
    (firstindex : A → FirstIndex) (subtractFirst : FirstIndex → I64 → Result Offset)
    (addN : Offset → I64 → Result IndexN) (addI : IndexN → I64 → Result IndexNI)
    (subtractOne : IndexNI → I64 → Result Index)
    (getindex : A → Index → Result V) (getindexRemainder : A → IndexN → Result V)
    (unionSplitHash : V → H → JInt .u64 → Result (JInt .u64))
    (leLimit : I64 → Limit → Bool) (leLength : I64 → Len → Bool)
    (hashMix : JInt .u64 → JInt .u64 → JInt .u64) (hashUInt : JInt .u64 → JInt .u64)
    (hashFib : A → JInt .u64 → Option (Result (JInt .u64)))
    (A : A) (h0 : JInt .u64) (hint : H) : Option (Result (JInt .u64)) :=
  match shapePrefix with
  | .error error => some (.error error)
  | .ok (h, len) =>
    if lessLength len (int 8) then some (shortChain h)
    else if lessLength len (int 32768) then
      match streamPrefix len with
      | .error error => some (.error error)
      | .ok (off, limit) =>
        match whileLoop (streamStep off limit) ⟨List.replicate 8 h, int 1⟩ with
        | none => none
        | some (.error error) => some (.error error)
        | some (.ok state) =>
          match whileLoop (remainderStep off len) state with
          | none => none
          | some (.error error) => some (.error error)
          | some (.ok state) =>
            some (.ok (hashUInt (state.streams.foldl (fun h stream => hashMix stream h) h)))
    else hashFib A h
where
  shapePrefix : Result (JInt .u64 × Len) := do
    let h ← hashAxes ((axes A).map first) h0
    let h ← hashAxes ((axes A).map last) h
    return (h, length A)
  shortChain (h : JInt .u64) : Result (JInt .u64) := do
    let mut h := h
    for elt in A do h ← unionSplitHash elt hint h
    return h
  streamPrefix (len : Len) : Result (Offset × Limit) := do
    let off ← subtractFirst (firstindex A) (int 1)
    let limit ← subtractLength len (int 7)
    return (off, limit)
  streamStep (off : Offset) (limit : Limit) (state : HashStreamState) :
      Result (Sum HashStreamState HashStreamState) := do
    if !leLimit state.index limit then return .inl state
    let mut streams := state.streams
    for i in List.range 8 do
      let old ← tupleGet streams (int (i + 1))
      let index ← subtractOne (← addI (← addN off state.index) (int (i + 1))) (int 1)
      streams := streams.set i (← unionSplitHash (← getindex A index) hint old)
    return .inr ⟨streams, state.index + int 8⟩
  remainderStep (off : Offset) (len : Len) (state : HashStreamState) :
      Result (Sum HashStreamState HashStreamState) := do
    if !leLength state.index len then return .inl state
    let old ← tupleGet state.streams (int 1)
    let value ← getindexRemainder A (← addN off state.index)
    let hash ← unionSplitHash value hint old
    return .inr ⟨state.streams.set 0 hash, state.index + int 1⟩
/--
Julia source: base/multidimensional.jl:2123-2123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(A::AbstractArray, h::UInt) = hash_shaped(A, h ⊻ hash_abstractarray_seed)
```
-/
def hashArray {A : Type} (hashShaped : A → JInt .u64 → Option (Result (JInt .u64))) (A : A) (h : JInt .u64) : Option (Result (JInt .u64)) :=
  hashShaped A (JInt.wrap .u64 (Int.ofNat (Nat.xor h.val.toNat 0x7e2d6fb6448beb77)))


/-! ## Overload selection for the tuple representations -/

def increment : CI → CIs → Bool × CI
  | [], [] => incEmpty
  | [s], [r] => incSingle s r
  | s :: s' :: ss, r :: r' :: rs =>
    incCons (fun _ _ => increment (s' :: ss) (r' :: rs)) s (s' :: ss) r (r' :: rs)
  | _, _ => (false, [])

def decrement : CI → CIs → Bool × CI
  | [], [] => decEmpty
  | [s], [r] => decSingle s r
  | s :: s' :: ss, r :: r' :: rs =>
    decCons (fun _ _ => decrement (s' :: ss) (r' :: rs)) s (s' :: ss) r (r' :: rs)
  | _, _ => (false, [])


def circcopyDispatch {Dest Src : Type} (length : Rng → I64) (mod : I64 → I64 → Result I64)
    (unitRange : I64 → I64 → Rng) (copyto : Dest → CIs → Src → CIs → Result Dest)
    (dest : Dest) (rdest : CIs) (indsdest : CIs) (src : Src) (rsrc : CIs) (indssrc : CIs) : Result Dest :=
  match indsdest, indssrc with
  | indd1 :: td, inds1 :: ts =>
    circcopyCons length mod unitRange
      (fun dest rd _ src rs _ => circcopyDispatch length mod unitRange copyto dest rd td src rs ts)
      dest rdest indd1 td src rsrc inds1 ts
  | _, _ => circcopyBase copyto dest rdest indsdest src rsrc indssrc
termination_by indsdest.length

def circshiftDispatch {Dest Src Z : Type} (mod : Z → I64 → Result I64) (length : Rng → I64)
    (unitRange : I64 → I64 → Rng) (copyto : Dest → CIs → Src → CIs → Result Dest)
    (dest : Dest) (rdest : CIs) (src : Src) (rsrc : CIs) (inds : CIs) (shift : List Z) : Result Dest :=
  match inds, shift with
  | ind1 :: ti, d :: ts => circshiftCons mod length unitRange
      (fun dest rd src rs _ _ => circshiftDispatch mod length unitRange copyto dest rd src rs ti ts)
      dest rdest src rsrc ind1 ti d ts
  | _, _ => circshiftBase copyto dest rdest src rsrc inds shift
termination_by inds.length

def flattenDispatch : List CI → Result CI
  | [] => .ok flattenEmpty
  | [x] => flattenSingle .ok x
  | h :: x :: xs => flattenCons (flattenSingle .ok) (fun _ => flattenDispatch (x :: xs)) h (x :: xs)
termination_by xs => xs.length

/-- Trusted function application for the `union_split` dispatch helper. -/
def applyHash {V : Type} (hash : V → JInt .u64 → Result (JInt .u64))
    (value : V) (seed : JInt .u64) : Result (JInt .u64) := hash value seed

/-- Julia dispatch between the empty and nonempty type-hint tuple methods. -/
def unionSplitHashDispatch {V Tag : Type} (isa : V → Tag → Bool)
    (hash : V → JInt .u64 → Result (JInt .u64)) (value : V) :
    List Tag → JInt .u64 → Result (JInt .u64)
  | [], seed => unionSplitEmpty applyHash hash value seed
  | tag :: rest, seed => unionSplitCons isa applyHash
      (fun hash value _ seed => unionSplitHashDispatch isa hash value rest seed)
      hash value tag rest seed

def split1Dispatch {A : Type} : List A → List Bool → List A
  | [], [] => split1EmptyEmpty
  | [], ref@(_ :: _) => split1EmptyRef ref
  | t@(_ :: _), [] => split1TupleEmpty t
  | h :: t, _ :: r => split1Cons (fun _ _ => split1Dispatch t r) h t r

def splitrestDispatch {A : Type} : List A → List Bool → List A
  | [], [] => splitrestEmptyEmpty
  | t@(_ :: _), [] => splitrestTupleEmpty t
  | [], ref@(_ :: _) => splitrestEmptyRef ref
  | _ :: t, _ :: r => splitrestCons (fun _ _ => splitrestDispatch t r) t r

def checkBooleanAxesDispatch {AX : Type} [BEq AX] (oneToOne : AX) : List AX → List AX → Bool
  | [], axes => checkBooleanAxesEmpty oneToOne axes
  | i :: is, a :: as => checkBooleanAxesCons (fun _ _ => checkBooleanAxesDispatch oneToOne is as) i a is as
  | _ :: _, [] => false

def ensureIndexableDispatch {I : Type} : List I → List I
  | [] => ensureIndexableEmpty
  | h :: t => ensureIndexableCons (fun _ => ensureIndexableDispatch t) h t

inductive IndexTraitItem (S A : Type) where
  | scalar (s : S)
  | colon
  | mask (m : A)
  | cart (c : CI)
  | array (n : Nat) (a : A)

def indexNdimsDispatch {S A : Type} : List (IndexTraitItem S A) → List Bool
  | [] => indexNdimsEmpty
  | .scalar s :: tail => indexNdimsScalar (fun _ => indexNdimsDispatch tail) (.scalar s) tail
  | .colon :: tail => indexNdimsScalar (fun _ => indexNdimsDispatch tail) .colon tail
  | .mask m :: tail => indexNdimsScalar (fun _ => indexNdimsDispatch tail) (.mask m) tail
  | .cart c :: tail => indexNdimsCartesian (fun _ => indexNdimsDispatch tail) c tail
  | .array n a :: tail => indexNdimsCartesianArray (fun _ => indexNdimsDispatch tail) n a tail

def indexDimsumDispatch {S A : Type} : List (IndexTraitItem S A) → List Bool
  | [] => indexDimsumEmpty
  | .scalar s :: tail => indexDimsumScalar (fun _ => indexDimsumDispatch tail) (.scalar s) tail
  | .colon :: tail => indexDimsumColon (fun _ => indexDimsumDispatch tail) tail
  | .mask m :: tail => indexDimsumMask (fun _ => indexDimsumDispatch tail) m tail
  | .cart c :: tail => indexDimsumScalar (fun _ => indexDimsumDispatch tail) (.cart c) tail
  | .array n a :: tail => indexDimsumArray (fun _ => indexDimsumDispatch tail) n a tail

def indexLengthsDispatch {S A : Type} (lenOf : A → I64) : List (Sum S A) → CI
  | [] => indexLengthsEmpty
  | .inl s :: rest => indexLengthsScalar (fun _ => indexLengthsDispatch lenOf rest) s rest
  | .inr a :: rest => indexLengthsArray lenOf (fun _ => indexLengthsDispatch lenOf rest) a rest

def indexShapeDispatch {S A AX : Type} (axesOf : A → List AX) : List (Sum S A) → List AX
  | [] => indexShapeEmpty
  | .inl s :: rest => indexShapeScalar (fun _ => indexShapeDispatch axesOf rest) s rest
  | .inr a :: rest => indexShapeArray axesOf (fun _ => indexShapeDispatch axesOf rest) a rest

def indexSizesDispatch {S A : Type} (sizeOf : A → CI) : List (Sum S A) → CI
  | [] => indexSizesEmpty
  | .inl s :: rest => indexSizesScalar (fun _ => indexSizesDispatch sizeOf rest) s rest
  | .inr a :: rest => indexSizesArray sizeOf (fun _ => indexSizesDispatch sizeOf rest) a rest

def intFld (x y : I64) : Jl I64 :=
  if y.val = 0 then .error .divideError else .ok (JInt.lit .i64 (x.val.fdiv y.val))

def intMod (a b : I64) : Result I64 :=
  (JuliaLean.base.int.mod_BitSigned intFld a b).mapError fromCoreError

def unitRange (lo hi : I64) : Rng := ⟨lo, int 1, (hi.val - lo.val + 1).toNat⟩

def cartesianIterTraceLoop (r : CIs) : Nat → CI → List (CI × CI)
  | 0, _ => []
  | fuel + 1, s =>
    match cartesianIterateNext increment r s with
    | none => []
    | some (idx', s') => (idx', s') :: cartesianIterTraceLoop r fuel s'

def cartesianIterTrace (r : CIs) : List (CI × CI) :=
  match cartesianIterateFirst r with
  | none => []
  | some (idx, st) => (idx, st) :: cartesianIterTraceLoop r ((r.map Rng.len).prod - 1) st

def linearIterTrace (r : CIs) : List (I64 × I64) :=
  (cartesianIterTrace [unitRange (int 1) (int (r.map Rng.len).prod)]).filterMap fun (c, s) =>
    match c, s with
    | i :: _, j :: _ => some (i, j)
    | _, _ => none
def ordinalRangeEq (r s : Rng) : Bool :=
  if r.len == 0 then s.len == 0
  else if r.len == 1 then s.len == 1 && JuliaLean.base.int.eqSame r.start s.start
  else r.len == s.len && JuliaLean.base.int.eqSame r.start s.start &&
    JuliaLean.base.int.eqSame r.step s.step && JuliaLean.base.int.eqSame r.last s.last

/-- A concrete finite abstract array interface. Storage identity is separate
from axes and cells, so distinct equal arrays and offset axes remain observable.
Cells use the standard fully assigned vector reader from `base.array`. -/
structure CellArray (V : Type) where
  identity : Nat
  axes : CIs
  cells : List (Option V)
  deriving DecidableEq

def CellArray.size (a : CellArray V) : CI :=
  cartesianIndicesSize (fun r => int r.len) a.axes

def CellArray.linearGet (a : CellArray V) (i : I64) : Result V := do
  match ← vectorRead a.cells i with
  | some value => return value
  | none => throw .undefRefError

def CellArray.linearSet (a : CellArray V) (value : V) (i : I64) : Result (CellArray V) := do
  let _ ← vectorRead a.cells i
  return { a with cells := a.cells.set (i.val - 1).toNat (some value) }

def CellArray.offset (a : CellArray V) (i : CI) : I64 :=
  int ((columnMajor (a.axes.map Rng.elems)).idxOf i + 1)

def CellArray.get (a : CellArray V) (i : CI) : Result V :=
  a.linearGet (a.offset i)

def CellArray.set (a : CellArray V) (value : V) (i : CI) : Result (CellArray V) :=
  a.linearSet value (a.offset i)

def CellArray.checkbounds (a : CellArray V) (i : CI) : Result Unit :=
  if i.length == a.axes.length && cartesianIndicesContains i a.axes then .ok ()
  else .error .boundsError

def CellArray.similar (a : CellArray V) (dims : CI) : Result (CellArray V) :=
  if dims.any (fun n => n.val < 0) then .error (.argumentError "negative dimensions")
  else .ok ⟨a.identity + 1, dims.map (unitRange (int 1)),
    List.replicate (dims.map (fun n => n.val.toNat)).prod none⟩

/-- Whole-array copying is the foreign `copyto!` interface: equal-size arrays
copy their complete linear contents while retaining the destination axes. -/
def CellArray.copy (dest src : CellArray V) : Result (CellArray V) :=
  if dest.cells.length = src.cells.length then .ok { dest with cells := src.cells }
  else .error .dimensionMismatch

def regionIndexAxes (ranges : CIs) : CIs :=
  cartesianIndicesAxes (fun r => unitRange (int 1) (int r.len)) ranges

def regionGet (ranges : CIs) (i : CI) : Result CI :=
  cartesianIndicesGetindex
    (fun ranges i =>
      if i.length == ranges.length && cartesianIndicesContains i (regionIndexAxes ranges) then .ok ()
      else .error .boundsError)
    (fun range i => vectorRead range.elems i) ranges i

def CellArray.copyRegion (dest : CellArray V) (rd : CIs)
    (src : CellArray V) (rs : CIs) : Result (CellArray V) :=
  copytoCartesian (fun ranges => ranges.any (·.len == 0))
    (cartesianIndicesSize (fun r => int r.len)) CellArray.checkbounds CellArray.checkbounds
    (fun _ src => .ok src) regionIndexAxes
    (fun ranges => columnMajor (ranges.map Rng.elems)) regionGet
    CellArray.get CellArray.set dest rd src rs

def circcopyOutcome (dest src : CellArray V) : Result (CellArray V) :=
  circcopy (fun a b => a.identity == b.identity) CellArray.axes CellArray.axes
    (fun r => int r.len) CellArray.copy
    (circcopyDispatch (fun r => int r.len) intMod unitRange CellArray.copyRegion) dest src

def permutationValid (perm : CI) : Bool :=
  decide (perm.map (fun x => x.val.toNat) |>.Perm ((List.range perm.length).map (· + 1)))

def CellArray.strides (first : I64) : CI → CI
  | [] => []
  | n :: ns => first :: CellArray.strides (first * n) ns

def permutedArrayOutcome (source : CellArray V) (perm : CI) : Result (CellArray V) :=
  permutedims CellArray.size List.length permutationValid vectorRead CellArray.similar
    (permutedimsBang CellArray.axes CellArray.axes
      (checkdimsPerm List.length permutationValid
        (fun p => (List.range p.length).map fun (i : Nat) => int (Int.ofNat i + 1)) vectorRead)
      CellArray.size CellArray.strides vectorRead
      (fun a => a.axes.map Rng.elems) CellArray.linearGet CellArray.linearSet) source perm

/-- Coordinate-indexed array interface for arbitrary-rank `copyto!`, `circshift!`, and `circcopy!`. -/
structure GridArray (V : Type) where
  identity : Nat
  axes : CIs
  cells : CI → Option V

def GridArray.size (a : GridArray V) : CI :=
  cartesianIndicesSize (fun r => int r.len) a.axes

def GridArray.checkbounds (a : GridArray V) (i : CI) : Result Unit :=
  if i.length == a.axes.length && cartesianIndicesContains i a.axes then .ok ()
  else .error .boundsError

def GridArray.get (a : GridArray V) (i : CI) : Result V :=
  match a.cells i with
  | some value => .ok value
  | none => .error .undefRefError

def GridArray.set (a : GridArray V) (value : V) (i : CI) : Result (GridArray V) :=
  .ok { a with cells := fun j => if j == i then some value else a.cells j }

def GridArray.copyRegion {VD VS : Type} (conv : VS → VD) (dest : GridArray VD) (rd : CIs)
    (src : GridArray VS) (rs : CIs) : Result (GridArray VD) :=
  copytoCartesian (fun ranges => ranges.any (·.len == 0))
    (cartesianIndicesSize (fun r => int r.len)) GridArray.checkbounds GridArray.checkbounds
    (fun _ src => .ok src) regionIndexAxes
    (fun ranges => columnMajor (ranges.map Rng.elems)) regionGet
    GridArray.get (fun d v i => GridArray.set d (conv v) i) dest rd src rs

def GridArray.copy {VD VS : Type} (conv : VS → VD) (dest : GridArray VD) (src : GridArray VS) :
    Result (GridArray VD) :=
  .ok { dest with cells := fun J =>
    let K := (J.zip (src.axes.zip dest.axes)).map (fun (j, s, d) => int (j.val - d.start.val + s.start.val))
    if J.length == dest.axes.length && cartesianIndicesContains J dest.axes then (src.cells K).map conv
    else dest.cells J }

def GridArray.circshift {VD VS : Type} (conv : VS → VD) (dest : GridArray VD) (src : GridArray VS)
    (shifts : List Int) : Result (GridArray VD) :=
  JuliaLean.base.multidimensional.circshift
    (fun a b => a.identity == b.identity) GridArray.axes GridArray.axes (· == ·)
    (fun a => a.axes.any (·.len == 0))
    (fun sh N => if sh.length > N then .error (.argumentError "tuple too long")
                 else .ok (sh ++ List.replicate (N - sh.length) 0))
    (circshiftDispatch (fun (d : Int) l => if l.val == 0 then .error .divideError else .ok (int (d % l.val)))
      (fun r => int r.len) unitRange (GridArray.copyRegion conv))
    src.axes.length dest src shifts

def GridArray.circcopy {VD VS : Type} (conv : VS → VD) (dest : GridArray VD) (src : GridArray VS) :
    Result (GridArray VD) :=
  JuliaLean.base.multidimensional.circcopy
    (fun a b => a.identity == b.identity) GridArray.axes GridArray.axes (fun r => int r.len)
    (GridArray.copy conv) (circcopyDispatch (fun r => int r.len) intMod unitRange (GridArray.copyRegion conv))
    dest src

def vectorSlice {α : Type} (v : List α) (ranges : CIs) : Result (List α) := do
  let r ← tupleGet ranges (int 1)
  r.elems.mapM (vectorRead v)

def vectorDiff {t : IntTy} (v : List (JInt t)) : Result (List (JInt t)) :=
  diffVector (diffArray (fun _ => .ok ()) (fun xs => [unitRange (int 1) (int xs.length)])
    Rng.last unitRange id vectorSlice
    (fun hi lo => if hi.length == lo.length then .ok (List.zipWith JuliaLean.base.int.sub hi lo)
                  else .error .dimensionMismatch)
    (fun d : I64 => d.val) 1) v

def rangeDiff {t : IntTy} {Z : Type} (value : Z → Int) (v : List (JInt t)) (dims : Z) :
    Result (List (JInt t)) :=
  diffRange value (fun _ => int 1) (fun xs => int xs.length) vectorRead
    (fun a b => .ok (JuliaLean.base.int.sub a b)) (fun lo hi => (unitRange lo hi).elems) v dims

def diffArrayAxes (sz : List Nat) (dims : Int) : Result CI :=
  diffArray (fun _ => .ok ())
    (fun sz : List Nat => sz.map (fun (n : Nat) => unitRange (int 1) (int n)))
    Rng.last unitRange id
    (fun _ rs => .ok (cartesianIndicesSize (fun r => int r.len) rs))
    (fun r1 r0 => if r1 == r0 then .ok r1 else .error .dimensionMismatch)
    id sz.length sz dims

namespace Alias

open AliasData

/-- Julia dispatch for index tuple overloads, with scalar, range and array
callees taken from the existing earlier-array interfaces. -/
def overlap : List Idx → List Idx → Result Bool
  | [], [] => .ok indicesOverlapEmpty
  | [], other@(_ :: _) => indicesOverlapLeftEmpty (fun message => .error (.errorException message)) other
  | other@(_ :: _), [] => indicesOverlapRightEmpty (fun message => .error (.errorException message)) other
  | a :: left, b :: right =>
    match a, b with
    | .other _, _ | _, .other _ =>
      .ok (indicesOverlapFallback (a :: left) (b :: right))
    | .urange alo ahi, .urange blo bhi =>
      indicesOverlapUnitRanges Prod.fst Prod.snd max min (fun a b => decide (a ≤ b))
        (fun _ _ => overlap left right) (alo, ahi) (blo, bhi) left right
    | .urange _ _, .srange _ _ _ | .srange _ _ _, .urange _ _ | .srange _ _ _, .srange _ _ _ =>
      indicesOverlapRanges
        (fun xs ys => .ok (xs.filter fun x => ys.any (fun y => y.eqb x)))
        List.isEmpty (fun _ _ => overlap left right) a.elems b.elems left right
    | .scalar x, .scalar y =>
      indicesOverlapScalars (fun x y => decide (x = y)) (fun _ _ => overlap left right) x y left right
    | .scalar x, _ =>
      indicesOverlapScalarArray inIdx (fun _ _ => overlap left right) (.int x) b left right
    | _, .scalar y =>
      indicesOverlapArrayScalar inIdx (fun _ _ => overlap left right) a (.int y) left right
    | _, _ =>
      indicesOverlapArrays (fun i => i.elems.length) (fun i n => vectorRead i.elems n)
        inIdx (fun _ _ => overlap left right) a b left right

termination_by structural left _right => left

def mightalias {V : Type} (a b : CellArray V × List Idx) : Result Bool :=
  mightaliasSubarray Prod.fst Prod.snd (fun _ => false)
    (parentsMatchAbstract (fun p q => p.identity == q.identity))
    overlap (fun p => [p.identity]) (fun _ => [])
    (fun xs ys => xs.all (fun x => !ys.contains x)) a b



end Alias

end JuliaLean.base.multidimensional
