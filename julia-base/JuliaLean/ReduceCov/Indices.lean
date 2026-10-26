import JuliaLean.ReduceCov.Basic

/-!
# `base/indices.jl`: index ranges, `LinearIndices`, shape checks, `to_index`

Master `bbfa0ce4150`. A unit range with `Int` elements is a `UR`: `Base.OneTo(n)`,
`a:b`, `IdentityUnitRange(r)` or `Slice(r)`. Its first and last elements are the
`Int64` values of its fields; `len` is its element count and `vals` its elements
in order (`Int` values in the model; every range here is an axis of fewer than
`typemax(Int)` elements, so Julia's `length` does not wrap). An index argument is
an `Ix`; Bool elements of a Bool range are `0`/`1`.
-/

namespace JuliaLean.ReduceCov.Indices

open JuliaLean.ReduceCov

/-- An `AbstractUnitRange{Int}`. -/
inductive UR where
  /-- `Base.OneTo(n)`, `n ≥ 0` (the constructor clamps at zero). -/
  | oneTo (n : I64)
  /-- `a:b`, with `b ≥ a - 1` (the constructor normalizes an empty range). -/
  | unit (a b : I64)
  | ident (r : UR)
  | slice (r : UR)
  deriving DecidableEq, Repr

namespace UR

/-- `first(r)`; `first(S::Slice) = first(S.indices)` (`base/indices.jl:347`),
`first(S::IdentityUnitRange) = first(S.indices)` (`:374`). -/
def first : UR → Int
  | .oneTo _ => 1
  | .unit a _ => a.val
  | .ident r | .slice r => r.first

/-- `last(r)`, `base/indices.jl:348, 375`. -/
def last : UR → Int
  | .oneTo n => n.val
  | .unit _ b => b.val
  | .ident r | .slice r => r.last

/-- `length(r)`; `size(S) = (length(S.indices),)` (`base/indices.jl:349, 376`) and
`unsafe_length(S::IdentityUnitRange) = unsafe_length(S.indices)` (`:377`). -/
def len (r : UR) : Nat := (r.last - r.first + 1).toNat

/-- The elements in iteration order: `iterate(S::Slice, s...) = iterate(S.indices, s...)`
and likewise for `IdentityUnitRange` (`base/indices.jl:354, 417`). -/
def vals (r : UR) : List Int := (List.range r.len).map fun (k : Nat) => r.first + (k : Int)

/-- `axes1(r)`: `axes1(S::Slice) = IdentityUnitRange(S.indices)` and
`axes1(S::Slice{<:AbstractOneTo}) = S.indices` (`base/indices.jl:344-345`),
`axes1(S::IdentityUnitRange) = S` and `axes1(S::IdentityUnitRange{<:AbstractOneTo}) =
S.indices` (`:371-372`); a plain range has `axes1 = OneTo(length(r))`. -/
def axes1 : UR → UR
  | .oneTo n => .oneTo n
  | .unit a b => .oneTo (i64 (UR.unit a b).len)
  | .ident (.oneTo n) => .oneTo n
  | .ident r => .ident r
  | .slice (.oneTo n) => .oneTo n
  | .slice r => .ident r

/-- `axes(S) = (axes1(S),)`, `base/indices.jl:343, 370`. -/
def axes (r : UR) : List UR := [r.axes1]

/-- `Slice(S::Slice) = S` (`base/indices.jl:340`); a `Slice` of any other range wraps it. -/
def mkSlice : UR → UR
  | .slice r => .slice r
  | r => .slice r

/-- `IdentityUnitRange(S::IdentityUnitRange) = S` (`base/indices.jl:366`). -/
def mkIdent : UR → UR
  | .ident r => .ident r
  | r => .ident r

/-- `T(r)` for `T = UnitRange{Int}`: the same elements as a plain range. -/
def toUnitRange (r : UR) : UR := .unit (i64 r.first) (i64 r.last)

/-- `Slice{UnitRange{Int}}(S::Slice) = Slice{T}(T(S.indices))` and the
`IdentityUnitRange` analogue, `base/indices.jl:341, 367`. -/
def convertWrapped : UR → UR
  | .slice r => .slice r.toUnitRange
  | .ident r => .ident r.toUnitRange
  | r => r

/-- `show(io, r)`: `Base.OneTo(n)`, `a:b`, `print(io, "Base.Slice(", r.indices, ")")` and
`print(io, "Base.IdentityUnitRange(", r.indices, ")")`, `base/indices.jl:353, 416`. -/
def str : UR → String
  | .oneTo n => s!"Base.OneTo({n.val})"
  | .unit a b => s!"{a.val}:{b.val}"
  | .ident r => "Base.IdentityUnitRange(" ++ r.str ++ ")"
  | .slice r => "Base.Slice(" ++ r.str ++ ")"

end UR

/-! ## Indexing `Slice` and `IdentityUnitRange`, `base/indices.jl:350-427` -/

/-- An index argument. -/
inductive Ix where
  /-- `i::Int`. -/
  | int (i : I64)
  /-- `i::Integer` of another `BitInteger` type. -/
  | integer (t : IntTy) (i : JInt t)
  /-- `i::Bool`. -/
  | bool (b : Bool)
  /-- An `AbstractUnitRange{Int}`. -/
  | urange (r : UR)
  /-- `a:b::UnitRange{Bool}`. -/
  | brange (a b : Bool)
  /-- `a:s:b::StepRange{Int,Int}`, `s ≠ 0`. -/
  | srange (a s b : I64)
  /-- `StepRange(a, s, b)::StepRange{Bool,Int}`, `s ≠ 0`. -/
  | bsrange (a : Bool) (s : I64) (b : Bool)
  deriving DecidableEq, Repr

/-- `Int(b)`. -/
def bInt (b : Bool) : Int := if b then 1 else 0

/-- The elements of `a:s:b`: `a, a + s, …` up to `b` (`s ≠ 0`). -/
def stepVals (a s b : Int) : List Int :=
  let n : Nat := if s > 0 then (if b < a then 0 else ((b - a) / s + 1).toNat)
    else if s < 0 then (if a < b then 0 else ((a - b) / (-s) + 1).toNat) else 0
  (List.range n).map fun (k : Nat) => a + (k : Int) * s

/-- Whether an index is a Bool mask (an `AbstractRange{Bool}`). -/
def Ix.isMask : Ix → Bool
  | .brange .. | .bsrange .. => true
  | _ => false

/-- The elements of a non-scalar index. -/
def Ix.elems : Ix → List Int
  | .urange r => r.vals
  | .brange a b => stepVals (bInt a) 1 (bInt b)
  | .srange a s b => stepVals a.val s.val b.val
  | .bsrange a s b => stepVals (bInt a) s.val (bInt b)
  | _ => []

/-- `checkindex(Bool, inds, i)` for a unit range `inds` (`base/abstractarray.jl:751-760`,
`base/multidimensional.jl:916-917`): a real scalar is in `first(inds):last(inds)`; a
range is empty or has its first and last elements in bounds; a Bool range must
have `axes1(I) == inds`. -/
def checkIndex (inds : UR) (i : Ix) : Bool :=
  let inB (x : Int) : Bool := decide (inds.first ≤ x ∧ x ≤ inds.last)
  match i with
  | .int i => inB i.val
  | .integer _ i => inB i.val
  | .bool b => inB (bInt b)
  | .brange .. | .bsrange .. =>
    decide ((List.range i.elems.length).map (fun (k : Nat) => (k : Int) + 1) = inds.vals)
  | _ => match i.elems.head?, i.elems.getLast? with
    | some x, some y => inB x && inB y
    | _, _ => true

/-- `@boundscheck checkbounds(S, i)` for a one-dimensional `S`. -/
def checkbounds (S : UR) (i : Ix) : RJ Unit :=
  if checkIndex S.axes1 i then .ok () else .error boundsErr

/-- `range(start; length = n, step = s)`: `n` elements from `start` in steps of `s`. -/
def rangeLen (start : Int) (n : Int) (s : Int) : List Int :=
  (List.range n.toNat).map fun (k : Nat) => start + (k : Int) * s

/-! ### The methods of `Slice` and `IdentityUnitRange`, one function each -/

namespace SliceM

/-- `Slice(S::Slice) = S`, `base/indices.jl:340`. -/
def ofSlice (S : UR) : UR := S

/-- `Slice{T}(S::Slice) = Slice{T}(T(S.indices))`, `base/indices.jl:341`, for
`T = UnitRange{Int}`. -/
def convert (indices : UR) : UR := .slice indices.toUnitRange

/-- `axes(S::Slice) = (axes1(S),)`, `base/indices.jl:343`. -/
def axes (S : UR) : List UR := [S.axes1]

/-- `axes1(S::Slice) = IdentityUnitRange(S.indices)`, `base/indices.jl:344`. -/
def axes1 (indices : UR) : UR := .ident indices

/-- `axes1(S::Slice{<:AbstractOneTo{<:Integer}}) = S.indices`, `base/indices.jl:345`. -/
def axes1OneTo (indices : UR) : UR := indices

/-- `first(S::Slice) = first(S.indices)`, `base/indices.jl:347`. -/
def first (indices : UR) : Int := indices.first

/-- `last(S::Slice) = last(S.indices)`, `base/indices.jl:348`. -/
def last (indices : UR) : Int := indices.last

/-- `size(S::Slice) = (length(S.indices),)`, `base/indices.jl:349`. -/
def size (indices : UR) : List Nat := [indices.len]

/-- `getindex(S::Slice, i::Int) = (@boundscheck checkbounds(S, i); i)`, `base/indices.jl:350`. -/
def getindexInt (S : UR) (i : I64) : RJ (List Int) := do checkbounds S (.int i); pure [i.val]

/-- `getindex(S::Slice, i::AbstractUnitRange{<:Integer})`, `base/indices.jl:351`: bounds
check, then `i` (`i` is a unit range, possibly of `Bool`s). -/
def getindexUnitRange (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::Slice, i::StepRange{<:Integer})`, `base/indices.jl:352`: bounds check,
then `i`. -/
def getindexStepRange (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::Slice{<:AbstractUnitRange{<:Integer}}, i::IdentityUnitRange)`,
`base/indices.jl:410-415`: bounds check, then `i`. -/
def getindexIdent (S : UR) (I : UR) : RJ (List Int) := do
  checkbounds S (.urange (.ident I)); pure (UR.ident I).vals

/-- `show(io, r::Slice) = print(io, "Base.Slice(", r.indices, ")")`, `base/indices.jl:353`. -/
def show_ (indices : UR) : String := "Base.Slice(" ++ indices.str ++ ")"

/-- `iterate(S::Slice, s...) = iterate(S.indices, s...)`, `base/indices.jl:354`: the
iterated values. -/
def iterate (indices : UR) : List Int := indices.vals

end SliceM

namespace IdentM

/-- `IdentityUnitRange(S::IdentityUnitRange) = S`, `base/indices.jl:366`. -/
def ofIdent (S : UR) : UR := S

/-- `IdentityUnitRange{T}(S::IdentityUnitRange) = IdentityUnitRange{T}(T(S.indices))`,
`base/indices.jl:367`, for `T = UnitRange{Int}`. -/
def convert (indices : UR) : UR := .ident indices.toUnitRange

/-- `axes(S::IdentityUnitRange) = (axes1(S),)`, `base/indices.jl:370`. -/
def axes (S : UR) : List UR := [S.axes1]

/-- `axes1(S::IdentityUnitRange) = S`, `base/indices.jl:371`. -/
def axes1 (indices : UR) : UR := .ident indices

/-- `axes1(S::IdentityUnitRange{<:AbstractOneTo{<:Integer}}) = S.indices`,
`base/indices.jl:372`. -/
def axes1OneTo (indices : UR) : UR := indices

/-- `first(S::IdentityUnitRange) = first(S.indices)`, `base/indices.jl:374`. -/
def first (indices : UR) : Int := indices.first

/-- `last(S::IdentityUnitRange) = last(S.indices)`, `base/indices.jl:375`. -/
def last (indices : UR) : Int := indices.last

/-- `size(S::IdentityUnitRange) = (length(S.indices),)`, `base/indices.jl:376`. -/
def size (indices : UR) : List Nat := [indices.len]

/-- `unsafe_length(S::IdentityUnitRange) = unsafe_length(S.indices)`, `base/indices.jl:377`. -/
def unsafeLength (indices : UR) : Nat := indices.len

/-- `getindex(S::IdentityUnitRange, i::Integer)`, `base/indices.jl:378`: bounds check,
then `convert(eltype(S), i)`, i.e. `Int(i)`. -/
def getindexInteger (S : UR) (i : Ix) (k : Int) : RJ (List Int) := do checkbounds S i; pure [k]

/-- `getindex(S::IdentityUnitRange, i::Bool)`, `base/indices.jl:379`. -/
def getindexBool (b : Bool) : RJ (List Int) := .error (argErr s!"invalid index: {b} of type Bool")

/-- `getindex(S::IdentityUnitRange, i::AbstractUnitRange{<:Integer})`,
`base/indices.jl:380-384`: bounds check, then `convert(AbstractUnitRange{Int}, i)`. -/
def getindexUnitRange (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::IdentityUnitRange, i::AbstractUnitRange{Bool})`, `base/indices.jl:385-389`:
bounds check, then `range(first(i) ? first(S) : last(S), length = last(i))`. -/
def getindexBoolUnitRange (S : UR) (a b : Bool) : RJ (List Int) := do
  checkbounds S (.brange a b); pure (rangeLen (if a then S.first else S.last) (bInt b) 1)

/-- `getindex(S::IdentityUnitRange, i::StepRange{<:Integer})`, `base/indices.jl:390-394`:
bounds check, then `convert(AbstractRange{Int}, i)`. -/
def getindexStepRange (S : UR) (i : Ix) : RJ (List Int) := do checkbounds S i; pure i.elems

/-- `getindex(S::IdentityUnitRange, i::StepRange{Bool})`, `base/indices.jl:395-399`: bounds
check, then `range(first(i) ? first(S) : last(S), length = last(i), step = Int(step(i)))`. -/
def getindexBoolStepRange (S : UR) (a : Bool) (s : I64) (b : Bool) : RJ (List Int) := do
  checkbounds S (.bsrange a s b); pure (rangeLen (if a then S.first else S.last) (bInt b) s.val)

/-- `getindex(S::IdentityUnitRange{<:AbstractUnitRange{<:Integer}}, i::IdentityUnitRange)`,
`base/indices.jl:404-409`: bounds check, then `i`. -/
def getindexIdent (S : UR) (I : UR) : RJ (List Int) := do
  checkbounds S (.urange (.ident I)); pure (UR.ident I).vals

/-- `show(io, r::IdentityUnitRange)`, `base/indices.jl:416`. -/
def show_ (indices : UR) : String := "Base.IdentityUnitRange(" ++ indices.str ++ ")"

/-- `iterate(S::IdentityUnitRange, s...) = iterate(S.indices, s...)`, `base/indices.jl:417`. -/
def iterate (indices : UR) : List Int := indices.vals

end IdentM

/-- `getindex(v::AbstractRange, i::Integer)` (`base/array.jl:3224-3230`), reached by a
`Slice` with a non-`Int` integer: `i isa Bool` throws, otherwise `checkbounds` and
`unsafe_getindex(v, i) = first(v) + (i - 1) * step(v)` (`base/range.jl:985`). -/
def rangeGetindexInteger (S : UR) (i : Ix) (k : Int) : RJ (List Int) := do
  checkbounds S i; pure [S.first + (k - 1)]

/-- `S[i]` for `S = Slice(r)`, dispatching to the methods above. -/
def sliceGet (r : UR) (i : Ix) : RJ (List Int) :=
  let S := UR.slice r
  match i with
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .int k => SliceM.getindexInt S k
  | .integer _ k => rangeGetindexInteger S i k.val
  | .urange (.ident I) => SliceM.getindexIdent S I
  | .urange _ | .brange .. => SliceM.getindexUnitRange S i
  | .srange .. | .bsrange .. => SliceM.getindexStepRange S i

/-- `S[i]` for `S = IdentityUnitRange(r)`, dispatching to the methods above. -/
def identGet (r : UR) (i : Ix) : RJ (List Int) :=
  let S := UR.ident r
  match i with
  | .bool b => IdentM.getindexBool b
  | .int k => IdentM.getindexInteger S i k.val
  | .integer _ k => IdentM.getindexInteger S i k.val
  | .urange (.ident I) => IdentM.getindexIdent S I
  | .urange _ => IdentM.getindexUnitRange S i
  | .brange a b => IdentM.getindexBoolUnitRange S a b
  | .srange .. => IdentM.getindexStepRange S i
  | .bsrange a s b => IdentM.getindexBoolStepRange S a s b

/-- `getindex(S::AbstractOneTo{<:Integer}, I::IdentityUnitRange)`,
`base/indices.jl:423-427`: `checkbounds(S, I)`, then `I`. -/
def oneToGetIdent (n : I64) (I : UR) : RJ (List Int) := do
  checkbounds (.oneTo n) (.urange (.ident I))
  pure (UR.ident I).vals

/-- What indexing a vector whose indices and values are `inds` (an identity-indexed
vector such as a `Slice` or `IdentityUnitRange`, for which `S[i] == i`) must give:
a `Bool` scalar is not an index, an integer in `inds` gives itself, a collection
of integers in `inds` gives its elements, a Bool mask with the vector's axes
`1:n` selects the elements where it is `true`, and any other index is out of
bounds. -/
def refGet (inds : List Int) : Ix → RJ (List Int)
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .int k => if k.val ∈ inds then .ok [k.val] else .error boundsErr
  | .integer _ k => if k.val ∈ inds then .ok [k.val] else .error boundsErr
  | i =>
    if i.isMask then
      if (List.range i.elems.length).map (fun (k : Nat) => (k : Int) + 1) = inds then
        .ok ((i.elems.zip inds).filterMap fun p => if p.1 = 1 then some p.2 else none)
      else .error boundsErr
    else if i.elems.all (· ∈ inds) then .ok i.elems else .error boundsErr

/-- The `Slice` docstring, `base/indices.jl:325-336`: "indexing into Slice objects with
an integer always returns that exact integer": for every `Int` index and every
range of integer indices, `Slice(r)[i]` agrees with identity indexing over the
indices of `r`. -/
def SliceGetindex : Prop :=
  ∀ (r : UR) (i : Ix), (match i with | .int _ | .urange _ | .srange .. => true | _ => false) →
    sliceGet r i = refGet (UR.slice r).axes1.vals i

/-- The same docstring for integer indices of every type: `Slice(r)[i] == i`. -/
def SliceIntegerIndex : Prop :=
  ∀ (r : UR) (t : IntTy) (k : JInt t), sliceGet r (.integer t k) = refGet (UR.slice r).axes1.vals (.integer t k)

/-- Logical indexing (doc/src/manual/arrays.md, "Logical indexing") of a `Slice` with a
Bool range selects the elements where the mask is `true`. -/
def SliceBoolMask : Prop :=
  ∀ (r : UR) (i : Ix), i.isMask = true → sliceGet r i = refGet (UR.slice r).axes1.vals i

/-- The `IdentityUnitRange` docstring, `base/indices.jl:356-364` ("range[i] == i") with
logical indexing: `IdentityUnitRange(r)[i]` agrees with identity indexing for every
index except Bool step ranges, and `OneTo(n)[I::IdentityUnitRange]` returns `I`'s
elements when they are in bounds. -/
def IdentityGetindex : Prop :=
  (∀ (r : UR) (i : Ix), (match i with | .bsrange .. => false | _ => true) →
    identGet r i = refGet (UR.ident r).axes1.vals i) ∧
  (∀ (n : I64) (I : UR), 0 ≤ n.val →
    oneToGetIdent n I = refGet (UR.oneTo n).vals (.urange (.ident I)))

/-- Logical indexing of an `IdentityUnitRange` with a Bool step range. -/
def IdentityBoolStep : Prop :=
  ∀ (r : UR) (a : Bool) (s : I64) (b : Bool), s.val ≠ 0 →
    identGet r (.bsrange a s b) = refGet (UR.ident r).axes1.vals (.bsrange a s b)

/-- The `Slice` and `IdentityUnitRange` docstrings (`base/indices.jl:325-364`), method by
method: both constructors are idempotent on their own type and converting the
wrapped range type keeps the elements; the axis of each is the range of its indices,
which has the same elements as the range (both are identity-indexed), dispatching
to the `AbstractOneTo` methods for a `OneTo`; `first` and `last` are the first and
last iterated values, `size` and `unsafe_length` count them; indexing with an
`Int` that is a value returns it; `show` prints the constructor call. -/
def WrappedRanges : Prop :=
  ∀ r : UR,
    SliceM.ofSlice (UR.slice r) = UR.slice r ∧ IdentM.ofIdent (UR.ident r) = UR.ident r ∧
    UR.mkSlice (UR.mkSlice r) = UR.mkSlice r ∧ UR.mkIdent (UR.mkIdent r) = UR.mkIdent r ∧
    (SliceM.convert r).vals = SliceM.iterate r ∧ (IdentM.convert r).vals = IdentM.iterate r ∧
    SliceM.axes (UR.slice r) = [(UR.slice r).axes1] ∧ IdentM.axes (UR.ident r) = [(UR.ident r).axes1] ∧
    (UR.slice r).axes1 = (match r with | .oneTo _ => SliceM.axes1OneTo r | _ => SliceM.axes1 r) ∧
    (UR.ident r).axes1 = (match r with | .oneTo _ => IdentM.axes1OneTo r | _ => IdentM.axes1 r) ∧
    (SliceM.axes1 r).vals = SliceM.iterate r ∧ (SliceM.axes1OneTo r).vals = SliceM.iterate r ∧
    (IdentM.axes1 r).vals = IdentM.iterate r ∧ (IdentM.axes1OneTo r).vals = IdentM.iterate r ∧
    (SliceM.iterate r ≠ [] → (SliceM.iterate r).head? = some (SliceM.first r) ∧
      (SliceM.iterate r).getLast? = some (SliceM.last r)) ∧
    (IdentM.iterate r ≠ [] → (IdentM.iterate r).head? = some (IdentM.first r) ∧
      (IdentM.iterate r).getLast? = some (IdentM.last r)) ∧
    SliceM.size r = [(SliceM.iterate r).length] ∧ IdentM.size r = [(IdentM.iterate r).length] ∧
    IdentM.unsafeLength r = (IdentM.iterate r).length ∧
    (∀ k : I64, k.val ∈ SliceM.iterate r → SliceM.getindexInt (UR.slice r) k = .ok [k.val]) ∧
    (∀ k : I64, k.val ∈ IdentM.iterate r →
      IdentM.getindexInteger (UR.ident r) (.int k) k.val = .ok [k.val]) ∧
    SliceM.show_ r = "Base.Slice(" ++ r.str ++ ")" ∧
    IdentM.show_ r = "Base.IdentityUnitRange(" ++ r.str ++ ")"

/-! ## Promotion rules, `base/indices.jl:492-502` -/

/-- The range types wrapped here. -/
inductive RT where
  | oneTo
  | unitRange
  deriving DecidableEq, Repr

/-- `promote_type(R1, R2)` of two `Int` range types. -/
def RT.promote : RT → RT → RT
  | .oneTo, .oneTo => .oneTo
  | _, _ => .unitRange

/-- Types for the promotion rules: `Slice{R}`, `IdentityUnitRange{R}`, the UnionAlls
`Slice` and `IdentityUnitRange`, and `LinearIndices{N, Tuple{R...}}`. -/
inductive WT where
  | slice (r : RT)
  | ident (r : RT)
  | sliceAll
  | identAll
  | linIdx (rs : List RT)
  deriving DecidableEq, Repr

/-- Element types that `el_same` compares: `Int` or a range type. -/
inductive ElT where
  | int
  | range (r : RT)
  deriving DecidableEq, Repr

/-- `eltype` of a wrapper type: every `Slice` and `IdentityUnitRange` has `Int` elements. -/
def WT.eltype : WT → ElT
  | _ => .int

/-- `promote_typejoin(a, b)` of two wrapper types. -/
def WT.typejoin (a b : WT) : WT :=
  if a = b then a else match a with
    | .slice _ | .sliceAll => .sliceAll
    | _ => .identAll

/-- `el_same(T, a, b)`, `base/range.jl:1321-1324`: `a` when `eltype(a) == T`, `b` when
`eltype(b) == T`, otherwise `promote_typejoin(a, b)`. -/
def elSame (T : ElT) (a b : WT) : WT :=
  if a.eltype = T then a else if b.eltype = T then b else WT.typejoin a b

/-- `promote_rule(::Type{Slice{T1}}, ::Type{Slice{T2}}) = el_same(promote_type(T1, T2), a, b)`,
`base/indices.jl:499-500`. -/
def promoteRuleSlice (t1 t2 : RT) : WT := elSame (.range (t1.promote t2)) (.slice t1) (.slice t2)

/-- `promote_rule` for `IdentityUnitRange`, `base/indices.jl:501-502`. -/
def promoteRuleIdent (t1 t2 : RT) : WT := elSame (.range (t1.promote t2)) (.ident t1) (.ident t2)

/-- `indices_promote_type` and `promote_rule(::Type{LinearIndices{N,R1}}, ...)`,
`base/indices.jl:492-498`: the wrapped tuple types promote elementwise. -/
def promoteRuleLinIdx (r1 r2 : List RT) : WT := .linIdx (List.zipWith RT.promote r1 r2)

/-- The promotion invariant of the `el_same` rules (`base/range.jl:1321-1324`, as for
`Array`): promoting two `Slice` (or `IdentityUnitRange`) types gives the wrapper of
the promoted range type, as the `LinearIndices` rule does. -/
def SlicePromoteRule : Prop :=
  ∀ t1 t2 : RT, promoteRuleSlice t1 t2 = .slice (t1.promote t2) ∧
    promoteRuleIdent t1 t2 = .ident (t1.promote t2)

/-- The `LinearIndices` promotion rule promotes each wrapped range type. -/
def LinIdxPromoteRule : Prop :=
  ∀ r1 r2 : List RT, r1.length = r2.length →
    promoteRuleLinIdx r1 r2 = .linIdx ((r1.zip r2).map fun p => p.1.promote p.2)

/-! ## `LinearIndices`, `base/indices.jl:429-533` -/

/-- `LinearIndices{N,R}` with `indices::R`. -/
structure LinIdx where
  inds : List UR
  deriving DecidableEq, Repr

namespace LinIdx

/-- `axes(iter) = map(axes1, iter.indices)`, `base/indices.jl:506`. -/
def axes (L : LinIdx) : List UR := L.inds.map UR.axes1

/-- `size(iter) = map(length, iter.indices)`, `base/indices.jl:507`. -/
def size (L : LinIdx) : List Nat := L.inds.map UR.len

/-- `length(iter) = prod(size(iter))`. -/
def length (L : LinIdx) : Nat := L.size.foldl (· * ·) 1

/-- `checkbounds(Bool, iter, i)` for one `Int` index (linear indexing): the index of a
one-dimensional `LinearIndices` must be in its axis, otherwise in `1:length(iter)`. -/
def inBounds (L : LinIdx) (i : Int) : Bool :=
  match L.inds with
  | [r] => decide (r.axes1.first ≤ i ∧ i ≤ r.axes1.last)
  | _ => decide (1 ≤ i ∧ i ≤ L.length)

/-- `isassigned(iter, i::Int) = checkbounds(Bool, iter, i)`, `base/indices.jl:508`. -/
def isassigned (L : LinIdx) (i : I64) : Bool := L.inBounds i.val

/-- `getindex(iter::LinearIndices, i::Int)`, `base/indices.jl:509-513`. -/
def get (L : LinIdx) (i : I64) : RJ Int :=
  if L.inBounds i.val then .ok i.val else .error boundsErr

/-- `first(iter::LinearIndices) = 1`, `base/indices.jl:526`. -/
def firstN (_L : LinIdx) : Int := 1

/-- `first(iter::LinearIndices{1}) = first(axes1(iter.indices[1]))`, `base/indices.jl:527`. -/
def first1 (r : UR) : Int := r.axes1.first

/-- `last(iter::LinearIndices) = length(iter)`, `base/indices.jl:528`. -/
def lastN (L : LinIdx) : Int := L.length

/-- `last(iter::LinearIndices{1}) = last(axes1(iter.indices[1]))`, `base/indices.jl:529`. -/
def last1 (r : UR) : Int := r.axes1.last

/-- `first(iter)`, dispatching on the number of dimensions. -/
def first (L : LinIdx) : Int :=
  match L.inds with
  | [r] => first1 r
  | _ => firstN L

/-- `last(iter)`, dispatching on the number of dimensions. -/
def last (L : LinIdx) : Int :=
  match L.inds with
  | [r] => last1 r
  | _ => lastN L

/-- `getindex(iter::LinearIndices, i::AbstractRange{<:Integer})`, `base/indices.jl:514-518`:
after `checkbounds`, `iter.indices[1][i]` for one dimension (indexing a unit range `r`
at `k` gives `first(r) + (k - first(axes1(r)))`) and `(first(iter):last(iter))[i]`
otherwise; `i` is a unit range of `Int`s. -/
def getRange (L : LinIdx) (i : UR) : RJ (List Int) :=
  let ok : Bool := match i.vals.head?, i.vals.getLast? with
    | some x, some y => L.inBounds x && L.inBounds y
    | _, _ => true
  if !ok then .error boundsErr
  else match L.inds with
    | [r] => .ok (i.vals.map fun k => r.first + (k - r.axes1.first))
    | _ => .ok (i.vals.map fun k => L.firstN + (k - 1))

/-- `iterate(iter::LinearIndices, i=1) = i > length(iter) ? nothing : (i, i+1)`,
`base/indices.jl:523`: the values from state `i`, `fuel` steps at most. -/
def iterateN (L : LinIdx) : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, i => if i > L.length then [] else i :: iterateN L fuel (i + 1)

/-- `iterate(iter::LinearIndices{1}, s...) = iterate(axes1(iter.indices[1]), s...)`,
`base/indices.jl:522`: the iterated values. -/
def iterate1 (r : UR) : List Int := r.axes1.vals

/-- The iterated values, dispatching on the number of dimensions; the general method
starts at state `1` and stops after `length(iter) + 1` calls. -/
def collect (L : LinIdx) : List Int :=
  match L.inds with
  | [r] => iterate1 r
  | _ => L.iterateN (L.length + 1) 1

/-- `copy(iter::LinearIndices) = iter`, `base/indices.jl:519`. -/
def copy (L : LinIdx) : LinIdx := L

/-- `show(io, iter::LinearIndices)`: `LinearIndices(` then the tuple of indices,
`base/indices.jl:531-533`. -/
def str (L : LinIdx) : String :=
  "LinearIndices((" ++ ", ".intercalate (L.inds.map UR.str) ++
    (if L.inds.length = 1 then "," else "") ++ "))"

end LinIdx

/-- An argument of the `LinearIndices` constructor tuple: an integer or a unit range. -/
inductive DimArg where
  | int (n : I64)
  | bool (b : Bool)
  | range (r : UR)
  deriving DecidableEq, Repr

/-- `_convert2ind(i::Integer) = oneto(i)`, `base/indices.jl:489`: `OneTo(n)` clamps a
negative `n` to `0` and rejects a `Bool`. -/
def convert2indInt : DimArg → RJ UR
  | .int n => .ok (.oneTo (if n.val < 0 then i64 0 else n))
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .range r => .ok r

/-- `_convert2ind(ind::AbstractUnitRange) = first(ind):last(ind)`, `base/indices.jl:490`. -/
def convert2indRange (r : UR) : UR := .unit (i64 r.first) (i64 r.last)

/-- `_convert2ind(x)`, dispatching on the argument type. -/
def convert2ind : DimArg → RJ UR
  | .range r => .ok (convert2indRange r)
  | a => convert2indInt a

/-- `LinearIndices(::Tuple{}) = LinearIndices{0,typeof(())}(())`, `base/indices.jl:482`. -/
def linearIndicesEmpty : LinIdx := ⟨[]⟩

/-- `LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}})`, `base/indices.jl:483-484`:
`LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))`, which keeps every
range of `Int`s. -/
def linearIndicesRanges (rs : List UR) : LinIdx := ⟨rs.map id⟩

/-- `LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}})`,
`base/indices.jl:485-486`: `LinearIndices(map(_convert2ind, inds))`. -/
def linearIndicesMixed (args : List DimArg) : RJ LinIdx := (args.mapM convert2ind).map LinIdx.mk

/-- `LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))`,
`base/indices.jl:487`: `axes` are the array's axes. -/
def linearIndicesOf (axes : List UR) : LinIdx :=
  if axes = [] then linearIndicesEmpty else linearIndicesRanges axes

/-- `LinearIndices(inds)` for a tuple, dispatching to the most specific method. -/
def linearIndices (args : List DimArg) : RJ LinIdx :=
  if args = [] then .ok linearIndicesEmpty
  else if args.all (fun a => match a with | .range _ => true | _ => false) then
    .ok (linearIndicesRanges (args.filterMap fun a => match a with | .range r => some r | _ => none))
  else linearIndicesMixed args

/-- The constructor docstring, `base/indices.jl:440-466`, for the methods that cannot
change the indices: `LinearIndices(())` is zero-dimensional with the single linear
index `1`; `LinearIndices(A)` has the axes of `A`; `_convert2ind` keeps the elements
of a range and turns an integer `n ≥ 0` into `OneTo(n)`. -/
def LinearIndicesConstructors : Prop :=
  linearIndicesEmpty.collect = [1] ∧ linearIndicesEmpty.size = [] ∧
  (∀ ax : List UR, (linearIndicesOf ax).axes = ax.map UR.axes1) ∧
  (∀ r : UR, (convert2indRange r).vals = r.vals) ∧
  (∀ n : I64, 0 ≤ n.val → convert2indInt (.int n) = .ok (.oneTo n)) ∧
  (∀ b, ∃ m, convert2indInt (.bool b) = .error (argErr m))

/-- `convert(::Type{LinearIndices{N,R}}, inds::LinearIndices{N})`, `base/indices.jl:479-480`:
the indices are converted to `R`; for `R = NTuple{N, UnitRange{Int}}` each becomes a
plain range with the same elements. -/
def convertToUnitRanges (L : LinIdx) : LinIdx := ⟨L.inds.map UR.toUnitRange⟩

/-- The `LinearIndices` docstring, `base/indices.jl:429-477`: the array holds the linear
index of each entry. With `n = length(iter)` (below `typemax(Int)`): a
multidimensional `LinearIndices` holds `1, …, n`, a one-dimensional one holds its
axis; indexing with an `Int` returns it when in bounds and throws `BoundsError`
otherwise, `isassigned` is the bounds check, `first`/`last` are the first and last
values, and `copy` is the identity. -/
def LinearIndicesValues : Prop :=
  ∀ L : LinIdx,
    (L.inds.length ≠ 1 → L.collect = (List.range L.length).map (fun (k : Nat) => (k : Int) + 1)) ∧
    (∀ r, L.inds = [r] → L.collect = r.axes1.vals) ∧
    (∀ i : I64, L.get i = if i.val ∈ L.collect then .ok i.val else .error boundsErr) ∧
    (∀ i : I64, L.isassigned i = decide (i.val ∈ L.collect)) ∧
    (L.collect ≠ [] → L.collect.head? = some L.first ∧ L.collect.getLast? = some L.last) ∧
    (convertToUnitRanges L).size = L.size ∧
    L.copy = L

/-- Indexing a `LinearIndices` with a range gives the values at those indices (the
range itself, since every value equals its index). -/
def LinearIndicesRangeIndex : Prop :=
  ∀ (L : LinIdx) (i : UR), (∀ k ∈ i.vals, k ∈ L.collect) → L.getRange i = .ok i.vals

/-- The constructor docstring, `base/indices.jl:463-466`: `LinearIndices(inds)` has the
specified axes: each integer `n` gives `OneTo(n)` and each range its own axis. -/
def LinearIndicesAxes : Prop :=
  ∀ args : List DimArg, (∀ a ∈ args, a ≠ .bool true ∧ a ≠ .bool false) →
    (linearIndices args).map LinIdx.axes = .ok (args.map fun a => match a with
      | .int n => UR.oneTo (if n.val < 0 then i64 0 else n)
      | .range r => r.axes1
      | .bool _ => UR.oneTo (i64 0))

/-! ## `promote_shape`, `base/indices.jl:106-203` -/

/-- A tuple as `print(io, t)` shows it: `(x1, x2)`, or `(x1,)` for one element. -/
def tupleStr (xs : List String) : String :=
  "(" ++ ", ".intercalate xs ++ (if xs.length = 1 then "," else "") ++ ")"

/-- An argument of `throw_promote_shape_mismatch`: `Dims` or a tuple of axes. -/
inductive Shape where
  | dims (ds : List Int)
  | axes (rs : List UR)

namespace Shape

/-- `s isa Tuple{Vararg{Base.OneTo}}` (the empty tuple included). -/
def allOneTo : Shape → Bool
  | .dims ds => ds.isEmpty
  | .axes rs => rs.all fun r => match r with | .oneTo _ => true | _ => false

/-- `s isa Dims`. -/
def isDims : Shape → Bool
  | .dims _ => true
  | .axes rs => rs.isEmpty

/-- `map(lastindex, s)::Dims` for a tuple of `OneTo`s. -/
def toDims : Shape → Shape
  | .axes rs => .dims (rs.map UR.last)
  | s => s

/-- `print(io, s)` after `_normalize(d) = map(x -> firstindex(x):lastindex(x), d)`
when `normalize` holds. -/
def str (normalize : Bool) : Shape → String
  | .dims ds => tupleStr (ds.map toString)
  | .axes rs => tupleStr (rs.map fun r =>
      if normalize then s!"{r.axes1.first}:{r.axes1.last}" else r.str)

end Shape

/-- `throw_promote_shape_mismatch(a, b, i)`, `base/indices.jl:112-137` (with the nested
`_normalize`, `:119`): tuples of `OneTo` are printed as sizes; unless both arguments
are then `Dims`, both are printed as normalized axes. `b = nothing` and `i = nothing`
leave out their parts of the message. -/
def promoteShapeMismatch (a : Shape) (b : Option Shape) (i : Option Nat) : Err :=
  let conv := a.allOneTo && b.all Shape.allOneTo
  let a := if conv then a.toDims else a
  let b := if conv then b.map Shape.toDims else b
  let hasAxes := !(a.isDims && b.all Shape.isDims)
  let things := if hasAxes then "axes " else "size "
  .dimensionMismatch ("a has " ++ things ++ a.str hasAxes ++
    (match b with | some b => ", b has " ++ things ++ b.str hasAxes | none => "") ++
    (match i with | some i => s!", mismatch at dim {i}" | none => ""))

/-- The loops of `promote_shape(a::Dims, b::Dims)`, `base/indices.jl:179-185`, once
`a` has at least as many dimensions as `b`: `for i=1:length(b)` requires
`a[i] == b[i]` and `for i=length(b)+1:length(a)` requires `a[i] == 1`; the first
failing `i` is reported. -/
def promoteShapeDimsGe (a b : List Int) : RJ (List Int) :=
  if !(a.zip b).all (fun p => p.1 = p.2) then
    .error (promoteShapeMismatch (.dims a) (some (.dims b))
      (some (((a.zip b).findIdx fun p => p.1 ≠ p.2) + 1)))
  else if !(a.drop b.length).all (· = 1) then
    .error (promoteShapeMismatch (.dims a) none
      (some (((a.drop b.length).findIdx (· ≠ 1)) + b.length + 1)))
  else .ok a

/-- `promote_shape(a::Dims, b::Dims)`, `base/indices.jl:175-186`:
`length(a) < length(b)` returns `promote_shape(b, a)`. -/
def promoteShapeDims (a b : List Int) : RJ (List Int) :=
  if a.length < b.length then promoteShapeDimsGe b a else promoteShapeDimsGe a b

/-- `promote_shape(::Tuple{}, ::Tuple{}) = ()`, `base/indices.jl:108`. -/
def promoteShape00 : RJ (List Int) := .ok []

/-- `promote_shape(a::Tuple{Int,}, b::Tuple{Int,})`, `base/indices.jl:139-142`. -/
def promoteShape11 (a1 b1 : Int) : RJ (List Int) :=
  if a1 ≠ b1 then .error (promoteShapeMismatch (.dims [a1]) (some (.dims [b1])) none) else .ok [a1]

/-- `promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})`, `base/indices.jl:144-147`. -/
def promoteShape21 (a1 a2 b1 : Int) : RJ (List Int) :=
  if a1 ≠ b1 ∨ a2 ≠ 1 then .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1])) none)
  else .ok [a1, a2]

/-- `promote_shape(a::Tuple{Int,}, b::Tuple{Int,Int}) = promote_shape(b, a)`,
`base/indices.jl:149`. -/
def promoteShape12 (a1 b1 b2 : Int) : RJ (List Int) := promoteShape21 b1 b2 a1

/-- `promote_shape(a::Tuple{Int, Int}, b::Tuple{Int, Int})`, `base/indices.jl:151-154`. -/
def promoteShape22 (a1 a2 b1 b2 : Int) : RJ (List Int) :=
  if a1 ≠ b1 ∨ a2 ≠ b2 then .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1, b2])) none)
  else .ok [a1, a2]

/-- `promote_shape` on `Dims`, dispatching to the most specific method. -/
def promoteShape (a b : List Int) : RJ (List Int) :=
  match a, b with
  | [], [] => promoteShape00
  | [a1], [b1] => promoteShape11 a1 b1
  | [a1, a2], [b1] => promoteShape21 a1 a2 b1
  | [a1], [b1, b2] => promoteShape12 a1 b1 b2
  | [a1, a2], [b1, b2] => promoteShape22 a1 a2 b1 b2
  | a, b => promoteShapeDims a b

/-- The loops of `promote_shape(a::Indices, b::Indices)`, `base/indices.jl:196-202`:
axes are compared as ranges (by their elements, `a[i] != b[i]`) and trailing axes
must equal `1:1`. -/
def promoteShapeAxesGe (a b : List UR) : RJ (List UR) :=
  if !(a.zip b).all (fun p => p.1.vals = p.2.vals) then
    .error (promoteShapeMismatch (.axes a) (some (.axes b))
      (some (((a.zip b).findIdx fun p => p.1.vals ≠ p.2.vals) + 1)))
  else if !(a.drop b.length).all (·.vals = [1]) then
    .error (promoteShapeMismatch (.axes a) none
      (some (((a.drop b.length).findIdx (·.vals ≠ [1])) + b.length + 1)))
  else .ok a

/-- `promote_shape(a::Indices, b::Indices)`, `base/indices.jl:192-203`:
`length(a) < length(b)` returns `promote_shape(b, a)`. -/
def promoteShapeAxes (a b : List UR) : RJ (List UR) :=
  if a.length < b.length then promoteShapeAxesGe b a else promoteShapeAxesGe a b

/-- `promote_shape(a::AbstractArray, b::AbstractArray) = promote_shape(axes(a), axes(b))`,
`base/indices.jl:188-190`; `ax` and `bx` are the arrays' axes. -/
def promoteShapeArrays (ax bx : List UR) : RJ (List UR) := promoteShapeAxes ax bx

/-- The shape after dropping trailing `1`s. -/
def dropOnes : List Int → List Int
  | [] => []
  | x :: a => if x = 1 ∧ dropOnes a = [] then [] else x :: dropOnes a

/-- The longer of two shapes, `a` when they have the same length. -/
def longer {α : Type} (a b : List α) : List α := if a.length < b.length then b else a

/-- Shapes that agree on their common dimensions and whose extra dimensions are `1`. -/
def compatible (a b : List Int) : Bool :=
  (a.zip b).all (fun p => p.1 = p.2) && (a.drop b.length ++ b.drop a.length).all (· = 1)

/-- The `promote_shape` docstring, `base/indices.jl:156-174`: "Check two array shapes
for compatibility, allowing trailing singleton dimensions, and return whichever shape
has more dimensions". The one- and two-dimensional methods return what the general
method returns and throw only `DimensionMismatch`; the general methods succeed
exactly for compatible shapes and then return the longer shape. -/
def PromoteShapeSpec : Prop :=
  (∀ a b : List Int, (promoteShape a b).toOption = (promoteShapeDims a b).toOption ∧
    ∀ e, promoteShape a b = .error e → ∃ m, e = .dimensionMismatch m) ∧
  (∀ a b : List Int, (promoteShapeDims a b).isOk = compatible a b ∧
    ∀ r, promoteShapeDims a b = .ok r → r = longer a b) ∧
  (∀ a b : List UR, (promoteShapeAxes a b).isOk =
      compatible' a b ∧ ∀ r, promoteShapeAxes a b = .ok r → r = longer a b) ∧
  (∀ ax bx : List UR, (promoteShapeArrays ax bx).isOk = compatible' ax bx)
where
  /-- `compatible` for axes, compared by their elements, with `1:1` as the singleton. -/
  compatible' (a b : List UR) : Bool :=
    (a.zip b).all (fun p => p.1.vals = p.2.vals) && (a.drop b.length ++ b.drop a.length).all (·.vals = [1])

/-- The error message of `promote_shape` (the comment at `base/indices.jl:110-111`:
"Consistent error message for promote_shape mismatch, hiding type details like
OneTo") describes the two arguments: when the axes of `a` and `b` differ at a
dimension, the message never shows the same axes for both. -/
def PromoteShapeMessage : Prop :=
  ∀ (a b : List UR) (s : String) (i : Nat),
    promoteShapeAxes a b ≠
      .error (.dimensionMismatch ("a has axes " ++ s ++ ", b has axes " ++ s ++ s!", mismatch at dim {i}"))

/-! ## `setindex_shape_check`, `base/indices.jl:205-228` -/

/-- `_shapes_match(::Tuple{}, ::Tuple{}) = true`, `base/indices.jl:217`. -/
def shapesMatch00 : Bool := true

/-- `_shapes_match(a::Tuple, ::Tuple{}) = all(isone, a)`, `base/indices.jl:218`. -/
def shapesMatchA0 (a : List Int) : Bool := a.all (· = 1)

/-- `_shapes_match(::Tuple{}, b::Tuple) = all(isone, b)`, `base/indices.jl:219`. -/
def shapesMatch0B (b : List Int) : Bool := b.all (· = 1)

/-- `_shapes_match(a::Tuple, b::Tuple) = first(a) == first(b) && _shapes_match(tail(a),
tail(b))`, `base/indices.jl:220`, with the dispatch to the three methods above. -/
def shapesMatch : List Int → List Int → Bool
  | [], [] => shapesMatch00
  | x :: a, [] => shapesMatchA0 (x :: a)
  | [], y :: b => shapesMatch0B (y :: b)
  | x :: a, y :: b => x = y && shapesMatch a b

/-- `dims2string(d)` (`base/show.jl`): `"0-dimensional"`, `"n-element"`, or the sizes
joined by `×`. -/
def dims2string : List Int → String
  | [] => "0-dimensional"
  | [n] => s!"{n}-element"
  | ds => "×".intercalate (ds.map toString)

/-- `throw_setindex_mismatch(X, I)`, `base/indices.jl:205-212`. -/
def setindexMismatch (sx : List Int) (I : List Int) : Err :=
  match I with
  | [i] => .dimensionMismatch s!"tried to assign {sx.foldl (· * ·) 1} elements to {i} destinations"
  | _ => .dimensionMismatch s!"tried to assign {dims2string sx} array to {dims2string I} destination"

/-- `setindex_shape_check(X::AbstractArray, shape::Tuple{Vararg{Integer}})`,
`base/indices.jl:222-225`. -/
def setindexShapeCheck (sx : List Int) (shape : List Int) : RJ Bool :=
  let ok : Bool := if sx.length = 1 ∨ shape.length = 1 then
      decide (sx.foldl (· * ·) 1 = shape.foldl (· * ·) 1)
    else shapesMatch sx shape
  if ok then .ok true else .error (setindexMismatch sx shape)

/-- `setindex_shape_check(X::AbstractArray, i::Integer) = (length(X) == i || throw...)`,
`base/indices.jl:214-215`. -/
def setindexShapeCheck1 (sx : List Int) (i : Int) : RJ Bool :=
  if sx.foldl (· * ·) 1 = i then .ok true else .error (setindexMismatch sx [i])

/-- `setindex_shape_check(::Any, ::Tuple)`, `base/indices.jl:227-228`: a non-array
right-hand side. -/
def setindexShapeCheckScalar : RJ Bool :=
  .error (argErr "indexed assignment with a single value to possibly many locations is not supported")

/-- The manual on indexed assignment (doc/src/manual/arrays.md, "Indexed Assignment")
and the shape rule of `setindex_shape_check`: a vector source or destination needs
the same number of elements; otherwise the shapes must agree after dropping
trailing singleton dimensions. A mismatch throws `DimensionMismatch`; a single
value is rejected with an `ArgumentError`. -/
def SetindexShapeSpec : Prop :=
  (∀ a b : List Int, shapesMatch a b = decide (dropOnes a = dropOnes b)) ∧
  (∀ sx shape : List Int, (setindexShapeCheck sx shape).isOk =
    if sx.length = 1 ∨ shape.length = 1 then decide (sx.foldl (· * ·) 1 = shape.foldl (· * ·) 1)
    else decide (dropOnes sx = dropOnes shape)) ∧
  (∀ sx i, (setindexShapeCheck1 sx i).isOk = decide (sx.foldl (· * ·) 1 = i)) ∧
  (∀ sx shape e, setindexShapeCheck sx shape = .error e → ∃ m, e = .dimensionMismatch m) ∧
  (∀ sx i e, setindexShapeCheck1 sx i = .error e → ∃ m, e = .dimensionMismatch m) ∧
  (∃ m, setindexShapeCheckScalar = .error (argErr m))

/-! ## `to_index`, `to_indices`, `base/indices.jl:230-323` -/

/-- An index value given to `to_index`. -/
inductive IV where
  | int (i : I64)
  | integer (t : IntTy) (i : JInt t)
  | bool (b : Bool)
  | boolArr (bs : List Bool)
  | intArr (xs : List I64)
  | bottomArr
  | nestedArr
  | colon
  | other
  deriving DecidableEq, Repr

/-- A converted index: an `Int`, an array of `Int`s, or a `LogicalIndex` of a mask. -/
inductive CI where
  | int (i : I64)
  | arr (xs : List I64)
  | logical (mask : List Bool)
  deriving DecidableEq, Repr

/-- `to_index(i)`, `base/indices.jl:258-266`: `convert(Int, i)` for an integer (an
`InexactError` when it does not fit), `ArgumentError` for a `Bool`,
`LogicalIndex(I)` for a Bool array, an integer array or `Union{}[]` itself, and
`ArgumentError` for arrays of arrays or colons, `:` and any other value. -/
def toIndex : IV → RJ CI
  | .int i => .ok (.int i)
  | .integer t i =>
    match JInt.convert .i64 i.val with
    | .ok j => .ok (.int j)
    | .error _ => .error (.jl (.inexactError "convert"))
  | .bool b => .error (argErr s!"invalid index: {b} of type Bool")
  | .boolArr bs => .ok (.logical bs)
  | .intArr xs => .ok (.arr xs)
  | .bottomArr => .ok (.arr [])
  | .nestedArr => .error (argErr "invalid index")
  | .colon => .error (argErr "colons must be converted by to_indices(...)")
  | .other => .error (argErr "invalid index")

/-- `to_index(A, i) = to_index(i)` (`base/indices.jl:243`) and
`to_index(A::Array, i::UInt) = reinterpret(Int, i)` (`:247`); `isArray` says whether
`A` is an `Array`. -/
def toIndexA (isArray : Bool) : IV → RJ CI
  | .integer .u64 i => if isArray then .ok (.int (JInt.wrap .i64 i.val)) else toIndex (.integer .u64 i)
  | i => toIndex i

/-- `to_indices(A, inds, I)`, `base/indices.jl:321-323`:
`(to_index(A, I[1]), to_indices(A, safe_tail(inds), tail(I))...)`. -/
def toIndicesInds (isArray : Bool) : List IV → RJ (List CI)
  | [] => .ok []
  | i :: rest => do
    let c ← toIndexA isArray i
    let cs ← toIndicesInds isArray rest
    pure (c :: cs)

/-- `to_indices(A, I::Tuple)`, `base/indices.jl:310-320`: `()` gives `()`, a tuple of
`Int`s is returned as is, a tuple of integers goes to `to_indices(A, (), I)`, and any
other tuple is processed with `axes(A)` (or with linear indices for one index, after
`_drop_zerodim`, which keeps every element of a tuple, `:314-315`). -/
def toIndices (isArray : Bool) (I : List IV) : RJ (List CI) :=
  if I.all (fun i => match i with | .int _ => true | _ => false) then
    .ok (I.filterMap fun i => match i with | .int j => some (.int j) | _ => none)
  else toIndicesInds isArray I

/-- The `to_index` and `to_indices` docstrings, `base/indices.jl:230-309`: the result is
an `Int` or an array of scalar indices, Bool arrays become logical indices, values
that are not indices throw `ArgumentError`, and `to_indices` applies `to_index` to
every element (keeping `Int`s). For `Array`s a `UInt` index is reinterpreted. -/
def ToIndexSpec : Prop :=
  (∀ i : I64, toIndex (.int i) = .ok (.int i)) ∧
  (∀ t (i : JInt t), IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
    toIndex (.integer t i) = .ok (.int (JInt.lit .i64 i.val))) ∧
  (∀ b, ∃ e, toIndex (.bool b) = .error e) ∧
  (∀ bs, toIndex (.boolArr bs) = .ok (.logical bs)) ∧
  (∀ v, (v = .nestedArr ∨ v = .colon ∨ v = .other) → ∃ m, toIndex v = .error (argErr m)) ∧
  (∀ isArray (I : List IV), toIndices isArray I = I.mapM (toIndexA isArray))

end JuliaLean.ReduceCov.Indices
