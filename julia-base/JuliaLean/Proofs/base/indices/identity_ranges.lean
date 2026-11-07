import JuliaLean.base.indices
import JuliaLean.base.abstractarray
import JuliaLean.base.array
import JuliaLean.base.show
import JuliaLean.Core

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

namespace UR

end UR

/-! ### The methods of `Slice` and `IdentityUnitRange`, one function each -/

namespace SliceM

end SliceM

namespace IdentM

end IdentM

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
    (sliceGet JuliaLean.ReduceCov.Indices.checkbounds JuliaLean.ReduceCov.Indices.rangeGetindexInteger) r i = refGet (UR.slice r).axes1.vals i

/-- The same docstring for integer indices of every type: `Slice(r)[i] == i`. -/
def SliceIntegerIndex : Prop :=
  ∀ (r : UR) (t : IntTy) (k : JInt t), (sliceGet JuliaLean.ReduceCov.Indices.checkbounds JuliaLean.ReduceCov.Indices.rangeGetindexInteger) r (.integer t k) = refGet (UR.slice r).axes1.vals (.integer t k)

/-- Logical indexing (doc/src/manual/arrays.md, "Logical indexing") of a `Slice` with a
Bool range selects the elements where the mask is `true`. -/
def SliceBoolMask : Prop :=
  ∀ (r : UR) (i : Ix), i.isMask = true → (sliceGet JuliaLean.ReduceCov.Indices.checkbounds JuliaLean.ReduceCov.Indices.rangeGetindexInteger) r i = refGet (UR.slice r).axes1.vals i

/-- The `IdentityUnitRange` docstring, `base/indices.jl:356-364` ("range[i] == i") with
logical indexing: `IdentityUnitRange(r)[i]` agrees with identity indexing for every
index except Bool step ranges, and `OneTo(n)[I::IdentityUnitRange]` returns `I`'s
elements when they are in bounds. -/
def IdentityGetindex : Prop :=
  (∀ (r : UR) (i : Ix), (match i with | .bsrange .. => false | _ => true) →
    (identGet JuliaLean.ReduceCov.Indices.checkbounds) r i = refGet (UR.ident r).axes1.vals i) ∧
  (∀ (n : I64) (I : UR), 0 ≤ n.val →
    (oneToGetIdent JuliaLean.ReduceCov.Indices.checkbounds) n I = refGet (UR.oneTo n).vals (.urange (.ident I)))

/-- Logical indexing of an `IdentityUnitRange` with a Bool step range. -/
def IdentityBoolStep : Prop :=
  ∀ (r : UR) (a : Bool) (s : I64) (b : Bool), s.val ≠ 0 →
    (identGet JuliaLean.ReduceCov.Indices.checkbounds) r (.bsrange a s b) = refGet (UR.ident r).axes1.vals (.bsrange a s b)

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
    (∀ k : I64, k.val ∈ SliceM.iterate r → (SliceM.getindexInt JuliaLean.ReduceCov.Indices.checkbounds) (UR.slice r) k = .ok [k.val]) ∧
    (∀ k : I64, k.val ∈ IdentM.iterate r →
      (IdentM.getindexInteger JuliaLean.ReduceCov.Indices.checkbounds) (UR.ident r) (.int k) k.val = .ok [k.val]) ∧
    SliceM.show_ r = "Base.Slice(" ++ r.str ++ ")" ∧
    IdentM.show_ r = "Base.IdentityUnitRange(" ++ r.str ++ ")"

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

namespace LinIdx

end LinIdx

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

namespace Shape

end Shape

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

/-- The manual on indexed assignment (doc/src/manual/arrays.md, "Indexed Assignment")
and the shape rule of `setindex_shape_check`: a vector source or destination needs
the same number of elements; otherwise the shapes must agree after dropping
trailing singleton dimensions. A mismatch throws `DimensionMismatch`; a single
value is rejected with an `ArgumentError`. -/
def SetindexShapeSpec : Prop :=
  (∀ a b : List Int, shapesMatch a b = decide (dropOnes a = dropOnes b)) ∧
  (∀ sx shape : List Int, (setindexShapeCheck dims2string sx shape).isOk =
    if sx.length = 1 ∨ shape.length = 1 then decide (sx.foldl (· * ·) 1 = shape.foldl (· * ·) 1)
    else decide (dropOnes sx = dropOnes shape)) ∧
  (∀ sx i, (setindexShapeCheck1 dims2string sx i).isOk = decide (sx.foldl (· * ·) 1 = i)) ∧
  (∀ sx shape e, setindexShapeCheck dims2string sx shape = .error e → ∃ m, e = .dimensionMismatch m) ∧
  (∀ sx i e, setindexShapeCheck1 dims2string sx i = .error e → ∃ m, e = .dimensionMismatch m) ∧
  (∃ m, setindexShapeCheckScalar = .error (argErr m))

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
