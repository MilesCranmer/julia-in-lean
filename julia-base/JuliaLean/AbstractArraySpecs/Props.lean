import JuliaLean.AbstractArraySpecs.Cat
import JuliaLean.AbstractArraySpecs.Iterate
import JuliaLean.AbstractArraySpecs.Copy

/-!
Spec-first properties for `base/abstractarray.jl`. Each statement is written from
the docstrings and the manual (doc/src/manual/arrays.md "Linear indexing" and
"Omitted and extra indices", doc/src/manual/interfaces.md "Abstract arrays"),
against the reference semantics of `Model.lean` (`refPos`: a single index is
linear, a vector's linear indices are its axis and other arrays' are
`1:length(A)`; any other number of indices is Cartesian, with omitted trailing
indices for length-one dimensions and extra indices equal to 1).
-/

namespace JuliaLean.AbstractArraySpecs

/-- Element of `A` at the reference position of the index list `I`, or `BoundsError`. -/
def refGet {α : Type} (A : Arr α) (I : List I64) : R α :=
  match refPos A I with
  | some p => match A.data[p]? with
    | some x => .ok x
    | none => .error .boundsError
  | none => .error .boundsError

/-- `A` with the element at the reference position of `I` replaced, or `BoundsError`. -/
def refSet {α : Type} (A : Arr α) (v : α) (I : List I64) : R (Arr α) :=
  match refPos A I with
  | some p => if p < A.data.length then .ok { A with data := A.data.set p v } else .error .boundsError
  | none => .error .boundsError

/-- `get(A, I, default)` returns the selected element, or `default` when no element
is selected; it never throws (base/abstractarray.jl:1632-1642). -/
def refGetDefault {α : Type} (A : Arr α) (I : List I64) (d : α) : R α :=
  match refGet A I with
  | .ok x => .ok x
  | .error _ => .ok d

/-- Integer indexing of any well-formed array, of either `IndexStyle` and with any
axes, with any number of `Int` indices (including none): `getindex` and `setindex!`
read and write the element the manual's indexing rules select and throw
`BoundsError` exactly when no element is selected, and `get(A, I, default)` returns
that element or `default`. -/
def IndexingAgreesWithReference : Prop :=
  ∀ (A : Arr Int) (I : List I64) (v d : Int), A.WF →
    getindex A I = refGet A I ∧ setindex A v I = refSet A v I ∧
      getDefault A I d = refGetDefault A I d

/-- Linear indexing (doc/src/manual/arrays.md "Linear indexing"): with one `Int`
index, `getindex`, `setindex!` and `get` select the element at that linear index,
for both `IndexStyle`s and any axes. -/
def LinearIndexingAgrees : Prop :=
  ∀ {α : Type} (A : Arr α) (k : I64) (v d : α), A.WF →
    getindex A [k] = refGet A [k] ∧ setindex A v [k] = refSet A v [k] ∧
      getDefault A [k] d = refGetDefault A [k] d

/-- Cartesian indexing with `ndims(A)` indices and with extra trailing indices
(doc/src/manual/arrays.md "Cartesian indexing" and the "more than `N` indices"
paragraph of "Omitted and extra indices"). -/
def CartesianIndexingAgrees : Prop :=
  ∀ {α : Type} (A : Arr α) (I : List I64) (v d : α), A.WF → A.axes.length ≤ I.length →
    getindex A I = refGet A I ∧ setindex A v I = refSet A v I ∧
      getDefault A I d = refGetDefault A I d

/-- `checkbounds(Bool, A, I...)` is true exactly when the index list selects an
element (base/abstractarray.jl:655-693 docstring), and `checkbounds(A, I...)` throws
`BoundsError` otherwise. -/
def CheckboundsAgreesWithReference : Prop :=
  ∀ {α : Type} (A : Arr α) (I : List I64), A.WF →
    checkboundsBool A I = (refPos A I).isSome ∧
    checkbounds A I = (if (refPos A I).isSome then .ok () else .error .boundsError)

/-- `first(A)` and `last(A)` are the first and last elements in column-major order,
and throw `BoundsError` for an empty array (docstrings at base/abstractarray.jl:457
and 512). -/
def FirstLastElements : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF →
    firstA A = (match A.data.head? with | some x => .ok x | none => .error .boundsError) ∧
    lastA A = (match A.data.getLast? with | some x => .ok x | none => .error .boundsError)

/-- `isempty(A)` is true exactly when `A` has no elements, and `length(A)` is the
number of elements (docstrings at base/abstractarray.jl:305-308). -/
def LengthIsemptyCount : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF →
    (lengthA A).val = A.data.length ∧ (isemptyA A = A.data.isEmpty)

/-- `eachindex(A, B)` throws `DimensionMismatch` when the arrays have different sizes
(docstring, base/abstractarray.jl:356-360: "If the arrays have different sizes
and/or dimensionalities, a `DimensionMismatch` exception will be thrown."). -/
def EachindexSizeMismatch : Prop :=
  ∀ (A B : Arr Int), A.WF → B.WF → sizeA A ≠ sizeA B → eachindex2 A B = .error .dimensionMismatch

/-- `cat` does not depend on where the axes of its arguments start: whenever
`cat(X, Y; dims)` returns, it returns what it returns for the same data with
1-based axes (cat docstring, base/abstractarray.jl:2058-2066: along a cat dimension
the output size is the sum of the argument sizes, so each argument occupies the next
`size(a, d)` positions of the 1-based output). -/
def CatOffsetInvariant : Prop :=
  ∀ (dims : List Int) (X Y : Arr Int) (out : CatOut Int), X.WF → Y.WF →
    catKw 0 [.arr X, .arr Y] dims = .ok out → catKw 0 [.arr (rebase X), .arr (rebase Y)] dims = .ok out

/-- Iterating an array visits its elements in column-major order, for both
`IndexStyle`s and any axes (doc/src/manual/arrays.md "Iteration": elements are
visited in memory/column-major order; eachindex docstring example,
base/abstractarray.jl:365-382). -/
def IterateColumnMajor : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF → iterAll A (fuelOf A) (iterStart A) = .ok A.data

/-- Pointwise comparison of two element lists. -/
def allPairs {α : Type} (p : α → α → Bool) (xs ys : List α) : Bool :=
  (xs.zip ys).all (fun q => p q.1 q.2)

/-- `isequal(A, B)` is true exactly when `A` and `B` have the same axes and their
elements are pairwise `isequal` (isequal and == docstrings: collections compare their
contents recursively; base/abstractarray.jl:3106). -/
def IsequalElementwise : Prop :=
  ∀ {α : Type} (iseq : α → α → Bool) (A B : Arr α), A.WF → B.WF →
    isequalA iseq A B = .ok (axesEq A.axes B.axes && allPairs iseq A.data B.data)

/-- Three-valued `==` over element lists: `false` if some pair is `false`, else
`missing` if some pair is `missing`, else `true` (== docstring, base/operators.jl:126-127:
"Collections generally implement three-valued logic akin to all, returning missing if
any operands contain missing values and all other pairs are equal."). -/
def eq3List {α : Type} (eq : Eq3 α) (xs ys : List α) : Option Bool :=
  if (xs.zip ys).any (fun q => eq q.1 q.2 == some false) then some false
  else if (xs.zip ys).any (fun q => eq q.1 q.2 == none) then none
  else some true

/-- `A == B` is `false` for different axes and otherwise the three-valued conjunction
of the elementwise `==`. -/
def EqElementwise : Prop :=
  ∀ {α : Type} (eq : Eq3 α) (A B : Arr α), A.WF → B.WF →
    eqA eq A B = .ok (if axesEq A.axes B.axes then eq3List eq A.data B.data else some false)

/-- `map!(f, dest, A)` overwrites the first `min(length(dest), length(A))` elements of
`dest` (in iteration order) with `f` of the corresponding elements of `A` and leaves
the rest unchanged (map! docstring, base/abstractarray.jl:3562-3592: "Like map, but
stores the result in destination"; the docstring example keeps trailing elements). -/
def MapBangPrefix : Prop :=
  ∀ {α : Type} (f : α → α) (dest A : Arr α), dest.WF → A.WF →
    mapBang f dest A =
      .ok { dest with data := (A.data.take dest.data.length).map f ++ dest.data.drop A.data.length }

/-- The indices produced by iterating `eachindex(A)` (at most `n` of them). -/
def eachAll {α : Type} (A : Arr α) : Nat → IterState → List (List I64)
  | 0, _ => []
  | n + 1, st =>
    match eachindexStep A st with
    | none => []
    | some (I, st') => I :: eachAll A n st'

/-- `eachindex(A)` yields every valid index of `A` exactly once, in column-major
order: its `k`-th index selects the `k`-th element under the manual's indexing rules,
and it yields `length(A)` indices (eachindex docstring, base/abstractarray.jl:322-360:
"an iterable object for visiting each index of an AbstractArray A in an efficient
manner"; doc/src/manual/arrays.md "Iteration"), for either `IndexStyle` and any axes. -/
def EachindexEnumerates : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF →
    (eachAll A (fuelOf A) (eachStart A)).length = A.data.length ∧
    ∀ (k : Nat) (h : k < (eachAll A (fuelOf A) (eachStart A)).length),
      refPos A ((eachAll A (fuelOf A) (eachStart A))[k]'h) = some k

/-- `copyto!(dest, src)` for arrays: when `length(dest) >= length(src)` the first
`length(src)` elements of `dest` (in iteration order) become the elements of `src` and
the others are left untouched; a shorter `dest` is an error (copyto! docstring,
base/abstractarray.jl:1042-1071: "Copy all elements from collection src to array dest,
whose length must be greater than or equal to the length n of src. The first n elements
of dest are overwritten, the other elements are left untouched."). Holds for every pair
of `IndexStyle`s and any axes of `dest` and `src`, for a `BitArray` `dest` (`destBit`; a
`BitArray` is a 1-based `IndexLinear` array), and whatever `mightalias(dest, src)` reports
(`aliased`). -/
def CopytoPrefix : Prop :=
  ∀ {α : Type} (destBit aliased : Bool) (dest src : Arr α), dest.WF → src.WF →
    (destBit = true → dest.style = .linear ∧ ∀ r ∈ dest.axes, r.kind = .oneTo) →
    (src.data.length ≤ dest.data.length →
      copytoA destBit aliased dest src = .ok { dest with data := src.data ++ dest.data.drop src.data.length }) ∧
    (dest.data.length < src.data.length → ∃ e, copytoA destBit aliased dest src = .error e)

/-- `copyto!(deststyle, dest, srcstyle, src)`: the `IndexStyle` arguments only choose the
copying loop, so for every pair of style arguments (whether or not they are the arrays'
own styles) the result is the `copyto!(dest, src)` contract above. -/
def CopytoStylesPrefix : Prop :=
  ∀ {α : Type} (ds ss : Style) (aliased : Bool) (dest src : Arr α), dest.WF → src.WF →
    (src.data.length ≤ dest.data.length →
      copytoStyles ds ss aliased dest src = .ok { dest with data := src.data ++ dest.data.drop src.data.length }) ∧
    (dest.data.length < src.data.length → ∃ e, copytoStyles ds ss aliased dest src = .error e)

/-- `copy(A)` of an array whose axes are `Base.OneTo`s returns an `Array` with the same
axes and the same elements in the same order, whatever the uninitialized contents of
`similar(A)` were (copy docstring, base/abstractarray.jl:1191-1209 for copymutable:
"Make a mutable copy of an array"; doc/src/manual/interfaces.md: similar returns an array
with the same shape). -/
def CopyEqual : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF → (∀ r ∈ A.axes, r.kind = .oneTo) →
    ∀ junk : List α, junk.length = A.data.length →
      copyA A junk = some (.ok ⟨A.axes, .linear, A.data⟩)

/-- Lexicographic comparison of element lists under element `isequal` and `isless`:
the first unequal pair decides, otherwise the shorter list is smaller. -/
def lexCmp {α : Type} (iseq lt : α → α → Bool) : List α → List α → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => if !iseq x y then (if lt x y then -1 else 1) else lexCmp iseq lt xs ys

/-- Vectors are "first compared by their starting indices, and then lexicographically by
their elements" (isless docstring, base/abstractarray.jl:3138-3144); `cmp` returns -1, 0
or 1 accordingly and `isless(A, B)` is `cmp(A, B) < 0`. Holds for any axes and either
`IndexStyle`. -/
def CmpVectorOrder : Prop :=
  ∀ {α : Type} (iseq lt : α → α → Bool) (A B : Arr α), A.WF → B.WF →
    A.axes.length = 1 → B.axes.length = 1 →
    let c := if (linearAxis A).lo.val < (linearAxis B).lo.val then -1
      else if (linearAxis B).lo.val < (linearAxis A).lo.val then 1
      else lexCmp iseq lt A.data B.data
    cmpV iseq lt A B = .ok c ∧ islessV iseq lt A B = .ok (decide (c < 0))

end JuliaLean.AbstractArraySpecs
