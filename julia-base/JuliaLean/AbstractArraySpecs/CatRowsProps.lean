import JuliaLean.AbstractArraySpecs.Cat

/-!
Spec-first contracts of the `cat` front ends and helpers modelled in `Cat.lean`.

The reference follows the `cat` docstring (base/abstractarray.jl:2058-2066: "Along a
dimension d in dims, the size of the output array is sum(size(a,d) for a in A). Along
other dimensions, all input arrays should have the same size, which will also be the
size of the output array along those dimensions. ... If dims is an iterable containing
several dimensions, the positions along these dimensions are increased simultaneously
for each input array, filling with zero elsewhere.") and the `vcat`/`hcat` docstrings
("Concatenate arrays or numbers vertically/horizontally"), which treat a number as a
one-element argument. It is computed from the arguments' sizes and elements only:
argument `k` occupies the block that starts after arguments `1..k-1` along every
concatenated dimension, and its elements fill that block in column-major order.
-/

namespace JuliaLean.AbstractArraySpecs

/-- The sizes of an argument: its axis lengths; a value has none (size 1 along every
dimension, like the trailing dimensions of an array). -/
def itemSizes {α : Type} : Item α → List Int
  | .arr a => a.axes.map Ax.len
  | .val _ => []

/-- The elements of an argument in column-major order. -/
def itemVals {α : Type} : Item α → List α
  | .arr a => a.data
  | .val x => [x]

/-- Whether the 0-based dimension `d` is concatenated. -/
def flagAt (catdims : List Bool) (d : Nat) : Bool := catdims.getD d false

/-- The concatenated dimensions of `dims`: `d` is concatenated when `d ∈ dims`. -/
def flagsOf (dims : List Int) : List Bool :=
  (List.range (dims.foldl max 0).toNat).map (fun (k : Nat) => dims.contains ((k : Int) + 1))

/-- The output size from the argument sizes: the sum along concatenated dimensions,
the common size along the others (`none` when they differ). -/
def refShapeOf (catdims : List Bool) (S : List (List Int)) : Option (List Int) :=
  let N := max catdims.length ((S.map List.length).foldl max 0)
  (List.range N).mapM fun d =>
    let len := fun (s : List Int) => s.getD d 1
    if flagAt catdims d then some (S.map len).sum
    else match S with
      | [] => some 0
      | s :: _ => if S.all (fun t => len t == len s) then some (len s) else none

def refShape {α : Type} (catdims : List Bool) (X : List (Item α)) : Option (List Int) :=
  refShapeOf catdims (X.map itemSizes)

/-- 0-based index tuples of an array of the given shape, in column-major order. -/
def colTuples : List Nat → List (List Nat)
  | [] => [[]]
  | n :: ns => (colTuples ns).flatMap (fun t => (List.range n).map (· :: t))

/-- Column-major position of a 0-based index tuple. -/
def colIndex : List Nat → List Nat → Nat
  | [], _ => 0
  | i :: is, n :: ns => i + n * colIndex is ns
  | i :: is, [] => i + colIndex is []

/-- The element at output index `I`: from the first argument whose block contains `I`
(`offs` is where the next block starts along each dimension). -/
def refCell {α : Type} (catdims : List Bool) (I : List Nat) : List (Item α) → List Nat → Option α
  | [], _ => none
  | x :: xs, offs =>
    let n := I.length
    let szs := (List.range n).map (fun d => ((itemSizes x).getD d 1).toNat)
    let inside := (List.range n).all (fun d =>
      if flagAt catdims d then decide (offs.getD d 0 ≤ I.getD d 0) && decide (I.getD d 0 < offs.getD d 0 + szs.getD d 0)
      else decide (I.getD d 0 < szs.getD d 0))
    if inside then
      (itemVals x)[colIndex ((List.range n).map (fun d =>
        if flagAt catdims d then I.getD d 0 - offs.getD d 0 else I.getD d 0)) szs]?
    else refCell catdims I xs ((List.range n).map (fun d =>
      if flagAt catdims d then offs.getD d 0 + szs.getD d 0 else offs.getD d 0))

/-- The documented concatenation written over the background `bg` (the cell at a
position outside every block): `DimensionMismatch` when the sizes disagree. -/
def refCatInto {α β : Type} (g : α → β) (bg : Nat → Option β) (catdims : List Bool) (X : List (Item α)) :
    R (CatOut β) :=
  match refShape catdims X with
  | none => .error .dimensionMismatch
  | some shape =>
    let sh := shape.map Int.toNat
    .ok ⟨shape.map i64, (colTuples sh).zipIdx.map (fun ⟨I, p⟩ =>
      match refCell catdims I X (List.replicate sh.length 0) with
      | some v => some (g v)
      | none => bg p)⟩

/-- The documented concatenation of a fresh output: zeros outside the blocks. -/
def refCat {α β : Type} (g : α → β) (zero : β) (catdims : List Bool) (X : List (Item α)) : R (CatOut β) :=
  refCatInto g (fun _ => some zero) catdims X

/-- Whether some array argument has an axis that does not start at 1. -/
def anyOffset {α : Type} (X : List (Item α)) : Bool :=
  X.any (fun | .arr a => a.axes.any (fun r => r.lo != i64 1) | .val _ => false)

/-- At least one argument, well-formed arrays, and a result whose sizes and element
count are representable as Julia's `Int`. -/
def CatPre {α : Type} (catdims : List Bool) (X : List (Item α)) : Prop :=
  X ≠ [] ∧ (∀ a, Item.arr a ∈ X → a.WF) ∧
    ∀ s, refShape catdims X = some s → (∀ n ∈ s, n ≤ tmax) ∧ s.foldl (· * ·) 1 ≤ tmax

/-- Every element converts to the output element type, as `g`. -/
def ConvOK {α β : Type} (conv : α → R β) (g : α → β) (X : List (Item α)) : Prop :=
  ∀ x ∈ X, ∀ v ∈ itemVals x, conv v = .ok (g v)

/-- A front end agrees with the reference: it returns the documented result or throws
its `DimensionMismatch`; an argument with offset axes may instead be rejected with
`ArgumentError` (as 1.13.2 does, "offset arrays are not supported"). -/
def CatAgrees {α β : Type} (X : List (Item α)) (r ref : R (CatOut β)) : Prop :=
  r = ref ∨ (anyOffset X = true ∧ r = .error .argumentError)

instance {α β : Type} [DecidableEq β] (X : List (Item α)) (r ref : R (CatOut β)) :
    Decidable (CatAgrees X r ref) := by unfold CatAgrees; infer_instance

/-- Valid `dims`: a nonempty list of positive dimensions. -/
def DimsOK (dims : List Int) : Prop := dims ≠ [] ∧ ∀ d ∈ dims, 1 ≤ d

/-! ## Front ends -/

/-- `vcat(X...)` concatenates its arguments (arrays or other values) vertically. -/
def VcatAnySpec : Prop :=
  ∀ {α : Type} (zero : α) (X : List (Item α)), CatPre [true] X →
    CatAgrees X (vcatAny zero X) (refCat id zero [true] X)

/-- `hcat(X...)` concatenates its arguments horizontally. -/
def HcatAnySpec : Prop :=
  ∀ {α : Type} (zero : α) (X : List (Item α)), CatPre [false, true] X →
    CatAgrees X (hcatAny zero X) (refCat id zero [false, true] X)

/-- `typed_vcat(T, X...)` is the vertical concatenation with elements converted to `T`. -/
def TypedVcatAnySpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (X : List (Item α)), CatPre [true] X →
    ConvOK conv g X → CatAgrees X (typedVcatAny conv zero X) (refCat g zero [true] X)

/-- `typed_hcat(T, X...)` is the horizontal concatenation with elements converted to `T`. -/
def TypedHcatAnySpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (X : List (Item α)), CatPre [false, true] X →
    ConvOK conv g X → CatAgrees X (typedHcatAny conv zero X) (refCat g zero [false, true] X)

/-- `vcat(A)` of one array is the array's elements in a 1-based `Array` of its size. -/
def Vcat1Spec : Prop :=
  ∀ {α : Type} (zero : α) (A : Arr α), CatPre [true] [.arr A] →
    CatAgrees [.arr A] (vcat1 zero A) (refCat id zero [true] [.arr A])

/-- `vcat(A, B)` stacks two arrays vertically. -/
def Vcat2Spec : Prop :=
  ∀ {α : Type} (zero : α) (A B : Arr α), CatPre [true] [.arr A, .arr B] →
    CatAgrees [.arr A, .arr B] (vcat2 zero A B) (refCat id zero [true] [.arr A, .arr B])

/-- `vcat(A...)` stacks arrays vertically. -/
def VcatArrsSpec : Prop :=
  ∀ {α : Type} (zero : α) (A : List (Arr α)), CatPre [true] (A.map .arr) →
    CatAgrees (A.map .arr) (vcatArrs zero A) (refCat id zero [true] (A.map .arr))

/-- `vcat(A...)` of arrays and numbers stacks them vertically. -/
def VcatMixedSpec : Prop :=
  ∀ {α : Type} (zero : α) (X : List (Item α)), CatPre [true] X →
    CatAgrees X (vcatMixed zero X) (refCat id zero [true] X)

def Hcat1Spec : Prop :=
  ∀ {α : Type} (zero : α) (A : Arr α), CatPre [false, true] [.arr A] →
    CatAgrees [.arr A] (hcat1 zero A) (refCat id zero [false, true] [.arr A])

def Hcat2Spec : Prop :=
  ∀ {α : Type} (zero : α) (A B : Arr α), CatPre [false, true] [.arr A, .arr B] →
    CatAgrees [.arr A, .arr B] (hcat2 zero A B) (refCat id zero [false, true] [.arr A, .arr B])

def HcatArrsSpec : Prop :=
  ∀ {α : Type} (zero : α) (A : List (Arr α)), CatPre [false, true] (A.map .arr) →
    CatAgrees (A.map .arr) (hcatArrs zero A) (refCat id zero [false, true] (A.map .arr))

def HcatMixedSpec : Prop :=
  ∀ {α : Type} (zero : α) (X : List (Item α)), CatPre [false, true] X →
    CatAgrees X (hcatMixed zero X) (refCat id zero [false, true] X)

def TypedVcat1Spec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A : Arr α), CatPre [true] [.arr A] →
    ConvOK conv g [.arr A] → CatAgrees [.arr A] (typedVcat1 conv zero A) (refCat g zero [true] [.arr A])

def TypedVcat2Spec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A B : Arr α), CatPre [true] [.arr A, .arr B] →
    ConvOK conv g [.arr A, .arr B] →
    CatAgrees [.arr A, .arr B] (typedVcat2 conv zero A B) (refCat g zero [true] [.arr A, .arr B])

def TypedVcatArrsSpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A : List (Arr α)), CatPre [true] (A.map .arr) →
    ConvOK conv g (A.map .arr) →
    CatAgrees (A.map .arr) (typedVcatArrs conv zero A) (refCat g zero [true] (A.map .arr))

def TypedHcat1Spec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A : Arr α), CatPre [false, true] [.arr A] →
    ConvOK conv g [.arr A] → CatAgrees [.arr A] (typedHcat1 conv zero A) (refCat g zero [false, true] [.arr A])

def TypedHcat2Spec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A B : Arr α), CatPre [false, true] [.arr A, .arr B] →
    ConvOK conv g [.arr A, .arr B] →
    CatAgrees [.arr A, .arr B] (typedHcat2 conv zero A B) (refCat g zero [false, true] [.arr A, .arr B])

def TypedHcatArrsSpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A : List (Arr α)), CatPre [false, true] (A.map .arr) →
    ConvOK conv g (A.map .arr) →
    CatAgrees (A.map .arr) (typedHcatArrs conv zero A) (refCat g zero [false, true] (A.map .arr))

/-- `_cat(dims, X...)` concatenates along `dims` in the arguments' common type. -/
def CatPromoteSpec : Prop :=
  ∀ {α : Type} (zero : α) (dims : List Int) (X : List (Item α)), DimsOK dims → CatPre (flagsOf dims) X →
    CatAgrees X (catPromote zero dims X) (refCat id zero (flagsOf dims) X)

/-- `cat_t(T, X...; dims)` concatenates along `dims` with elements converted to `T`. -/
def CatTKwSpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (X : List (Item α)) (dims : List Int),
    DimsOK dims → CatPre (flagsOf dims) X → ConvOK conv g X →
    CatAgrees X (catTKw conv zero X dims) (refCat g zero (flagsOf dims) X)

/-- `__cat(A, shape, catdims, X...)` writes every argument into its block of the
preallocated output `A` (whose shape is the concatenation's) and leaves the other
cells as they were. -/
def CatInnerSpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (A : CatOut β) (catdims : List Bool) (X : List (Item α))
    (s : List Int), CatPre catdims X → ConvOK conv g X → refShape catdims X = some s →
    A.shape = s.map i64 → A.cells.length = (s.map Int.toNat).foldl (· * ·) 1 →
    CatAgrees X (catInner conv A A.shape catdims X) (refCatInto g (fun p => A.cells.getD p none) catdims X)

/-! ## Shape helpers -/

/-- `cat_shape(dims, shapes)` for one or more argument shapes is the output size:
the sum along concatenated dimensions, the common size along the others, and
`DimensionMismatch` when they differ. -/
def CatShapeSpec : Prop :=
  ∀ (catdims : List Bool) (shapes : List (List I64)), shapes ≠ [] → (∀ s ∈ shapes, ∀ n ∈ s, 0 ≤ n.val ∧ n.val ≤ tmax) →
    catShape catdims shapes = match refShapeOf catdims (shapes.map (·.map (·.val))) with
      | none => .error .dimensionMismatch
      | some s => .ok (s.map i64)

/-- `_cat_size_shape(dims, shape, X...)`, given the running output shape of earlier
arguments, is the output size of those arguments and `X`. -/
def CatSizeShapeFromSpec : Prop :=
  ∀ {α : Type} (catdims : List Bool) (shape : List I64) (X : List (Item α)), X ≠ [] →
    (∀ a, Item.arr a ∈ X → a.WF) → (∀ n ∈ shape, 0 ≤ n.val ∧ n.val ≤ tmax) →
    (∀ s, refShapeOf catdims (shape.map (·.val) :: X.map itemSizes) = some s → ∀ n ∈ s, n ≤ tmax) →
    catSizeShapeFrom catdims shape X = match refShapeOf catdims (shape.map (·.val) :: X.map itemSizes) with
      | none => .error .dimensionMismatch
      | some s => .ok (s.map i64)

end JuliaLean.AbstractArraySpecs
