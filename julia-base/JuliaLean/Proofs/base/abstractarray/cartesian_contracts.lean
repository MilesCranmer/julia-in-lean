import JuliaLean.base.abstractarray

namespace JuliaLean.Multidim

/-- `cat` of arrays with the same number of dimensions `M ≥ length(catdims)`: the shape
is the sum of the sizes along the concatenated dimensions and the common size along the
others; any disagreement along a non-concatenated dimension is a `DimensionMismatch`. -/
def CatSameNdims : Prop :=
  ∀ (catdims : List Bool) (M : Nat) (x : List Nat) (xs : List (List Nat)),
    catdims.length ≤ M → x.length = M → (∀ s ∈ xs, s.length = M) →
    catSizeShape catdims ((x :: xs).map .array) =
      if ∀ i < M, catdims.getD i false = false → ∀ s ∈ xs, s.getD i 0 = x.getD i 0 then
        .ok ((List.range M).map fun i =>
          if catdims.getD i false then x.getD i 0 + (xs.map (·.getD i 0)).sum else x.getD i 0)
      else .error .dimensionMismatch

/-- Along every dimension not in `dims`, every argument of a successful `cat` has the size
of the result (scalars count as size 1). -/
def CatShapeChecked : Prop :=
  ∀ (dims : List Int) (xs : List CatArg),
    match cat dims xs with
    | .ok shape => ∀ x ∈ xs, ∀ i < shape.length, dims.contains ((i : Int) + 1) = false →
        x.sizeAt i = shape.getD i 0
    | .error _ => True

/-- `hvcat(rows, xs...)` with numbers of one type throws the same exception as with
numbers of mixed types (the generic `typed_hvcat`). -/
def HvcatNumbersAgree : Prop :=
  ∀ (rows : List Nat) (n : Nat), errKind (hvcatSame rows n) = errKind (hvcatTyped rows n)

/-- `hvcat(nbc, values...)` with a block-column count `nbc ≤ 0` and at least one value
throws `ArgumentError`. -/
def HvcatColumnsError : Prop :=
  ∀ (nbc : I64) (n : Nat), nbc.val ≤ 0 → 0 < n → n < 2 ^ 62 → hvcatCols nbc n = .error .argumentError

end JuliaLean.Multidim
