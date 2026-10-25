import JuliaLean.Multidim.Model

/-! Properties of the multidimensional-array model, as Julia documents or obviously
promises them. -/

namespace JuliaLean.Multidim

/-! ## Proven -/

/-- Iterating a `CartesianIndices` visits its elements in the order of the nested loops
of its docstring (first dimension fastest), once each, then stops: `iterate(R)` gives
the first element (or `nothing` when empty) and `iterate(R, I)` the next one. -/
def CartesianIterOrder : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) →
    iterFirst R = (elems R).head? ∧
    ∀ k : Nat, k < (elems R).length → iterNext R ((elems R).getD k []) = (elems R)[k + 1]?

/-- `Iterators.reverse(R)` for a `CartesianIndices` visits the elements in exactly the
reverse order. -/
def CartesianRevOrder : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) →
    revFirst R = (elems R).reverse.head? ∧
    ∀ k : Nat, k < (elems R).length →
      revNext R ((elems R).reverse.getD k []) = (elems R).reverse[k + 1]?

/-- `isless` on `CartesianIndex{N}` is a strict total order (reverse-lexicographic). -/
def CartesianIslessOrder : Prop :=
  ∀ a b c : List I64, a.length = b.length → b.length = c.length →
    ciLess a a = false ∧ (ciLess a b = true → ciLess b c = true → ciLess a c = true) ∧
    (ciLess a b = true ∨ a = b ∨ ciLess b a = true)

/-- `reverse(R::CartesianIndices; dims)` accepts exactly the `dims` that are distinct
dimensions in `1:ndims(R)`. -/
def ReverseDimsCheck : Prop :=
  ∀ (N : Nat) (dims : List Int),
    reverseDimsOk N dims = true ↔ (dims.Nodup ∧ ∀ d ∈ dims, 1 ≤ d ∧ d ≤ N)

/-- The documented result of `circshift`: `circshift(A, s)[J] == A[mod.(J .- 1 .- s, n) .+ 1]`
for each dimension (missing shifts are zero), for every `Array` and every tuple of
integer shift amounts no longer than `ndims(A)`. -/
def CircshiftFormula : Prop :=
  ∀ (sz : List Nat) (shifts : List Int) (src : List Int → Int),
    (∀ n ∈ sz, n < 2 ^ 62) → shifts.length ≤ sz.length →
    ∃ dest, circshift sz src shifts = .ok dest ∧
      ∀ J : List Int, inAxes (oneAxes sz) J = true →
        dest J = some (src ((J.zip (sz.zip (shifts ++ List.replicate (sz.length - shifts.length) 0))).map
          fun (j, n, s) => (j - 1 - s) % (n : Int) + 1))

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

/-- The size of `repeat(A; inner, outer)` is `size(A) .* inner .* outer` after padding all
three with ones to a common length; negative counts, and too few `inner` counts (or too few
`outer` counts when `inner` is given), are an `ArgumentError`. -/
def RepeatShape : Prop :=
  ∀ (sz : List Int) (inner outer : Option (List Int)),
    (∀ n ∈ sz, 0 ≤ n ∧ n < 2 ^ 20) →
    (∀ i, inner = some i → ∀ x ∈ i, x < 2 ^ 20 ∧ -2 ^ 20 < x) →
    (∀ o, outer = some o → ∀ x ∈ o, x < 2 ^ 20 ∧ -2 ^ 20 < x) →
    let N := max sz.length (max ((inner.map List.length).getD 0) ((outer.map List.length).getD 0))
    let ii := (inner.map (padOnes · N)).getD (List.replicate N 1)
    let oo := (outer.map (padOnes · N)).getD (List.replicate N 1)
    repeatSize sz inner outer =
      if (∀ i, inner = some i → (∀ x ∈ i, 0 ≤ x) ∧ sz.length ≤ i.length) ∧
          (∀ o, outer = some o → (∀ x ∈ o, 0 ≤ x) ∧ (sz.length ≤ o.length ∨ inner = none))
      then .ok ((List.range N).map fun d => (padOnes sz N).getD d 1 * ii.getD d 1 * oo.getD d 1)
      else .error .argumentError

/-- `diff(A; dims)` has the size of `A` with `size(A, dims)` reduced by one (not below
zero), and throws `ArgumentError` for `dims` outside `1:ndims(A)`. -/
def DiffSize : Prop :=
  ∀ (sz : List Nat) (dims : Int),
    diffSize sz dims =
      if 1 ≤ dims ∧ dims ≤ sz.length then
        .ok (sz.set (dims.toNat - 1) (sz.getD (dims.toNat - 1) 0 - 1))
      else .error .argumentError

/-- `circcopy!(dest, src)` on nonempty arrays of the same size copies `src` with each
dimension indexed modulo its length: `dest[J] == src[K]` where `K ≡ J (mod size)` lies in
the axes of `src`. -/
def CirccopyNonempty : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int),
    (∀ p ∈ axd, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    (∀ p ∈ axs, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    ∃ out, circcopy axd dest axs src = .ok out ∧
      ∀ J : List Int, inAxes axd J = true →
        out J = some (src ((J.zip axs).map fun (j, s) => s.1 + (j - s.1) % (s.2 - s.1 + 1)))

/-- `findfirst(f, A)` on an array with no empty dimension returns the first index
(column-major) where `f` holds, or `nothing`. -/
def FindfirstNonempty : Prop :=
  ∀ (sz : List Nat) (A : List Int → Bool), (∀ n ∈ sz, 0 < n ∧ n < 2 ^ 20) →
    findfirst sz A = .ok (firstTrue sz A)

/-- For `1 ≤ d ≤ ndims(A)` and a one-dimensional index `i`, `selectdim(A, d, i)` is
`view(A, :, ..., :, i, :, ..., :)` with `i` in position `d` (same size or same exception). -/
def SelectdimInRange : Prop :=
  ∀ (sz : List Nat) (d : Nat) (i : Idx), 1 ≤ d → d ≤ sz.length → i.ndims = 1 → (∀ n, i ≠ .slice n) →
    (selectdim sz d i >>= view sz) =
      view sz (List.replicate (d - 1) .colon ++ [i] ++ List.replicate (sz.length - d) .colon)

/-! ## Refuted -/

/-- `findfirst(f, A)` returns the first index (column-major) where `f` holds, or
`nothing`; it never throws. -/
def FindfirstCartesian : Prop :=
  ∀ (sz : List Nat) (A : List Int → Bool), (∀ n ∈ sz, n < 2 ^ 20) →
    findfirst sz A = .ok (firstTrue sz A)

/-- A view returned by `selectdim(A, d, i)` addresses only positions inside `A`. -/
def SelectdimInBounds : Prop :=
  ∀ (sz : List Nat) (d : Int) (i : Idx), i ≠ .cart [] → (∀ n, i ≠ .slice n) →
    match selectdim sz d i with
    | .ok I => viewInBounds sz I = true
    | .error _ => True

/-- `selectdim(A, d, i)` is `view(A, :, ..., :, i, :, ..., :)` with `i` in position `d`
(same size, or the same exception), for every `d ≥ 1` and every one-dimensional index. -/
def SelectdimViewAgrees : Prop :=
  ∀ (sz : List Nat) (d : Nat) (i : Idx), 1 ≤ d → i.ndims = 1 → (∀ n, i ≠ .slice n) →
    (selectdim sz d i >>= view sz) =
      view sz (List.replicate (d - 1) .colon ++ [i] ++ List.replicate (sz.length - d) .colon)

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

/-- `circcopy!(dest, src)` succeeds whenever `src` and `dest` have the same size. -/
def CirccopyCorrect : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int),
    (∀ p ∈ axd, p.1 - 1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    (∀ p ∈ axs, p.1 - 1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    ∃ out, circcopy axd dest axs src = .ok out

/-- `copyto!(dest, Rdest, src, Rsrc)` throws `ArgumentError` when the regions differ in size. -/
def CopytoSizeChecked : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int)
    (Rd Rs : List Rng),
    Rd.length = Rs.length → Rd.map (·.len) ≠ Rs.map (·.len) →
    errKind (copytoCI axd dest Rd axs src Rs) = some .argumentError

/-- `==` on `CartesianIndices` agrees with `==` on the arrays they represent: equal size and
equal elements. -/
def CartesianEqArrays : Prop :=
  ∀ R S : List Rng, R.length = S.length → (∀ r ∈ R, r.WF) → (∀ s ∈ S, s.WF) →
    ciEq R S = (R.map (·.len) == S.map (·.len) && elems R == elems S)

/-- `isempty(R)` for a `CartesianIndices` holds exactly when one of its ranges is empty
(`isempty` docstring: "Determine whether a collection is empty (has no elements)"). -/
def CartesianIsEmpty : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) → (ciIsEmpty R = true ↔ ∃ r ∈ R, r.len = 0)

end JuliaLean.Multidim
