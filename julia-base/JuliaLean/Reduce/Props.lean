import JuliaLean.Reduce.Vec
import JuliaLean.Reduce.Dims

/-!
Properties of the reductions in `base/reduce.jl`, `base/reducedim.jl`,
`base/accumulate.jl` and `base/anyall.jl`, stated over the models of this area.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- Slice `k` (0-based) of a matrix reduced along `d`: column `k` for `d = 1`, row `k`
for `d = 2`. -/
def Mat.slice (A : Mat Val) (d k : Nat) : List Val := if d = 1 then A.col k else A.row k

/-- A `BitInteger` type narrower than `Int`. -/
def smallTy (t : IntTy) : Bool := Val.smallSigned t || Val.smallUnsigned t

/-- The element type of `sum`/`prod`/`cumsum`/`cumprod` of a `Vector{T}` (`base/reduce.jl:
511-513`): `Int` for small signed types, `UInt` for small unsigned types. -/
def sumTy (t : IntTy) : IntTy :=
  if Val.smallSigned t then .i64 else if Val.smallUnsigned t then .u64 else t

/-- Values of integers of type `t`. -/
def ints (t : IntTy) (v : List (JInt t)) : List Val := v.map (Val.int t)

/-! ### Whole-collection reductions -/

/-- `reduce(op, A)` (pairwise, `base/reduce.jl:252-274, 436-457`) equals the left fold
`foldl(op, map(f, A))` whenever `op` is associative, for every block size: the
association is unspecified (`base/reduce.jl:480-483`) but the result of an associative
operation does not depend on it. -/
def PairwiseFoldl : Prop :=
  ∀ (α β : Type) (f : α → β) (op : β → β → β) (blk : Nat) (e : R β) (x : α) (xs : List α),
    (∀ a b c, op (op a b) c = op a (op b c)) →
    mapreduceArr f op f e blk (x :: xs) = .ok (xs.foldl (fun v y => op v (f y)) (f x))

/-- `extrema(v) == (minimum(v), maximum(v))` for every vector, including `NaN`,
`missing`, signed zeros and the empty vector (both throw). -/
def ExtremaAgree : Prop :=
  ∀ v : List Val, Vec.extrema v = (do let a ← Vec.minimum v; let b ← Vec.maximum v; pure (a, b))

/-- For a nonempty `Vector{Float64}`, `findmax(v)` returns an element `v[i]` that is
`isequal` to `maximum(v)` with its index `i`, and `findmin(v)` one `isequal` to
`minimum(v)` (`base/reduce.jl:855-863, 921-926`: "Return the maximal element ... and its
index"; `argmax(itr) = findmax(itr)[2]`). -/
def FindmaxAgree : Prop :=
  ∀ v : List F64, v ≠ [] →
    (∃ a b i, Vec.findmax (v.map .f64) = .ok (.f64 a, i) ∧ Vec.maximum (v.map .f64) = .ok (.f64 b) ∧
      F64.isequal a b = true ∧ v[i - 1]? = some a) ∧
    (∃ a b i, Vec.findmin (v.map .f64) = .ok (.f64 a, i) ∧ Vec.minimum (v.map .f64) = .ok (.f64 b) ∧
      F64.isequal a b = true ∧ v[i - 1]? = some a)

/-- `foldl(op, itr; init)` and `foldr(op, itr; init)` use `init` exactly once, as the
start of the left (right) fold (`base/reduce.jl:166-241`). -/
def FoldInit : Prop :=
  ∀ (α β : Type) (f : α → β) (op : β → β → β) (init : β) (v : List α),
    mapfoldlInit f op init v = (v.map f).foldl op init ∧
    mapfoldrInit f op init v = (v.map f).foldr op init

/-- `foldr(op, [x])` returns `reduce_first(op, x)`, the value `reduce_first`'s docstring
promises for `reduce`, `foldl` and `foldr` over a single element (`base/reduce.jl:397-403`);
here `op = +`, where `reduce_first(+, x::Bool) = Int(x)`. -/
def FoldrReduceFirst : Prop :=
  ∀ (x : Val) (ty : Ty), Vec.foldr Val.plus (Vec.emptyPlus ty) [x] = .ok (Val.firstPlus x)

/-- `any(f, itr)` and `all(f, itr)` follow three-valued logic when `f` returns `Bool` or
`missing`, and short-circuit: once a prefix decides the result, the rest of the
collection is never inspected (`base/anyall.jl:3-10, 32-39`). -/
def AnyAllThreeValued : Prop :=
  ∀ (f : Val → Val) (v : List Val),
    ((∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) →
      Vec.any f v = .ok (if v.any (fun x => f x = .bool true) then .bool true
        else if v.any (fun x => f x = .missing) then .missing else .bool false) ∧
      Vec.all f v = .ok (if v.any (fun x => f x = .bool false) then .bool false
        else if v.any (fun x => f x = .missing) then .missing else .bool true)) ∧
    (∀ w, Vec.any f v = .ok (.bool true) → Vec.any f (v ++ w) = .ok (.bool true)) ∧
    (∀ w, Vec.all f v = .ok (.bool false) → Vec.all f (v ++ w) = .ok (.bool false))

/-- `count(A; init)` gives the same value for an `Array{Bool}` as for any other
collection of the same `Bool`s, for an integer or `Float64` `init` ("init optionally
specifies the value to start counting from and therefore also determines the output
type", `base/reduce.jl:1067-1072`). -/
def CountInitAgrees : Prop :=
  ∀ (init : Val) (xs : List Bool), ((∃ t x, init = .int t x) ∨ (∃ x, init = .f64 x)) →
    Vec.countBoolArray init xs = .ok (Vec.countIter init xs)

/-- `sum(v; init = zero(S))` for small integer types `T`, `S` and nonempty `v::Vector{T}`
is the exact sum in `Int` or `UInt` (`base/reduce.jl:511-513, 539-541`). -/
def SumInitWidened : Prop :=
  ∀ (t s : IntTy) (v : List (JInt t)), smallTy t → smallTy s → v ≠ [] → v.length < 2 ^ 30 →
    ∃ w, (w = .i64 ∨ w = .u64) ∧
      Vec.sumInit (.int s (JInt.lit s 0)) (ints t v) = .int w (JInt.wrap w (v.map (·.val)).sum)

/-- `prod(v; init = one(S))` for small integer types `T`, `S` and nonempty `v::Vector{T}`
is the product in `Int` or `UInt`, wrapping only there (`base/reduce.jl:582-584`). -/
def ProdInitWidened : Prop :=
  ∀ (t s : IntTy) (v : List (JInt t)), smallTy t → smallTy s → v ≠ [] → v.length < 2 ^ 30 →
    ∃ w, (w = .i64 ∨ w = .u64) ∧
      Vec.prodInit (.int s (JInt.lit s 1)) (ints t v) = .int w (JInt.wrap w (v.map (·.val)).prod)

/-- `foldl(op, Iterators.flatten(vs); init)` is the left fold over the concatenation, and
without `init` the left fold from `reduce_first` of the first element whenever the
concatenation is nonempty (`base/reduce.jl:112-125`). -/
def FlattenFoldl : Prop :=
  ∀ (op : Val → Val → Val) (first : Val → Val) (init : Val) (vs : List (List Val)),
    Vec.foldlFlattenInit op init vs = vs.flatten.foldl op init ∧
    ∀ x rest, vs.flatten = x :: rest → Vec.foldlFlatten op first vs = .ok (rest.foldl op (first x))

/-- `sum(Iterators.flatten(vs))` equals `sum(collect(Iterators.flatten(vs)))` for vectors
`vs` of `Vector{Int}`: the element type `Int` is known, so the empty sum is `0`
(`base/reduce.jl:470-472`). -/
def FlattenSumAgrees : Prop :=
  ∀ vs : List (List Val), (∀ v ∈ vs, ∀ x ∈ v, ∃ y, x = .int .i64 y) →
    Vec.foldlFlatten Val.addSum Val.firstAddSum vs = Vec.sum (.int .i64) vs.flatten

/-- `reduce(vcat, vs)` concatenates a nonempty vector of vectors; `reduce(hcat, vs)` puts
them side by side as columns when they have equal lengths and throws
`DimensionMismatch` otherwise. -/
def ReduceCatSpec : Prop :=
  ∀ vs : List (List Int), vs ≠ [] →
    Cat.reduceVcat vs = .ok vs.flatten ∧
    (∀ v1 rest, vs = v1 :: rest →
      ((∀ v ∈ vs, v.length = v1.length) → Cat.reduceHcat vs = .ok (v1.length, vs.length, vs.flatten)) ∧
      ((∃ v ∈ vs, v.length ≠ v1.length) → Cat.reduceHcat vs = .error .dimensionMismatch))

/-- Empty collections: `maximum`, `minimum`, `extrema`, `findmax`, `findmin` throw
`ArgumentError`; with `init` the reductions return `init`; `sum(T[])` is `zero` of the
widened type (`base/reduce.jl:317-356, 636-714`). -/
def EmptyReductions : Prop :=
  ∀ (init : Val) (t : IntTy),
    Vec.maximum [] = .error .argumentError ∧ Vec.minimum [] = .error .argumentError ∧
    Vec.extrema [] = .error .argumentError ∧ Vec.findmax [] = .error .argumentError ∧
    Vec.findmin [] = .error .argumentError ∧ Vec.maximumInit init [] = init ∧
    Vec.sumInit init [] = init ∧ Vec.prodInit init [] = init ∧
    Vec.sum (.int t) [] = .ok (.int (sumTy t) (JInt.lit _ 0)) ∧
    Vec.prod (.int t) [] = .ok (.int (sumTy t) (JInt.lit _ 1))

/-! ### Reductions along a dimension -/

/-- `sum(A; dims = d)` for a `BitInteger` matrix has the reduced shape and holds the exact
slice sums in the widened type, wrapping only there (`base/reducedim.jl:464-485`). -/
def SumDimsExact : Prop :=
  ∀ (t : IntTy) (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) →
    (∀ x ∈ A.data, ∃ y, x = .int t y) →
    ∃ Rr, sumDims (fun x => .ok x) (.int t) A d = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n d ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        Rr.get k = .int (sumTy t) (JInt.wrap (sumTy t) ((A.slice d k).map Val.intVal).sum)

/-- `maximum(A; dims = d)` and `minimum(A; dims = d)` of a nonempty `Matrix{Int}` hold
`maximum`/`minimum` of each slice, in the reduced shape (`base/reducedim.jl:613-743`). -/
def MaxDimsInt : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .int .i64 y) →
    ∃ Rr, maxminDims (fun x => .ok x) isMax (.int .i64) A d = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n d ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        (if isMax then Vec.maximum (A.slice d k) else Vec.minimum (A.slice d k)) = .ok (Rr.get k)

/-- Numeric equality `x == y` of two numbers. -/
def Val.numEq (x y : Val) : Prop := F64.eq x.toF64 y.toF64 = true

/-- `maximum(A; dims = d)` succeeds for a nonempty matrix with element type `Int`,
`Float64` or `Union{Int, Float64}` and holds values equal to `maximum` of each slice. -/
def MaxDimsUnion : Prop :=
  ∀ (A : Mat Val) (d : Nat) (ty : Ty), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (ty = .int .i64 ∨ ty = .f64 ∨ ty = .union (.int .i64) .f64) →
    (∀ x ∈ A.data, ty.isa x = true ∧ x.isnan = false) →
    ∃ Rr, maxminDims (fun x => .ok x) true ty A d = .ok Rr ∧
      ∀ k < Rr.data.length, ∃ y, Vec.maximum (A.slice d k) = .ok y ∧ Val.numEq (Rr.get k) y

/-- `maximum(A; dims = d)` of a nonempty matrix whose entries are all `missing` is a
matrix of `missing`, as `maximum` of each slice is (`base/missing.jl:129-137`). -/
def MaxDimsMissing : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, x = .missing) →
    ∃ Rr, maxminDims (fun x => .ok x) isMax .missing A d = .ok Rr ∧
      ∀ k < Rr.data.length, Rr.get k = .missing

/-- `maximum(abs, A; dims = d)` of a nonempty `Matrix{Int}` holds `maximum(abs, slice)`
for every slice. -/
def MaxAbsDims : Prop :=
  ∀ (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .int .i64 y) →
    ∃ Rr, maxAbsDims (.int .i64) A d = .ok Rr ∧
      ∀ k < Rr.data.length, Vec.maxAbs (.int .i64) (A.slice d k) = .ok (Rr.get k)

/-- `sum(A; dims = d, init = zero(S))` of a small-integer matrix holds `sum(slice;
init = zero(S))` for every slice, as the dimension-free `sum` with `init` does. -/
def SumDimsInit : Prop :=
  ∀ (t s : IntTy) (A : Mat Val) (d : Nat), smallTy t → smallTy s → A.WF → (d = 1 ∨ d = 2) →
    (∀ x ∈ A.data, ∃ y, x = .int t y) →
    ∃ Rr, mapreduceDimsInit (fun x => .ok x) (fun x y => .ok (Val.addSum x y)) 1024
        (.int s (JInt.lit s 0)) A d = .ok Rr ∧
      ∀ k < Rr.data.length,
        Val.intVal (Rr.get k) = Val.intVal (Vec.sumInit (.int s (JInt.lit s 0)) (A.slice d k))

/-- `any(A; dims = d)` of a nonempty matrix of `Bool`s and `missing`s holds `any(slice)`
for every slice, three-valued as `any` is (`base/anyall.jl:8-10`). -/
def AnyDimsSlices : Prop :=
  ∀ (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, x = .missing ∨ x = .bool true ∨ x = .bool false) →
    ∃ Rr, anyDims id A d = .ok Rr ∧
      ∀ k < Rr.data.length, Vec.any id (A.slice d k) = .ok (Rr.get k)

/-- The 1-based `CartesianIndex` of element `i` (1-based) of slice `k` along `d`. -/
def sliceIndex (d k i : Nat) : Nat × Nat := if d = 1 then (i, k + 1) else (k + 1, i)

/-- `findmax(A; dims = d)` and `findmin(A; dims = d)` of a nonempty `Matrix{Float64}` hold,
for every slice, `findmax`/`findmin` of the slice with the index mapped to a
`CartesianIndex` (`base/reducedim.jl:1169-1212`). -/
def FindDimsSlices : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .f64 y) →
    ∃ Rr, findDims id isMax .f64 A d = .ok Rr ∧
      (Rr.vals.m, Rr.vals.n) = reducedShape A.m A.n d ∧
      Rr.vals.data.length = Rr.vals.m * Rr.vals.n ∧ Rr.idx.length = Rr.vals.data.length ∧
      ∀ k < Rr.vals.data.length, ∃ i,
        (if isMax then Vec.findmax (A.slice d k) else Vec.findmin (A.slice d k)) =
          .ok (Rr.vals.get k, i) ∧ Rr.idx[k]? = some (sliceIndex d k i)

/-- `findmax(A; dims = d)` returns arrays of the reduced shape (size 1 along `d`), the shape
`sum(A; dims = d)` has, whenever it returns. -/
def FindDimsShape : Prop :=
  ∀ (A : Mat Val) (d : Nat) (ty : Ty) (Rr : FindRes), A.WF → (d = 1 ∨ d = 2) →
    findDims id true ty A d = .ok Rr → (Rr.vals.m, Rr.vals.n) = reducedShape A.m A.n d

/-! ### Accumulation -/

/-- `accumulate(op, v; dims = d, init)` with `d` beyond the dimensions of `v` (a slice of
length 1 along `d`) returns `op(init, v[i])` for every element: `init` instantiates the
accumulation (`base/accumulate.jl:306-310`). -/
def AccumulateDimsInit : Prop :=
  ∀ (v : List (JInt .i64)) (init : JInt .i64) (d : Int), 2 ≤ d →
    accumulateVecDims (fun a b => a + b) id id (some init) v d = .ok (v.map (init + ·))

/-- `accumulate(op, A; dims, init)` scans the columns (`dims = 1`) or rows (`dims = 2`) of a
matrix like `accumulate(op, slice; init)`, and `dims = 1` on a vector is the plain
`accumulate` (`base/accumulate.jl:235-293`). -/
def AccumulateDimsScan : Prop :=
  ∀ (α β : Type) [Inhabited α] [Inhabited β] (op : β → α → β) (first copy : α → β)
    (init : Option β) (A : Mat α) (v : List α),
    accumulateVecDims op first copy init v 1 = .ok (accumulateVec op first init v) ∧
    (A.WF → ∃ B, accumulateDims op first copy init A 1 = .ok B ∧
      ∀ j < A.n, B.col j = accumulateVec op first init (A.col j)) ∧
    (A.WF → 0 < A.n → ∃ B, accumulateDims op first copy init A 2 = .ok B ∧
      ∀ i < A.m, B.row i = accumulateVec op first init (A.row i))

/-- `cumsum(v; dims)` equals `accumulate(+, v; dims)` for every `dims`: both scan for
`dims = 1`, copy for `dims > 1` and throw `ArgumentError` for `dims ≤ 0`
(`base/accumulate.jl:70-119, 374-375`). -/
def CumsumAccumulate : Prop :=
  ∀ (v : List (JInt .i64)) (d : Int),
    cumsumVecDims id (fun a b => a + b) id v d = accumulateVecDims (fun a b => a + b) id id none v d

/-- `cumprod(v)` of a small-integer vector holds the prefix products in `Int`/`UInt`,
wrapping only there (`base/accumulate.jl:94-98, 196-198, 230`). -/
def CumprodWidened : Prop :=
  ∀ (t : IntTy) (v : List (JInt t)), smallTy t →
    accumulateVecDims Val.mulProd Val.firstMulProd id none (ints t v) 1 =
      .ok ((List.range v.length).map fun k =>
        .int (sumTy t) (JInt.wrap (sumTy t) ((v.take (k + 1)).map (·.val)).prod))

end JuliaLean.Reduce
