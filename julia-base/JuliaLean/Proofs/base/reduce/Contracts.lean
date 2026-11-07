import JuliaLean.base.reduce
import JuliaLean.base.reducedim

/-!
Properties of the reductions in `base/reduce.jl`, stated over the models of this area.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

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
  ∀ (x : Val) (ty : Ty), Vec.foldr Val.plus Val.firstPlus (Vec.emptyPlus ty) [x] = .ok (Val.firstPlus x)

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
    ∀ x rest, vs.flatten = x :: rest → Vec.foldlFlatten op first (fun _ => .error .argumentError) (.vector .bottom) vs = .ok (rest.foldl op (first x))

/-- `sum(Iterators.flatten(vs))` equals `sum(collect(Iterators.flatten(vs)))` for vectors
`vs` of `Vector{Int}`: the element type `Int` is known, so the empty sum is `0`
(`base/reduce.jl:470-472`). -/
def FlattenSumAgrees : Prop :=
  ∀ vs : List (List Val), (∀ v ∈ vs, ∀ x ∈ v, ∃ y, x = .int .i64 y) →
    Vec.foldlFlatten Val.addSum Val.firstAddSum Vec.emptyAddSum (.vector (.int .i64)) vs = Vec.sum (.int .i64) vs.flatten

/-- An empty flattened integer iterator has the additive identity. -/
def FlattenEmptySum : Prop :=
  ∀ vs : List (List Val), vs.flatten = [] →
    Vec.foldlFlatten Val.addSum Val.firstAddSum Vec.emptyAddSum (.vector (.int .i64)) vs =
      .ok (Val.i64 0)

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

end JuliaLean.Reduce
