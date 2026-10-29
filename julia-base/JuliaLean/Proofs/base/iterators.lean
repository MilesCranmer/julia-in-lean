import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.iterators

namespace JuliaLean.Proofs.base.iterators

set_option linter.deprecated false

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.iterators

/-!
# Properties of `base/iterators.jl`

Specifications of the iterator adapters, trait combinators, metadata queries, and iteration
protocols modelled in `JuliaLean.base.iterators`, stated from the docstrings, the manual, and
collection invariants, with their proofs and refutations.

## Nothing to promise (pure forwarding / struct construction / trait plumbing)
- `map@56`: `map(f, arg, args...) = Base.Generator(f, arg, args...)` forwards directly to `Base.Generator` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@113`: `reverse(itr) = Reverse(itr)` wraps an arbitrary iterator in `Reverse` (also covered in `iteratorscov-reverse-yields`).
- `eltype@128`: `eltype(::Type{Reverse{T}}) where {T} = eltype(T)` forwards the element type of the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `length@129`: `length(r::Reverse) = length(r.itr)` forwards `length` to the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `size@130`: `size(r::Reverse) = size(r.itr)` forwards `size` to the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `IteratorSize@131`: `IteratorSize(::Type{Reverse{T}}) where {T} = IteratorSize(T)` forwards the size trait of `T` (also covered in `iteratorscov-reverse-traits`).
- `IteratorEltype@132`: `IteratorEltype(::Type{Reverse{T}}) where {T} = IteratorEltype(T)` forwards the eltype trait of `T` (also covered in `iteratorscov-reverse-traits`).
- `last@133`: `last(r::Reverse) = first(r.itr)` forwards `last` on a reversed iterator to `first` of the underlying iterator (also covered in `iteratorscov-reverse-traits`).
- `reverse@156`: `reverse(R::AbstractRange) = Base.reverse(R)` delegates range reversal to `Base.reverse` (also covered in `iteratorscov-reverse-yields`).
- `reverse@157`: `reverse(G::Generator) = Generator(G.f, reverse(G.iter))` reconstructs the `Generator` over the reversed inner iterator (also covered in `iteratorscov-reverse-yields`).
- `reverse@158`: `reverse(r::Reverse) = r.itr` unwraps `Reverse` (also covered in `iteratorscov-reverse-yields`).
- `reverse@159`: `reverse(x::Union{Number,AbstractChar}) = x` is the identity on scalars (also covered in `iteratorscov-reverse-yields`).
- `reverse@160`: `reverse(p::Pair) = Base.reverse(p)` delegates pair reversal to `Base.reverse` (also covered in `iteratorscov-reverse-yields`).
- `enumerate@207`: `enumerate(iter) = Enumerate(iter)` wraps `iter` in `Enumerate` (also covered in `iterators-enumerate`).
- `length@209`: `length(e::Enumerate) = length(e.itr)` forwards `length` to `e.itr` (also covered in `iterators-enumerate`).
- `size@210`: `size(e::Enumerate) = size(e.itr)` forwards `size` to `e.itr` (also covered in `iteratorscov-enumerate`).
- `eltype@219`: `eltype(::Type{Enumerate{I}}) where {I} = TupleOrBottom(Int, eltype(I))` pairs `Int` with `eltype(I)` (also covered in `iteratorscov-enumerate`).
- `IteratorSize@221`: `IteratorSize(::Type{Enumerate{I}}) where {I} = IteratorSize(I)` forwards the size trait of `I` (also covered in `iteratorscov-enumerate`).
- `IteratorEltype@222`: `IteratorEltype(::Type{Enumerate{I}}) where {I} = IteratorEltype(I)` forwards the eltype trait of `I` (also covered in `iteratorscov-enumerate`).
- `pairs@281`: `pairs(::IndexLinear, A::AbstractArray) = Pairs(A, LinearIndices(A))` constructs `Pairs` with `LinearIndices(A)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@285`: `pairs(tuple::Tuple) = Pairs{Int}(tuple, keys(tuple))` constructs `Pairs` with `keys(tuple)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@286`: `pairs(nt::NamedTuple) = Pairs{Symbol}(nt, nothing)` constructs `Pairs` over a `NamedTuple` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@287`: `pairs(v::Core.SimpleVector) = Pairs(v, LinearIndices(v))` constructs `Pairs` with `LinearIndices(v)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@288`: `pairs(A::AbstractVector) = pairs(IndexLinear(), A)` forwards vector `pairs` to linear indexing (also covered in `iteratorscov-pairs-semantics`).
- `pairs@291`: `pairs(::IndexCartesian, A::AbstractArray) = Pairs(A, CartesianIndices(A))` constructs `Pairs` with `CartesianIndices(A)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@292`: `pairs(A::AbstractArray) = pairs(IndexCartesian(), A)` forwards general array `pairs` to Cartesian indexing (also covered in `iteratorscov-pairs-semantics`).
- `length@294`: `length(v::Pairs) = length(keys(v))` forwards `length` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `axes@295`: `axes(v::Pairs) = axes(keys(v))` forwards `axes` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `size@296`: `size(v::Pairs) = size(keys(v))` forwards `size` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `isdone@316`: `isdone(v::Pairs, state...) = isdone(keys(v), state...)` forwards `isdone` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `IteratorSize@318`: `IteratorSize(::Type{<:Pairs{<:Any,<:Any,I}}) where {I} = IteratorSize(I)` forwards the key iterator's size trait (also covered in `iteratorscov-pairs-semantics`).
- `IteratorSize@319`: `IteratorSize(::Type{<:Pairs{<:Any,<:Any,<:AbstractUnitRange}}) = HasLength()` reports `HasLength()` for unit-range keys (also covered in `iteratorscov-pairs-semantics`).
- `haskey@326`: `haskey(v::Pairs, key) = key in keys(v)` delegates membership to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `values@328`: `values(v::Pairs) = getfield(v, :data)` projects the underlying data collection (also covered in `iteratorscov-pairs-semantics`).
- `getindex@329`: `getindex(v::Pairs, key) = values(v)[key]` delegates indexing to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `setindex!@330`: `setindex!(v::Pairs, value, key) = (values(v)[key] = value; v)` delegates mutation to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `get@331`: `get(v::Pairs, key, default) = get(values(v), key, default)` delegates default lookup to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `get@332`: `get(f::Base.Callable, v::Pairs, key) = get(f, values(v), key)` delegates thunk lookup to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `zip@379`: `zip(a...) = Zip(a)` wraps the tuple of iterators in `Zip` (also covered in `iterators-zip`).
- `_promote_tuple_shape@416`: `_promote_tuple_shape(a, b) = promote_shape(a, b)` forwards to `promote_shape` (also covered in `iteratorscov-zip-metadata`).
- `_promote_tuple_shape@418`: `_promote_tuple_shape(a) = a` is the unary identity base case (also covered in `iteratorscov-zip-metadata`).
- `last@519`: `last(z::Zip) = nth(z, length(z))` delegates `last` to `nth` at `length(z)` (also covered in `iteratorscov-zip-metadata`).
- `filter@576`: `filter(flt, itr) = Filter(flt, itr)` wraps `flt` and `itr` in `Filter` (also covered in `iteratorscov-filter`).
- `eltype@594`: `eltype(::Type{Filter{F,I}}) where {F,I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-filter`).
- `IteratorEltype@595`: `IteratorEltype(::Type{Filter{F,I}}) where {F,I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-filter`).
- `IteratorSize@596`: `IteratorSize(::Type{<:Filter}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-filter`).
- `reverse@598`: `reverse(f::Filter) = Filter(f.flt, reverse(f.itr))` wraps `reverse(f.itr)` in `Filter` (also covered in `iteratorscov-filter`).
- `last@599`: `last(f::Filter) = first(reverse(f))` delegates `last` to `first(reverse(f))` (also covered in `iteratorscov-filter`).
- `accumulate@641`: `accumulate(f, itr; init=...) = Accumulate(f, itr, init)` constructs `Accumulate` (also covered in `iterators-accumulate`).
- `length@661`: `length(itr::Accumulate) = length(itr.itr)` forwards `length` to `itr.itr` (also covered in `iteratorscov-accumulate`).
- `size@662`: `size(itr::Accumulate) = size(itr.itr)` forwards `size` to `itr.itr` (also covered in `iteratorscov-accumulate`).
- `IteratorSize@664`: `IteratorSize(::Type{<:Accumulate{<:Any,I}}) where {I} = IteratorSize(I)` forwards `IteratorSize(I)` (also covered in `iteratorscov-accumulate`).
- `IteratorEltype@665`: `IteratorEltype(::Type{<:Accumulate}) = EltypeUnknown()` reports `EltypeUnknown()` (also covered in `iteratorscov-accumulate`).
- `rest@696`: `rest(itr, state) = Rest(itr, state)` constructs `Rest` (also covered in `iteratorscov-rest`).
- `rest@697`: `rest(itr::Rest, state) = Rest(itr.itr, state)` replaces the state of an existing `Rest` (also covered in `iteratorscov-rest`).
- `rest@698`: `rest(itr) = itr` is the unary identity (also covered in `iteratorscov-rest`).
- `eltype@735`: `eltype(::Type{<:Rest{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-rest`).
- `IteratorEltype@736`: `IteratorEltype(::Type{<:Rest{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-rest`).
- `eltype@770`: `eltype(::Type{<:Count{T}}) where {T} = T` returns the type parameter `T` (also covered in `iteratorscov-countfrom-eltype`).
- `IteratorSize@774`: `IteratorSize(::Type{<:Count}) = IsInfinite()` reports `IsInfinite()` (also covered in `iteratorscov-countfrom-integers`).
- `eltype@818`: `eltype(::Type{Take{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-take`).
- `IteratorEltype@819`: `IteratorEltype(::Type{Take{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-take`).
- `eltype@875`: `eltype(::Type{Drop{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-drop`).
- `IteratorEltype@876`: `IteratorEltype(::Type{Drop{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-drop`).
- `iterate@891`: `iterate(it::Drop, state) = iterate(it.xs, state)` forwards subsequent iteration steps to `it.xs` (also covered in `iteratorscov-drop`).
- `isdone@892`: `isdone(it::Drop, state) = isdone(it.xs, state)` forwards `isdone` with state to `it.xs` (also covered in `iteratorscov-drop`).
- `takewhile@928`: `takewhile(pred, xs) = TakeWhile(pred, xs)` constructs `TakeWhile` (also covered in `iterators-takewhile-dropwhile`).
- `IteratorSize@937`: `IteratorSize(::Type{<:TakeWhile}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-while`).
- `eltype@938`: `eltype(::Type{TakeWhile{I,P}} where P) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-while`).
- `IteratorEltype@939`: `IteratorEltype(::Type{TakeWhile{I,P}} where P) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-while`).
- `dropwhile@976`: `dropwhile(pred, itr) = DropWhile(pred, itr)` constructs `DropWhile` (also covered in `iterators-takewhile-dropwhile`).
- `iterate@978`: `iterate(ibl::DropWhile, itr) = iterate(ibl.xs, itr)` forwards subsequent iteration steps to `ibl.xs` (also covered in `iteratorscov-while`).
- `IteratorSize@988`: `IteratorSize(::Type{<:DropWhile}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-while`).
- `eltype@989`: `eltype(::Type{DropWhile{I,P}}) where {I,P} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-while`).
- `IteratorEltype@990`: `IteratorEltype(::Type{DropWhile{I,P}}) where {I,P} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-while`).
- `findeach@1018`: `findeach(it) = findeach(identity, it)` forwards to `findeach` with `identity` (also covered in `iteratorscov-cycle-repeated`).
- `cycle@1058`: `cycle(xs) = Cycle(xs)` constructs `Cycle` (also covered in `iteratorscov-cycle-repeated`).
- `eltype@1061`: `eltype(::Type{Cycle{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-cycle-repeated`).
- `IteratorEltype@1062`: `IteratorEltype(::Type{Cycle{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@1074`: `reverse(it::Cycle) = Cycle(reverse(it.xs))` wraps `reverse(it.xs)` in `Cycle` (also covered in `iteratorscov-cycle-repeated`).
- `last@1075`: `last(it::Cycle) = last(it.xs)` forwards `last` to `it.xs` (also covered in `iteratorscov-cycle-repeated`).
- `repeated@1083`: `repeated(x) = Repeated(x)` constructs `Repeated` (also covered in `iterators-repeated-n`).
- `eltype@1113`: `eltype(::Type{Repeated{O}}) where {O} = O` returns `O` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@1120`: `reverse(it::Union{Repeated,Take{<:Repeated}}) = it` is the identity on repeated iterators (also covered in `iteratorscov-cycle-repeated`).
- `last@1121`: `last(it::Union{Repeated,Take{<:Repeated}}) = first(it)` forwards `last` to `first` (also covered in `iteratorscov-cycle-repeated`).
- `product@1148`: `product(iters...) = ProductIterator(iters)` constructs `ProductIterator` (also covered in `iterators-product`).
- `reverse@1255`: `reverse(p::ProductIterator) = ProductIterator(Base.map(reverse, p.iterators))` maps `reverse` over factor iterators (also covered in `iteratorscov-product-methods`).
- `flatten@1291`: `flatten(itr) = Flatten(itr)` constructs `Flatten` (also covered in `iterators-flatten`).
- `eltype@1293`: `eltype(::Type{Flatten{I}}) where {I} = eltype(eltype(I))` delegates to the inner `eltype` (also covered in `iteratorscov-flatten-methods`).
- `last@1380`: `last(f::Flatten) = first(reverse(f))` delegates `last` to `first(reverse(f))` (also covered in `iteratorscov-flatten-methods`).
- `flatmap@1421`: `flatmap(f, c...) = flatten(map(f, c...))` composes `flatten` and `map` (also covered in `iteratorscov-cycle-repeated`).
- `PartitionIterator@1446`: `PartitionIterator(A::AbstractArray, n::Int) = PartitionIterator(vec(A), n)` forwards arrays through `vec(A)` (also covered in `iteratorscov-partition-methods`).
- `PartitionIterator@1447`: `PartitionIterator(v::AbstractVector, n::Int) = PartitionIterator{typeof(v)}(v, n)` constructs `PartitionIterator` (also covered in `iteratorscov-partition-methods`).
- `Stateful@1605`: `Stateful(x::Stateful) = x` is the identity on an existing `Stateful` (also covered in `iteratorscov-stateful-methods`).
- `convert@1606`: `convert(::Type{Stateful}, itr) = Stateful(itr)` forwards conversion to `Stateful(itr)` (also covered in `iteratorscov-stateful-methods`).
- `eltype@1626`: `eltype(::Type{<:Stateful{T}}) where {T} = eltype(T)` forwards `eltype(T)` (also covered in `iteratorscov-stateful-methods`).
- `IteratorEltype@1627`: `IteratorEltype(::Type{<:Stateful{T}}) where {T} = IteratorEltype(T)` forwards `IteratorEltype(T)` (also covered in `iteratorscov-stateful-methods`).
- `only@1659`: `only(x) = _only(x, iterate)` forwards to `_only` with `iterate` (also covered in `iteratorscov-only-nth-methods`).
- `only@1680`: `only(x::IdDict) = _only(x, first)` forwards to `_only` with `first` (also covered in `iteratorscov-only-nth-methods`).
- `IteratorSize@1704`: `IteratorSize(::Type{<:IterableStatePairs{T}}) where T = IteratorSize(T)` forwards `IteratorSize(T)` (also covered in `iteratorscov-iterable-state-pairs`).
- `length@1705`: `length(x::IterableStatePairs) = length(x.x)` forwards `length` to `x.x` (also covered in `iteratorscov-iterable-state-pairs`).
- `Base.eltype@1706`: `Base.eltype(::Type{IterableStatePairs{T}}) where T = Pair{<:Any, eltype(T)}` forms the pair element type (also covered in `iteratorscov-iterable-state-pairs`).
- `reverse@1714`: `reverse(x::IterableStatePairs) = IterableStatePairs(Iterators.reverse(x.x))` wraps `Iterators.reverse(x.x)` (also covered in `iteratorscov-iterable-state-pairs`).
- `reverse@1715`: `reverse(x::IterableStatePairs{<:Iterators.Reverse}) = IterableStatePairs(x.x.itr)` unwraps the inner `Reverse` (also covered in `iteratorscov-iterable-state-pairs`).
- `pairs@1725`: `pairs(s::AbstractString) = IterableStatePairs(s)` wraps `s` in `IterableStatePairs` (also covered in `iteratorscov-iterable-state-pairs`).
- `nth@1753`: `nth(itr, n::Integer) = _nth(IteratorSize(itr), itr, n)` dispatches on `IteratorSize(itr)` (also covered in `iteratorscov-only-nth-methods`).
- `nth@1754`: `nth(itr::Cycle{I}, n::Integer) where I = _nth(IteratorSize(I), itr, n)` dispatches on `IteratorSize(I)` (also covered in `iterators-nth-cycle-overflow`).
- `nth@1755`: `nth(itr::Flatten{Take{Repeated{O}}}, n::Integer) where O = _nth(IteratorSize(O), itr, n)` dispatches on `IteratorSize(O)` (also covered in `iterators-nth-cycle-overflow`).
- `nth@1810`: `nth(n::Integer) = Base.Fix2(nth, n)` constructs the curried `Fix2` adapter (also covered in `iteratorscov-only-nth-methods`).
- `eltype@425`: `eltype(::Type{Zip{Is}}) = TupleOrBottom(ntuple(n -> eltype(fieldtype(Is, n)), N)...)` forms the tuple of component element types (also covered in `iteratorscov-zip-metadata`).
- `IteratorSize@503`: `IteratorSize(::Type{Zip{Is}}) = zip_iteratorsize(...)` forwards to `zip_iteratorsize` over component traits (also covered in `iteratorscov-zip-traits`).
- `IteratorEltype@504`: `IteratorEltype(::Type{Zip{Is}}) = zip_iteratoreltype(...)` forwards to `zip_iteratoreltype` over component traits (also covered in `iteratorscov-zip-traits`).
- `eltype@1197`: `eltype(::Type{ProductIterator{I}}) = _prod_eltype(I)` forwards to `_prod_eltype` (also covered in `iteratorscov-product-methods`).
- `_prod_eltype@1198`: `_prod_eltype(::Type{Tuple{}}) = Tuple{}` is the empty product element type (also covered in `iteratorscov-product-methods`).
- `_prod_eltype@1199`: `_prod_eltype(::Type{I}) = TupleOrBottom(ntuple(n -> eltype(fieldtype(I, n)), N)...)` forms the tuple of factor element types (also covered in `iteratorscov-product-methods`).
- `eltype@1298`: `eltype(::Type{Flatten{I}}) = Any` falls back to `Any` when the outer eltype is unknown (also covered in `iteratorscov-flatten-methods`).
- `eltype@1301`: `eltype(::Type{Flatten{Tuple{}}}) = eltype(Tuple{})` forwards the empty tuple element type (also covered in `iteratorscov-flatten-methods`).
- `IteratorEltype@1305`: `IteratorEltype(::Type{Flatten{I}}) = _flatteneltype(I, IteratorEltype(I))` forwards to `_flatteneltype` (also covered in `iteratorscov-flatten-methods`).
- `IteratorEltype@1306`: `IteratorEltype(::Type{Flatten{Tuple{}}}) = IteratorEltype(Tuple{})` forwards `IteratorEltype(Tuple{})` (also covered in `iteratorscov-flatten-methods`).
- `_flatteneltype@1307`: `_flatteneltype(I, ::HasEltype) = IteratorEltype(eltype(I))` returns the inner iterator's eltype trait (also covered in `iteratorscov-flatten-methods`).
- `_flatteneltype@1308`: `_flatteneltype(I, et) = EltypeUnknown()` reports `EltypeUnknown()` when the outer eltype is unknown (also covered in `iteratorscov-flatten-methods`).
- `eltype@1449`: `eltype(::Type{PartitionIterator{T}}) = Vector{eltype(T)}` forms `Vector{eltype(T)}` for generic partitions (also covered in `iteratorscov-partition-methods`).
- `eltype@1451`: `eltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = AbstractVector{eltype(T)}` forms `AbstractVector{eltype(T)}` for array partitions (also covered in `iteratorscov-partition-methods`).
- `eltype@1453`: `eltype(::Type{PartitionIterator{T}}) where {T<:Vector} = Base.SubArray{...}` forms the 1D `SubArray` view type for vector partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1455`: `IteratorEltype(::Type{PartitionIterator{T}}) = IteratorEltype(T)` forwards `IteratorEltype(T)` (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1456`: `IteratorEltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = EltypeUnknown()` reports `EltypeUnknown()` for general `AbstractArray` partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1457`: `IteratorEltype(::Type{PartitionIterator{T}}) where {T<:Vector} = IteratorEltype(T)` forwards `IteratorEltype(T)` for `Vector` partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorSize@1625`: `IteratorSize(::Type{<:Stateful{T}}) = IteratorSize(T) isa IsInfinite ? IsInfinite() : SizeUnknown()` preserves `IsInfinite()` and otherwise reports `SizeUnknown()` (also covered in `iteratorscov-stateful-methods`).
-/

def nothingToPromise : List (String × String) := [
  ("map@56", "forwards directly to Base.Generator"),
  ("reverse@113", "wraps an iterator in Reverse"),
  ("eltype@128", "forwards eltype to the wrapped iterator type"),
  ("length@129", "forwards length to r.itr"),
  ("size@130", "forwards size to r.itr"),
  ("IteratorSize@131", "forwards IteratorSize to the wrapped iterator type"),
  ("IteratorEltype@132", "forwards IteratorEltype to the wrapped iterator type"),
  ("last@133", "forwards last(Reverse(itr)) to first(itr)"),
  ("reverse@156", "forwards range reversal to Base.reverse"),
  ("reverse@157", "reconstructs Generator over reverse(G.iter)"),
  ("reverse@158", "unwraps r.itr from Reverse"),
  ("reverse@159", "returns scalar numbers and characters unchanged"),
  ("reverse@160", "forwards pair reversal to Base.reverse"),
  ("enumerate@207", "wraps an iterator in Enumerate"),
  ("length@209", "forwards length to e.itr"),
  ("size@210", "forwards size to e.itr"),
  ("eltype@219", "constructs TupleOrBottom(Int, eltype(I))"),
  ("IteratorSize@221", "forwards IteratorSize to the wrapped iterator type"),
  ("IteratorEltype@222", "forwards IteratorEltype to the wrapped iterator type"),
  ("pairs@281", "constructs Pairs with LinearIndices(A)"),
  ("pairs@285", "constructs Pairs with keys(tuple)"),
  ("pairs@286", "constructs Pairs over a NamedTuple"),
  ("pairs@287", "constructs Pairs with LinearIndices(v)"),
  ("pairs@288", "forwards AbstractVector pairs to IndexLinear"),
  ("pairs@291", "constructs Pairs with CartesianIndices(A)"),
  ("pairs@292", "forwards AbstractArray pairs to IndexCartesian"),
  ("length@294", "forwards length to keys(v)"),
  ("axes@295", "forwards axes to keys(v)"),
  ("size@296", "forwards size to keys(v)"),
  ("isdone@316", "forwards isdone to keys(v)"),
  ("IteratorSize@318", "forwards IteratorSize of the key iterator"),
  ("IteratorSize@319", "reports HasLength for unit-range keys"),
  ("haskey@326", "forwards membership to keys(v)"),
  ("values@328", "returns the underlying data field"),
  ("getindex@329", "forwards getindex to values(v)"),
  ("setindex!@330", "forwards setindex! to values(v) and returns v"),
  ("get@331", "forwards default get lookup to values(v)"),
  ("get@332", "forwards callable fallback get lookup to values(v)"),
  ("zip@379", "wraps the argument tuple in Zip"),
  ("_promote_tuple_shape@416", "forwards two-shape promotion to promote_shape"),
  ("_promote_tuple_shape@418", "returns a single shape tuple unchanged"),
  ("last@519", "forwards last(z::Zip) to nth(z, length(z))"),
  ("filter@576", "constructs Filter(flt, itr)"),
  ("eltype@594", "forwards eltype(I)"),
  ("IteratorEltype@595", "forwards IteratorEltype(I)"),
  ("IteratorSize@596", "reports SizeUnknown for Filter"),
  ("reverse@598", "constructs Filter(f.flt, reverse(f.itr))"),
  ("last@599", "forwards last(f::Filter) to first(reverse(f))"),
  ("accumulate@641", "constructs Accumulate(f, itr, init)"),
  ("length@661", "forwards length to itr.itr"),
  ("size@662", "forwards size to itr.itr"),
  ("IteratorSize@664", "forwards IteratorSize(I)"),
  ("IteratorEltype@665", "reports EltypeUnknown for Accumulate"),
  ("rest@696", "constructs Rest(itr, state)"),
  ("rest@697", "replaces the state of an existing Rest"),
  ("rest@698", "returns itr unchanged when no state is given"),
  ("eltype@735", "forwards eltype(I)"),
  ("IteratorEltype@736", "forwards IteratorEltype(I)"),
  ("eltype@770", "returns the type parameter T of Count{T}"),
  ("IteratorSize@774", "reports IsInfinite for Count"),
  ("eltype@818", "forwards eltype(I)"),
  ("IteratorEltype@819", "forwards IteratorEltype(I)"),
  ("eltype@875", "forwards eltype(I)"),
  ("IteratorEltype@876", "forwards IteratorEltype(I)"),
  ("iterate@891", "forwards subsequent Drop iteration steps to it.xs"),
  ("isdone@892", "forwards state-ful isdone on Drop to it.xs"),
  ("takewhile@928", "constructs TakeWhile(pred, xs)"),
  ("IteratorSize@937", "reports SizeUnknown for TakeWhile"),
  ("eltype@938", "forwards eltype(I)"),
  ("IteratorEltype@939", "forwards IteratorEltype(I)"),
  ("dropwhile@976", "constructs DropWhile(pred, itr)"),
  ("iterate@978", "forwards subsequent DropWhile iteration steps to ibl.xs"),
  ("IteratorSize@988", "reports SizeUnknown for DropWhile"),
  ("eltype@989", "forwards eltype(I)"),
  ("IteratorEltype@990", "forwards IteratorEltype(I)"),
  ("findeach@1018", "forwards findeach(it) to findeach(identity, it)"),
  ("cycle@1058", "constructs Cycle(xs)"),
  ("eltype@1061", "forwards eltype(I)"),
  ("IteratorEltype@1062", "forwards IteratorEltype(I)"),
  ("reverse@1074", "constructs Cycle(reverse(it.xs))"),
  ("last@1075", "forwards last(it::Cycle) to last(it.xs)"),
  ("repeated@1083", "constructs Repeated(x)"),
  ("eltype@1113", "returns the type parameter O of Repeated{O}"),
  ("reverse@1120", "returns Repeated or Take{<:Repeated} unchanged"),
  ("last@1121", "forwards last on Repeated to first"),
  ("product@1148", "constructs ProductIterator(iters)"),
  ("reverse@1255", "maps reverse across P.iterators"),
  ("flatten@1291", "constructs Flatten(itr)"),
  ("eltype@1293", "forwards eltype(eltype(I))"),
  ("last@1380", "forwards last(f::Flatten) to first(reverse(f))"),
  ("flatmap@1421", "forwards flatmap(f, c...) to flatten(map(f, c...))"),
  ("PartitionIterator@1446", "forwards AbstractArray to PartitionIterator(vec(A), n)"),
  ("PartitionIterator@1447", "constructs PartitionIterator{typeof(v)}(v, n)"),
  ("Stateful@1605", "returns an existing Stateful unchanged"),
  ("convert@1606", "forwards conversion to Stateful(itr)"),
  ("eltype@1626", "forwards eltype(T)"),
  ("IteratorEltype@1627", "forwards IteratorEltype(T)"),
  ("only@1659", "forwards only(x) to _only(x, iterate)"),
  ("only@1680", "forwards only(x::IdDict) to _only(x, first)"),
  ("IteratorSize@1704", "forwards IteratorSize(T)"),
  ("length@1705", "forwards length to x.x"),
  ("Base.eltype@1706", "constructs Pair{<:Any, eltype(T)}"),
  ("reverse@1714", "wraps Iterators.reverse(x.x) in IterableStatePairs"),
  ("reverse@1715", "unwraps x.x.itr into IterableStatePairs"),
  ("pairs@1725", "wraps AbstractString in IterableStatePairs"),
  ("nth@1753", "dispatches nth(itr, n) on IteratorSize(itr)"),
  ("nth@1754", "dispatches nth(itr::Cycle, n) on IteratorSize(I)"),
  ("nth@1755", "dispatches nth(itr::Flatten{Take{Repeated}}, n) on IteratorSize(O)"),
  ("nth@1810", "constructs Base.Fix2(nth, n)"),
  ("eltype@425", "constructs TupleOrBottom of component eltypes"),
  ("IteratorSize@503", "forwards Zip IteratorSize to zip_iteratorsize"),
  ("IteratorEltype@504", "forwards Zip IteratorEltype to zip_iteratoreltype"),
  ("eltype@1197", "forwards ProductIterator eltype to _prod_eltype"),
  ("_prod_eltype@1198", "returns Tuple{} for empty ProductIterator"),
  ("_prod_eltype@1199", "constructs TupleOrBottom of factor eltypes"),
  ("eltype@1298", "returns Any when outer eltype is unknown"),
  ("eltype@1301", "forwards eltype(Tuple{}) for empty Flatten"),
  ("IteratorEltype@1305", "forwards Flatten IteratorEltype to _flatteneltype"),
  ("IteratorEltype@1306", "forwards IteratorEltype(Tuple{}) for empty Flatten"),
  ("_flatteneltype@1307", "returns IteratorEltype(eltype(I)) when HasEltype"),
  ("_flatteneltype@1308", "returns EltypeUnknown when outer eltype is unknown"),
  ("eltype@1449", "returns Vector{eltype(T)} for generic PartitionIterator"),
  ("eltype@1451", "returns AbstractVector{eltype(T)} for AbstractArray PartitionIterator"),
  ("eltype@1453", "returns SubArray view type for Vector PartitionIterator"),
  ("IteratorEltype@1455", "forwards IteratorEltype(T) for PartitionIterator"),
  ("IteratorEltype@1456", "returns EltypeUnknown for AbstractArray PartitionIterator"),
  ("IteratorEltype@1457", "forwards IteratorEltype(T) for Vector PartitionIterator"),
  ("IteratorSize@1625", "preserves IsInfinite and otherwise returns SizeUnknown for Stateful")
]

@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → Jl β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem err_bind {α β : Type} (e : JlError) (f : α → Jl β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem pure_jl {α : Type} (x : α) : (pure x : Jl α) = .ok x := rfl

theorem ok_bind_iter {α β : Type} (x : α) (f : α → IteratorResult β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem pure_iter {α : Type} (x : α) :
    (pure x : IteratorResult α) = .ok x := rfl

@[simp] theorem liftM_jl_ok {α : Type} (x : α) :
    (liftM (Except.ok x : Jl α) : IteratorResult α) = .ok x := rfl

@[simp] theorem monadLift_jl_ok {α : Type} (x : α) :
    (MonadLift.monadLift (Except.ok x : Jl α) : IteratorResult α) = .ok x := rfl

@[simp] theorem listIterator_length {α : Type} (xs : List α) :
    (listIterator xs).length = .ok xs.length := rfl

/-- A finite iterator emits exactly the listed values and then stops. -/
def emitsExactly {α S : Type} (itr : IteratorModel α S) (xs : List α) : Prop :=
  collectPrefix itr (xs.length + 1) none = .ok xs

def collectAfterStep {α S : Type} (itr : IteratorModel α S) (f : Nat)
    (step : Jl (Option (α × S))) : Jl (List α) := do
  match ← step with
  | none => pure []
  | some (x, next) => pure (x :: (← collectPrefix itr f (some next)))

theorem collectPrefix_succ {α S : Type} (itr : IteratorModel α S) (f : Nat) (state : Option S) :
    collectPrefix itr (f + 1) state = collectAfterStep itr f (itr.run state) := rfl

@[simp] theorem collectAfterStep_none {α S : Type} (itr : IteratorModel α S) (f : Nat) :
    collectAfterStep itr f (.ok none) = .ok [] := rfl

@[simp] theorem collectAfterStep_some {α S : Type} (itr : IteratorModel α S) (f : Nat)
    (x : α) (next : S) :
    collectAfterStep itr f (.ok (some (x, next))) =
      (do pure (x :: (← collectPrefix itr f (some next)))) := rfl

def enumerateFrom {α : Type} : JInt64 → List α → List (JInt64 × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: enumerateFrom (k + JInt.lit .i64 1) xs

def enumerateSpec {α : Type} (xs : List α) : List (JInt64 × α) :=
  enumerateFrom (JInt.lit .i64 1) xs

def enumerateNatFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: enumerateNatFrom (k + 1) xs

def chunksSpec {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  if n = 0 then [] else
    (List.range ((xs.length + n - 1) / n)).map fun i => (xs.drop (i * n)).take n

def productInt (xs : List JInt64) : Int := xs.foldl (fun acc x => acc * x.val) 1

def countChain (start step : JInt64) : Nat → List JInt64
  | 0 => []
  | n + 1 => start :: countChain (start + step) step n

def scanAccum {α : Type} (f : α → α → α) : α → List α → List α
  | _, [] => []
  | acc, x :: xs => let next := f acc x; next :: scanAccum f next xs

def accumulateSpec {α : Type} (f : α → α → α) (init : Option α) : List α → List α
  | [] => []
  | x :: xs =>
      let first := match init with | none => x | some acc => f acc x
      first :: scanAccum f first xs

/-! ## Core list-iterator lemmas -/

theorem listGet_eq_drop_head? {α : Type} (xs : List α) (i : Nat) :
    listGet xs i = (xs.drop i).head? := by
  induction xs generalizing i with
  | nil => simp [listGet]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [listGet, List.drop] using ih i

theorem listIterator_run_some {α : Type} (xs : List α) (i : Nat) :
    (listIterator xs).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (x, i + 1)) := by
  simp only [listIterator, Option.getD_some, listGet_eq_drop_head?]
  cases xs.drop i <;> rfl

theorem listIterator_run_none {α : Type} (xs : List α) :
    (listIterator xs).run none = (listIterator xs).run (some 0) := rfl

theorem collectPrefix_listIterator_at {α : Type} (xs : List α) (fuel i : Nat)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (listIterator xs) fuel (some i) = .ok (xs.drop i) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, listIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by
        rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by
        rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop]

theorem collectPrefix_listIterator {α : Type} (xs : List α) (fuel : Nat)
    (hf : xs.length < fuel) :
    collectPrefix (listIterator xs) fuel none = .ok xs := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have h0 : collectPrefix (listIterator xs) (fuel + 1) none =
        collectPrefix (listIterator xs) (fuel + 1) (some 0) := rfl
    rw [h0]
    simpa using collectPrefix_listIterator_at xs (fuel + 1) 0 (by simpa using hf)

@[simp] theorem listIterator_isdone_some {α : Type} (xs : List α) (i : Nat) :
    (listIterator xs).isdone (some i) = .ok (some (decide (xs.length ≤ i))) := rfl

theorem jint_convert_i64_val_of_lt (b : Nat) (hb : b < 2 ^ 63) :
    ∃ n64 : JInt64, JInt.convert .i64 (b : Int) = .ok n64 ∧ n64.val = (b : Int) := by
  have hr : IntTy.i64.min ≤ (b : Int) ∧ (b : Int) ≤ IntTy.i64.max := by
    change -(2 ^ 63 : Int) ≤ (b : Int) ∧ (b : Int) ≤ 2 ^ 63 - 1
    omega
  exact ⟨⟨(b : Int), hr⟩, by simp [JInt.convert, hr], rfl⟩

@[simp] theorem jint_convert_i64_self (n : JInt64) :
    JInt.convert .i64 n.val = .ok n := by
  simp [JInt.convert, n.property]

theorem jint_convert_i64_out (n : Int) (h : n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) :
    JInt.convert .i64 n = .error (.inexactError "Int64") := by
  have hnot : ¬ (IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) := by
    change ¬ (-(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1)
    omega
  simp [JInt.convert, hnot, IntTy.name]

/-! ## Refuted properties (16) -/

def TakeIsemptyCorrect : Prop :=
  ∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    let itr := takeAsIterator base ⟨base, n⟩
    (itr.isdone none = .ok (some true) ↔ collectPrefix itr 1 none = .ok [])

theorem takeIsemptyCorrect_refuted : ¬ TakeIsemptyCorrect := by
  intro h
  exact nomatch (h [1] 0).mpr rfl

def PeelRestIsempty : Prop :=
  ∀ (xs : List Int) (x : Int) (rest : Rest (IteratorModel Int Nat) Nat),
    peelModel (fun itr state => itr.run state) restWithState (listIterator xs) =
      .ok (some (x, rest)) →
    (isdoneRest (fun itr state => itr.isdone state) rest none = .ok (some true) ↔
      iterateRest (fun itr state => itr.run state) rest none = .ok none)

theorem peelRestIsempty_refuted : ¬ PeelRestIsempty := by
  intro h
  exact nomatch (h [1] 1 ⟨listIterator [1], 1⟩ rfl).mpr rfl

def DropDropCorrect : Prop :=
  ∀ (xs : List Int) (a b : Nat),
    let base := listIterator xs
    ∃ d, dropDropModel ⟨base, a⟩ (Int.ofNat b) = .ok d ∧
      emitsExactly (dropAsIterator base d) (xs.drop (a + b))

theorem dropDropCorrect_refuted : ¬ DropDropCorrect := by
  intro h
  obtain ⟨_, hd, _⟩ := h [1, 2, 3] (2 ^ 63 - 1) 1
  exact nomatch hd

def NthCycleCorrect : Prop :=
  ∀ (xs : List Int) (m k : Nat) (x : Int),
    0 < xs.length → 1 ≤ k → k ≤ xs.length * m →
      listGet xs ((k - 1) % xs.length) = some x →
      ∃ cyc, cycleNModel (listIterator xs) (Int.ofNat m) = .ok cyc ∧
        sourceMethod1767 (fun it => (it.length.map fun n => JInt.lit .i64 (Int.ofNat n)))
          (fun it n => nthModel it n.val) cyc (JInt.lit .i64 (Int.ofNat k)) = .ok x

theorem nthCycleCorrect_refuted : ¬ NthCycleCorrect := by
  intro h
  obtain ⟨cyc, hcyc, hnth⟩ := h [1, 2, 3] (2 ^ 62) 1 1 (by decide) (by decide) (by decide) rfl
  cases hcyc
  exact nomatch hnth

def NthZipNonpositive : Prop :=
  ∀ {α : Type} (iters : List (IteratorModel α Nat)) (n : Int), n ≤ 0 →
    nthZip iters n = .error .boundsError

theorem nthZipNonpositive_refuted : ¬ NthZipNonpositive := by
  intro h
  exact nomatch h ([] : List (IteratorModel Int Nat)) 0 (by decide)

def NthAnyIntegerType : Prop :=
  ∀ (t : IntTy) (first last : JInt64) (n : JInt t),
    first.val ≤ last.val → 1 ≤ n.val → n.val ≤ last.val - first.val + 1 →
      nthArray first (unitRangeIndex first.val last.val) n =
        .ok (first.val + n.val - 1)

theorem nthAnyIntegerType_refuted : ¬ NthAnyIntegerType := by
  intro h
  exact nomatch h .u64 (JInt.lit .i64 (-5)) (JInt.lit .i64 (-3)) (JInt.lit .u64 1)
    (by decide) (by decide) (by decide)

def ProductLengthExact : Prop :=
  ∀ (mul : JInt64 → JInt64 → Jl JInt64)
    (reduce : (JInt64 → JInt64 → Jl JInt64) → List JInt64 → JInt64 → Jl JInt64),
    (∀ a b, mul a b = checkedMulI64 a b) →
    (∀ values init, reduce mul values init = checkedProductFold mul init values) →
    ∀ sizes, (∀ x ∈ sizes, 0 ≤ x.val) →
      -(2 ^ 63) ≤ productInt sizes → productInt sizes ≤ 2 ^ 63 - 1 →
        productLength (fun sizes : List JInt64 => pure sizes)
          reduce mul (productModel sizes) = .ok (JInt.lit .i64 (productInt sizes))

theorem productLengthExact_refuted : ¬ ProductLengthExact := by
  intro h
  exact nomatch h checkedMulI64 (fun m vs init => checkedProductFold m init vs)
    (fun _ _ => rfl) (fun _ _ => rfl)
    [JInt.lit .i64 (2 ^ 32), JInt.lit .i64 (2 ^ 32), JInt.lit .i64 0]
    (by decide) (by decide) (by decide)

def ProductLastNonempty : Prop :=
  ∀ (ranges : List (JInt64 × JInt64)) (vals : List JInt64),
    lastProduct (fun r : JInt64 × JInt64 => pure r.2) (productModel ranges) = .ok vals →
      ∀ r ∈ ranges, r.1.val ≤ r.2.val

theorem productLastNonempty_refuted : ¬ ProductLastNonempty := by
  intro h
  have h0 := h [(JInt.lit .i64 1, JInt.lit .i64 2), (JInt.lit .i64 1, JInt.lit .i64 0)]
    [JInt.lit .i64 2, JInt.lit .i64 0] rfl
    (JInt.lit .i64 1, JInt.lit .i64 0) (by decide)
  revert h0
  decide

def CycleFirstN : Prop :=
  ∀ (xs : List Int) (n : Nat), n < 2 ^ 63 →
    let cyc := cycleAsIterator (cycleModel (listIterator xs))
    ∃ t ys, takeModel cyc (Int.ofNat n) = .ok t ∧
      collectPrefix (takeAsIterator cyc t) (n + 1) none = .ok ys ∧
      takeLength (fun _ => cycleIteratorSize) (fun _ => cyc.length) t = .ok ys.length

theorem cycleFirstN_refuted : ¬ CycleFirstN := by
  intro h
  obtain ⟨t, ys, ht, hys, hlen⟩ := h [] 3 (by decide)
  cases ht
  cases hys
  exact nomatch hlen

def PartitionRangeChunks : Prop :=
  ∀ (fi li : JInt64) (n : Nat) (state : Option JInt64) (chunk : JInt64 × JInt64) (next : JInt64),
    fi.val ≤ li.val → 0 < n →
      sourceMethod1470 ⟨(fi, li), n⟩ state = some (chunk, next) →
        chunk.1.val ≤ chunk.2.val ∧ chunk.2.val - chunk.1.val + 1 ≤ Int.ofNat n

theorem partitionRangeChunks_refuted : ¬ PartitionRangeChunks := by
  intro h
  have h0 := (h (JInt.lit .i64 (2 ^ 63 - 3)) (JInt.lit .i64 (2 ^ 63 - 1)) 2
    (some (JInt.lit .i64 (2 ^ 63 - 1)))
    (JInt.lit .i64 (2 ^ 63 - 1), JInt.lit .i64 (2 ^ 63 - 2))
    (JInt.lit .i64 (-(2 ^ 63) + 1)) (by decide) (by decide) (by decide)).1
  revert h0
  decide

def PartitionFirstChunk : Prop :=
  ∀ (xs : List Int) (n : Nat), xs ≠ [] → 0 < n →
    ∃ nextState,
      sourceMethod1484 ⟨listIterator xs, n⟩ (.at none) (fun itr st => itr.run st) =
        .ok (some (xs.take n, nextState))

theorem partitionFirstChunk_refuted : ¬ PartitionFirstChunk := by
  intro h
  obtain ⟨_, h0⟩ := h [1, 2, 3] (2 ^ 62) (by decide) (by decide)
  exact nomatch h0

def FirstNAnyInteger : Prop :=
  ∀ (t : IntTy) (xs : List Int) (n : JInt t), 0 ≤ n.val →
    let base := listIterator xs
    ∃ take drop, takeModel base n.val = .ok take ∧
      dropModel base n.val = .ok drop ∧
      emitsExactly (takeAsIterator base take) (xs.take n.val.toNat) ∧
      emitsExactly (dropAsIterator base drop) (xs.drop n.val.toNat)

theorem firstNAnyInteger_refuted : ¬ FirstNAnyInteger := by
  intro h
  obtain ⟨_, _, htake, _⟩ := h .u64 [1, 2, 3] (JInt.typemax .u64) (by decide)
  exact nomatch htake

def ProductOneFactor : Prop :=
  ∀ (xs : List Int) (isdoneAfter : Option Nat → Jl (Option Bool)),
    (∀ st, isdoneAfter st = .ok (some (xs.length ≤ st.getD xs.length))) →
    let base := { listIterator xs with isdone := fun st =>
      match st with | none => pure (some xs.isEmpty) | some s => isdoneAfter (some s) }
    emitsExactly (productAsIterator (productModel [base])
      (fun _ state => isdoneAfter state) (fun itr state => itr.run state))
      (xs.map fun x => [x])

theorem productOneFactor_refuted : ¬ ProductOneFactor := by
  intro h
  exact nomatch h [1] (fun st => .ok (some (1 ≤ st.getD 1))) (fun _ => rfl)

def ProductSizeSound : Prop :=
  ∀ (xs : List Int), sourceMethod1151
    [ (listIterator xs).iteratorSize, .isInfinite ] = .hasLength

theorem productSizeSound_refuted : ¬ ProductSizeSound := by
  intro h
  exact nomatch h []

def CountfromEltype : Prop :=
  let oneunit : Bool ⊕ JInt64 → Bool ⊕ JInt64
    | .inl _ => .inl true
    | .inr _ => .inr (JInt.lit .i64 1)
  let add : Bool ⊕ JInt64 → Bool ⊕ JInt64 → Bool ⊕ JInt64
    | .inl a, .inl b => .inr (JInt.lit .i64 (if a then 1 else 0) + JInt.lit .i64 (if b then 1 else 0))
    | .inl a, .inr y => .inr (JInt.lit .i64 (if a then 1 else 0) + y)
    | .inr x, .inl b => .inr (x + JInt.lit .i64 (if b then 1 else 0))
    | .inr x, .inr y => .inr (x + y)
  ∀ (start : Bool ⊕ JInt64) (k : Nat) (xs : List (Bool ⊕ JInt64)),
    let c := countfromOneunit oneunit add start
    collectPrefix (countAsIterator c) k none = .ok xs →
      ∀ x ∈ xs, x.isLeft = c.start.isLeft

theorem countfromEltype_refuted : ¬ CountfromEltype := by
  intro h
  exact nomatch h (.inl true) 2 [.inl true, .inr (JInt.lit .i64 2)] rfl (.inr (JInt.lit .i64 2))
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

def ProductIntersect : Prop :=
  ∀ (left right : List (List Int)), left.length ≠ right.length →
    (∀ common ∈ List.zipWith (fun xs ys => xs.filter (fun x => ys.contains x)) left right,
      common ≠ []) →
      (intersectProduct (fun xs ys => xs.filter (fun x => ys.contains x))
        (productModel left) (productModel right)).iterators.any List.isEmpty

theorem productIntersect_refuted : ¬ ProductIntersect := by
  intro h
  exact nomatch h [[1, 2, 3]] [[1, 2], [1, 2]] (by decide) (by decide)

/-! ## Proven properties (44) -/

theorem takeAsIterator_run_some {α : Type} (xs : List α) (t : Take (IteratorModel α Nat))
    (m i : Nat) :
    (takeAsIterator (listIterator xs) t).run (some (m, i)) =
      if m = 0 then .ok none else
        match xs.drop i with
        | [] => .ok none
        | x :: _ => .ok (some (x, (m - 1, i + 1))) := by
  simp only [takeAsIterator, iterateTake, Nat.le_zero_eq]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte, listIterator_run_some]
    cases xs.drop i <;> rfl

theorem collectPrefix_take_at {α : Type} (xs : List α) (t : Take (IteratorModel α Nat))
    (fuel m i : Nat) (hf : min m (xs.drop i).length < fuel) :
    collectPrefix (takeAsIterator (listIterator xs) t) fuel (some (m, i)) =
      .ok ((xs.drop i).take m) := by
  induction fuel generalizing m i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, takeAsIterator_run_some]
    by_cases hm : m = 0
    · subst hm; simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      cases hd : xs.drop i with
      | nil => simp
      | cons x rest =>
        have hdrop : xs.drop (i + 1) = rest := by
          rw [← List.drop_drop, hd]; rfl
        have hlen : min k (xs.drop (i + 1)).length < fuel := by
          rw [hdrop]; simp [hd] at hf; omega
        simp only [ok_bind, pure_jl, ih k (i + 1) hlen, hdrop, List.take_succ_cons]

theorem collectPrefix_take {α : Type} (xs : List α) (t : Take (IteratorModel α Nat))
    (fuel : Nat) (hf : (xs.take t.n).length < fuel) :
    collectPrefix (takeAsIterator (listIterator xs) t) fuel none = .ok (xs.take t.n) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have h0 : collectPrefix (takeAsIterator (listIterator xs) t) (fuel + 1) none =
        collectPrefix (takeAsIterator (listIterator xs) t) (fuel + 1) (some (t.n, 0)) := rfl
    rw [h0]
    rw [List.length_take] at hf
    simpa using collectPrefix_take_at xs t (fuel + 1) t.n 0 (by simpa using hf)

theorem emitsExactly_take {α : Type} (xs : List α) (n : Nat) :
    emitsExactly (takeAsIterator (listIterator xs) ⟨listIterator xs, n⟩) (xs.take n) :=
  collectPrefix_take xs ⟨listIterator xs, n⟩ ((xs.take n).length + 1) (Nat.lt_succ_self _)

theorem dropAdvance_listIterator {α : Type} (xs : List α) (n : Nat) :
    ∀ (st : Option Nat),
      dropAdvance (listIterator xs).run n st =
        (listIterator xs).run (some (st.getD 0 + n)) := by
  induction n with
  | zero =>
    intro st
    cases st <;> simp [dropAdvance] <;> rfl
  | succ n ih =>
    intro st
    have hst : (listIterator xs).run st = (listIterator xs).run (some (st.getD 0)) := by
      cases st <;> rfl
    simp only [dropAdvance, hst, listIterator_run_some]
    cases hd : xs.drop (st.getD 0) with
    | nil =>
      have hnil : xs.drop (st.getD 0 + (n + 1)) = [] := by
        have := List.drop_eq_nil_iff.mp hd
        exact List.drop_eq_nil_iff.mpr (by omega)
      simp [hnil]
    | cons x rest =>
      simp only [ok_bind]
      rw [ih (some (st.getD 0 + 1))]
      simp only [Option.getD_some]
      have heq : st.getD 0 + 1 + n = st.getD 0 + (n + 1) := by omega
      rw [heq, listIterator_run_some]

theorem collectPrefix_drop {α : Type} (xs : List α) (d : Drop (IteratorModel α Nat))
    (fuel : Nat) (hf : (xs.drop d.n).length < fuel) :
    collectPrefix (dropAsIterator (listIterator xs) d) fuel none = .ok (xs.drop d.n) := by
  have hrun_some : ∀ s, (dropAsIterator (listIterator xs) d).run (some s) = (listIterator xs).run (some s) :=
    fun _ => rfl
  have hprefix_some : ∀ f i, (xs.drop i).length < f →
      collectPrefix (dropAsIterator (listIterator xs) d) f (some i) = .ok (xs.drop i) := by
    intro f
    induction f with
    | zero => intro i h; omega
    | succ f ih =>
      intro i h
      simp only [collectPrefix, hrun_some, listIterator_run_some]
      cases hd : xs.drop i with
      | nil => rfl
      | cons x rest =>
        have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
        have hlen : (xs.drop (i + 1)).length < f := by rw [hdrop]; simp [hd] at h; omega
        simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop]
  cases fuel with
  | zero => omega
  | succ fuel =>
    have h0 : (dropAsIterator (listIterator xs) d).run none = (listIterator xs).run (some d.n) := by
      simpa [dropAsIterator, iterateDrop] using dropAdvance_listIterator xs d.n none
    simp only [collectPrefix, h0, listIterator_run_some]
    cases hd : xs.drop d.n with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (d.n + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (d.n + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, hprefix_some fuel (d.n + 1) hlen, hdrop]

theorem emitsExactly_drop {α : Type} (xs : List α) (n : Nat) :
    emitsExactly (dropAsIterator (listIterator xs) ⟨listIterator xs, n⟩) (xs.drop n) :=
  collectPrefix_drop xs ⟨listIterator xs, n⟩ ((xs.drop n).length + 1) (Nat.lt_succ_self _)

def TakeCorrect : Prop :=
  ∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    let take := takeAsIterator base ⟨base, n⟩
    emitsExactly take (xs.take n) ∧ take.length = .ok (min n xs.length)

theorem takeCorrect : TakeCorrect := by
  intro xs n
  refine ⟨emitsExactly_take xs n, ?_⟩
  show Except.ok (min xs.length n) = Except.ok (min n xs.length)
  rw [Nat.min_comm]

def TakeTakeCorrect : Prop :=
  (∀ (xs : List Int) (a : Nat) (b : JInt64), 0 ≤ b.val →
    let base := listIterator xs
    ∃ t, takeTakeModel ⟨base, a⟩ b.val = .ok t ∧
      emitsExactly (takeAsIterator base t) (xs.take (min a b.val.toNat))) ∧
  (∀ (xs : List Int) (a : Nat) (b : JInt64), b.val < 0 →
    takeTakeModel ⟨listIterator xs, a⟩ b.val =
      .error (.argumentError "Take length must be non-negative")) ∧
  (∀ (xs : List Int) (a : Nat) (b : Int), (b < -(2 ^ 63) ∨ 2 ^ 63 ≤ b) →
    takeTakeModel ⟨listIterator xs, a⟩ b = .error (.inexactError "Int64"))

theorem takeTakeCorrect : TakeTakeCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs a b hb
    refine ⟨⟨listIterator xs, min a b.val.toNat⟩, ?_, emitsExactly_take xs (min a b.val.toNat)⟩
    simp only [takeTakeModel, jint_convert_i64_self, ok_bind, mkTake]
    have hnn : ¬ min b.val (a : Int) < 0 := by
      simp only [Int.min_def]; split <;> omega
    have hmin : (min b.val (a : Int)).toNat = min a b.val.toNat := by
      simp only [Int.min_def, Nat.min_def]; split <;> split <;> omega
    simp [hnn, hmin]
  · intro xs a b hb
    simp only [takeTakeModel, jint_convert_i64_self, ok_bind, mkTake]
    have hneg : min b.val (a : Int) < 0 := by
      simp only [Int.min_def]; split <;> omega
    simp [hneg]
  · intro xs a b hb
    simp [takeTakeModel, jint_convert_i64_out b hb]

def DropCorrect : Prop :=
  ∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    let drop := dropAsIterator base ⟨base, n⟩
    emitsExactly drop (xs.drop n) ∧ drop.length = .ok (xs.length - n)

theorem dropCorrect : DropCorrect := by
  intro xs n
  exact ⟨emitsExactly_drop xs n, rfl⟩

def TakeDropComplement : Prop :=
  ∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    collectPrefix (takeAsIterator base ⟨base, n⟩) (xs.length + 1) none = .ok (xs.take n) ∧
      collectPrefix (dropAsIterator base ⟨base, n⟩) (xs.length + 1) none = .ok (xs.drop n) ∧
      xs.take n ++ xs.drop n = xs

theorem takeDropComplement : TakeDropComplement := by
  intro xs n
  refine ⟨?_, ?_, List.take_append_drop n xs⟩
  · exact collectPrefix_take xs ⟨listIterator xs, n⟩ (xs.length + 1) (by rw [List.length_take]; omega)
  · exact collectPrefix_drop xs ⟨listIterator xs, n⟩ (xs.length + 1) (by rw [List.length_drop]; omega)

theorem takeWhileAsIterator_run_some {α : Type} (xs : List α) (p : α → Bool) (i : Nat) :
    (takeWhileAsIterator (listIterator xs) p).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => if p x then .ok (some (x, i + 1)) else .ok none := by
  simp only [takeWhileAsIterator, iterateTakeWhile, listIterator_run_some]
  cases xs.drop i <;> rfl

theorem collectPrefix_takeWhile_at {α : Type} (xs : List α) (p : α → Bool) (fuel i : Nat)
    (hf : ((xs.drop i).takeWhile p).length < fuel) :
    collectPrefix (takeWhileAsIterator (listIterator xs) p) fuel (some i) =
      .ok ((xs.drop i).takeWhile p) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, takeWhileAsIterator_run_some]
    cases hd : xs.drop i with
    | nil => simp
    | cons x rest =>
      by_cases hp : p x
      · have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
        have hlen : ((xs.drop (i + 1)).takeWhile p).length < fuel := by
          rw [hdrop]; simp [hd, hp] at hf; omega
        simp [hp, ih (i + 1) hlen, hdrop]
      · simp [hp]

theorem emitsExactly_takeWhile {α : Type} (xs : List α) (p : α → Bool) :
    emitsExactly (takeWhileAsIterator (listIterator xs) p) (xs.takeWhile p) := by
  unfold emitsExactly
  have h0 : collectPrefix (takeWhileAsIterator (listIterator xs) p) ((xs.takeWhile p).length + 1) none =
      collectPrefix (takeWhileAsIterator (listIterator xs) p) ((xs.takeWhile p).length + 1) (some 0) := rfl
  rw [h0]
  simpa using collectPrefix_takeWhile_at xs p ((xs.takeWhile p).length + 1) 0 (by simp)

theorem collectPrefix_dropWhile_some {α : Type} (xs : List α) (p : α → Bool) (fuel i : Nat)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (dropWhileAsIterator (listIterator xs) p) fuel (some i) = .ok (xs.drop i) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    have hrun : (dropWhileAsIterator (listIterator xs) p).run (some i) = (listIterator xs).run (some i) := rfl
    simp only [collectPrefix, hrun, listIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop]

theorem drop_takeWhile_length {α : Type} (ys : List α) (p : α → Bool) :
    ys.drop (ys.takeWhile p).length = ys.dropWhile p := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    by_cases hp : p y
    · simp [hp, ih]
    · simp [hp]

theorem dropWhileLoop_listIterator {α : Type} (xs : List α) (p : α → Bool) :
    ∀ (k i : Nat), (xs.drop i).length ≤ k →
      (do
        let y ← (listIterator xs).run (some i)
        dropWhileLoop (fun (pred : α → Bool) x => pred x) (fun _ s => (listIterator xs).run s)
          ⟨p, listIterator xs⟩ y) =
      (listIterator xs).run (some (i + ((xs.drop i).takeWhile p).length)) := by
  intro k
  induction k with
  | zero =>
    intro i hl
    have hnil : xs.drop i = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [listIterator_run_some, hnil, ok_bind, dropWhileLoop.eq_def]
    simp [listIterator_run_some, hnil]
  | succ k ih =>
    intro i hl
    rw [listIterator_run_some]
    cases hd : xs.drop i with
    | nil =>
      rw [ok_bind, dropWhileLoop.eq_def]
      simp [listIterator_run_some, hd]
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length ≤ k := by
        have hlt : (xs.drop (i + 1)).length < (xs.drop i).length := by
          rw [hd, hdrop, List.length_cons]; omega
        omega
      rw [ok_bind, dropWhileLoop.eq_def]
      by_cases hp : p x
      · simp only [hp, ↓reduceIte, List.takeWhile_cons, List.length_cons]
        have hstep := ih (i + 1) hlen
        rw [hdrop] at hstep
        have heq : i + 1 + (rest.takeWhile p).length = i + ((rest.takeWhile p).length + 1) := by omega
        rw [heq] at hstep
        rw [← hstep]
        cases (listIterator xs).run (some (i + 1)) <;> rfl
      · simp [hp, listIterator_run_some, hd]

theorem emitsExactly_dropWhile {α : Type} (xs : List α) (p : α → Bool) :
    emitsExactly (dropWhileAsIterator (listIterator xs) p) (xs.dropWhile p) := by
  unfold emitsExactly
  have hrun0 : (dropWhileAsIterator (listIterator xs) p).run none =
      (listIterator xs).run (some (xs.takeWhile p).length) := by
    have h := dropWhileLoop_listIterator xs p xs.length 0 (by simp)
    simpa [dropWhileAsIterator, iterateDropWhileStart, listIterator_run_none] using h
  have heq : collectPrefix (dropWhileAsIterator (listIterator xs) p) ((xs.dropWhile p).length + 1) none =
      collectPrefix (dropWhileAsIterator (listIterator xs) p) ((xs.dropWhile p).length + 1)
        (some (xs.takeWhile p).length) := by
    simp only [collectPrefix, hrun0]
    rfl
  rw [heq]
  have h := collectPrefix_dropWhile_some xs p ((xs.dropWhile p).length + 1) (xs.takeWhile p).length
    (by rw [drop_takeWhile_length]; omega)
  rwa [drop_takeWhile_length] at h

def TakeWhileDropWhile : Prop :=
  ∀ (p : Int → Bool) (xs : List Int),
    emitsExactly (takeWhileAsIterator (listIterator xs) p) (xs.takeWhile p) ∧
      emitsExactly (dropWhileAsIterator (listIterator xs) p) (xs.dropWhile p) ∧
      xs.takeWhile p ++ xs.dropWhile p = xs

theorem takeWhileDropWhile : TakeWhileDropWhile := by
  intro p xs
  exact ⟨emitsExactly_takeWhile xs p, emitsExactly_dropWhile xs p, List.takeWhile_append_dropWhile⟩

theorem enumerateFrom_length {α : Type} (k : JInt64) (xs : List α) :
    (enumerateFrom k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp [enumerateFrom, ih]

theorem enumerateSpec_length {α : Type} (xs : List α) :
    (enumerateSpec xs).length = xs.length :=
  enumerateFrom_length (JInt.lit .i64 1) xs

theorem enumerateAsIterator_run_some {α : Type} (xs : List α) (k : JInt64) (i : Nat) :
    (enumerateAsIterator (listIterator xs)).run (some (k, i)) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some ((k, x), (k + JInt.lit .i64 1, i + 1))) := by
  simp only [enumerateAsIterator, iterateEnumerate, listIterator_run_some]
  cases xs.drop i <;> rfl

theorem collectPrefix_enumerate_at {α : Type} (xs : List α) (fuel i : Nat) (k : JInt64)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (enumerateAsIterator (listIterator xs)) fuel (some (k, i)) =
      .ok (enumerateFrom k (xs.drop i)) := by
  induction fuel generalizing i k with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, enumerateAsIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) (k + JInt.lit .i64 1) hlen, hdrop, enumerateFrom]

def EnumerateCorrect : Prop :=
  ∀ (xs : List Int),
    let itr := enumerateAsIterator (listIterator xs)
    emitsExactly itr (enumerateSpec xs) ∧ itr.length = .ok xs.length

theorem enumerateCorrect : EnumerateCorrect := by
  intro xs
  refine ⟨?_, rfl⟩
  unfold emitsExactly
  rw [enumerateSpec_length]
  have h0 : collectPrefix (enumerateAsIterator (listIterator xs)) (xs.length + 1) none =
      collectPrefix (enumerateAsIterator (listIterator xs)) (xs.length + 1) (some (JInt.lit .i64 1, 0)) := rfl
  rw [h0]
  simpa [enumerateSpec] using collectPrefix_enumerate_at xs (xs.length + 1) 0 (JInt.lit .i64 1) (by simp)

theorem zipListModel_run_some {α : Type} (xs ys : List α) (i j : Nat) :
    (zipListModel xs ys).run (some [some i, some j]) =
      match xs.drop i, ys.drop j with
      | x :: _, y :: _ => .ok (some ([x, y], [some (i + 1), some (j + 1)]))
      | _, _ => .ok none := by
  simp only [zipListModel, zipAsIterator, iterateZipState, zipModel, List.zip_cons_cons,
    List.zip_nil_left, zipIterateInOrder, listIterator_run_some]
  cases xs.drop i <;> cases ys.drop j <;> rfl

theorem collectPrefix_zip_at {α : Type} (xs ys : List α) (fuel i j : Nat)
    (hf : (List.zipWith (fun x y => [x, y]) (xs.drop i) (ys.drop j)).length < fuel) :
    collectPrefix (zipListModel xs ys) fuel (some [some i, some j]) =
      .ok (List.zipWith (fun x y => [x, y]) (xs.drop i) (ys.drop j)) := by
  induction fuel generalizing i j with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, zipListModel_run_some]
    cases hx : xs.drop i with
    | nil => simp [List.zipWith]
    | cons x xrest =>
      cases hy : ys.drop j with
      | nil => simp [List.zipWith]
      | cons y yrest =>
        have hdx : xs.drop (i + 1) = xrest := by rw [← List.drop_drop, hx]; rfl
        have hdy : ys.drop (j + 1) = yrest := by rw [← List.drop_drop, hy]; rfl
        have hlen : (List.zipWith (fun x y => [x, y]) (xs.drop (i + 1)) (ys.drop (j + 1))).length < fuel := by
          rw [hdx, hdy]; rw [hx, hy, List.zipWith_cons_cons, List.length_cons] at hf; omega
        simp only [ok_bind, pure_jl, ih (i + 1) (j + 1) hlen, hdx, hdy, List.zipWith_cons_cons]

def ZipCorrect : Prop :=
  ∀ (xs ys : List Int),
    let itr := zipListModel xs ys
    emitsExactly itr (List.zipWith (fun x y => [x, y]) xs ys) ∧
      itr.length = .ok (min xs.length ys.length)

theorem zipCorrect : ZipCorrect := by
  intro xs ys
  refine ⟨?_, ?_⟩
  · unfold emitsExactly
    have h0 : collectPrefix (zipListModel xs ys) ((List.zipWith (fun x y => [x, y]) xs ys).length + 1) none =
        collectPrefix (zipListModel xs ys) ((List.zipWith (fun x y => [x, y]) xs ys).length + 1)
          (some [some 0, some 0]) := rfl
    rw [h0]
    simpa using collectPrefix_zip_at xs ys ((List.zipWith (fun x y => [x, y]) xs ys).length + 1) 0 0 (by simp)
  · show Except.ok (min ys.length xs.length) = Except.ok (min xs.length ys.length)
    rw [Nat.min_comm]

def ZipReverse : Prop :=
  (∀ (xs ys : List Int),
    xs.length = ys.length →
      reverseZipModel (fun is => zipLengthsFiniteEqual is)
        (fun _ => [listIterator xs.reverse, listIterator ys.reverse])
        (zipModel [listIterator xs, listIterator ys]) =
          .ok (zipModel [listIterator xs.reverse, listIterator ys.reverse]) ∧
      emitsExactly (zipListModel xs.reverse ys.reverse)
        (List.zipWith (fun x y => [x, y]) xs ys).reverse) ∧
  (∀ (xs ys : List Int),
    xs.length ≠ ys.length →
      ∃ msg, reverseZipModel (fun is => zipLengthsFiniteEqual is)
        (fun _ => [listIterator xs.reverse, listIterator ys.reverse])
        (zipModel [listIterator xs, listIterator ys]) =
          .error (.argumentError msg))

theorem zipWith_reverse_eq {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) :
    List.zipWith f xs.reverse ys.reverse = (List.zipWith f xs ys).reverse := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simp at hlen; omega
      have hrev_len : xs.reverse.length = ys.reverse.length := by simp [hlen']
      simp [List.reverse_cons, List.zipWith_append hrev_len, ih ys hlen']

theorem zipReverse : ZipReverse := by
  refine ⟨?_, ?_⟩
  · intro xs ys hlen
    refine ⟨?_, ?_⟩
    · simp [reverseZipModel, zipLengthsFiniteEqual, listIterator, hlen, zipModel]
    · rw [← zipWith_reverse_eq (fun x y => [x, y]) xs ys hlen]
      exact (zipCorrect xs.reverse ys.reverse).1
  · intro xs ys hne
    have hne' : ¬ (ys.length = xs.length) := fun h => hne h.symm
    refine ⟨"Cannot reverse zipped iterators of unknown, infinite, or unequal lengths", ?_⟩
    simp [reverseZipModel, zipLengthsFiniteEqual, listIterator, zipModel, hne']

def prodState {α : Type} (xs ys : List α) (curX curY : α) (i j : Nat) :
    List (IteratorModel α Nat × (α × Nat)) :=
  [(listIterator xs, (curX, i)), (listIterator ys, (curY, j))]

theorem productListModel_isdone_cons {α : Type} (a0 : α) (xtail ys : List α)
    (curX curY : α) (i j : Nat) :
    isdoneProductState (fun itr state => itr.isdone state)
      (productModel [listIterator (a0 :: xtail), listIterator ys])
      (prodState (a0 :: xtail) ys curX curY i j) = .ok (some false) := by
  simp only [isdoneProductState, productModel, prodState, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left, pisdone, listIterator, Option.getD_some, Option.getD_none]
  by_cases hi : (a0 :: xtail).length ≤ i <;> simp

theorem productListModel_run_some {α : Type} (a0 : α) (xtail ys : List α)
    (curX curY : α) (i j : Nat) :
    (productListModel (a0 :: xtail) ys).run (some (prodState (a0 :: xtail) ys curX curY i j)) =
      match (a0 :: xtail).drop i with
      | x :: _ => .ok (some ([x, curY], prodState (a0 :: xtail) ys x curY (i + 1) j))
      | [] =>
          match ys.drop j with
          | [] => .ok none
          | y :: _ => .ok (some ([a0, y], prodState (a0 :: xtail) ys a0 y 1 (j + 1))) := by
  simp only [productListModel, productAsIterator, iterateProductState,
    productListModel_isdone_cons, ok_bind]
  change piterateNext (fun (itr : IteratorModel α Nat) state => itr.isdone state)
      (fun (itr : IteratorModel α Nat) state => itr.run state)
      (prodState (a0 :: xtail) ys curX curY i j) = _
  simp only [prodState, piterateNext, listIterator_run_some]
  cases hx : (a0 :: xtail).drop i with
  | cons x xrest =>
    rfl
  | nil =>
    have hisdone0 : (listIterator (a0 :: xtail)).isdone none = .ok (some false) := rfl
    simp only [ok_bind, hisdone0]
    cases hy : ys.drop j with
    | nil =>
      by_cases hys : (ys.length ≤ 0) <;> simp [listIterator, hys, piterateNextEmpty]
    | cons y yrest =>
      rfl

theorem collectPrefix_product_at {α : Type} (a0 : α) (xtail ys : List α)
    (fuel i j : Nat) (curX curY : α)
    (hf : ((a0 :: xtail).drop i).length + (a0 :: xtail).length * (ys.drop j).length < fuel) :
    collectPrefix (productListModel (a0 :: xtail) ys) fuel
      (some (prodState (a0 :: xtail) ys curX curY i j)) =
    .ok (((a0 :: xtail).drop i).map (fun x => [x, curY]) ++
      (ys.drop j).flatMap (fun y => (a0 :: xtail).map (fun x => [x, y]))) := by
  induction fuel generalizing i j curX curY with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, productListModel_run_some]
    cases hx : (a0 :: xtail).drop i with
    | cons x xrest =>
      have hdx : (a0 :: xtail).drop (i + 1) = xrest := by rw [← List.drop_drop, hx]; rfl
      have hf' : ((a0 :: xtail).drop (i + 1)).length + (a0 :: xtail).length * (ys.drop j).length < fuel := by
        rw [hdx]; rw [hx, List.length_cons] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) j x curY hf', hdx, List.map_cons, List.cons_append]
    | nil =>
      cases hy : ys.drop j with
      | nil => simp
      | cons y yrest =>
        have hdy : ys.drop (j + 1) = yrest := by rw [← List.drop_drop, hy]; rfl
        have hf' : ((a0 :: xtail).drop 1).length + (a0 :: xtail).length * (ys.drop (j + 1)).length < fuel := by
          rw [hdy]
          simp only [hx, hy, List.length_nil, Nat.zero_add, List.length_cons, Nat.mul_add, Nat.mul_one] at hf
          simp only [List.drop_succ_cons, List.drop_zero, List.length_cons]
          omega
        simp only [ok_bind, pure_jl, ih 1 (j + 1) a0 y hf', hdy, List.drop_succ_cons, List.drop_zero,
          List.map_nil, List.nil_append, List.flatMap_cons, List.map_cons, List.cons_append]

def ProductCorrect : Prop :=
  ∀ (xs ys : List Int),
    emitsExactly (productListModel xs ys)
      (ys.flatMap fun y => xs.map fun x => [x, y]) ∧
    sourceMethod1169 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize)
      (productModel [listIterator xs, listIterator ys]) = .ok [xs.length, ys.length]

theorem flatMap_map_length {α β : Type} (xs ys : List α) (f : α → α → β) :
    (ys.flatMap fun y => xs.map fun x => f x y).length = xs.length * ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp [List.flatMap_cons, ih, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem productCorrect : ProductCorrect := by
  intro xs ys
  refine ⟨?_, rfl⟩
  unfold emitsExactly
  cases xs with
  | nil =>
    have hnil : (ys.flatMap fun y => ([] : List Int).map fun x => [x, y]) = [] := by
      induction ys with
      | nil => rfl
      | cons y ys ih => exact ih
    rw [hnil]
    rfl
  | cons a0 xtail =>
    cases ys with
    | nil => rfl
    | cons b0 ytail =>
      rw [flatMap_map_length]
      have hrun0 : (productListModel (a0 :: xtail) (b0 :: ytail)).run none =
          .ok (some ([a0, b0], prodState (a0 :: xtail) (b0 :: ytail) a0 b0 1 1)) := rfl
      have hf : ((a0 :: xtail).drop 1).length + (a0 :: xtail).length * ((b0 :: ytail).drop 1).length <
          (a0 :: xtail).length * (b0 :: ytail).length := by
        simp [List.drop_succ_cons, List.drop_zero, Nat.mul_add, Nat.mul_one]
        omega
      have h := collectPrefix_product_at a0 xtail (b0 :: ytail)
        ((a0 :: xtail).length * (b0 :: ytail).length) 1 1 a0 b0 hf
      simp only [List.drop_succ_cons, List.drop_zero] at h
      simp only [collectPrefix, hrun0, ok_bind, pure_jl, h, List.flatMap_cons, List.map_cons, List.cons_append]

theorem flatten_run_some_nil {α O : Type}
    (outer : IteratorModel (IteratorModel α Nat) O)
    (so : O) (cur : List α) (si : Nat) (hnil : cur.drop si = []) :
    (flattenAsIterator (flattenModel outer)).run (some (so, listIterator cur, si)) =
      flattenAdvanceOuter outer so := by
  unfold flattenAsIterator iterateFlattenState
  simp only [flattenModel, listIterator_run_some, hnil, ok_bind]

theorem flatten_run_some_cons {α O : Type}
    (outer : IteratorModel (IteratorModel α Nat) O)
    (so : O) (cur : List α) (si : Nat) (x : α) (rest : List α) (hd : cur.drop si = x :: rest) :
    (flattenAsIterator (flattenModel outer)).run (some (so, listIterator cur, si)) =
      .ok (some (x, (so, listIterator cur, si + 1))) := by
  unfold flattenAsIterator iterateFlattenState
  simp only [flattenModel, listIterator_run_some, hd, ok_bind, pure_jl]

theorem collectPrefix_flatten_inner {α O : Type}
    (outer : IteratorModel (IteratorModel α Nat) O)
    (so : O) (tailFlat : List α)
    (h_adv : ∀ f, tailFlat.length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel outer)) f
        (flattenAdvanceOuter outer so) =
      .ok tailFlat)
    (cur : List α) :
    ∀ (k si f : Nat), (cur.drop si).length ≤ k →
      (cur.drop si).length + tailFlat.length < f →
      collectPrefix (flattenAsIterator (flattenModel outer)) f (some (so, listIterator cur, si)) =
        .ok (cur.drop si ++ tailFlat) := by
  intro k
  induction k with
  | zero =>
    intro si f hk hf
    cases f with
    | zero => omega
    | succ f =>
      have hnil : cur.drop si = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [collectPrefix_succ, flatten_run_some_nil outer so cur si hnil, hnil, List.nil_append]
      exact h_adv f (by rw [hnil, List.length_nil, Nat.zero_add] at hf; omega)
  | succ k ih =>
    intro si f hk hf
    cases f with
    | zero => omega
    | succ f =>
      cases hd : cur.drop si with
      | nil =>
        rw [collectPrefix_succ, flatten_run_some_nil outer so cur si hd, List.nil_append]
        exact h_adv f (by rw [hd, List.length_nil, Nat.zero_add] at hf; omega)
      | cons x rest =>
        have hdrop : cur.drop (si + 1) = rest := by rw [← List.drop_drop, hd]; rfl
        have hk' : (cur.drop (si + 1)).length ≤ k := by
          have hlt : (cur.drop (si + 1)).length < (cur.drop si).length := by
            rw [hd, hdrop, List.length_cons]; omega
          omega
        have hf' : (cur.drop (si + 1)).length + tailFlat.length < f := by
          rw [hdrop]; rw [hd, List.length_cons] at hf; omega
        rw [collectPrefix_succ, flatten_run_some_cons outer so cur si x rest hd]
        simp only [collectAfterStep_some, ih (si + 1) f hk' hf', ok_bind, pure_jl, hdrop, List.cons_append]

theorem listIterator_map_run_some {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    (listIterator (xs.map f)).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (f x, i + 1)) := by
  rw [listIterator_run_some, ← List.map_drop]
  cases xs.drop i <;> rfl

theorem flattenAdvanceOuter_list {α : Type} (rows : List (List α)) :
    ∀ (k i f : Nat), (rows.drop i).length ≤ k →
      ((rows.drop i).flatten).length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel (listIterator (rows.map listIterator)))) f
        (flattenAdvanceOuter (listIterator (rows.map listIterator)) i) =
      .ok ((rows.drop i).flatten) := by
  intro k
  induction k with
  | zero =>
    intro i f hk _
    have hnil : rows.drop i = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [flattenAdvanceOuter.eq_def]
    simp [listIterator_map_run_some, hnil]
  | succ k ih =>
    intro i f hk hf
    cases hd : rows.drop i with
    | nil =>
      rw [flattenAdvanceOuter.eq_def]
      simp [listIterator_map_run_some, hd]
    | cons r restRows =>
      have hdrop : rows.drop (i + 1) = restRows := by rw [← List.drop_drop, hd]; rfl
      have hk' : (rows.drop (i + 1)).length ≤ k := by
        have hlt : (rows.drop (i + 1)).length < (rows.drop i).length := by
          rw [hd, hdrop, List.length_cons]; omega
        omega
      cases r with
      | nil =>
        have hf' : ((rows.drop (i + 1)).flatten).length ≤ f := by
          rw [hd, List.flatten_cons, List.nil_append, ← hdrop] at hf
          exact hf
        have hstep : flattenAdvanceOuter (listIterator (rows.map listIterator)) i =
            flattenAdvanceOuter (listIterator (rows.map listIterator)) (i + 1) := by
          conv => lhs; rw [flattenAdvanceOuter.eq_def]
          rw [listIterator_map_run_some, hd]
          rfl
        rw [hstep, List.flatten_cons, List.nil_append, ← hdrop]
        exact ih (i + 1) f hk' hf'
      | cons x rx =>
        rw [hd, List.flatten_cons, List.cons_append, List.length_cons, List.length_append, ← hdrop] at hf
        cases f with
        | zero => omega
        | succ f =>
          have hstep : flattenAdvanceOuter (listIterator (rows.map listIterator)) i =
              .ok (some (x, (i + 1, listIterator (x :: rx), 1))) := by
            rw [flattenAdvanceOuter.eq_def, listIterator_map_run_some, hd]
            rfl
          rw [hstep, collectAfterStep_some, List.flatten_cons, List.cons_append, ← hdrop]
          have h_adv : ∀ f', ((rows.drop (i + 1)).flatten).length ≤ f' →
              collectAfterStep (flattenAsIterator (flattenModel (listIterator (rows.map listIterator)))) f'
                (flattenAdvanceOuter (listIterator (rows.map listIterator)) (i + 1)) =
              .ok ((rows.drop (i + 1)).flatten) :=
            fun f' hf' => ih (i + 1) f' hk' hf'
          have hinner := collectPrefix_flatten_inner (listIterator (rows.map listIterator)) (i + 1)
            ((rows.drop (i + 1)).flatten) h_adv (x :: rx) rx.length 1 (f + 1)
            (by simp) (by simp only [List.drop_succ_cons, List.drop_zero]; omega)
          rw [List.drop_succ_cons, List.drop_zero] at hinner
          simp only [hinner, ok_bind, pure_jl]

def FlattenCorrect : Prop :=
  ∀ (rows : List (List Int)),
    emitsExactly (flattenListModel rows) rows.flatten

theorem flattenCorrect : FlattenCorrect := by
  intro rows
  unfold emitsExactly flattenListModel
  have hrun0 : (flattenAsIterator (flattenModel (listIterator (rows.map listIterator)))).run none =
      flattenAdvanceOuter (listIterator (rows.map listIterator)) 0 := by
    dsimp [flattenAsIterator, iterateFlattenStart, flattenModel]
    rw [flattenAdvanceOuter.eq_def]
    rw [listIterator_run_none, listIterator_map_run_some]
    cases rows with
    | nil => rfl
    | cons r rest =>
      cases r <;> rfl
  rw [collectPrefix_succ, hrun0]
  have h := flattenAdvanceOuter_list rows rows.length 0 rows.flatten.length
    (by simp) (Nat.le_refl _)
  rwa [List.drop_zero] at h

theorem flatten_uniform_length {α : Type} (k : Nat) (rows : List (List α))
    (h : ∀ r ∈ rows, r.length = k) :
    rows.flatten.length = k * rows.length := by
  induction rows with
  | nil => simp
  | cons r rest ih =>
    have hr := h r (List.mem_cons_self ..)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [List.flatten_cons, hr, hrest, Nat.mul_add, Nat.mul_one, Nat.add_comm]

def FlattenTupleLength : Prop :=
  ∀ (k : Nat) (rows : List (List Int)),
    (∀ r ∈ rows, r.length = k) →
      let outer := flattenModel (listIterator rows)
      if k * rows.length < 2 ^ 63 then
        flattenLengthTuple checkedMulNatI64 (fun it => it.length) outer k =
          .ok rows.flatten.length ∧
        sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64 outer =
          .ok rows.flatten.length
      else
        flattenLengthTuple checkedMulNatI64 (fun it => it.length) outer k =
          .error (.overflowError "checked_mul") ∧
        sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64 outer =
          .error (.overflowError "checked_mul")

theorem flattenTupleLength : FlattenTupleLength := by
  intro k rows h
  dsimp only
  rw [flatten_uniform_length k rows h]
  by_cases hlt : k * rows.length < 2 ^ 63
  · simp [hlt, flattenLengthTuple, sourceMethod1332, checkedMulNatI64, flattenModel]
  · simp [hlt, flattenLengthTuple, sourceMethod1332, checkedMulNatI64, flattenModel]

theorem flattenAdvanceOuter_cycle {α : Type} (xs : List α) :
    ∀ (m f : Nat),
      ((List.replicate m xs).flatten).length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel (cycleOuter xs n))) f
        (flattenAdvanceOuter (cycleOuter xs n) (m, ())) =
      .ok ((List.replicate m xs).flatten) := by
  intro m
  induction m with
  | zero =>
    intro f _
    rw [flattenAdvanceOuter.eq_def]
    simp [cycleOuter, takeAsIterator, iterateTake]
  | succ m ih =>
    intro f hf
    cases xs with
    | nil =>
      have hstep : flattenAdvanceOuter (cycleOuter ([] : List α) n) (m + 1, ()) =
          flattenAdvanceOuter (cycleOuter ([] : List α) n) (m, ()) := by
        conv => lhs; rw [flattenAdvanceOuter.eq_def]
        rfl
      have hf' : ((List.replicate m ([] : List α)).flatten).length ≤ f := by
        rw [List.replicate_succ, List.flatten_cons, List.nil_append] at hf
        exact hf
      rw [hstep, List.replicate_succ, List.flatten_cons, List.nil_append]
      exact ih f hf'
    | cons x rx =>
      rw [List.replicate_succ, List.flatten_cons, List.cons_append, List.length_cons, List.length_append] at hf
      cases f with
      | zero => omega
      | succ f =>
        have hstep : flattenAdvanceOuter (cycleOuter (x :: rx) n) (m + 1, ()) =
            .ok (some (x, ((m, ()), listIterator (x :: rx), 1))) := by
          rw [flattenAdvanceOuter.eq_def]
          rfl
        rw [hstep, collectAfterStep_some, List.replicate_succ, List.flatten_cons, List.cons_append]
        have h_adv : ∀ f', ((List.replicate m (x :: rx)).flatten).length ≤ f' →
            collectAfterStep (flattenAsIterator (flattenModel (cycleOuter (x :: rx) n))) f'
              (flattenAdvanceOuter (cycleOuter (x :: rx) n) (m, ())) =
            .ok ((List.replicate m (x :: rx)).flatten) :=
          fun f' hf' => ih f' hf'
        have hinner := collectPrefix_flatten_inner (cycleOuter (x :: rx) n) (m, ())
          ((List.replicate m (x :: rx)).flatten) h_adv (x :: rx) rx.length 1 (f + 1)
          (by simp) (by simp only [List.drop_succ_cons, List.drop_zero]; omega)
        rw [List.drop_succ_cons, List.drop_zero] at hinner
        simp only [hinner, ok_bind, pure_jl]

theorem emitsExactly_finiteCycle {α : Type} (xs : List α) (n : Nat) :
    emitsExactly (finiteCycleListModel xs n) (List.replicate n xs).flatten := by
  unfold emitsExactly finiteCycleListModel
  have hrun0 : (flattenAsIterator (flattenModel (cycleOuter xs n))).run none =
      flattenAdvanceOuter (cycleOuter xs n) (n, ()) := by
    dsimp [flattenAsIterator, iterateFlattenStart, flattenModel]
    rw [flattenAdvanceOuter.eq_def]
    cases n with
    | zero => rfl
    | succ m =>
      cases xs <;> rfl
  rw [collectPrefix_succ, hrun0]
  exact flattenAdvanceOuter_cycle xs n ((List.replicate n xs).flatten).length (Nat.le_refl _)

def CycleNCorrect : Prop :=
  (∀ (xs : List Int) (n : JInt64), 0 ≤ n.val →
    ∃ c, cycleNModel (listIterator xs) n.val = .ok c ∧
      emitsExactly (finiteCycleListModel xs n.val.toNat) (List.replicate n.val.toNat xs).flatten) ∧
  (∀ (xs : List Int) (n : JInt64), n.val < 0 →
    cycleNModel (listIterator xs) n.val =
      .error (.argumentError "Take length must be non-negative")) ∧
  (∀ (xs : List Int) (n : Int), (n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) →
    cycleNModel (listIterator xs) n = .error (.inexactError "Int64"))

theorem cycleNCorrect : CycleNCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs n hn
    refine ⟨⟨⟨repeatedModel (listIterator xs), n.val.toNat⟩⟩, ?_, emitsExactly_finiteCycle xs n.val.toNat⟩
    simp only [cycleNModel, repeatedNModel, takeModel, jint_convert_i64_self, ok_bind, mkTake]
    have hnn : ¬ n.val < 0 := by omega
    simp [hnn, flattenModel]
  · intro xs n hn
    simp [cycleNModel, repeatedNModel, takeModel, jint_convert_i64_self, mkTake, hn]
  · intro xs n hn
    simp [cycleNModel, repeatedNModel, takeModel, jint_convert_i64_out n hn]

theorem repeatedListModel_run_some {α : Type} (x : α) (n m : Nat) :
    (repeatedListModel x n).run (some (m, ())) =
      if m = 0 then .ok none else .ok (some (x, (m - 1, ()))) := by
  simp only [repeatedListModel, takeAsIterator, iterateTake, Nat.le_zero_eq,
    repeatedAsIterator, iterateRepeated, repeatedModel]
  by_cases hm : m = 0 <;> simp [hm]

theorem collectPrefix_repeated_at {α : Type} (x : α) (n fuel m : Nat) (hf : m < fuel) :
    collectPrefix (repeatedListModel x n) fuel (some (m, ())) =
      .ok (List.replicate m x) := by
  induction fuel generalizing m with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, repeatedListModel_run_some]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ok_bind, pure_jl,
        ih m (by omega), List.replicate_succ]

theorem emitsExactly_repeated {α : Type} (x : α) (n : Nat) :
    emitsExactly (repeatedListModel x n) (List.replicate n x) := by
  unfold emitsExactly
  rw [List.length_replicate]
  have h0 : collectPrefix (repeatedListModel x n) (n + 1) none =
      collectPrefix (repeatedListModel x n) (n + 1) (some (n, ())) := rfl
  rw [h0]
  exact collectPrefix_repeated_at x n (n + 1) n (Nat.lt_succ_self _)

def RepeatedNCorrect : Prop :=
  (∀ (x : Int) (n : JInt64), 0 ≤ n.val →
    ∃ repeated, repeatedNModel x n.val = .ok repeated ∧
      emitsExactly (repeatedListModel x n.val.toNat) (List.replicate n.val.toNat x) ∧
      (repeatedListModel x n.val.toNat).length = .ok n.val.toNat) ∧
  (∀ (x : Int) (n : JInt64), n.val < 0 →
    repeatedNModel x n.val =
      .error (.argumentError "Take length must be non-negative")) ∧
  (∀ (x : Int) (n : Int), (n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) →
    repeatedNModel x n = .error (.inexactError "Int64"))

theorem repeatedNCorrect : RepeatedNCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro x n hn
    refine ⟨⟨repeatedModel x, n.val.toNat⟩, ?_, emitsExactly_repeated x n.val.toNat, rfl⟩
    simp only [repeatedNModel, takeModel, jint_convert_i64_self, ok_bind, mkTake]
    have hnn : ¬ n.val < 0 := by omega
    simp [hnn]
  · intro x n hn
    simp [repeatedNModel, takeModel, jint_convert_i64_self, mkTake, hn]
  · intro x n hn
    simp [repeatedNModel, takeModel, jint_convert_i64_out n hn]

theorem partCount (L k i : Nat) (hk : 0 < k) :
    i < (L + k - 1) / k ↔ i * k < L := by
  have h := Nat.le_div_iff_mul_le hk (x := i + 1) (y := L + k - 1)
  rw [Nat.add_mul] at h
  simp only [Nat.one_mul] at h
  omega

theorem partTake {α : Type} (xs : List α) (a k : Nat) :
    (xs.drop a).take (min (a + k) xs.length - a) = (xs.drop a).take k := by
  by_cases h : a + k ≤ xs.length
  · rw [Nat.min_eq_left h]
    congr 1; omega
  · rw [Nat.min_eq_right (by omega)]
    have hl : (xs.drop a).length = xs.length - a := List.length_drop
    rw [← hl, List.take_length]
    symm
    exact List.take_of_length_le (by rw [hl]; omega)

theorem partitionVector_run_at {α : Type} (xs : List α) (n i : Nat) (hn : 0 < n) :
    (partitionVectorAsIterator ⟨xs, n⟩).run (some (min (i * n) xs.length)) =
      if i < (xs.length + n - 1) / n then
        .ok (some ((xs.drop (i * n)).take n, min ((i + 1) * n) xs.length))
      else .ok none := by
  have hiff := partCount xs.length n i hn
  by_cases hi : i < (xs.length + n - 1) / n
  · have hlt : i * n < xs.length := hiff.mp hi
    have hmin : min (i * n) xs.length = i * n := Nat.min_eq_left (by omega)
    have hnotge : ¬ (i * n ≥ xs.length) := by omega
    have hmul : i * n + n = (i + 1) * n := by simp [Nat.add_mul]
    simp only [partitionVectorAsIterator, iteratePartitionVector, Option.getD_some,
      hmin, ge_iff_le, hnotge, ↓reduceIte, partTake, hmul, hi, pure_jl]
  · have hge : xs.length ≤ i * n := by omega
    have hmin : min (i * n) xs.length = xs.length := Nat.min_eq_right hge
    simp [partitionVectorAsIterator, iteratePartitionVector, hmin, hi]

theorem collectPrefix_partitionVector_at {α : Type} (xs : List α) (n fuel i : Nat) (hn : 0 < n)
    (hf : (xs.length + n - 1) / n - i < fuel) :
    collectPrefix (partitionVectorAsIterator ⟨xs, n⟩) fuel (some (min (i * n) xs.length)) =
      .ok ((List.range ((xs.length + n - 1) / n - i)).map fun j => (xs.drop ((i + j) * n)).take n) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, partitionVector_run_at xs n i hn]
    by_cases hi : i < (xs.length + n - 1) / n
    · have hlen : (xs.length + n - 1) / n - (i + 1) < fuel := by omega
      have hsub : (xs.length + n - 1) / n - i = ((xs.length + n - 1) / n - (i + 1)) + 1 := by omega
      simp only [hi, ↓reduceIte, ok_bind, pure_jl, ih (i + 1) hlen, hsub,
        List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have heq : i + 1 + j = i + (j + 1) := by omega
      rw [heq]
    · have hz : (xs.length + n - 1) / n - i = 0 := by omega
      simp [hi, hz]

theorem emitsExactly_partitionVector {α : Type} (xs : List α) (n : Nat) (hn : 0 < n) :
    emitsExactly (partitionVectorAsIterator ⟨xs, n⟩) (chunksSpec n xs) := by
  unfold emitsExactly
  have hne : n ≠ 0 := by omega
  have hlen : (chunksSpec n xs).length = (xs.length + n - 1) / n := by
    simp [chunksSpec, hne]
  rw [hlen]
  have h0 : collectPrefix (partitionVectorAsIterator ⟨xs, n⟩) ((xs.length + n - 1) / n + 1) none =
      collectPrefix (partitionVectorAsIterator ⟨xs, n⟩) ((xs.length + n - 1) / n + 1)
        (some (min (0 * n) xs.length)) := by
    simp [Nat.zero_mul]
    rfl
  rw [h0]
  have h := collectPrefix_partitionVector_at xs n ((xs.length + n - 1) / n + 1) 0 hn (by omega)
  simpa [chunksSpec, hne] using h

def PartitionVectorCorrect : Prop :=
  ∀ (xs : List Int) (n : Nat), 0 < n →
    let itr := partitionVectorAsIterator ⟨xs, n⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n)

theorem partitionVectorCorrect : PartitionVectorCorrect := by
  intro xs n hn
  refine ⟨emitsExactly_partitionVector xs n hn, ?_⟩
  simp [partitionVectorAsIterator, partitionLength]

def statefulCurAt {α : Type} (xs : List α) (i : Nat) : Option (α × Nat) :=
  match xs.drop i with
  | [] => none
  | x :: _ => some (x, i + 1)

theorem collectStateful_at {α : Type} (xs : List α) :
    ∀ (fuel i : Nat),
      (xs.drop i).length < fuel →
      collectStateful (fun _ st => (listIterator xs).run st) fuel
        ⟨listIterator xs, statefulCurAt xs i⟩ =
        .ok (xs.drop i, ⟨listIterator xs, none⟩) := by
  intro fuel
  induction fuel with
  | zero => intro i hf; omega
  | succ fuel ih =>
    intro i hf
    unfold statefulCurAt
    cases hd : xs.drop i with
    | nil =>
      rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      have hstep : iterateStateful (fun _ st => (listIterator xs).run st)
          ⟨listIterator xs, some (x, i + 1)⟩ =
          .ok (some (x, ()), ⟨listIterator xs, statefulCurAt xs (i + 1)⟩) := by
        unfold statefulCurAt
        simp only [iterateStateful, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          popfirstStateful, listIterator_run_some]
        cases xs.drop (i + 1) <;> rfl
      simp only [collectStateful, hstep, ok_bind_iter, ih (i + 1) hlen, pure_iter]
      rw [hdrop]

theorem collectStateful_full {α : Type} (xs : List α) :
    (do
      let s0 ← (sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) : IteratorResult _)
      collectStateful (fun _ st => (listIterator xs).run st) (xs.length + 1) s0) =
    .ok (xs, ⟨listIterator xs, none⟩) := by
  have hs0 : sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) =
      .ok ⟨listIterator xs, statefulCurAt xs 0⟩ := by
    unfold statefulCurAt
    simp only [sourceMethod1569, listIterator_run_none, listIterator_run_some]
    cases xs.drop 0 <;> rfl
  rw [hs0, liftM_jl_ok, ok_bind_iter]
  simpa using collectStateful_at xs (xs.length + 1) 0 (by simp)

def StatefulConsistent : Prop :=
  (∀ (xs : List Int) (pos : Nat) (sentinel : Int),
    let s : Stateful (IteratorModel Int Nat) (Int × Nat) := ⟨listIterator xs, statefulCurAt xs pos⟩
    isdoneStateful s = (xs.drop pos).isEmpty ∧
    peekStateful s sentinel = ((xs.drop pos).head?).getD sentinel ∧
    collectStateful (fun _ st => (listIterator xs).run st) ((xs.drop pos).length + 1) s =
      .ok (xs.drop pos, ⟨listIterator xs, none⟩) ∧
    (xs.drop pos = [] →
      popfirstStateful (fun _ st => (listIterator xs).run st) s =
        .error .eofError) ∧
    (∀ x rest, xs.drop pos = x :: rest →
      ∃ sNext, popfirstStateful (fun _ st => (listIterator xs).run st) s = .ok (x, sNext) ∧
        iterateStateful (fun _ st => (listIterator xs).run st) s = .ok (some (x, ()), sNext) ∧
        collectStateful (fun _ st => (listIterator xs).run st) (rest.length + 1) sNext =
          .ok (rest, ⟨listIterator xs, none⟩))) ∧
  (∀ (xs : List Int),
    (do
      let s0 ← (sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) : IteratorResult _)
      collectStateful (fun _ st => (listIterator xs).run st) (xs.length + 1) s0) =
    .ok (xs, ⟨listIterator xs, none⟩))

theorem statefulConsistent : StatefulConsistent := by
  refine ⟨?_, fun xs => collectStateful_full xs⟩
  intro xs pos sentinel
  refine ⟨?_, ?_, collectStateful_at xs ((xs.drop pos).length + 1) pos (Nat.lt_succ_self _), ?_, ?_⟩
  · unfold statefulCurAt; cases xs.drop pos <;> rfl
  · unfold statefulCurAt; cases xs.drop pos <;> rfl
  · intro hnil
    unfold statefulCurAt
    simp [popfirstStateful, hnil]
  · intro x rest hd
    have hdrop : xs.drop (pos + 1) = rest := by rw [← List.drop_drop, hd]; rfl
    refine ⟨⟨listIterator xs, statefulCurAt xs (pos + 1)⟩, ?_, ?_, ?_⟩
    · unfold statefulCurAt
      simp only [popfirstStateful, hd, listIterator_run_some]
      cases xs.drop (pos + 1) <;> rfl
    · unfold statefulCurAt
      simp only [iterateStateful, popfirstStateful, hd, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte, listIterator_run_some]
      cases xs.drop (pos + 1) <;> rfl
    · have h := collectStateful_at xs (rest.length + 1) (pos + 1)
        (by rw [hdrop]; exact Nat.lt_succ_self _)
      rwa [hdrop] at h

def OnlyCorrect : Prop :=
  ∀ (xs : List Int),
    (xs.length = 1 → ∃ x, xs = [x] ∧ onlyModel (listIterator xs) = .ok x ∧
      onlyTupleDispatch xs = .ok x ∧ onlyNamedTupleDispatch xs = .ok x) ∧
    (xs.length ≠ 1 → ∃ m1 m2 m3,
      onlyModel (listIterator xs) = .error (.argumentError m1) ∧
      onlyTupleDispatch xs = .error (.argumentError m2) ∧
      onlyNamedTupleDispatch xs = .error (.argumentError m3))

theorem onlyCorrect : OnlyCorrect := by
  intro xs
  constructor
  · intro h
    cases xs with
    | nil => simp at h
    | cons x rest =>
      cases rest with
      | nil => exact ⟨x, rfl, rfl, rfl, rfl⟩
      | cons y ys => simp at h
  · intro h
    cases xs with
    | nil => exact ⟨_, _, _, rfl, rfl, rfl⟩
    | cons x rest =>
      cases rest with
      | nil => exact absurd rfl h
      | cons y ys => exact ⟨_, _, _, rfl, rfl, rfl⟩

theorem scanAccum_length {α : Type} (f : α → α → α) (acc : α) (xs : List α) :
    (scanAccum f acc xs).length = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [scanAccum, ih]

theorem accumulateSpec_length {α : Type} (f : α → α → α) (init : Option α) (xs : List α) :
    (accumulateSpec f init xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [accumulateSpec, scanAccum_length]

theorem accumulateAsIterator_run_some (f : Int → Int → Int) (init : Option Int) (xs : List Int)
    (acc : Int) (i : Nat) :
    (accumulateAsIterator (listIterator xs) f (fun op a b => op a b) init
      (fun state x => match state with | none => x | some a => f a x)).run (some (acc, i)) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (f acc x, (f acc x, i + 1))) := by
  simp only [accumulateAsIterator, iterateAccumulateState, listIterator_run_some]
  cases xs.drop i <;> rfl

theorem collectPrefix_accumulate_at (f : Int → Int → Int) (init : Option Int) (xs : List Int)
    (fuel i : Nat) (acc : Int) (hf : (xs.drop i).length < fuel) :
    collectPrefix (accumulateAsIterator (listIterator xs) f (fun op a b => op a b) init
      (fun state x => match state with | none => x | some a => f a x)) fuel (some (acc, i)) =
      .ok (scanAccum f acc (xs.drop i)) := by
  induction fuel generalizing i acc with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, accumulateAsIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) (f acc x) hlen, hdrop, scanAccum]

def AccumulateCorrect : Prop :=
  ∀ (f : Int → Int → Int) (init : Option Int) (xs : List Int),
    let itr := accumulateAsIterator (listIterator xs) f (fun op a b => op a b) init
      (fun state x => match state with | none => x | some acc => f acc x)
    emitsExactly itr (accumulateSpec f init xs) ∧ itr.length = .ok xs.length

theorem accumulateCorrect : AccumulateCorrect := by
  intro f init xs
  refine ⟨?_, rfl⟩
  unfold emitsExactly
  rw [accumulateSpec_length]
  cases xs with
  | nil => rfl
  | cons x rest =>
    let first := match init with | none => x | some acc => f acc x
    have hrun0 : (accumulateAsIterator (listIterator (x :: rest)) f (fun op a b => op a b) init
        (fun state x => match state with | none => x | some acc => f acc x)).run none =
        .ok (some (first, (first, 1))) := rfl
    have h := collectPrefix_accumulate_at f init (x :: rest) (rest.length + 1) 1 first (by simp)
    rw [List.drop_succ_cons, List.drop_zero] at h
    rw [List.length_cons, collectPrefix, hrun0]
    simp only [ok_bind, pure_jl, accumulateSpec, first, h]
    cases init <;> rfl

theorem except_bind_assoc {ε α β γ : Type} (m : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (m >>= fun a => f a >>= g) = ((m >>= f) >>= g) := by
  cases m <;> rfl

theorem nthAdvance_listIterator {α : Type} (xs : List α) (k i : Nat) :
    ((listIterator xs).run (some i) >>= nthAdvance (listIterator xs).run k) =
      (listIterator xs).run (some (i + k)) := by
  induction k generalizing i with
  | zero =>
    cases (listIterator xs).run (some i) <;> rfl
  | succ k ih =>
    rw [listIterator_run_some]
    cases hd : xs.drop i with
    | nil =>
      have hnil : xs.drop (i + (k + 1)) = [] := by
        have := List.drop_eq_nil_iff.mp hd
        exact List.drop_eq_nil_iff.mpr (by omega)
      simp [nthAdvance, listIterator_run_some, hnil]
    | cons x rest =>
      simp only [ok_bind, nthAdvance]
      rw [ih (i + 1)]
      congr 2
      omega

theorem nthModel_listIterator_pos {α : Type} (xs : List α) (n : Int) (hn : 1 ≤ n) :
    nthModel (listIterator xs) n =
      match xs.drop (n.toNat - 1) with
      | [] => .error .boundsError
      | x :: _ => .ok x := by
  have hnotle : ¬ n ≤ 0 := by omega
  have heq : (n - 1).toNat = n.toNat - 1 := by omega
  unfold nthModel nthGeneric
  simp only [hnotle, ↓reduceIte, heq, listIterator_run_none]
  rw [except_bind_assoc, nthAdvance_listIterator, Nat.zero_add, listIterator_run_some]
  cases xs.drop (n.toNat - 1) <;> rfl

theorem jint_add_val {u : IntTy} (a b : JInt u) : (a + b).val = wrapInt u (a.val + b.val) := rfl
theorem jint_sub_val {u : IntTy} (a b : JInt u) : (a - b).val = wrapInt u (a.val - b.val) := rfl
theorem jint_rem_val {t u : IntTy} (a : JInt t) : (JInt.rem u a).val = wrapInt u a.val := rfl
theorem jint_lit_val (u : IntTy) (x : Int) : (JInt.lit u x).val = wrapInt u x := rfl

theorem nthArray_index_val (t : IntTy) (n : JInt t) :
    (JInt.rem (IntTy.promote .i64 t) (JInt.lit .i64 1) +
      JInt.rem (IntTy.promote .i64 t) n -
      JInt.lit (IntTy.promote .i64 t) 1).val = n.val := by
  have hn := n.property
  rw [jint_sub_val, jint_add_val, jint_rem_val, jint_rem_val, jint_lit_val, jint_lit_val]
  cases t <;>
    (simp [IntTy.promote, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hn ⊢;
     omega)

theorem nthArray_vector_eq (t : IntTy) (xs : List Int) (n : JInt t) :
    if 1 ≤ n.val ∧ n.val ≤ xs.length then
      ∃ x, listGet xs (n.val.toNat - 1) = some x ∧
        nthArray (JInt.lit .i64 1) (vectorGetIndex xs) n = .ok x
    else
      nthArray (JInt.lit .i64 1) (vectorGetIndex xs) n = .error .boundsError := by
  unfold nthArray vectorGetIndex
  dsimp only
  rw [nthArray_index_val t n]
  by_cases h : 1 ≤ n.val ∧ n.val ≤ xs.length
  · simp only [h, and_self, ↓reduceIte]
    have hlt : n.val.toNat - 1 < xs.length := by omega
    have hdrop : xs.drop (n.val.toNat - 1) ≠ [] := by
      intro he; have := List.drop_eq_nil_iff.mp he; omega
    cases hd : xs.drop (n.val.toNat - 1) with
    | nil => exact absurd hd hdrop
    | cons x rest =>
      have hget : listGet xs (n.val.toNat - 1) = some x := by
        rw [listGet_eq_drop_head?, hd]; rfl
      exact ⟨x, hget, by simp [hget]⟩
  · simp [h]

def NthVectorCorrect : Prop :=
  (∀ (t : IntTy) (xs : List Int) (n : JInt t),
    if 1 ≤ n.val ∧ n.val ≤ xs.length then
      ∃ x, listGet xs (n.val.toNat - 1) = some x ∧
        nthArray (JInt.lit .i64 1) (vectorGetIndex xs) n = .ok x
    else
      nthArray (JInt.lit .i64 1) (vectorGetIndex xs) n = .error .boundsError) ∧
  (∀ (xs : List Int) (n : Int),
    if 1 ≤ n ∧ n ≤ xs.length then
      ∃ x, listGet xs (n.toNat - 1) = some x ∧
        nthModel (listIterator xs) n = .ok x ∧
        nthGeneric (listIterator xs) n = .ok x
    else
      nthModel (listIterator xs) n = .error .boundsError ∧
      nthGeneric (listIterator xs) n = .error .boundsError)

theorem nthVectorCorrect : NthVectorCorrect := by
  refine ⟨nthArray_vector_eq, ?_⟩
  intro xs n
  by_cases h : 1 ≤ n ∧ n ≤ xs.length
  · simp only [h, and_self, ↓reduceIte, nthModel_listIterator_pos xs n h.1]
    have hlt : n.toNat - 1 < xs.length := by omega
    have hdrop : xs.drop (n.toNat - 1) ≠ [] := by
      intro he
      have := List.drop_eq_nil_iff.mp he
      omega
    cases hd : xs.drop (n.toNat - 1) with
    | nil => exact absurd hd hdrop
    | cons x rest =>
      refine ⟨x, ?_, rfl, ?_⟩
      · rw [listGet_eq_drop_head?, hd]; rfl
      · change nthModel (listIterator xs) n = .ok x
        rw [nthModel_listIterator_pos xs n h.1, hd]
  · simp only [h, ↓reduceIte]
    by_cases hn : n ≤ 0
    · simp [nthModel, nthGeneric, hn]
    · have hpos : 1 ≤ n := by omega
      have hge : xs.length ≤ n.toNat - 1 := by omega
      have hnil : xs.drop (n.toNat - 1) = [] := List.drop_eq_nil_iff.mpr hge
      have hm := nthModel_listIterator_pos xs n hpos
      rw [hnil] at hm
      exact ⟨hm, hm⟩

theorem countAsIterator_run_some (start step s : JInt64) :
    (countAsIterator ⟨start, step, fun a b => a + b⟩).run (some s) =
      .ok (some (s, s + step)) := rfl

theorem countAsIterator_run_none (start step : JInt64) :
    (countAsIterator ⟨start, step, fun a b => a + b⟩).run none =
      .ok (some (start, start + step)) := rfl

theorem collectPrefix_count_some (start step : JInt64) (k : Nat) (s : JInt64) :
    collectPrefix (countAsIterator ⟨start, step, fun a b => a + b⟩) k (some s) =
      .ok (countChain s step k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp [collectPrefix, countAsIterator_run_some, ih, countChain]

theorem collectPrefix_count (start step : JInt64) (k : Nat) :
    collectPrefix (countAsIterator ⟨start, step, fun a b => a + b⟩) k none =
      .ok (countChain start step k) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp [collectPrefix, countAsIterator_run_none, collectPrefix_count_some, countChain]

def CountfromCorrect : Prop :=
  ∀ (start step : JInt64) (k : Nat),
    let cTyped := countfromTyped (fun a b => a + b) id (fun a b => a + b) start step
    collectPrefix (countAsIterator cTyped) k none = .ok (countChain start step k) ∧
    (do
      let cProm ← countfromPromoted (fun a b => pure (a, b)) start step
      collectPrefix (countAsIterator cProm) k none) = .ok (countChain start step k)

theorem countfromCorrect : CountfromCorrect :=
  fun start step k => ⟨collectPrefix_count start step k, collectPrefix_count start step k⟩

theorem enumerateNatFrom_length {α : Type} (k : Nat) (xs : List α) :
    (enumerateNatFrom k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp [enumerateNatFrom, ih]

theorem drop_reverse_range (n i : Nat) (hi : i ≤ n) :
    (List.range n).reverse.drop i = (List.range (n - i)).reverse := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.drop_succ_cons, Nat.add_sub_add_right]
    exact ih m (by omega)

theorem listGet_take_last {α : Type} (xs : List α) (m : Nat) (hm : m < xs.length) :
    ∃ x, listGet xs m = some x ∧ (xs.take (m + 1)).reverse = x :: (xs.take m).reverse := by
  induction xs generalizing m with
  | nil => simp at hm
  | cons a rest ih =>
    cases m with
    | zero => exact ⟨a, rfl, rfl⟩
    | succ m =>
      obtain ⟨x, hx, hrev⟩ := ih m (by simp at hm; omega)
      refine ⟨x, hx, ?_⟩
      simp only [List.take_succ_cons, List.reverse_cons, hrev, List.cons_append]

theorem enumerateNatFrom_take_succ {α : Type} (xs : List α) (k m : Nat) (x : α)
    (hx : listGet xs m = some x) (hm : m < xs.length) :
    (enumerateNatFrom k (xs.take (m + 1))).reverse =
      (k + m, x) :: (enumerateNatFrom k (xs.take m)).reverse := by
  induction xs generalizing k m with
  | nil => simp at hm
  | cons a rest ih =>
    cases m with
    | zero =>
      cases hx
      simp [enumerateNatFrom]
    | succ m =>
      have h := ih (k + 1) m hx (by simp at hm; omega)
      have heq : k + 1 + m = k + (m + 1) := by omega
      rw [heq] at h
      simp [List.take_succ_cons, enumerateNatFrom, h]

theorem pairsListAsIterator_run_some {α : Type} (xs : List α) (i : Nat) :
    (pairsListAsIterator xs).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some ((i, x), i + 1)) := by
  unfold pairsListAsIterator iteratePairsModel pairsElement
  simp only [Option.getD_some, listGet_eq_drop_head?]
  cases hd : xs.drop i with
  | nil => rfl
  | cons x tail =>
    simp only [List.head?_cons, pairsLinear, ok_bind, pure_jl, hd]

theorem collectPrefix_pairsList_at {α : Type} (xs : List α) (fuel i : Nat)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (pairsListAsIterator xs) fuel (some i) =
      .ok (enumerateNatFrom i (xs.drop i)) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, pairsListAsIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop, enumerateNatFrom]

theorem emitsExactly_pairsList {α : Type} (xs : List α) :
    emitsExactly (pairsListAsIterator xs) (enumerateNatFrom 0 xs) := by
  unfold emitsExactly
  rw [enumerateNatFrom_length]
  have h0 : collectPrefix (pairsListAsIterator xs) (xs.length + 1) none =
      collectPrefix (pairsListAsIterator xs) (xs.length + 1) (some 0) := rfl
  rw [h0]
  simpa using collectPrefix_pairsList_at xs (xs.length + 1) 0 (by simp)

theorem collectPrefix_reversePairsList_at {α : Type} (xs : List α) :
    ∀ (k fuel : Nat), k ≤ xs.length → k < fuel →
      collectPrefix (reversePairsListAsIterator xs) fuel
        (some ((List.range xs.length).reverse, xs.length - k)) =
      .ok ((enumerateNatFrom 0 (xs.take k)).reverse) := by
  intro k
  induction k with
  | zero =>
    intro fuel _ hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hd : (List.range xs.length).reverse.drop xs.length = [] := by
        rw [drop_reverse_range xs.length xs.length (Nat.le_refl _), Nat.sub_self]; rfl
      simp [collectPrefix, reversePairsListAsIterator, iterateReversePairs,
        keysPairs, pairsLinear, reverseDefault, listIterator_run_some, hd, enumerateNatFrom]
  | succ m ih =>
    intro fuel hm hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
      have hrev := enumerateNatFrom_take_succ xs 0 m x hx (by omega)
      rw [Nat.zero_add] at hrev
      have hd : (List.range xs.length).reverse.drop (xs.length - (m + 1)) =
          m :: (List.range m).reverse := by
        rw [drop_reverse_range xs.length (xs.length - (m + 1)) (by omega)]
        have hsub : xs.length - (xs.length - (m + 1)) = m + 1 := by omega
        rw [hsub, List.range_succ, List.reverse_append]; rfl
      have hnext : xs.length - (m + 1) + 1 = xs.length - m := by omega
      have hrun : (reversePairsListAsIterator xs).run
          (some ((List.range xs.length).reverse, xs.length - (m + 1))) =
          .ok (some ((m, x), ((List.range xs.length).reverse, xs.length - m))) := by
        simp [reversePairsListAsIterator, iterateReversePairs, keysPairs, pairsLinear,
          reverseDefault, pairsElement, listIterator_run_some, hd, hx, hnext]
      simp only [collectPrefix, hrun, ok_bind, pure_jl, ih fuel (by omega) (by omega), hrev]

theorem emitsExactly_reversePairsList {α : Type} (xs : List α) :
    emitsExactly (reversePairsListAsIterator xs) (enumerateNatFrom 0 xs).reverse := by
  unfold emitsExactly
  have hlen : (enumerateNatFrom 0 xs).reverse.length = xs.length := by
    rw [List.length_reverse, enumerateNatFrom_length]
  have h0 : (reversePairsListAsIterator xs).run none =
      (reversePairsListAsIterator xs).run (some ((List.range xs.length).reverse, 0)) := rfl
  rw [collectPrefix_succ, h0, ← collectPrefix_succ, hlen]
  have h := collectPrefix_reversePairsList_at xs xs.length (xs.length + 1) (Nat.le_refl _) (Nat.lt_succ_self _)
  rwa [Nat.sub_self, List.take_length] at h

theorem listLastModel_append_singleton {α : Type} (ys : List α) (y : α) :
    listLastModel (ys ++ [y]) = .ok y := by
  induction ys with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b bs => exact ih

theorem lastPairs_eq_last_enumerate {α : Type} (xs : List α) :
    lastPairs (K := Nat) (V := α) (I := Nat) (D := List α)
      (keysPairs (K := Nat) (V := α) (I := Nat) (D := List α) (fun ys => List.range ys.length) (fun _ => List.range xs.length))
      listLastModel
      (pairsElement (K := Nat) (V := α) (I := Nat) (D := List α) (fun ys i =>
        (listGet ys i).elim (.error .boundsError) pure))
      (pairsLinear (K := Nat) (V := α) (fun _ => 0) xs) =
    listLastModel (enumerateNatFrom 0 xs) := by
  unfold lastPairs keysPairs pairsLinear pairsElement
  dsimp only
  cases hxs : xs.reverse with
  | nil =>
    have hnil : xs = [] := List.reverse_eq_nil_iff.mp hxs
    subst hnil
    rfl
  | cons lastX revRest =>
    have hlen : 0 < xs.length := by
      cases xs with
      | nil => simp at hxs
      | cons _ _ => simp
    obtain ⟨m, hm⟩ : ∃ m, xs.length = m + 1 := ⟨xs.length - 1, by omega⟩
    obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
    have hrev_enum := enumerateNatFrom_take_succ xs 0 m x hx (by omega)
    rw [Nat.zero_add, ← hm, List.take_length] at hrev_enum
    have hlast_range : listLastModel (List.range (m + 1)) = .ok m := by
      rw [List.range_succ, listLastModel_append_singleton]
    have hlast_enum : listLastModel (enumerateNatFrom 0 xs) = .ok (m, x) := by
      have hre : enumerateNatFrom 0 xs = ((enumerateNatFrom 0 xs).reverse).reverse :=
        (List.reverse_reverse _).symm
      rw [hre, hrev_enum, List.reverse_cons, listLastModel_append_singleton]
    simp only [hm, hlast_range, ok_bind, hx, Option.elim, pure_jl, hlast_enum]

theorem firstIterModel_of_emitsExactly {α S : Type} (itr : IteratorModel α S) (ys : List α)
    (h : emitsExactly itr ys) :
    firstIterModel itr = (ys.head?).elim (.error .boundsError) pure := by
  unfold emitsExactly at h
  rw [collectPrefix_succ] at h
  unfold firstIterModel
  cases hrun : itr.run none with
  | error e =>
    rw [hrun] at h
    cases h
  | ok step =>
    rw [hrun] at h
    cases step with
    | none =>
      cases h
      rfl
    | some pair =>
      dsimp [collectAfterStep] at h
      cases htail : collectPrefix itr ys.length (some pair.2) with
      | error e =>
        rw [htail] at h
        cases h
      | ok rest =>
        rw [htail] at h
        injection h with hys
        subst hys
        rfl

theorem head?_append_of_ne_nil {α : Type} (l1 l2 : List α) (h : l1 ≠ []) :
    (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem head_reverse_eq_listLastModel {α : Type} (ys : List α) :
    (ys.reverse.head?).elim (.error .boundsError) pure = listLastModel ys := by
  induction ys with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y tail =>
      have hne : (y :: tail).reverse ≠ [] := by simp
      have hhead : ((x :: y :: tail).reverse).head? = ((y :: tail).reverse).head? := by
        rw [List.reverse_cons, head?_append_of_ne_nil _ _ hne]
      rw [hhead, ih]
      rfl

theorem listLastModel_err {α : Type} (ys : List α) (e : JlError)
    (h : listLastModel ys = .error e) : e = .boundsError := by
  rw [← head_reverse_eq_listLastModel ys] at h
  cases ho : ys.reverse.head? with
  | none =>
    rw [ho] at h
    injection h with he
    exact he.symm
  | some _ =>
    rw [ho] at h
    cases h

theorem reverseLast_eq_last_reverse {α : Type} (xs : List α) :
    reverseLast (fun ys : List α => (ys.head?).elim (.error .boundsError) pure) (reverseDefault xs) =
      listLastModel xs.reverse := by
  unfold reverseLast reverseDefault
  dsimp only
  rw [← head_reverse_eq_listLastModel xs.reverse, List.reverse_reverse]

theorem emitsExactly_listIterator {α : Type} (xs : List α) :
    emitsExactly (listIterator xs) xs := by
  unfold emitsExactly
  have h0 : collectPrefix (listIterator xs) (xs.length + 1) none =
      collectPrefix (listIterator xs) (xs.length + 1) (some 0) := rfl
  rw [h0]
  simpa using collectPrefix_listIterator_at xs (xs.length + 1) 0 (by simp)

theorem collectPrefix_generator {α β S : Type} (f : α → β) (itr : IteratorModel α S) :
    ∀ (fuel : Nat) (st : Option S) (ys : List α),
      collectPrefix itr fuel st = .ok ys →
      collectPrefix (generatorAsIterator ⟨f, itr, []⟩) fuel st = .ok (ys.map f) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st ys h
    simp [collectPrefix] at h
    subst h
    rfl
  | succ fuel ih =>
    intro st ys h
    rw [collectPrefix_succ] at h ⊢
    have hrun_gen : (generatorAsIterator ⟨f, itr, []⟩).run st = (do
        match ← itr.run st with
        | none => pure none
        | some (x, next) => pure (some (f x, next))) := rfl
    rw [hrun_gen]
    cases hrun : itr.run st with
    | error e =>
      rw [hrun] at h
      cases h
    | ok step =>
      rw [hrun] at h
      cases step with
      | none =>
        cases h
        rfl
      | some pair =>
        dsimp [collectAfterStep] at h
        cases htail : collectPrefix itr fuel (some pair.2) with
        | error e =>
          rw [htail] at h
          cases h
        | ok rest =>
          rw [htail] at h
          injection h with hys
          subst hys
          dsimp [ok_bind, pure_jl, collectAfterStep]
          rw [ih (some pair.2) rest htail]
          rfl

theorem emitsExactly_generator {α β S : Type} (f : α → β) (itr : IteratorModel α S) (ys : List α)
    (h : emitsExactly itr ys) :
    emitsExactly (generatorAsIterator ⟨f, itr, []⟩) (ys.map f) := by
  unfold emitsExactly at h ⊢
  rw [List.length_map]
  exact collectPrefix_generator f itr (ys.length + 1) none ys h

theorem emitsExactly_mapModel {α β : Type} (f : α → β) (xs : List α) :
    emitsExactly (generatorAsIterator (mapModel f (listIterator xs) [])) (xs.map f) :=
  emitsExactly_generator f (listIterator xs) xs (emitsExactly_listIterator xs)

theorem emitsExactly_reverseGenerator {α β : Type} (f : α → β) (xs : List α) :
    emitsExactly
      (generatorAsIterator (sourceMethod157 (fun _ => listIterator xs.reverse) ⟨f, listIterator xs, []⟩))
      (xs.map f).reverse := by
  rw [← List.map_reverse]
  exact emitsExactly_generator f (listIterator xs.reverse) xs.reverse (emitsExactly_listIterator xs.reverse)

theorem flatmap_outer_run_some {α β : Type} (f : α → List β) (xs : List α) (i : Nat) :
    (generatorAsIterator (flatmapModel (fun x => listIterator (f x)) (listIterator xs)).it).run (some i) =
      match (xs.map f).drop i with
      | [] => .ok none
      | r :: _ => .ok (some (listIterator r, i + 1)) := by
  unfold generatorAsIterator flatmapModel mapModel flattenModel
  dsimp only
  rw [listIterator_run_some, ← List.map_drop]
  cases xs.drop i <;> rfl

theorem flattenAdvanceOuter_of_outer {α : Type} (rows : List (List α))
    (outer : IteratorModel (IteratorModel α Nat) Nat)
    (hsome : ∀ i, outer.run (some i) =
      match rows.drop i with
      | [] => .ok none
      | r :: _ => .ok (some (listIterator r, i + 1))) :
    ∀ (k i f : Nat), (rows.drop i).length ≤ k →
      ((rows.drop i).flatten).length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel outer)) f
        (flattenAdvanceOuter outer i) =
      .ok ((rows.drop i).flatten) := by
  intro k
  induction k with
  | zero =>
    intro i f hk _
    have hnil : rows.drop i = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [flattenAdvanceOuter.eq_def, hsome, hnil]
    rfl
  | succ k ih =>
    intro i f hk hf
    cases hd : rows.drop i with
    | nil =>
      rw [flattenAdvanceOuter.eq_def, hsome, hd]
      rfl
    | cons r restRows =>
      have hdrop : rows.drop (i + 1) = restRows := by rw [← List.drop_drop, hd]; rfl
      have hk' : (rows.drop (i + 1)).length ≤ k := by
        have hlt : (rows.drop (i + 1)).length < (rows.drop i).length := by
          rw [hd, hdrop, List.length_cons]; omega
        omega
      cases r with
      | nil =>
        have hf' : ((rows.drop (i + 1)).flatten).length ≤ f := by
          rw [hd, List.flatten_cons, List.nil_append, ← hdrop] at hf
          exact hf
        have hstep : flattenAdvanceOuter outer i =
            flattenAdvanceOuter outer (i + 1) := by
          conv => lhs; rw [flattenAdvanceOuter.eq_def]
          rw [hsome, hd]
          rfl
        rw [hstep, List.flatten_cons, List.nil_append, ← hdrop]
        exact ih (i + 1) f hk' hf'
      | cons x rx =>
        rw [hd, List.flatten_cons, List.cons_append, List.length_cons, List.length_append, ← hdrop] at hf
        cases f with
        | zero => omega
        | succ f =>
          have hstep : flattenAdvanceOuter outer i =
              .ok (some (x, (i + 1, listIterator (x :: rx), 1))) := by
            rw [flattenAdvanceOuter.eq_def, hsome, hd]
            rfl
          rw [hstep, collectAfterStep_some, List.flatten_cons, List.cons_append, ← hdrop]
          have h_adv : ∀ f', ((rows.drop (i + 1)).flatten).length ≤ f' →
              collectAfterStep (flattenAsIterator (flattenModel outer)) f'
                (flattenAdvanceOuter outer (i + 1)) =
              .ok ((rows.drop (i + 1)).flatten) :=
            fun f' hf' => ih (i + 1) f' hk' hf'
          have hinner := collectPrefix_flatten_inner outer (i + 1)
            ((rows.drop (i + 1)).flatten) h_adv (x :: rx) rx.length 1 (f + 1)
            (by simp) (by simp only [List.drop_succ_cons, List.drop_zero]; omega)
          rw [List.drop_succ_cons, List.drop_zero] at hinner
          simp only [hinner, ok_bind, pure_jl]

theorem emitsExactly_flatmap {α β : Type} (f : α → List β) (xs : List α) :
    let outer := generatorAsIterator (flatmapModel (fun x => listIterator (f x)) (listIterator xs)).it
    emitsExactly (flattenAsIterator (flattenModel outer)) ((xs.map f).flatten) := by
  intro outer
  unfold emitsExactly
  have hrun0 : (flattenAsIterator (flattenModel outer)).run none =
      flattenAdvanceOuter outer 0 := by
    dsimp [flattenAsIterator, iterateFlattenStart, flattenModel]
    rw [flattenAdvanceOuter.eq_def]
    have h0 : outer.run none = outer.run (some 0) := rfl
    rw [h0, flatmap_outer_run_some]
    cases xs.map f with
    | nil => rfl
    | cons r rest =>
      cases r <;> rfl
  rw [collectPrefix_succ, hrun0]
  have h := flattenAdvanceOuter_of_outer (xs.map f) outer (flatmap_outer_run_some f xs)
    (xs.map f).length 0 ((xs.map f).flatten).length (by simp) (Nat.le_refl _)
  rwa [List.drop_zero] at h

theorem collectPrefix_repeatedInf {α : Type} (x : α) (k : Nat) :
    ∀ st, collectPrefix (repeatedAsIterator (repeatedModel x)) k st =
      .ok (List.replicate k x) := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro st
    rw [collectPrefix_succ]
    have hrun : (repeatedAsIterator (repeatedModel x)).run st = .ok (some (x, ())) := rfl
    rw [hrun, collectAfterStep_some, ih (some ()), ok_bind, pure_jl, List.replicate_succ]

theorem collectPrefix_cycle_at {α : Type} (x0 : α) (xs : List α) :
    ∀ (k i : Nat), (xs.drop i).length = k →
      collectPrefix (cycleAsIterator (cycleModel (listIterator (x0 :: xs)))) (k + 1) (some (i + 1)) =
        .ok ((xs.drop i) ++ [x0]) := by
  intro k
  induction k with
  | zero =>
    intro i hk
    have hnil : xs.drop i = [] := List.eq_nil_of_length_eq_zero hk
    simp [collectPrefix, cycleAsIterator, iterateCycleState, cycleModel,
      listIterator_run_some, listIterator_run_none, hnil]
  | succ k ih =>
    intro i hk
    cases hd : xs.drop i with
    | nil => simp [hd] at hk
    | cons y rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hk' : (xs.drop (i + 1)).length = k := by rw [hdrop]; simp [hd] at hk; omega
      have hrun : (cycleAsIterator (cycleModel (listIterator (x0 :: xs)))).run (some (i + 1)) =
          .ok (some (y, (i + 1) + 1)) := by
        simp [cycleAsIterator, iterateCycleState, cycleModel, listIterator_run_some, hd]
      rw [collectPrefix_succ, hrun, collectAfterStep_some, ih (i + 1) hk', hdrop]
      rfl

theorem collectPrefix_cycle_wrap {α : Type} (x0 : α) (xs : List α) :
    collectPrefix (cycleAsIterator (cycleModel (listIterator (x0 :: xs)))) (xs.length + 2) none =
      .ok ((x0 :: xs) ++ [x0]) := by
  rw [collectPrefix_succ]
  have hrun0 : (cycleAsIterator (cycleModel (listIterator (x0 :: xs)))).run none =
      .ok (some (x0, 1)) := rfl
  rw [hrun0, collectAfterStep_some]
  have h := collectPrefix_cycle_at x0 xs xs.length 0 (by simp)
  rw [List.drop_zero] at h
  simp [h, ok_bind, pure_jl]

theorem collectPartitionChunk_listIterator {α : Type} (xs : List α) :
    ∀ (k i : Nat),
      collectPartitionChunk (fun itr st => itr.run st) (listIterator xs) k (some i) =
        .ok ((xs.drop i).take k,
          if (xs.drop i).length < k then none else some (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [collectPartitionChunk]
  | succ k ih =>
    intro i
    simp only [collectPartitionChunk, listIterator_run_some]
    cases hd : xs.drop i with
    | nil => simp
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      simp only [ok_bind, ih (i + 1), hdrop, List.length_cons, List.take_succ_cons, pure_jl]
      by_cases hlt : rest.length < k
      · have hlt' : rest.length + 1 < k + 1 := by omega
        simp [hlt, hlt']
      · have hlt' : ¬ (rest.length + 1 < k + 1) := by omega
        have hadd : i + 1 + k = i + (k + 1) := by omega
        simp [hlt, hlt', hadd]


theorem allocPartitionVector_ok (n : Nat) (hn : n < 2 ^ 60) :
    allocPartitionVector n = .ok () := by
  unfold allocPartitionVector
  have h : ¬ (n ≥ 2 ^ 63 - 2 ∨ n * 8 ≥ 2 ^ 63 - 2) := by omega
  simp [h]

theorem partitionGeneric_run_at {α : Type} (xs : List α) (n i : Nat) (hbound : n < 2 ^ 60) :
    (partitionGenericAsIterator xs n).run (some (.at (some (i * n)))) =
      let items := (xs.drop (i * n)).take n
      if items.isEmpty then .ok none
      else .ok (some (items,
        if (xs.drop (i * n)).length < n then .cutShort else .at (some (i * n + n)))) := by
  unfold partitionGenericAsIterator sourceMethod1484
  dsimp only [Option.getD_some]
  rw [allocPartitionVector_ok n hbound, ok_bind, collectPartitionChunk_listIterator, ok_bind]
  by_cases hrem : (xs.drop (i * n)).length < n <;> simp only [hrem, ↓reduceIte, pure_jl]

theorem collectPrefix_partitionGeneric_at {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60) :
    ∀ (fuel i : Nat),
      (xs.length + n - 1) / n - i < fuel →
      collectPrefix (partitionGenericAsIterator xs n) fuel (some (.at (some (i * n)))) =
        .ok ((List.range ((xs.length + n - 1) / n - i)).map fun j => (xs.drop ((i + j) * n)).take n) := by
  intro fuel
  induction fuel with
  | zero => omega
  | succ fuel ih =>
    intro i hf
    have hiff := partCount xs.length n i hn
    rw [collectPrefix_succ, partitionGeneric_run_at xs n i hbound]
    by_cases hi : i < (xs.length + n - 1) / n
    · have hlt : i * n < xs.length := hiff.mp hi
      have hne : ((xs.drop (i * n)).take n).isEmpty = false := by
        cases hd : xs.drop (i * n) with
        | nil =>
          have := List.drop_eq_nil_iff.mp hd
          omega
        | cons x rest =>
          cases n with
          | zero => omega
          | succ m => rfl
      dsimp only
      rw [hne, if_neg Bool.false_ne_true]
      by_cases hrem : (xs.drop (i * n)).length < n
      · have hlast : (xs.length + n - 1) / n - i = 1 := by
          rw [List.length_drop] at hrem
          have h1 : xs.length < (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
          have hnot : ¬ (i + 1 < (xs.length + n - 1) / n) := by
            rw [partCount xs.length n (i + 1) hn]; omega
          omega
        rw [if_pos hrem, collectAfterStep_some, hlast]
        cases fuel with
        | zero => omega
        | succ fuel' =>
          simp [collectPrefix, partitionGenericAsIterator, sourceMethod1484]
      · have hmul : i * n + n = (i + 1) * n := by simp [Nat.add_mul]
        have hlen : (xs.length + n - 1) / n - (i + 1) < fuel := by omega
        have hsub : (xs.length + n - 1) / n - i = ((xs.length + n - 1) / n - (i + 1)) + 1 := by omega
        rw [if_neg hrem, hmul, collectAfterStep_some, ih (i + 1) hlen]
        simp only [ok_bind, pure_jl, hsub, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
        congr 2
        apply List.map_congr_left
        intro j _
        simp only [Function.comp]
        have heq : i + 1 + j = i + (j + 1) := by omega
        rw [heq]
    · have hge : xs.length ≤ i * n := by omega
      have hnil : xs.drop (i * n) = [] := List.drop_eq_nil_iff.mpr hge
      have hz : (xs.length + n - 1) / n - i = 0 := by omega
      simp [hnil, hz, collectAfterStep]

theorem emitsExactly_partitionGeneric {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60) :
    emitsExactly (partitionGenericAsIterator xs n) (chunksSpec n xs) := by
  unfold emitsExactly
  have hne : n ≠ 0 := by omega
  have hlen : (chunksSpec n xs).length = (xs.length + n - 1) / n := by
    simp [chunksSpec, hne]
  rw [hlen]
  have hchunk0 : collectPartitionChunk (fun itr st => itr.run st) (listIterator xs) n none =
      collectPartitionChunk (fun itr st => itr.run st) (listIterator xs) n (some 0) := by
    cases n with
    | zero => omega
    | succ m => rfl
  have hrun0 : (partitionGenericAsIterator xs n).run none =
      (partitionGenericAsIterator xs n).run (some (.at (some (0 * n)))) := by
    simp [partitionGenericAsIterator, sourceMethod1484, Nat.zero_mul, hchunk0]
  rw [collectPrefix_succ, hrun0, ← collectPrefix_succ]
  have h := collectPrefix_partitionGeneric_at xs n hn hbound ((xs.length + n - 1) / n + 1) 0 (by omega)
  simpa [chunksSpec, hne] using h

theorem flatMap_reverse_map_reverse {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → γ) :
    (ys.reverse.flatMap fun y => xs.reverse.map fun x => f x y) =
      (ys.flatMap fun y => xs.map fun x => f x y).reverse := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    rw [List.reverse_cons, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_reverse, ← List.reverse_append, List.flatMap_cons]

theorem lastProduct_two_lists {α : Type} (xs ys : List α) :
    (xs = [] ∨ ys = [] → lastProduct listLastModel (productModel [xs, ys]) = .error .boundsError) ∧
    (xs ≠ [] → ys ≠ [] →
      lastProduct listLastModel (productModel [xs, ys]) =
        listLastModel (ys.flatMap fun y => xs.map fun x => [x, y])) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with rfl | rfl
    · rfl
    · unfold lastProduct productModel
      dsimp [List.mapM, List.mapM.loop]
      cases hx : listLastModel xs with
      | error e =>
        have he := listLastModel_err xs e hx
        subst he
        rfl
      | ok v => rfl
  · intro hxs hys
    have hrx : xs.reverse ≠ [] := by simpa using hxs
    have hry : ys.reverse ≠ [] := by simpa using hys
    cases hxr : xs.reverse with
    | nil => exact absurd hxr hrx
    | cons lx rxs =>
      cases hyr : ys.reverse with
      | nil => exact absurd hyr hry
      | cons ly rys =>
        have hlx : listLastModel xs = .ok lx := by
          rw [← head_reverse_eq_listLastModel xs, hxr]; rfl
        have hly : listLastModel ys = .ok ly := by
          rw [← head_reverse_eq_listLastModel ys, hyr]; rfl
        have hlhs : lastProduct listLastModel (productModel [xs, ys]) = .ok [lx, ly] := by
          unfold lastProduct productModel
          dsimp [List.mapM, List.mapM.loop]
          rw [hlx, ok_bind, hly, ok_bind]
          rfl
        have hrhs : listLastModel (ys.flatMap fun y => xs.map fun x => [x, y]) = .ok [lx, ly] := by
          rw [← head_reverse_eq_listLastModel, ← flatMap_reverse_map_reverse xs ys (fun x y => [x, y]),
            hyr, hxr]
          rfl
        rw [hlhs, hrhs]

theorem nthZip_two_lists (xs ys : List Int) (n : Int) :
    if 1 ≤ n ∧ n ≤ min xs.length ys.length then
      ∃ x y, listGet xs (n.toNat - 1) = some x ∧ listGet ys (n.toNat - 1) = some y ∧
        nthZip [listIterator xs, listIterator ys] n = .ok [x, y]
    else
      nthZip [listIterator xs, listIterator ys] n = .error .boundsError := by
  have hx := nthVectorCorrect.2 xs n
  have hy := nthVectorCorrect.2 ys n
  by_cases h : 1 ≤ n ∧ n ≤ min xs.length ys.length
  · have hx_cond : 1 ≤ n ∧ n ≤ xs.length := ⟨h.1, by omega⟩
    have hy_cond : 1 ≤ n ∧ n ≤ ys.length := ⟨h.1, by omega⟩
    simp only [hx_cond, and_self, ↓reduceIte] at hx
    simp only [hy_cond, and_self, ↓reduceIte] at hy
    obtain ⟨x, hgx, hnx, _⟩ := hx
    obtain ⟨y, hgy, hny, _⟩ := hy
    simp only [h, and_self, ↓reduceIte]
    refine ⟨x, y, hgx, hgy, ?_⟩
    unfold nthZip nthCurry
    dsimp [List.mapM, List.mapM.loop]
    rw [hnx, ok_bind, hny, ok_bind]
    rfl
  · simp only [h, ↓reduceIte]
    unfold nthZip nthCurry
    dsimp [List.mapM, List.mapM.loop]
    by_cases hx_cond : 1 ≤ n ∧ n ≤ xs.length
    · have hy_cond : ¬ (1 ≤ n ∧ n ≤ ys.length) := by omega
      simp only [hx_cond, and_self, ↓reduceIte] at hx
      simp only [hy_cond, ↓reduceIte] at hy
      obtain ⟨x, _, hnx, _⟩ := hx
      rw [hnx, ok_bind, hy.1]
      rfl
    · simp only [hx_cond, ↓reduceIte] at hx
      rw [hx.1]
      rfl

theorem jint_wrap_i64_val (x : Int) (hlo : -(2 ^ 63) ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (JInt.wrap .i64 x).val = x := by
  change wrapInt .i64 x = x
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem jint_lit_i64_val (x : Int) (hlo : -(2 ^ 63) ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (JInt.lit .i64 x).val = x :=
  jint_wrap_i64_val x hlo hhi

theorem except_map_ok_bind {α β γ : Type} (x : α) (f : α → β) (g : β → Jl γ) :
    (Except.map f (Except.ok x : Jl α) >>= g) = g (f x) := rfl

theorem sourceMethod519_two_lists (xs ys : List Int)
    (hbound : ((min xs.length ys.length : Nat) : Int) < 2 ^ 63) :
    let call := sourceMethod519 (zipModel [listIterator xs, listIterator ys])
      (fun is => Except.map (fun (n : Nat) => JInt.lit .i64 (Int.ofNat n)) (zipLength ⟨is⟩))
      (fun itr n => nthModel itr n.val)
    if 0 < min xs.length ys.length then
      ∃ x y, listGet xs (min xs.length ys.length - 1) = some x ∧
        listGet ys (min xs.length ys.length - 1) = some y ∧
        call = .ok [x, y]
    else
      call = .error .boundsError := by
  dsimp only
  have hlen : zipLength ⟨[listIterator xs, listIterator ys]⟩ = .ok (min xs.length ys.length) :=
    (zipCorrect xs ys).2
  generalize hm_eq : min xs.length ys.length = m at hbound hlen ⊢
  have hval : (JInt.lit .i64 (Int.ofNat m)).val = (m : Int) :=
    jint_lit_i64_val (m : Int) (by omega) (by omega)
  have hcall : sourceMethod519 (zipModel [listIterator xs, listIterator ys])
      (fun is => Except.map (fun (n : Nat) => JInt.lit .i64 (Int.ofNat n)) (zipLength ⟨is⟩))
      (fun itr n => nthModel itr n.val) =
      nthZip [listIterator xs, listIterator ys] (m : Int) := by
    unfold sourceMethod519 zipModel nthZip nthCurry
    dsimp only
    rw [hlen, except_map_ok_bind]
    simp only [hval]
  rw [hcall]
  have hzip := nthZip_two_lists xs ys (m : Int)
  rw [hm_eq] at hzip
  by_cases hm : 0 < m
  · have hcond : 1 ≤ (m : Int) ∧ (m : Int) ≤ m := by omega
    rw [if_pos hcond, Int.toNat_natCast] at hzip
    rw [if_pos hm]
    exact hzip
  · have hcond : ¬ (1 ≤ (m : Int) ∧ (m : Int) ≤ m) := by omega
    rw [if_neg hcond] at hzip
    rw [if_neg hm]
    exact hzip

theorem sourceMethod1755_spec (xs : List Int) (cycles : Nat) (n : JInt64)
    (hlen : (xs.length : Int) < 2 ^ 63) (hcyc : (cycles : Int) < 2 ^ 63) (hmul : (xs.length : Int) * (cycles : Int) < 2 ^ 63) :
    let ftr : Flatten (Take (Repeated (IteratorModel Int Nat))) :=
      ⟨⟨repeatedModel (listIterator xs), cycles⟩⟩
    let call := sourceMethod1755 .hasLength ftr n.val
      (fun _ it _ => sourceMethod1767
        (fun o => Except.map (fun (l : Nat) => JInt.lit .i64 (Int.ofNat l)) o.length)
        (fun o idx => nthModel o idx.val) it n)
    if 0 < xs.length ∧ 1 ≤ n.val ∧ n.val ≤ (xs.length : Int) * (cycles : Int) then
      ∃ x, listGet xs ((n.val.toNat - 1) % xs.length) = some x ∧ call = .ok x
    else
      call = .error .boundsError := by
  dsimp only
  have hk_val : (JInt.lit .i64 (Int.ofNat xs.length)).val = (xs.length : Int) :=
    jint_lit_i64_val (xs.length : Int) (by omega) (by omega)
  have hc_val : (JInt.lit .i64 (cycles : Int)).val = (cycles : Int) :=
    jint_lit_i64_val (cycles : Int) (by omega) (by omega)
  have hkc_val : (JInt.lit .i64 (Int.ofNat xs.length) * JInt.lit .i64 (cycles : Int)).val =
      (xs.length : Int) * (cycles : Int) := by
    change (JInt.wrap .i64 ((JInt.lit .i64 (Int.ofNat xs.length)).val * (JInt.lit .i64 (cycles : Int)).val)).val = _
    rw [hk_val, hc_val]
    exact jint_wrap_i64_val ((xs.length : Int) * (cycles : Int)) (by have : 0 ≤ (xs.length : Int) * (cycles : Int) := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _); omega) (by omega)
  have hStep : sourceMethod1755 .hasLength
      ⟨⟨repeatedModel (listIterator xs), cycles⟩⟩ n.val
      (fun _ it _ => sourceMethod1767
        (fun o => Except.map (fun (l : Nat) => JInt.lit .i64 (Int.ofNat l)) o.length)
        (fun o idx => nthModel o idx.val) it n) =
      if (decide (n.val > (xs.length : Int) * (cycles : Int)) || ((xs.length : Int) == 0)) = true then
        .error .boundsError
      else
        nthModel (listIterator xs)
          (if n.val > 0 then JInt.wrap .i64 ((n.val - 1) % (xs.length : Int) + 1) else n).val := by
    unfold sourceMethod1755 sourceMethod1767 repeatedModel
    dsimp only
    have hlen_ok : (listIterator xs).length = .ok xs.length := rfl
    rw [hlen_ok, except_map_ok_bind, hkc_val, hk_val]
  rw [hStep]
  clear hk_val hc_val hkc_val hStep hmul
  generalize (xs.length : Int) * (cycles : Int) = N
  cases xs with
  | nil =>
    simp
  | cons x0 rest =>
    have hlen_pos : 0 < (x0 :: rest).length := Nat.succ_pos _
    have hbeq : (((x0 :: rest).length : Int) == 0) = false := by
      change decide (((rest.length + 1 : Nat) : Int) = 0) = false
      simp; omega
    rw [hbeq, Bool.or_false]
    by_cases h : 0 < (x0 :: rest).length ∧ 1 ≤ n.val ∧ n.val ≤ N
    · rw [if_pos h]
      have hnot : decide (n.val > N) = false := by simp; omega
      have hpos : n.val > 0 := by omega
      rw [hnot, if_neg Bool.false_ne_true, if_pos hpos]
      let m := (n.val - 1) % ((x0 :: rest).length : Int) + 1
      have hm1 : 1 ≤ m := by
        have hmod : 0 ≤ (n.val - 1) % ((x0 :: rest).length : Int) := Int.emod_nonneg (n.val - 1) (by omega)
        change 1 ≤ (n.val - 1) % ((x0 :: rest).length : Int) + 1; omega
      have hm2 : m ≤ (x0 :: rest).length := by
        have hmod : (n.val - 1) % ((x0 :: rest).length : Int) < ((x0 :: rest).length : Int) :=
          Int.emod_lt_of_pos (n.val - 1) (by omega)
        change (n.val - 1) % ((x0 :: rest).length : Int) + 1 ≤ ((x0 :: rest).length : Int); omega
      have hm_wrap : (JInt.wrap .i64 m).val = m :=
        jint_wrap_i64_val m (by omega) (by omega)
      rw [hm_wrap]
      have hvec := nthVectorCorrect.2 (x0 :: rest) m
      have hm_cond : 1 ≤ m ∧ m ≤ (x0 :: rest).length := ⟨hm1, hm2⟩
      simp only [hm_cond, and_self, ↓reduceIte] at hvec
      obtain ⟨x, hx, hnth, _⟩ := hvec
      have hidx : m.toNat - 1 = (n.val.toNat - 1) % (x0 :: rest).length := by
        change ((n.val - 1) % ((x0 :: rest).length : Int) + 1).toNat - 1 = (n.val.toNat - 1) % (x0 :: rest).length
        have hn_eq : n.val - 1 = ((n.val.toNat - 1 : Nat) : Int) := by omega
        have hmod_eq : (n.val - 1) % ((x0 :: rest).length : Int) = (((n.val.toNat - 1) % (x0 :: rest).length : Nat) : Int) := by
          rw [hn_eq, Int.natCast_emod]
        rw [hmod_eq]; omega
      rw [hidx] at hx
      exact ⟨x, hx, hnth⟩
    · rw [if_neg h]
      by_cases hguard : decide (n.val > N) = true
      · rw [if_pos hguard]
      · have hguard_f : ¬ (n.val > N) := by simpa using hguard
        rw [if_neg hguard]
        have hn_le : n.val ≤ 0 := by omega
        have hnotpos : ¬ (n.val > 0) := by omega
        rw [if_neg hnotpos]
        unfold nthModel nthGeneric
        simp [hn_le]

theorem sourceMethod1470_spec (a b s : JInt64) (n : Nat) :
    (s.val > b.val → sourceMethod1470 ⟨(a, b), n⟩ (some s) = none) ∧
    (a.val > b.val → sourceMethod1470 ⟨(a, b), n⟩ none = none) ∧
    (s.val ≤ b.val → 0 < n → (n : Int) < 2 ^ 63 → -(2 ^ 63) < s.val →
      s.val + (n : Int) < 2 ^ 63 → b.val < 2 ^ 63 - 1 →
      ∃ stop r1 : JInt64,
        stop.val = min (s.val + (n : Int) - 1) b.val ∧
        r1.val = stop.val + 1 ∧
        sourceMethod1470 ⟨(a, b), n⟩ (some s) = some ((s, stop), r1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    unfold sourceMethod1470
    have hgt : s > b := h
    simp [hgt]
  · intro h
    unfold sourceMethod1470
    have hgt : a > b := h
    simp [hgt]
  · intro hs hn hn_hi hs_lo hsum_hi hb_hi
    have hs_bounds : -(2 ^ 63) ≤ s.val ∧ s.val ≤ 2 ^ 63 - 1 := s.property
    have hb_bounds : -(2 ^ 63) ≤ b.val ∧ b.val ≤ 2 ^ 63 - 1 := b.property
    unfold sourceMethod1470
    dsimp only [Option.getD_some]
    have hnotgt : ¬ (s > b) := by change ¬ (b.val < s.val); omega
    rw [if_neg hnotgt]
    have hn_val : (JInt.lit .i64 (n : Int)).val = (n : Int) :=
      jint_lit_i64_val (n : Int) (by omega) (by omega)
    have h1_val : (JInt.lit .i64 1).val = 1 := rfl
    have hadd_val : (s + JInt.lit .i64 (n : Int)).val = s.val + (n : Int) := by
      change (JInt.wrap .i64 (s.val + (JInt.lit .i64 (n : Int)).val)).val = _
      rw [hn_val]
      exact jint_wrap_i64_val (s.val + (n : Int)) (by omega) (by omega)
    have hsum_val : (s + JInt.lit .i64 (n : Int) - JInt.lit .i64 1).val = s.val + (n : Int) - 1 := by
      change (JInt.wrap .i64 ((s + JInt.lit .i64 (n : Int)).val - (JInt.lit .i64 1).val)).val = _
      rw [hadd_val, h1_val]
      exact jint_wrap_i64_val (s.val + (n : Int) - 1) (by omega) (by omega)
    generalize hsum_eq : s + JInt.lit .i64 (n : Int) - JInt.lit .i64 1 = sum at hsum_val ⊢
    generalize hr_eq : (if b < sum then b else sum) = r
    have hr_props : r.val = min (s.val + (n : Int) - 1) b.val ∧ s.val ≤ r.val ∧ r.val ≤ b.val := by
      by_cases hlt : b < sum
      · have hlt' : b.val < sum.val := hlt
        rw [if_pos hlt] at hr_eq
        subst hr_eq
        refine ⟨by omega, hs, Int.le_refl _⟩
      · have hge' : ¬ (b.val < sum.val) := hlt
        rw [if_neg hlt] at hr_eq
        subst hr_eq
        refine ⟨by omega, by omega, by omega⟩
    obtain ⟨hr_val, hsr_val, hrb_val⟩ := hr_props
    have hsr : s ≤ r := hsr_val
    have hr1_val : (r + JInt.lit .i64 1).val = r.val + 1 := by
      change (JInt.wrap .i64 (r.val + (JInt.lit .i64 1).val)).val = _
      rw [h1_val]
      exact jint_wrap_i64_val (r.val + 1) (by omega) (by omega)
    refine ⟨r, r + JInt.lit .i64 1, hr_val, hr1_val, ?_⟩
    simp [hsr]


def PairsSemantics : Prop :=
  (∀ (xs : List Int),
    let p : PairsModel Nat Int Nat (List Int) := pairsLinear (K := Nat) (V := Int) (I := Nat) (fun _ => 0) xs
    let ks := keysPairs (K := Nat) (V := Int) (I := Nat) (D := List Int)
      (fun ys => List.range ys.length) (fun _ => List.range xs.length)
    emitsExactly (pairsListAsIterator xs) (enumerateNatFrom 0 xs) ∧
    emitsExactly (reversePairsListAsIterator xs) (enumerateNatFrom 0 xs).reverse ∧
    lastPairs (K := Nat) (V := Int) (I := Nat) (D := List Int)
      ks listLastModel
      (pairsElement (K := Nat) (V := Int) (I := Nat) (D := List Int) (fun ys i =>
        (listGet ys i).elim (.error .boundsError) pure))
      p = listLastModel (enumerateNatFrom 0 xs) ∧
    (pairsListAsIterator xs).length = .ok xs.length ∧
    (pairsListAsIterator xs).size = .ok [xs.length] ∧
    pairsAxes ks (fun r => pure [r.length]) p = .ok [xs.length] ∧
    (∀ st, isdonePairsModel (fun _ s => (listIterator xs).isdone s) (fun _ => 0) p st =
      .ok (some (decide (xs.length ≤ st.getD 0)))) ∧
    sourceMethod318 .hasLength p = .hasLength ∧
    sourceMethod319 p = .hasLength ∧
    (∀ k : Nat, haskeyPairsModel ks (fun r key => decide (key ∈ r)) p k = decide (k < xs.length))) ∧
  (∀ {K V I D : Type} (data : D) (selected : Option I)
    (keysData : D → List K) (indices : I → List K) (idxFn : D → I),
    let p : PairsModel K V I D := ⟨data, selected⟩
    keysPairs keysData indices p =
      (match selected with | none => keysData data | some i => indices i) ∧
    valuesPairsModel p = data ∧
    pairsLinear (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsTuple (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsNamedTuple (K := K) (V := V) idxFn data = ⟨data, none⟩ ∧
    pairsSimpleVector (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsVector (pairsLinear (K := K) (V := V) idxFn) data = ⟨data, some (idxFn data)⟩ ∧
    pairsCartesian (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsArray (pairsCartesian (K := K) (V := V) idxFn) data = ⟨data, some (idxFn data)⟩) ∧
  (∀ {K V I D R : Type} (getindex : D → K → Jl R)
    (p : PairsModel K V I D) (key : K),
    getindexPairsModel getindex p key = getindex p.data key) ∧
  (∀ {K V I D R : Type} (setindex : D → K → R → Jl D) (getindex : D → K → Jl R)
    (p : PairsModel K V I D) (key : K) (value : R) (d' : D),
    setindex p.data key value = .ok d' →
      setindexPairsModel setindex p value key = .ok { p with data := d' } ∧
      (do
        let p' ← setindexPairsModel setindex p value key
        getindexPairsModel getindex p' key) = getindex d' key) ∧
  (∀ {K V I D R : Type} (get : D → K → R → Jl R)
    (p : PairsModel K V I D) (key : K) (default : R),
    getPairsModel get p key default = get p.data key default) ∧
  (∀ {F K V I D R : Type} (getFn : F → D → K → Jl R)
    (f : F) (p : PairsModel K V I D) (key : K),
    getPairsWithFunction getFn f p key = getFn f p.data key)

theorem pairsSemantics : PairsSemantics := by
  refine ⟨fun xs => ⟨emitsExactly_pairsList xs, emitsExactly_reversePairsList xs,
    lastPairs_eq_last_enumerate xs, ?_, ?_, ?_, fun _ => rfl, rfl, rfl, ?_⟩,
    fun _ selected _ _ _ => ⟨by cases selected <;> rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ _ _ => rfl,
    ?_,
    fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩
  · simp [pairsListAsIterator, pairsLength, keysPairs, pairsLinear]
  · simp [pairsListAsIterator, pairsSize, keysPairs, pairsLinear]
  · simp [pairsAxes, keysPairs, pairsLinear]
  · intro k
    simp [haskeyPairsModel, keysPairs, pairsLinear, List.mem_range]
  · intro K V I D R setindex getindex p key value d' hset
    simp [setindexPairsModel, getindexPairsModel, hset]

theorem reverseListAsIterator_run_zero {α : Type} (xs : List α) :
    (reverseListAsIterator xs).run (some (0 : Int)) = .ok none := rfl

theorem reverseListAsIterator_run_succ {α : Type} (xs : List α) (m : Nat) (x : α)
    (hx : listGet xs m = some x) :
    (reverseListAsIterator xs).run (some ((m + 1 : Nat) : Int)) =
      .ok (some (x, (m : Int))) := by
  have hnotlt : ¬ ((m : Int) + 1 < 1) := by omega
  have hsub : (m : Int) + 1 - 1 = (m : Int) := by omega
  simp [reverseListAsIterator, iterateReverseTuple, reverseDefault, hnotlt, hx, hsub, Except.map]

theorem collectPrefix_reverseList_at {α : Type} (xs : List α) (fuel k : Nat)
    (hk : k ≤ xs.length) (hf : k < fuel) :
    collectPrefix (reverseListAsIterator xs) fuel (some (k : Int)) =
      .ok ((xs.take k).reverse) := by
  induction k generalizing fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [collectPrefix, reverseListAsIterator_run_zero]
  | succ m ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
      simp only [collectPrefix, reverseListAsIterator_run_succ xs m x hx, ok_bind, pure_jl,
        ih fuel (by omega) (by omega), hrev]

theorem emitsExactly_reverseList {α : Type} (xs : List α) :
    emitsExactly (reverseListAsIterator xs) xs.reverse := by
  unfold emitsExactly
  have h0 : collectPrefix (reverseListAsIterator xs) (xs.reverse.length + 1) none =
      collectPrefix (reverseListAsIterator xs) (xs.reverse.length + 1) (some (xs.length : Int)) := by
    cases xs.reverse.length <;> rfl
  rw [h0, List.length_reverse]
  have h := collectPrefix_reverseList_at xs (xs.length + 1) xs.length (Nat.le_refl _) (Nat.lt_succ_self _)
  rwa [List.take_length] at h

theorem collectPrefix_reverseArray_at {α : Type} (xs : List α) :
    ∀ (k fuel : Nat), k ≤ xs.length → k < fuel →
      collectPrefix (reverseArrayAsIterator xs) fuel
        (some ((List.range xs.length).reverse, xs.length - k)) =
      .ok ((xs.take k).reverse) := by
  intro k
  induction k with
  | zero =>
    intro fuel _ hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hd : (List.range xs.length).reverse.drop xs.length = [] := by
        rw [drop_reverse_range xs.length xs.length (Nat.le_refl _), Nat.sub_self]; rfl
      simp [collectPrefix, reverseArrayAsIterator, sourceMethod136, listIterator_run_some, hd]
  | succ m ih =>
    intro fuel hm hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
      have hd : (List.range xs.length).reverse.drop (xs.length - (m + 1)) =
          m :: (List.range m).reverse := by
        rw [drop_reverse_range xs.length (xs.length - (m + 1)) (by omega)]
        have hsub : xs.length - (xs.length - (m + 1)) = m + 1 := by omega
        rw [hsub, List.range_succ, List.reverse_append]; rfl
      have hnext : xs.length - (m + 1) + 1 = xs.length - m := by omega
      have hrun : (reverseArrayAsIterator xs).run
          (some ((List.range xs.length).reverse, xs.length - (m + 1))) =
          .ok (some (x, ((List.range xs.length).reverse, xs.length - m))) := by
        unfold reverseArrayAsIterator sourceMethod136 reverseDefault
        dsimp only
        rw [listIterator_run_some, hd, ok_bind]
        dsimp only
        rw [hx]
        dsimp only
        rw [pure_jl, ok_bind, pure_jl, hnext]
      rw [collectPrefix_succ, hrun, collectAfterStep_some]
      simp only [ih fuel (by omega) (by omega), ok_bind, pure_jl, hrev]

theorem emitsExactly_reverseArray {α : Type} (xs : List α) :
    emitsExactly (reverseArrayAsIterator xs) xs.reverse := by
  unfold emitsExactly
  have h0 : (reverseArrayAsIterator xs).run none =
      (reverseArrayAsIterator xs).run (some ((List.range xs.length).reverse, 0)) := rfl
  rw [collectPrefix_succ, h0, ← collectPrefix_succ, List.length_reverse]
  have h := collectPrefix_reverseArray_at xs xs.length (xs.length + 1) (Nat.le_refl _) (Nat.lt_succ_self _)
  rwa [Nat.sub_self, List.take_length] at h

theorem emitsExactly_reverseGeneric {α : Type} (xs : List α) :
    emitsExactly (reverseGenericAsIterator xs) xs.reverse :=
  emitsExactly_reverseArray xs

def CycleRepeatedSemantics : Prop :=
  (∀ (f : Int → Int) (xs : List Int),
    emitsExactly (generatorAsIterator (mapModel f (listIterator xs) [])) (xs.map f)) ∧
  (∀ (f : Int → List Int) (xs : List Int),
    let outer := generatorAsIterator (flatmapModel (fun x => listIterator (f x)) (listIterator xs)).it
    emitsExactly (flattenAsIterator (flattenModel outer)) ((xs.map f).flatten)) ∧
  (∀ (predicate : Int → Bool) (pairs : List (Nat × Int)),
    collectFindEach (sourceMethod1016 predicate pairs) =
      (pairs.filter fun pair => predicate pair.2).map Prod.fst) ∧
  (∀ (pairs : List (Nat × Bool)),
    collectFindEach (sourceMethod1018 id pairs) =
      (pairs.filter fun pair => pair.2).map Prod.fst) ∧
  CycleNCorrect ∧
  RepeatedNCorrect ∧
  (∀ (xs : List Int),
    let c := cycleModel (listIterator xs)
    cycleEltype Int c = Int ∧
    cycleIteratorEltype (fun it => it.iteratorEltype) c = .hasEltype ∧
    cycleIteratorSize = .isInfinite ∧
    isdoneCycle (fun _ st => (listIterator xs).isdone st) c = .ok (some xs.isEmpty) ∧
    (∀ i, isdoneCycleState (fun _ st => (listIterator xs).isdone st) c i = .ok (some false)) ∧
    lastCycle listLastModel (cycleModel xs) = listLastModel xs ∧
    (reverseCycle List.reverse (cycleModel xs)).xs = xs.reverse ∧
    emitsExactly (reverseListAsIterator (reverseCycle List.reverse (cycleModel xs)).xs) xs ∧
    (xs = [] → collectPrefix (cycleAsIterator c) 1 none = .ok []) ∧
    (∀ x0 rest, xs = x0 :: rest →
      collectPrefix (cycleAsIterator c) (rest.length + 2) none = .ok ((x0 :: rest) ++ [x0]))) ∧
  (∀ (x : Int) (k : Nat),
    let r := repeatedModel x
    collectPrefix (repeatedAsIterator r) k none = .ok (List.replicate k x) ∧
    collectPrefix (repeatedAsIterator (reverseRepeated r)) k none = .ok (List.replicate k x) ∧
    repeatedEltype r = Int ∧
    repeatedIteratorSize = .isInfinite ∧
    repeatedIteratorEltype = .hasEltype ∧
    reverseRepeated r = r ∧
    lastRepeated (fun it => firstIterModel (repeatedAsIterator it)) r = .ok x)

theorem cycleRepeatedSemantics : CycleRepeatedSemantics := by
  refine ⟨emitsExactly_mapModel, emitsExactly_flatmap, fun _ _ => rfl, fun _ => rfl,
    cycleNCorrect, repeatedNCorrect, ?_, ?_⟩
  · intro xs
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl, rfl, rfl, ?_, ?_, ?_⟩
    · cases xs <;> rfl
    · have h := emitsExactly_reverseList xs.reverse
      rwa [List.reverse_reverse] at h
    · intro hnil; subst hnil; rfl
    · intro x0 rest hcons
      subst hcons
      exact collectPrefix_cycle_wrap x0 rest
  · intro x k
    refine ⟨collectPrefix_repeatedInf x k none, collectPrefix_repeatedInf x k none,
      rfl, rfl, rfl, rfl, rfl⟩

theorem iterableStatePairs_run_some {α : Type} (xs : List α) (i : Nat) :
    (iterableStatePairsAsIterator xs).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some ((i, x), i + 1)) := by
  simp only [iterableStatePairsAsIterator, iterateIterableStatePairs, pairsStringModel,
    pure_jl, ok_bind, listIterator_run_some]
  cases xs.drop i <;> simp

theorem collectPrefix_iterableStatePairs_at {α : Type} (xs : List α) (fuel i : Nat)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (iterableStatePairsAsIterator xs) fuel (some i) =
      .ok (enumerateNatFrom i (xs.drop i)) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    simp only [collectPrefix, iterableStatePairs_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop, enumerateNatFrom]

theorem collectPrefix_reverseIterableStatePairs_at {α : Type} (xs : List α) :
    ∀ (k fuel : Nat), k ≤ xs.length → k < fuel →
      collectPrefix (reverseIterableStatePairsAsIterator xs) fuel (some (k : Int)) =
      .ok (((enumerateNatFrom 1 (xs.take k)).reverse).map fun (i, v) => (Int.ofNat i, v)) := by
  intro k
  induction k with
  | zero =>
    intro fuel _ hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [collectPrefix, reverseIterableStatePairsAsIterator, iterateReverseIterableStatePairs,
        pairsStringModel, reverseListAsIterator_run_zero, enumerateNatFrom]
  | succ m ih =>
    intro fuel hm hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
      have hrev := enumerateNatFrom_take_succ xs 1 m x hx (by omega)
      have h1m : 1 + m = m + 1 := by omega
      rw [h1m] at hrev
      have hrun : (reverseIterableStatePairsAsIterator xs).run (some ((m + 1 : Nat) : Int)) =
          .ok (some ((((m + 1 : Nat) : Int), x), (m : Int))) := by
        simp only [reverseIterableStatePairsAsIterator, iterateReverseIterableStatePairs,
          pairsStringModel, pure_jl, ok_bind, reverseListAsIterator_run_succ xs m x hx]
      rw [collectPrefix_succ, hrun, collectAfterStep_some]
      simp only [ih fuel (by omega) (by omega), ok_bind, pure_jl, hrev, List.map_cons]
      rfl

theorem emitsExactly_reverseIterableStatePairs {α : Type} (xs : List α) :
    emitsExactly (reverseIterableStatePairsAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (Int.ofNat i, v)) := by
  unfold emitsExactly
  have hlen : (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (Int.ofNat i, v)).length = xs.length := by
    rw [List.length_map, List.length_reverse, enumerateNatFrom_length]
  have h0 : (reverseIterableStatePairsAsIterator xs).run none =
      (reverseIterableStatePairsAsIterator xs).run (some (xs.length : Int)) := rfl
  rw [collectPrefix_succ, h0, ← collectPrefix_succ, hlen]
  have h := collectPrefix_reverseIterableStatePairs_at xs xs.length (xs.length + 1) (Nat.le_refl _) (Nat.lt_succ_self _)
  rwa [List.take_length] at h

def IterableStatePairsSemantics : Prop :=
  (∀ (xs : List Int),
    emitsExactly (iterableStatePairsAsIterator xs) (enumerateNatFrom 0 xs) ∧
    emitsExactly (reverseIterableStatePairsAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (Int.ofNat i, v))) ∧
  (∀ (xs : List Int) (i : Nat) (x : Int), listGet xs i = some x →
    let firstKey : List Int → Jl Nat := fun _ => pure 0
    let iterate : List Int → Option Nat → Jl (Option (Int × Nat)) :=
      fun values state => (listIterator values).run state
    iterateIterableStatePairs (K := Nat) firstKey iterate ⟨xs⟩ (some i) =
      .ok (some ((i, x), i + 1))) ∧
  (∀ (xs : List Int), iterableStatePairsLength (fun ys => pure ys.length) ⟨xs⟩ =
    .ok xs.length) ∧
  (∀ (xs : List Int), reverseIterableStatePairs (fun ys => ys.reverse) ⟨xs⟩ =
    ⟨xs.reverse⟩)

theorem iterableStatePairsSemantics : IterableStatePairsSemantics := by
  refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · intro xs
    refine ⟨?_, emitsExactly_reverseIterableStatePairs xs⟩
    unfold emitsExactly
    rw [enumerateNatFrom_length]
    have h0 : collectPrefix (iterableStatePairsAsIterator xs) (xs.length + 1) none =
        collectPrefix (iterableStatePairsAsIterator xs) (xs.length + 1) (some 0) := rfl
    rw [h0]
    simpa using collectPrefix_iterableStatePairs_at xs (xs.length + 1) 0 (by simp)
  · intro xs i x hx
    simp [iterateIterableStatePairs, listIterator, hx]

def ProductShapeFinite : Prop :=
  ∀ tags, (∀ tag ∈ tags, tag = .hasLength ∨ ∃ n, tag = .hasShape n) →
    productIteratorSizeFold tags = .hasShape (tags.foldl (fun n tag =>
      n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) 0)

theorem foldl_dims_shift (tags : List IteratorSizeTag) (acc : Nat) :
    tags.foldl (fun n tag => n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) acc =
      acc + tags.foldl (fun n tag => n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) 0 := by
  induction tags generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + _), ih (match t with | .hasLength => 1 | .hasShape d => d | _ => 0)]
    omega

theorem productShapeFinite : ProductShapeFinite := by
  intro tags htags
  induction tags with
  | nil => rfl
  | cons a rest ih =>
    have ha := htags a (List.mem_cons_self ..)
    cases rest with
    | nil =>
      rcases ha with rfl | ⟨d, rfl⟩ <;> simp [productIteratorSizeFold, productIteratorSizePair]
    | cons b tail =>
      have hrest : ∀ tag ∈ b :: tail, tag = .hasLength ∨ ∃ n, tag = .hasShape n :=
        fun tag h => htags tag (List.mem_cons_of_mem _ h)
      have ih' := ih hrest
      show productIteratorSizePair a (productIteratorSizeFold (b :: tail)) = _
      rw [ih']
      rcases ha with rfl | ⟨d, rfl⟩
      · simp only [productIteratorSizePair, List.foldl_cons, Nat.zero_add]
        congr 1
        rw [foldl_dims_shift]
        conv => rhs; rw [foldl_dims_shift]
        omega
      · simp only [productIteratorSizePair, List.foldl_cons, Nat.zero_add]
        congr 1
        rw [foldl_dims_shift]
        conv => rhs; rw [foldl_dims_shift]
        omega

def ProductIelSpec : Prop :=
  ∀ tags, productEltypeFold tags = .hasEltype ↔ tags.all (· == .hasEltype)

theorem productIelSpec : ProductIelSpec := by
  intro tags
  induction tags with
  | nil => simp [productEltypeFold]
  | cons a rest ih =>
    cases a with
    | hasEltype =>
      simp [productEltypeFold, ih]
    | eltypeUnknown =>
      simp [productEltypeFold]

theorem sourceMethod1171_listIterators (xss : List (List Int)) :
    sourceMethod1171 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (xss.map listIterator) =
    .ok (xss.map List.length) := by
  induction xss with
  | nil => rfl
  | cons xs rest ih =>
    simp [sourceMethod1171, sourceMethod1173, listIterator, ih]

theorem sourceMethod1179_listIterators (xss : List (List Int)) :
    sourceMethod1179 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (xss.map listIterator) =
    .ok (xss.map List.length) := by
  induction xss with
  | nil => rfl
  | cons xs rest ih =>
    simp [sourceMethod1179, sourceMethod1181, listIterator, ih]

def ProductMethodSemantics : Prop :=
  ProductCorrect ∧
  (productIteratorSizeFold [.hasLength, .hasLength] = .hasShape 2) ∧
  ProductShapeFinite ∧
  ProductIelSpec ∧
  (∀ (xs ys : List Int),
    let revP := reverseProduct (List.map List.reverse) (productModel [xs, ys])
    emitsExactly
      (productAsIterator (productModel (revP.iterators.map listIterator))
        (fun itr st => itr.isdone st) (fun itr st => itr.run st))
      ((ys.flatMap fun y => xs.map fun x => [x, y]).reverse) ∧
    (xs = [] ∨ ys = [] → lastProduct listLastModel (productModel [xs, ys]) = .error .boundsError) ∧
    (xs ≠ [] → ys ≠ [] →
      lastProduct listLastModel (productModel [xs, ys]) =
        listLastModel (ys.flatMap fun y => xs.map fun x => [x, y]))) ∧
  (∀ (xss : List (List Int)),
    sourceMethod1169 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel (xss.map listIterator)) =
        .ok (xss.map List.length) ∧
    sourceMethod1177 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel (xss.map listIterator)) =
        .ok (xss.map List.length) ∧
    sourceMethod1185 (fun iters => sourceMethod1177 (fun itr => itr.size)
      (fun itr => itr.length) (fun itr => itr.iteratorSize) (productModel iters))
      (productModel (xss.map listIterator)) = .ok xss.length) ∧
  (∀ (start step : JInt64),
    let inf := countAsIterator ⟨start, step, (· + ·)⟩
    sourceMethod1169 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel [inf]) =
        .error (.argumentError "Cannot compute size for iterator") ∧
    sourceMethod1177 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel [inf]) =
        .error (.argumentError "Cannot compute indices for iterator")) ∧
  (iterateEmptyProduct (α := Int) = ([], true) ∧
   (∀ s : Bool, iterateEmptyProductState (α := Int) s = none ∧
     isdoneEmptyProductState s = .ok (some true)) ∧
   sourceMethod1188 = .hasEltype ∧
   (∀ (it : IteratorModel Int Nat), sourceMethod1189 (fun i => i.iteratorEltype) it = it.iteratorEltype) ∧
   (∀ (its : List (IteratorModel Int Nat)),
     productIteratorEltype (List.map fun i => i.iteratorEltype) (productModel its) =
       productEltypeFold (its.map fun i => i.iteratorEltype)) ∧
   (∀ (eltype : IteratorModel Int Nat → Type) (tupleOrBottom : List Type → Type)
      (items : List (IteratorModel Int Nat)),
     sourceMethod1197 eltype (productModel ([] : List (IteratorModel Int Nat))) tupleOrBottom =
       tupleOrBottom sourceMethod1198 ∧
     sourceMethod1199 eltype items tupleOrBottom = tupleOrBottom (items.map eltype)))

theorem productMethodSemantics : ProductMethodSemantics := by
  refine ⟨productCorrect, rfl, productShapeFinite, productIelSpec, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩,
    ⟨rfl, fun _ => ⟨rfl, rfl⟩, rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩⟩
  · intro xs ys
    refine ⟨?_, (lastProduct_two_lists xs ys).1, (lastProduct_two_lists xs ys).2⟩
    rw [← flatMap_reverse_map_reverse xs ys (fun x y => [x, y])]
    exact (productCorrect xs.reverse ys.reverse).1
  · intro xss
    refine ⟨sourceMethod1171_listIterators xss, sourceMethod1179_listIterators xss, ?_⟩
    simp [sourceMethod1185, sourceMethod1177, productModel, sourceMethod1179_listIterators]

theorem flatten_reverse_map_reverse {α : Type} (rows : List (List α)) :
    (rows.reverse.map List.reverse).flatten = rows.flatten.reverse := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, ih, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.flatten_cons, List.reverse_append]

theorem flatten_rev_run_some_zero {α O : Type}
    (outer : IteratorModel (IteratorModel α Int) O)
    (so : O) (cur : List α) :
    (flattenAsIterator (flattenModel outer)).run (some (so, reverseListAsIterator cur, ((0 : Nat) : Int))) =
      flattenAdvanceOuter outer so := rfl

theorem flatten_rev_run_some_succ {α O : Type}
    (outer : IteratorModel (IteratorModel α Int) O)
    (so : O) (cur : List α) (m : Nat) (x : α) (hx : listGet cur m = some x) :
    (flattenAsIterator (flattenModel outer)).run (some (so, reverseListAsIterator cur, ((m + 1 : Nat) : Int))) =
      .ok (some (x, (so, reverseListAsIterator cur, (m : Int)))) := by
  unfold flattenAsIterator iterateFlattenState
  simp only [flattenModel, reverseListAsIterator_run_succ cur m x hx, ok_bind, pure_jl]

theorem collectPrefix_flatten_rev_inner {α O : Type}
    (outer : IteratorModel (IteratorModel α Int) O)
    (so : O) (tailFlat : List α)
    (h_adv : ∀ f, tailFlat.length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel outer)) f
        (flattenAdvanceOuter outer so) =
      .ok tailFlat)
    (cur : List α) :
    ∀ (si f : Nat), si ≤ cur.length →
      si + tailFlat.length < f →
      collectPrefix (flattenAsIterator (flattenModel outer)) f
        (some (so, reverseListAsIterator cur, (si : Int))) =
      .ok ((cur.take si).reverse ++ tailFlat) := by
  intro si
  induction si with
  | zero =>
    intro f _ hf
    cases f with
    | zero => omega
    | succ f =>
      rw [collectPrefix_succ, flatten_rev_run_some_zero, List.take_zero, List.reverse_nil, List.nil_append]
      exact h_adv f (by omega)
  | succ m ih =>
    intro f hsi hf
    cases f with
    | zero => omega
    | succ f =>
      obtain ⟨x, hx, hrev⟩ := listGet_take_last cur m (by omega)
      rw [collectPrefix_succ, flatten_rev_run_some_succ outer so cur m x hx]
      simp only [collectAfterStep_some, ih f (by omega) (by omega), ok_bind, pure_jl, hrev, List.cons_append]

theorem flattenAdvanceOuter_rev_list {α : Type} (rows : List (List α)) :
    let outer := generatorAsIterator (sourceMethod1379 reverseListAsIterator reverseListAsIterator (flattenModel rows)).it
    ∀ (k f : Nat), k ≤ rows.length →
      (((rows.take k).reverse.map List.reverse).flatten).length ≤ f →
      collectAfterStep (flattenAsIterator (flattenModel outer)) f
        (flattenAdvanceOuter outer (k : Int)) =
      .ok (((rows.take k).reverse.map List.reverse).flatten) := by
  intro outer k
  induction k with
  | zero =>
    intro f _ _
    rw [flattenAdvanceOuter.eq_def]
    simp [outer, generatorAsIterator, sourceMethod1379, flattenModel, reverseListAsIterator_run_zero]
  | succ m ih =>
    intro f hm hf
    obtain ⟨r, hr, hrev⟩ := listGet_take_last rows m (by omega)
    have houter : outer.run (some ((m + 1 : Nat) : Int)) =
        .ok (some (reverseListAsIterator r, (m : Int))) := by
      show (generatorAsIterator (sourceMethod1379 reverseListAsIterator reverseListAsIterator (flattenModel rows)).it).run (some ((m + 1 : Nat) : Int)) = _
      unfold generatorAsIterator sourceMethod1379 flattenModel
      dsimp only
      rw [reverseListAsIterator_run_succ rows m r hr]
      rfl
    cases hrc : r.reverse with
    | nil =>
      have hrnil : r = [] := List.reverse_eq_nil_iff.mp hrc
      subst hrnil
      have hstep : flattenAdvanceOuter outer ((m + 1 : Nat) : Int) =
          flattenAdvanceOuter outer (m : Int) := by
        conv => lhs; rw [flattenAdvanceOuter.eq_def]
        rw [houter]
        rfl
      have hf' : (((rows.take m).reverse.map List.reverse).flatten).length ≤ f := by
        rw [hrev, List.map_cons, List.reverse_nil, List.flatten_cons, List.nil_append] at hf
        exact hf
      rw [hstep, hrev, List.map_cons, List.reverse_nil, List.flatten_cons, List.nil_append]
      exact ih f (by omega) hf'
    | cons x rx =>
      have hrlen : 0 < r.length := by
        cases r with
        | nil => simp at hrc
        | cons _ _ => simp
      obtain ⟨k_r, hkr⟩ : ∃ k_r, r.length = k_r + 1 := ⟨r.length - 1, by omega⟩
      obtain ⟨x', hx', hrev_r⟩ := listGet_take_last r k_r (by omega)
      rw [← hkr, List.take_length, hrc] at hrev_r
      injection hrev_r with hxx' hrx
      subst hxx'
      rw [hrev, List.map_cons, List.flatten_cons, hrc, List.cons_append, List.length_cons, List.length_append] at hf
      cases f with
      | zero => omega
      | succ f =>
        have hinner0 : (reverseListAsIterator r).run none =
            .ok (some (x, (k_r : Int))) := by
          change (reverseListAsIterator r).run (some (r.length : Int)) = _
          rw [hkr]
          exact reverseListAsIterator_run_succ r k_r x hx'
        have hstep : flattenAdvanceOuter outer ((m + 1 : Nat) : Int) =
            .ok (some (x, ((m : Int), reverseListAsIterator r, (k_r : Int)))) := by
          rw [flattenAdvanceOuter.eq_def, houter]
          dsimp only
          rw [hinner0]
        rw [hstep, collectAfterStep_some, hrev, List.map_cons, List.flatten_cons, hrc, List.cons_append]
        have h_adv : ∀ f', (((rows.take m).reverse.map List.reverse).flatten).length ≤ f' →
            collectAfterStep (flattenAsIterator (flattenModel outer)) f'
              (flattenAdvanceOuter outer (m : Int)) =
            .ok (((rows.take m).reverse.map List.reverse).flatten) :=
          fun f' hf' => ih f' (by omega) hf'
        have hlen_rx : rx.length = k_r := by
          have := congrArg List.length hrx
          simp [List.length_reverse, List.length_take] at this
          omega
        have hinner := collectPrefix_flatten_rev_inner outer (m : Int)
          (((rows.take m).reverse.map List.reverse).flatten) h_adv r k_r (f + 1)
          (by omega) (by omega)
        rw [← hrx] at hinner
        simp only [hinner, ok_bind, pure_jl]

theorem emitsExactly_reverseFlatten {α : Type} (rows : List (List α)) :
    emitsExactly (reverseFlattenAsIterator rows) rows.flatten.reverse := by
  unfold emitsExactly reverseFlattenAsIterator
  let outer := generatorAsIterator (sourceMethod1379 reverseListAsIterator reverseListAsIterator (flattenModel rows)).it
  have houter0 : outer.run none = outer.run (some (rows.length : Int)) := rfl
  have hrun0 : (flattenAsIterator ⟨outer⟩).run none =
      flattenAdvanceOuter outer (rows.length : Int) := by
    dsimp [flattenAsIterator, iterateFlattenStart]
    rw [flattenAdvanceOuter.eq_def, houter0]
    cases outer.run (some (rows.length : Int)) with
    | error _ => rfl
    | ok o =>
      cases o with
      | none => rfl
      | some p =>
        dsimp only [ok_bind]
        cases hp : p.1.run none with
        | error _ => rfl
        | ok v => cases v <;> rfl
  rw [collectPrefix_succ, hrun0, ← flatten_reverse_map_reverse]
  have h := flattenAdvanceOuter_rev_list rows rows.length ((rows.reverse.map List.reverse).flatten).length
    (Nat.le_refl _) (by simp [List.take_length])
  rwa [List.take_length] at h

theorem flatten_iteratorsize_iff (sz : IteratorSizeTag) (eltypeKnown : Bool) (kind : FlattenInnerKind) :
    (sourceMethod1322 sz eltypeKnown kind = .hasLength ↔
      (eltypeKnown = true ∧
        (kind = .emptyTuple ∨
          ((sz = .hasLength ∨ ∃ d, sz = .hasShape d) ∧
            (kind = .bottom ∨ (∃ n, kind = .fixedTuple n) ∨ kind = .number))))) ∧
    (sourceMethod1322 sz eltypeKnown kind ≠ .hasLength →
      sourceMethod1322 sz eltypeKnown kind = .sizeUnknown) := by
  cases sz <;> cases eltypeKnown <;> cases kind <;>
    simp [sourceMethod1322, sourceMethod1318, sourceMethod1319, sourceMethod1320,
      sourceMethod1310, sourceMethod1313, sourceMethod1314, sourceMethod1315, sourceMethod1316]

def FlattenMethodSemantics : Prop :=
  FlattenCorrect ∧ FlattenTupleLength ∧
  (∀ (rows : List (List Int)),
    emitsExactly (reverseFlattenAsIterator rows) rows.flatten.reverse ∧
    lastFlatten
      (fun rf => firstIterModel (flattenAsIterator ⟨generatorAsIterator rf.it⟩))
      (sourceMethod1379 reverseListAsIterator reverseListAsIterator)
      (flattenModel rows) = listLastModel rows.flatten) ∧
  (∀ (sz : IteratorSizeTag) (eltypeKnown : Bool) (kind : FlattenInnerKind),
    (sourceMethod1322 sz eltypeKnown kind = .hasLength ↔
      (eltypeKnown = true ∧
        (kind = .emptyTuple ∨
          ((sz = .hasLength ∨ ∃ d, sz = .hasShape d) ∧
            (kind = .bottom ∨ (∃ n, kind = .fixedTuple n) ∨ kind = .number))))) ∧
    (sourceMethod1322 sz eltypeKnown kind ≠ .hasLength →
      sourceMethod1322 sz eltypeKnown kind = .sizeUnknown)) ∧
  (∀ (sz : IteratorSizeTag) (kind : FlattenInnerKind) (slurp : List FlattenInnerKind),
    sourceMethod1311 sz kind slurp = .error (.methodError "flatten_iteratorsize")) ∧
  (∀ (xs : List Int),
    let f := flattenModel (listIterator xs)
    sourceMethod1332 (fun it => it.length) .bottom checkedMulNatI64 f = .ok 0 ∧
    sourceMethod1332 (fun it => it.length) .emptyTuple checkedMulNatI64 f = .ok 0 ∧
    sourceMethod1332 (fun it => it.length) .number checkedMulNatI64 f = .ok xs.length ∧
    sourceMethod1332 (fun it => it.length) .tuple checkedMulNatI64 f =
      .error (.argumentError "Iterates of the argument to Flatten are not known to have constant length") ∧
    sourceMethod1332 (fun it => it.length) .other checkedMulNatI64 f =
      .error (.argumentError "Iterates of the argument to Flatten are not known to have constant length") ∧
    sourceMethod1325 xs ([] : List Int) = .error (.methodError "flatten_length") ∧
    flattenEmptyLength = 0) ∧
  (∀ (outerTag innerTag : IteratorEltypeTag) (xs : List Int),
    flattenIteratorEltype (fun _ => outerTag) (fun _ => innerTag) id (flattenModel xs) = .hasEltype ↔
      (outerTag = .hasEltype ∧ innerTag = .hasEltype)) ∧
  (∀ (join : Type → Type → Type) (bottom : Type) (items : List Type) (xs : List Int),
    flattenEltype Int (flattenModel xs) = Int ∧
    sourceMethod1298 join bottom items = items.foldl join bottom ∧
    sourceMethod1301 join bottom items = items.foldl join bottom)

theorem flattenMethodSemantics : FlattenMethodSemantics := by
  refine ⟨flattenCorrect, flattenTupleLength, ?_,
    flatten_iteratorsize_iff, fun _ _ _ => rfl, ?_, ?_, fun _ _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  · intro rows
    refine ⟨emitsExactly_reverseFlatten rows, ?_⟩
    unfold lastFlatten
    change firstIterModel (reverseFlattenAsIterator rows) = listLastModel rows.flatten
    rw [firstIterModel_of_emitsExactly _ _ (emitsExactly_reverseFlatten rows),
      head_reverse_eq_listLastModel]
  · intro xs
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp [sourceMethod1332, flattenLengthTuple, checkedMulNatI64, flattenModel]
  · intro outerTag innerTag xs
    cases outerTag <;> cases innerTag <;>
      simp [flattenIteratorEltype, flattenHasEltype, flattenUnknownEltype]

theorem partition_iteratorsize_iff (sz : IteratorSizeTag) (it : PartitionIterator (List Int)) :
    (sourceMethod1461 sz it = .hasLength ↔ (sz = .hasLength ∨ ∃ d, sz = .hasShape d)) ∧
    ((∀ d, sz ≠ .hasShape d) → sourceMethod1461 sz it = sz) := by
  cases sz <;> simp [sourceMethod1461, sourceMethod1459, sourceMethod1460]

def PartitionMethodSemantics : Prop :=
  PartitionVectorCorrect ∧
  (∀ (xs : List Int) (n : JInt64), n.val < 1 →
    partitionModel xs n = .error (.argumentError s!"cannot create partitions of length {n.val}")) ∧
  (∀ (xs : List Int) (n : JInt64), 1 ≤ n.val →
    ∃ p, partitionModel xs n = .ok p ∧
      emitsExactly (partitionVectorAsIterator p) (chunksSpec n.val.toNat xs) ∧
      (partitionVectorAsIterator p).length = .ok ((xs.length + n.val.toNat - 1) / n.val.toNat)) ∧
  (∀ (xs : List Int) (n : Nat), 0 < n → n < 2 ^ 60 →
    emitsExactly (partitionGenericAsIterator xs n) (chunksSpec n xs)) ∧
  (∀ (a b s : JInt64) (n : Nat),
    (s.val > b.val → sourceMethod1470 ⟨(a, b), n⟩ (some s) = none) ∧
    (a.val > b.val → sourceMethod1470 ⟨(a, b), n⟩ none = none) ∧
    (s.val ≤ b.val → 0 < n → (n : Int) < 2 ^ 63 → -(2 ^ 63) < s.val →
      s.val + (n : Int) < 2 ^ 63 → b.val < 2 ^ 63 - 1 →
      ∃ stop r1 : JInt64,
        stop.val = min (s.val + (n : Int) - 1) b.val ∧
        r1.val = stop.val + 1 ∧
        sourceMethod1470 ⟨(a, b), n⟩ (some s) = some ((s, stop), r1))) ∧
  (∀ (sz : IteratorSizeTag) (it : PartitionIterator (List Int)),
    (sourceMethod1461 sz it = .hasLength ↔ (sz = .hasLength ∨ ∃ d, sz = .hasShape d)) ∧
    ((∀ d, sz ≠ .hasShape d) → sourceMethod1461 sz it = sz) ∧
    sourceMethod1455 .hasEltype it = .hasEltype ∧
    sourceMethod1456 it = .eltypeUnknown ∧
    sourceMethod1457 .hasEltype it = .hasEltype) ∧
  (∀ (xs : List Int) (n : Nat),
    sourceMethod1446 id xs n = ⟨xs, n⟩ ∧
    sourceMethod1447 xs n = ⟨xs, n⟩ ∧
    sourceMethod1449 Int (sourceMethod1447 xs n) = List Int ∧
    sourceMethod1451 Int (sourceMethod1447 xs n) = List Int ∧
    sourceMethod1453 List Int (sourceMethod1447 xs n) = List Int)

theorem partitionMethodSemantics : PartitionMethodSemantics := by
  refine ⟨partitionVectorCorrect, ?_, ?_,
    fun xs n hn hbound => emitsExactly_partitionGeneric xs n hn hbound,
    sourceMethod1470_spec,
    fun sz it => ⟨(partition_iteratorsize_iff sz it).1,
      (partition_iteratorsize_iff sz it).2, rfl, rfl, rfl⟩,
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro xs n hn
    simp [partitionModel, hn]
  · intro xs n hn
    have hnot : ¬ n.val < 1 := by omega
    have hpos : 0 < n.val.toNat := by omega
    refine ⟨⟨xs, n.val.toNat⟩, ?_, partitionVectorCorrect xs n.val.toNat hpos⟩
    simp [partitionModel, hnot, jint_convert_i64_self]

theorem approx_iter_type_spec (itrIsBottom : Bool) (nextfn : StatefulVS → StatefulVS) (vs : StatefulVS) :
    (sourceMethod1589 itrIsBottom vs nextfn = vs ↔
      (vs = .bottom ∨ vs = .any ∨
        ∃ tag, vs = .pairOrNothing tag ∧ itrIsBottom = false ∧
          (nextfn vs = .bottom ∨ nextfn vs = .pairOrNothing tag))) ∧
    (∀ tag, vs = .pairOrNothing tag → itrIsBottom = true →
      sourceMethod1589 itrIsBottom vs nextfn = .bottom) ∧
    (∀ tag, vs = .pairOrNothing tag → itrIsBottom = false →
      nextfn vs ≠ .bottom → nextfn vs ≠ .pairOrNothing tag →
      sourceMethod1589 itrIsBottom vs nextfn = .any) := by
  refine ⟨?_, ?_, ?_⟩
  · cases vs with
    | bottom => simp [sourceMethod1589, sourceMethod1597]
    | any => simp [sourceMethod1589, sourceMethod1597]
    | other t => simp [sourceMethod1589, sourceMethod1597]
    | pairOrNothing tag =>
      cases itrIsBottom <;> cases h : nextfn (.pairOrNothing tag) <;>
        simp [sourceMethod1589, sourceMethod1597, h] <;> omega
  · intro tag hvs hb
    subst hvs hb
    rfl
  · intro tag hvs hb hnb hnp
    subst hvs hb
    cases h : nextfn (.pairOrNothing tag) <;>
      simp_all [sourceMethod1589, sourceMethod1597]

def StatefulMethodSemantics : Prop :=
  StatefulConsistent ∧
  (∀ (xs ys : List Int),
    (do
      let s0 ← (sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) : IteratorResult _)
      let (out1, s1) ← collectStateful (fun _ st => (listIterator xs).run st) (xs.length + 1) s0
      let s2 ← (resetStateful (fun _ st => (listIterator xs).run st) s1 : IteratorResult _)
      let (out2, s3) ← collectStateful (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
      let s4 ← (resetStatefulTo (fun (it : IteratorModel Int Nat) st => it.run st) s3 (listIterator ys) : IteratorResult _)
      let (out3, _) ← collectStateful (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
      pure (out1, out2, out3)) = .ok (xs, xs, ys)) ∧
  (∀ (xs : List Int),
    let s : Stateful (IteratorModel Int Nat) (Int × Nat) := ⟨listIterator xs, statefulCurAt xs 0⟩
    sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) .bottom =
      .error (.methodError "typeassert") ∧
    sourceMethod1566 (fun _ st => (listIterator xs).run st) (listIterator xs) =
      sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) ∧
    sourceMethod1605 s = s ∧
    sourceMethod1606 (sourceMethod1569 (fun _ st => (listIterator xs).run st)) (listIterator xs) =
      sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) ∧
    sourceMethod1626 Int s = Int ∧
    sourceMethod1627 .hasEltype s = .hasEltype) ∧
  (∀ (xs : List Int) (x : Int) (i : Nat),
    sourceMethod1592 (fun _ st => (listIterator xs).run st) (listIterator xs) none = .ok none ∧
    sourceMethod1592 (fun _ st => (listIterator xs).run st) (listIterator xs) (some (x, i)) =
      (listIterator xs).run (some i)) ∧
  (∀ (itrIsBottom : Bool) (nextfn : StatefulVS → StatefulVS) (vs : StatefulVS),
    (sourceMethod1589 itrIsBottom vs nextfn = vs ↔
      (vs = .bottom ∨ vs = .any ∨
        ∃ tag, vs = .pairOrNothing tag ∧ itrIsBottom = false ∧
          (nextfn vs = .bottom ∨ nextfn vs = .pairOrNothing tag))) ∧
    (∀ tag, vs = .pairOrNothing tag → itrIsBottom = true →
      sourceMethod1589 itrIsBottom vs nextfn = .bottom) ∧
    (∀ tag, vs = .pairOrNothing tag → itrIsBottom = false →
      nextfn vs ≠ .bottom → nextfn vs ≠ .pairOrNothing tag →
      sourceMethod1589 itrIsBottom vs nextfn = .any)) ∧
  (∀ (tag : IteratorSizeTag),
    (sourceMethod1625 tag = .isInfinite ↔ tag = .isInfinite) ∧
    (tag ≠ .isInfinite → sourceMethod1625 tag = .sizeUnknown))

theorem statefulMethodSemantics : StatefulMethodSemantics := by
  refine ⟨statefulConsistent, ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩, approx_iter_type_spec, ?_⟩
  · intro xs ys
    have h1 := collectStateful_full xs
    have hreset1 : (resetStateful (fun _ st => (listIterator xs).run st) ⟨listIterator xs, none⟩ : IteratorResult _) =
        (sourceMethod1569 (fun _ st => (listIterator xs).run st) (listIterator xs) : IteratorResult _) := rfl
    have hreset2 : (resetStatefulTo (fun (it : IteratorModel Int Nat) st => it.run st) ⟨listIterator xs, none⟩ (listIterator ys) : IteratorResult _) =
        (sourceMethod1569 (fun _ st => (listIterator ys).run st) (listIterator ys) : IteratorResult _) := rfl
    have h2 := collectStateful_full ys
    rw [except_bind_assoc, h1, ok_bind_iter]
    dsimp only
    rw [hreset1, except_bind_assoc, h1, ok_bind_iter]
    dsimp only
    rw [hreset2, except_bind_assoc, h2, ok_bind_iter]
    rfl
  · intro xs
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [sourceMethod1569, listIterator_run_none, listIterator_run_some]
    cases xs <;> rfl
  · intro tag
    cases tag <;> simp [sourceMethod1625]

def OnlyNthMethodSemantics : Prop :=
  OnlyCorrect ∧ NthVectorCorrect ∧
    (∀ (xs : List Int), sourceMethod1661 (listIterator xs) (fun itr st => itr.run st) = onlyModel (listIterator xs)) ∧
    (∀ (x : Int) (rest : List Int),
      sourceMethod1661 (listIterator (x :: rest)) (fun itr st => itr.run st) false = .ok x ∧
      sourceMethod1661 (listIterator ([] : List Int)) (fun itr st => itr.run st) false =
        .error (.methodError "NTuple{2,Any}")) ∧
    (∀ (xs : List Int),
      (xs.length = 1 → ∃ x, xs = [x] ∧
        sourceMethod1673 (fun ys : List Int => pure ys.length) listLastModel xs = .ok x ∧
        sourceMethod1680 (fun ys : List Int => pure ys.length) listLastModel xs = .ok x ∧
        sourceMethod1683 xs = .ok x ∧ sourceMethod1687 xs = .ok x) ∧
      (xs.length ≠ 1 → ∃ m1 m2 m3,
        sourceMethod1673 (fun ys : List Int => pure ys.length) listLastModel xs = .error (.argumentError m1) ∧
        sourceMethod1684 xs = .error (.argumentError m2) ∧
        sourceMethod1688 xs = .error (.argumentError m3)) ∧
      sourceMethod1673 (fun ys : List Int => pure ys.length) listLastModel xs false = listLastModel xs) ∧
    (∀ (xs : List Int) (n : Int), nthGeneric (listIterator xs) n = nthModel (listIterator xs) n) ∧
    (∀ {α S : Type} (itr : IteratorModel α S) (n : Int), nthCurry n (fun it k => nthModel it k) itr = nthModel itr n) ∧
    (∀ (xs ys : List Int) (n : Int),
      if 1 ≤ n ∧ n ≤ min xs.length ys.length then
        ∃ x y, listGet xs (n.toNat - 1) = some x ∧ listGet ys (n.toNat - 1) = some y ∧
          nthZip [listIterator xs, listIterator ys] n = .ok [x, y]
      else
        nthZip [listIterator xs, listIterator ys] n = .error .boundsError) ∧
    (∀ (xs : List Int) (cycles : Nat) (n : JInt64),
      (xs.length : Int) < 2 ^ 63 → (cycles : Int) < 2 ^ 63 → (xs.length : Int) * (cycles : Int) < 2 ^ 63 →
      let ftr : Flatten (Take (Repeated (IteratorModel Int Nat))) :=
        ⟨⟨repeatedModel (listIterator xs), cycles⟩⟩
      let call := sourceMethod1755 .hasLength ftr n.val
        (fun _ it _ => sourceMethod1767
          (fun o => Except.map (fun (l : Nat) => JInt.lit .i64 (Int.ofNat l)) o.length)
          (fun o idx => nthModel o idx.val) it n)
      if 0 < xs.length ∧ 1 ≤ n.val ∧ n.val ≤ (xs.length : Int) * (cycles : Int) then
        ∃ x, listGet xs ((n.val.toNat - 1) % xs.length) = some x ∧ call = .ok x
      else
        call = .error .boundsError) ∧
    (∀ (xs : List Int) (n : Int),
      (xs = [] →
        sourceMethod1754 .hasLength (cycleModel (listIterator xs)) n
          (fun _ c k => sourceMethod1758 (fun it => it.length) nthModel c k) = .error .boundsError) ∧
      (0 < xs.length → n ≤ 0 →
        sourceMethod1754 .hasLength (cycleModel (listIterator xs)) n
          (fun _ c k => sourceMethod1758 (fun it => it.length) nthModel c k) = .error .boundsError) ∧
      (0 < xs.length → 0 < n →
        ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧
          sourceMethod1754 .hasLength (cycleModel (listIterator xs)) n
            (fun _ c k => sourceMethod1758 (fun it => it.length) nthModel c k) = .ok x))

theorem onlyNthMethodSemantics : OnlyNthMethodSemantics := by
  refine ⟨onlyCorrect, nthVectorCorrect, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
    ?_, fun _ _ => rfl, fun _ _ => rfl, nthZip_two_lists, sourceMethod1755_spec, ?_⟩
  · intro xs
    refine ⟨?_, ?_, rfl⟩
    · intro h
      cases xs with
      | nil => simp at h
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x, rfl, rfl, rfl, rfl, rfl⟩
        | cons y ys => simp at h
    · intro h
      cases xs with
      | nil => exact ⟨_, _, _, rfl, rfl, rfl⟩
      | cons x rest =>
        cases rest with
        | nil => exact absurd rfl h
        | cons y ys => exact ⟨_, _, _, rfl, rfl, rfl⟩
  · intro xs n
    refine ⟨?_, ?_, ?_⟩
    · intro hnil; subst hnil; rfl
    · intro hlen hn
      have h0 : ¬ (xs.length = 0) := by omega
      have hnotpos : ¬ (n > 0) := by omega
      simp [sourceMethod1754, sourceMethod1758, cycleModel, listIterator, hnotpos,
        nthModel, nthGeneric, hn]
    · intro hlen hn
      have h0 : ¬ (xs.length = 0) := by omega
      have hStep : sourceMethod1754 .hasLength (cycleModel (listIterator xs)) n
          (fun _ c k => sourceMethod1758 (fun it => it.length) nthModel c k) =
          nthModel (listIterator xs) ((n - 1) % Int.ofNat xs.length + 1) := by
        simp [sourceMethod1754, sourceMethod1758, cycleModel, listIterator, h0, hn]
      rw [hStep]
      let m := (n - 1) % Int.ofNat xs.length + 1
      have hm1 : 1 ≤ m := by
        have hmod : 0 ≤ (n - 1) % (xs.length : Int) :=
          Int.emod_nonneg (n - 1) (by omega)
        change 1 ≤ (n - 1) % (xs.length : Int) + 1
        omega
      have hm2 : m ≤ xs.length := by
        have hmod : (n - 1) % (xs.length : Int) < (xs.length : Int) :=
          Int.emod_lt_of_pos (n - 1) (by omega)
        change (n - 1) % (xs.length : Int) + 1 ≤ (xs.length : Int)
        omega
      have hvec := nthVectorCorrect.2 xs m
      have hm_cond : 1 ≤ m ∧ m ≤ xs.length := ⟨hm1, hm2⟩
      simp only [hm_cond, and_self, ↓reduceIte] at hvec
      obtain ⟨x, hx, hnth, _⟩ := hvec
      have hidx : m.toNat - 1 = (n.toNat - 1) % xs.length := by
        change ((n - 1) % (xs.length : Int) + 1).toNat - 1 = (n.toNat - 1) % xs.length
        have hn_eq : n - 1 = ((n.toNat - 1 : Nat) : Int) := by omega
        have hmod_eq : (n - 1) % (xs.length : Int) = (((n.toNat - 1) % xs.length : Nat) : Int) := by
          rw [hn_eq, Int.natCast_emod]
        rw [hmod_eq]
        omega
      rw [hidx] at hx
      exact ⟨x, hx, hnth⟩

inductive TrueLen where
  | fin (n : Nat)
  | inf
  deriving Repr, DecidableEq

def AgreeSize : IteratorSizeTag → TrueLen → Prop
  | .hasLength, .fin _ => True
  | .hasShape _, .fin _ => True
  | .isInfinite, .inf => True
  | .sizeUnknown, _ => True
  | _, _ => False

def TrueLen.min : TrueLen → TrueLen → TrueLen
  | .fin a, .fin b => .fin (Nat.min a b)
  | .fin a, .inf => .fin a
  | .inf, l => l

def zipTrueLen : List TrueLen → TrueLen
  | [] => .inf
  | l :: ls => TrueLen.min l (zipTrueLen ls)

def AgreeSizeAll : List IteratorSizeTag → List TrueLen → Prop
  | [], [] => True
  | a :: as, l :: ls => AgreeSize a l ∧ AgreeSizeAll as ls
  | _, _ => False

theorem agree_zipIteratorSizePair (a b : IteratorSizeTag) (la lb : TrueLen)
    (ha : AgreeSize a la) (hb : AgreeSize b lb) :
    AgreeSize (zipIteratorSizePair a b) (TrueLen.min la lb) := by
  cases a <;> cases b <;> cases la <;> cases lb <;>
    try simp_all [zipIteratorSizePair, AgreeSize, TrueLen.min]
  rename_i m n _ _
  by_cases h : m = n <;> simp [h]

def isFiniteSizeTag : IteratorSizeTag → Bool
  | .hasLength => true
  | .hasShape _ => true
  | _ => false

def AndTraitsSpec : Prop :=
  (∀ a b : IteratorSizeTag, andIteratorSizeDispatch a b = andIteratorSizeDispatch b a) ∧
  (∀ a : IteratorSizeTag, andIteratorSizeDispatch a a = a) ∧
  (∀ a b : IteratorSizeTag,
    isFiniteSizeTag (andIteratorSizeDispatch a b) = (isFiniteSizeTag a && isFiniteSizeTag b)) ∧
  (∀ (a b : IteratorSizeTag) (n : Nat),
    andIteratorSizeDispatch a b = .hasShape n ↔ a = .hasShape n ∧ b = .hasShape n) ∧
  (∀ a b : IteratorSizeTag,
    andIteratorSizeDispatch a b = .isInfinite ↔ a = .isInfinite ∧ b = .isInfinite) ∧
  (∀ a b : IteratorEltypeTag,
    andIteratorEltypeDispatch a b = andIteratorEltypeDispatch b a ∧
    (andIteratorEltypeDispatch a b = .hasEltype ↔ a = .hasEltype ∧ b = .hasEltype))

theorem andTraitsSpec : AndTraitsSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> try rfl
    rename_i m n
    simp only [andIteratorSizeDispatch, andIteratorSizeSameShape, andIteratorSizeShapeShape]
    by_cases h : m = n
    · subst h; simp
    · have h' : n ≠ m := Ne.symm h
      simp [h, h']
  · intro a
    cases a <;> simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape]
  · intro a b
    cases a <;> cases b <;> try rfl
    rename_i m n
    simp only [andIteratorSizeDispatch]
    split <;> rfl
  · intro a b n
    cases a <;> cases b <;> simp [andIteratorSizeDispatch, andIteratorSizeSame,
      andIteratorSizeLengthShape, andIteratorSizeShapeLength, andIteratorSizeSameShape,
      andIteratorSizeShapeShape, andIteratorSizeOther]
    rename_i p q
    by_cases h : p = q
    · subst h; simp
    · simp [h]; omega
  · intro a b
    cases a <;> cases b <;> simp [andIteratorSizeDispatch, andIteratorSizeSame,
      andIteratorSizeLengthShape, andIteratorSizeShapeLength, andIteratorSizeSameShape,
      andIteratorSizeShapeShape, andIteratorSizeOther]
    rename_i p q
    split <;> simp
  · intro a b
    cases a <;> cases b <;> decide

def ZipTraitsSound : Prop :=
  (∀ (cs : List IteratorSizeTag) (ls : List TrueLen),
    AgreeSizeAll cs ls → AgreeSize (zipIteratorSizeFold cs) (zipTrueLen ls)) ∧
  (∀ tags : List IteratorEltypeTag,
    zipIteratorEltypeFold tags = .hasEltype ↔ tags.all (· == .hasEltype)) ∧
  (∀ (is : List (IteratorModel Int Nat)),
    zipIteratorSize (zipModel is) = zipIteratorSizeFold (is.map fun itr => itr.iteratorSize) ∧
    zipIteratorEltype (zipModel is) = zipIteratorEltypeFold (is.map fun itr => itr.iteratorEltype)) ∧
  zipIteratorSizeEmpty = .isInfinite ∧
  zipIteratorEltypeEmpty = .hasEltype ∧
  (∀ t, zipIteratorSizeOne t = t) ∧
  (∀ t, zipIteratorEltypeOne t = t) ∧
  (∀ a b, zipIteratorSizeTwo a b = andIteratorSizeDispatch a b) ∧
  (∀ a b, zipIteratorSizeLengthInfinite a b = .hasLength ∧
    zipIteratorSizeShapeInfinite a b = .hasLength ∧
    zipIteratorSizeInfiniteOther a b = zipIteratorSizePair b a ∧
    zipIteratorSizeInfiniteInfinite a b = .isInfinite) ∧
  (∀ a rest, zipIteratorSizeMany a rest = zipIteratorSizePair a (zipIteratorSizeFold rest)) ∧
  (∀ a rest, zipIteratorEltypeMany a rest = zipIteratorEltypeFold (a :: rest))

theorem zipTraitsSound : ZipTraitsSound := by
  refine ⟨?_, ?_, ?_, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, ?_⟩
  · intro cs
    induction cs with
    | nil =>
      intro ls h
      cases ls with
      | nil => trivial
      | cons _ _ => exact absurd h id
    | cons a as ih =>
      intro ls h
      cases ls with
      | nil => exact absurd h id
      | cons l ls =>
        obtain ⟨ha, hs⟩ := h
        cases as with
        | nil =>
          cases ls with
          | nil =>
            show AgreeSize a (TrueLen.min l .inf)
            cases l <;> exact ha
          | cons _ _ => exact absurd hs id
        | cons b bs =>
          exact agree_zipIteratorSizePair a _ l _ ha (ih ls hs)
  · intro tags
    induction tags with
    | nil => simp [zipIteratorEltypeFold]
    | cons a rest ih =>
      cases rest with
      | nil => cases a <;> simp [zipIteratorEltypeFold]
      | cons b tail =>
        cases a with
        | hasEltype =>
          change (if zipIteratorEltypeFold (b :: tail) == .hasEltype then IteratorEltypeTag.hasEltype else .eltypeUnknown) = .hasEltype ↔
            (true && (b :: tail).all (· == .hasEltype)) = true
          rw [Bool.true_and, ← ih]
          cases zipIteratorEltypeFold (b :: tail) <;> decide
        | eltypeUnknown => simp [zipIteratorEltypeFold]
  · intro is
    cases is with
    | nil => exact ⟨rfl, rfl⟩
    | cons a rest =>
      cases rest with
      | nil =>
        refine ⟨rfl, ?_⟩
        cases a.iteratorEltype <;> rfl
      | cons b tail => exact ⟨rfl, rfl⟩
  · intro a rest
    cases rest with
    | nil => cases a <;> rfl
    | cons b tail => rfl

def ZipMetadata : Prop :=
  (sourceMethod394 = .ok none) ∧
  (∀ (xs ys : List Int),
    let inf : IteratorModel Int Nat := { listIterator xs with iteratorSize := .isInfinite }
    sourceMethod385 (listIterator xs) [inf, listIterator ys] =
      .ok (some (min xs.length ys.length)) ∧
    sourceMethod385 inf [inf] = .ok none) ∧
  (∀ (xs ys : List Int), (zipListModel xs ys).length = .ok (min xs.length ys.length)) ∧
  (∀ (xs ys : List Int),
    zipLengthsFiniteEqual [listIterator xs, listIterator ys] =
      .ok (decide (xs.length = ys.length), some xs.length) ∧
    zipLengthsFiniteEqualEmpty = (true, none)) ∧
  (∀ (xs ys : List Int),
    sourceMethod412 (fun itr => itr.size) promoteSizeShape1D
      (zipModel [listIterator xs, listIterator ys]) = .ok [min xs.length ys.length] ∧
    sourceMethod413 (fun itr => itr.size) (promoteAxesShape1D min)
      (zipModel [listIterator xs, listIterator ys]) = .ok [min xs.length ys.length]) ∧
  (∀ (xs ys zs : List Int),
    sourceMethod412 (fun itr => itr.size) promoteSizeShape1D
      (zipModel [listIterator xs, listIterator ys, listIterator zs]) =
        .ok [min xs.length (min ys.length zs.length)] ∧
    sourceMethod413 (fun itr => itr.size) (promoteAxesShape1D min)
      (zipModel [listIterator xs, listIterator ys, listIterator zs]) =
        .ok [min xs.length (min ys.length zs.length)]) ∧
  (∀ (its : List (IteratorModel Int Nat)) (eltype : IteratorModel Int Nat → Type)
    (tupleOrBottom : List Type → Type),
    sourceMethod425 id eltype tupleOrBottom (zipModel its) = tupleOrBottom (its.map eltype)) ∧
  (∀ (xs ys : List Int), ((min xs.length ys.length : Nat) : Int) < 2 ^ 63 →
    let call := sourceMethod519 (zipModel [listIterator xs, listIterator ys])
      (fun is => Except.map (fun (n : Nat) => JInt.lit .i64 (Int.ofNat n)) (zipLength ⟨is⟩))
      (fun itr n => nthModel itr n.val)
    if 0 < min xs.length ys.length then
      ∃ x y, listGet xs (min xs.length ys.length - 1) = some x ∧
        listGet ys (min xs.length ys.length - 1) = some y ∧
        call = .ok [x, y]
    else
      call = .error .boundsError)

theorem zipMetadata : ZipMetadata := by
  refine ⟨rfl, ?_, fun xs ys => (zipCorrect xs ys).2, ?_, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, sourceMethod519_two_lists⟩
  · intro xs ys
    refine ⟨?_, rfl⟩
    show Except.ok (some (min ys.length xs.length)) = Except.ok (some (min xs.length ys.length))
    rw [Nat.min_comm]
  · intro xs ys
    refine ⟨?_, rfl⟩
    unfold zipLengthsFiniteEqual
    dsimp only [listIterator, ok_bind, pure_jl]
    unfold zipLengthsFiniteEqual
    dsimp only [listIterator, ok_bind, pure_jl]
    unfold zipLengthsFiniteEqual
    by_cases h : xs.length = ys.length
    · simp [h]
    · have h' : ¬ (ys.length = xs.length) := fun he => h he.symm
      simp [h, h']

def LengthHelpersSpec : Prop :=
  (∀ (xs ys : List Int),
    minLengthOtherOther List.length xs ys = (List.zipWith Prod.mk xs ys).length ∧
    diffLengthOtherOther List.length xs ys = (xs.drop ys.length).length) ∧
  (∀ (a b : Nat), minLengthInfiniteInfinite (fun n => n) a b = min a b) ∧
  (∀ (a b : Nat), minLengthOtherInfinite (fun n => n) a b = a) ∧
  (∀ (a b : Nat), minLengthInfiniteOther (fun n => n) a b = b) ∧
  (∀ (a b : Nat), minLengthOtherOther (fun n => n) a b = min a b) ∧
  (∀ (a b : Nat), diffLengthOtherInfinite (fun n => n) a b = 0) ∧
  (∀ (a b : Nat), diffLengthInfiniteInfinite (fun n => n) a b = 0) ∧
  (∀ (a b : Nat), diffLengthInfiniteOther (fun n => n) a b = a) ∧
  (∀ (a b : Nat), diffLengthOtherOther (fun n => n) a b = a - b)

theorem lengthHelpersSpec : LengthHelpersSpec := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  · intro xs ys
    refine ⟨by simp [minLengthOtherOther], ?_⟩
    simp only [diffLengthOtherOther, List.length_drop]
    split <;> omega
  · intro a b
    simp only [diffLengthOtherOther]
    split <;> omega

def TakeSound : Prop :=
  (∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    emitsExactly (takeAsIterator base ⟨base, n⟩) (xs.take n)) ∧
  (∀ (xs : List Int) (n : Int), n < 0 →
    mkTake (listIterator xs) n = .error (.argumentError "Take length must be non-negative")) ∧
  (∀ (it : IteratorSizeTag), takeIteratorSize it = .hasLength ∧
    takeIteratorSizeUnknown it = .sizeUnknown) ∧
  (∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    takeIteratorSizeOf (fun i => i.iteratorSize) ⟨base, n⟩ = .hasLength ∧
    takeIteratorEltype (fun i => i.iteratorEltype) ⟨base, n⟩ = .hasEltype) ∧
  (∀ (xs : List Int) (n rem i : Nat),
    let itr := takeAsIterator (listIterator xs) ⟨listIterator xs, n⟩
    itr.isdone (some (rem, i)) = .ok (some (decide (rem = 0 ∨ xs.length ≤ i))) ∧
    (itr.isdone (some (rem, i)) = .ok (some true) ↔ itr.run (some (rem, i)) = .ok none))

theorem takeSound : TakeSound := by
  refine ⟨emitsExactly_take, ?_, fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  · intro xs n hn
    simp [mkTake, hn]
  · intro xs n rem i
    refine ⟨?_, ?_⟩
    · simp only [takeAsIterator, takeIsdoneState, listIterator_isdone_some, ok_bind,
        pure_jl, boolOrMissing, Nat.le_zero_eq]
      by_cases hr : rem = 0 <;> by_cases hi : xs.length ≤ i <;> simp [hr, hi]
    · simp only [takeAsIterator_run_some]
      have hd : (takeAsIterator (listIterator xs) ⟨listIterator xs, n⟩).isdone (some (rem, i)) =
          .ok (some (decide (rem = 0 ∨ xs.length ≤ i))) := by
        simp only [takeAsIterator, takeIsdoneState, listIterator_isdone_some, ok_bind,
          pure_jl, boolOrMissing, Nat.le_zero_eq]
        by_cases hr : rem = 0 <;> by_cases hi : xs.length ≤ i <;> simp [hr, hi]
      rw [hd]
      by_cases hr : rem = 0
      · simp [hr]
      · simp only [hr, false_or, ↓reduceIte]
        cases hdrop : xs.drop i with
        | nil =>
          have hi : xs.length ≤ i := List.drop_eq_nil_iff.mp hdrop
          simp [hi]
        | cons x rest =>
          have hnot : ¬ xs.length ≤ i := by
            intro hi; rw [List.drop_eq_nil_iff.mpr hi] at hdrop; cases hdrop
          simp [hnot]

theorem collectPrefix_dropTake_at {α : Type} (xs : List α) (d n : Nat) :
    ∀ (fuel m i : Nat), min m (xs.drop i).length < fuel →
      collectPrefix (dropTakeAsIterator (listIterator xs) ⟨⟨listIterator xs, d⟩, n⟩) fuel (some (m, i)) =
        .ok ((xs.drop i).take m) := by
  intro fuel
  induction fuel with
  | zero => intro m i hf; omega
  | succ fuel ih =>
    intro m i hf
    by_cases hm : m = 0
    · subst hm
      simp [collectPrefix, dropTakeAsIterator, takeAsIterator, iterateTake]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hrun : (dropTakeAsIterator (listIterator xs) ⟨⟨listIterator xs, d⟩, n⟩).run (some (k + 1, i)) =
          match xs.drop i with
          | [] => .ok none
          | x :: _ => .ok (some (x, (k, i + 1))) := by
        simp only [dropTakeAsIterator, takeAsIterator, iterateTake, dropAsIterator, iterateDrop,
          Nat.le_zero_eq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, listIterator_run_some]
        cases xs.drop i <;> rfl
      rw [collectPrefix_succ, hrun]
      cases hd : xs.drop i with
      | nil => simp
      | cons x rest =>
        have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
        have hlen : min k (xs.drop (i + 1)).length < fuel := by
          rw [hdrop]; simp [hd] at hf; omega
        simp only [collectAfterStep_some, ih k (i + 1) hlen, ok_bind, pure_jl, hdrop, List.take_succ_cons]

theorem emitsExactly_dropTake {α : Type} (xs : List α) (d m : Nat) :
    emitsExactly (dropTakeAsIterator (listIterator xs) ⟨⟨listIterator xs, d⟩, m⟩) ((xs.drop d).take m) := by
  unfold emitsExactly
  have h0 : (dropTakeAsIterator (listIterator xs) ⟨⟨listIterator xs, d⟩, m⟩).run none =
      (dropTakeAsIterator (listIterator xs) ⟨⟨listIterator xs, d⟩, m⟩).run (some (m, d)) := by
    simp only [dropTakeAsIterator, takeAsIterator, iterateTake, dropAsIterator, iterateDrop]
    by_cases hm : m ≤ 0
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      have h := dropAdvance_listIterator xs d none
      simp only [Option.getD_none, Nat.zero_add] at h
      rw [h]
  rw [collectPrefix_succ, h0, ← collectPrefix_succ]
  exact collectPrefix_dropTake_at xs d m (((xs.drop d).take m).length + 1) m d
    (by rw [List.length_take]; omega)

def DropSound : Prop :=
  (∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    emitsExactly (dropAsIterator base ⟨base, n⟩) (xs.drop n)) ∧
  (∀ (xs : List Int) (n : Int), n < 0 →
    mkDrop (listIterator xs) n = .error (.argumentError "Drop length must be non-negative")) ∧
  (∀ (xs : List Int) (a : Nat) (b : JInt64), a < 2 ^ 63 → 0 ≤ b.val →
    ∃ td, dropTakeModel ⟨listIterator xs, a⟩ b.val = .ok td ∧
      emitsExactly (dropTakeAsIterator (listIterator xs) td) ((xs.drop b.val.toNat).take (a - b.val.toNat))) ∧
  (∀ (xs : List Int) (a : Nat) (b : JInt64), b.val < 0 →
    dropTakeModel ⟨listIterator xs, a⟩ b.val =
      .error (.argumentError "Drop length must be non-negative")) ∧
  (∀ (it : IteratorSizeTag), dropIteratorSizeFinite it = .hasLength ∧
    dropIteratorSizeUnknown it = .sizeUnknown ∧
    dropIteratorSizeInfinite it = .isInfinite) ∧
  (∀ (xs : List Int) (n : Nat),
    let base := listIterator xs
    dropIteratorSizeOf (fun i => i.iteratorSize) ⟨base, n⟩ = .hasLength ∧
    dropIteratorEltype (fun i => i.iteratorEltype) ⟨base, n⟩ = .hasEltype)

theorem dropSound : DropSound := by
  refine ⟨emitsExactly_drop, ?_, ?_, ?_, fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro xs n hn
    simp [mkDrop, hn]
  · intro xs a b ha hb
    have hnotneg : ¬ b.val < 0 := by omega
    refine ⟨⟨⟨listIterator xs, b.val.toNat⟩, a - b.val.toNat⟩, ?_,
      emitsExactly_dropTake xs b.val.toNat (a - b.val.toNat)⟩
    have hb_hi : b.val < 2 ^ 63 := by
      have := b.property.2
      change b.val ≤ 2 ^ 63 - 1 at this
      omega
    have ha_wrap : (JInt.lit .i64 (a : Int)).val = (a : Int) :=
      wrapInt_of_inRange .i64 (a : Int) (by
        change -(2 ^ 63 : Int) ≤ (a : Int) ∧ (a : Int) ≤ 2 ^ 63 - 1; omega)
    have hdiff_range : IntTy.i64.min ≤ (a : Int) - b.val ∧ (a : Int) - b.val ≤ IntTy.i64.max := by
      change -(2 ^ 63 : Int) ≤ (a : Int) - b.val ∧ (a : Int) - b.val ≤ 2 ^ 63 - 1
      omega
    have hsub_val : ((JInt.lit .i64 (a : Int)) - b).val = (a : Int) - b.val := by
      change wrapInt .i64 ((JInt.lit .i64 (a : Int)).val - b.val) = _
      rw [ha_wrap]
      exact wrapInt_of_inRange .i64 ((a : Int) - b.val) hdiff_range
    have hrem_val : (JInt.wrap .i64 ((JInt.lit .i64 (a : Int)) - b).val).val = (a : Int) - b.val := by
      change wrapInt .i64 ((JInt.lit .i64 (a : Int)) - b).val = _
      rw [hsub_val]
      exact wrapInt_of_inRange .i64 ((a : Int) - b.val) hdiff_range
    unfold dropTakeModel
    rw [jint_convert_i64_self, ok_bind]
    simp only [mkDrop, hnotneg, ↓reduceIte, ok_bind, hrem_val, mkTake]
    by_cases hgt : b.val < (a : Int)
    · have hnn : ¬ ((a : Int) - b.val) < 0 := by omega
      have htonat : ((a : Int) - b.val).toNat = a - b.val.toNat := by omega
      simp [hgt, hnn, htonat]
    · have htonat : a - b.val.toNat = 0 := by omega
      simp [hgt, htonat]
  · intro xs a b hb
    simp [dropTakeModel, jint_convert_i64_self, mkDrop, hb]

def CountfromInts : Prop :=
  CountfromCorrect ∧
  (∀ (start : JInt64) (k : Nat),
    let c1 := countfromOneunit (fun _ => JInt.lit .i64 1) (fun a b => a + b) start
    collectPrefix (countAsIterator c1) k none = .ok (countChain start (JInt.lit .i64 1) k)) ∧
  (∀ (k : Nat),
    collectPrefix (countAsIterator countfromDefault) k none =
      .ok (countChain (JInt.lit .i64 1) (JInt.lit .i64 1) k)) ∧
  countIteratorSize = .isInfinite

theorem countfromInts : CountfromInts :=
  ⟨countfromCorrect, fun start k => (countfromCorrect start (JInt.lit .i64 1) k).1,
    fun k => (countfromCorrect (JInt.lit .i64 1) (JInt.lit .i64 1) k).1, rfl⟩

theorem filterAsIterator_run_nil {α : Type} (xs : List α) (p : α → Bool) (i : Nat)
    (hd : xs.drop i = []) :
    (filterAsIterator (listIterator xs) p).run (some i) = .ok none := by
  dsimp [filterAsIterator]
  rw [iterateFilter.eq_def]
  simp [listIterator_run_some, hd]

theorem filterAsIterator_run_pos {α : Type} (xs : List α) (p : α → Bool) (i : Nat)
    (x : α) (rest : List α) (hd : xs.drop i = x :: rest) (hp : p x = true) :
    (filterAsIterator (listIterator xs) p).run (some i) = .ok (some (x, i + 1)) := by
  dsimp [filterAsIterator]
  rw [iterateFilter.eq_def]
  simp [listIterator_run_some, hd, hp]

theorem filterAsIterator_run_neg {α : Type} (xs : List α) (p : α → Bool) (i : Nat)
    (x : α) (rest : List α) (hd : xs.drop i = x :: rest) (hp : p x = false) :
    (filterAsIterator (listIterator xs) p).run (some i) =
      (filterAsIterator (listIterator xs) p).run (some (i + 1)) := by
  conv => lhs; dsimp [filterAsIterator]; rw [iterateFilter.eq_def]
  simp [listIterator_run_some, hd, hp, filterAsIterator]

theorem collectPrefix_filter_at {α : Type} (xs : List α) (p : α → Bool) :
    ∀ (k i fuel : Nat), (xs.drop i).length ≤ k → ((xs.drop i).filter p).length < fuel →
      collectPrefix (filterAsIterator (listIterator xs) p) fuel (some i) =
        .ok ((xs.drop i).filter p) := by
  intro k
  induction k with
  | zero =>
    intro i fuel hk hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hnil : xs.drop i = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [collectPrefix, filterAsIterator_run_nil xs p i hnil, hnil]
  | succ k ih =>
    intro i fuel hk hf
    cases hd : xs.drop i with
    | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [collectPrefix, filterAsIterator_run_nil xs p i hd]
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hk' : (xs.drop (i + 1)).length ≤ k := by
        have hlt : (xs.drop (i + 1)).length < (xs.drop i).length := by
          rw [hd, hdrop, List.length_cons]; omega
        omega
      by_cases hp : p x
      · cases fuel with
        | zero => omega
        | succ fuel =>
          have hf' : ((xs.drop (i + 1)).filter p).length < fuel := by
            rw [hdrop]; simp [hd, hp] at hf; omega
          simp [collectPrefix, filterAsIterator_run_pos xs p i x rest hd hp,
            ih (i + 1) fuel hk' hf', hdrop, hp]
      · have hp' : p x = false := Bool.eq_false_iff.mpr hp
        have hstep : collectPrefix (filterAsIterator (listIterator xs) p) fuel (some i) =
            collectPrefix (filterAsIterator (listIterator xs) p) fuel (some (i + 1)) := by
          cases fuel with
          | zero => rfl
          | succ fuel => simp [collectPrefix, filterAsIterator_run_neg xs p i x rest hd hp']
        have hf' : ((xs.drop (i + 1)).filter p).length < fuel := by
          rw [hdrop]; simpa [hd, hp] using hf
        rw [hstep, ih (i + 1) fuel hk' hf', hdrop]
        simp [hp]

theorem emitsExactly_filter {α : Type} (xs : List α) (p : α → Bool) :
    emitsExactly (filterAsIterator (listIterator xs) p) (xs.filter p) := by
  unfold emitsExactly
  have hrun0 : (filterAsIterator (listIterator xs) p).run none =
      (filterAsIterator (listIterator xs) p).run (some 0) := by
    conv => lhs; dsimp [filterAsIterator]; rw [iterateFilter.eq_def]
    conv => rhs; dsimp [filterAsIterator]; rw [iterateFilter.eq_def]
    rfl
  have hstep : collectPrefix (filterAsIterator (listIterator xs) p) ((xs.filter p).length + 1) none =
      collectPrefix (filterAsIterator (listIterator xs) p) ((xs.filter p).length + 1) (some 0) := by
    simp [collectPrefix, hrun0]
  rw [hstep]
  simpa using collectPrefix_filter_at xs p xs.length 0 ((xs.filter p).length + 1) (by simp) (by simp)

def FilterSound : Prop :=
  ∀ (xs : List Int) (p : Int → Bool),
    let f := sourceMethod576 p (listIterator xs)
    let rf := reverseFilter List.reverse (sourceMethod576 p xs)
    emitsExactly (filterAsIterator (listIterator xs) p) (xs.filter p) ∧
    emitsExactly (filterAsIterator (listIterator rf.itr) rf.flt) (xs.filter p).reverse ∧
    lastFilter (fun g => firstIterModel (filterAsIterator (listIterator g.itr) g.flt))
      (reverseFilter List.reverse) (sourceMethod576 p xs) = listLastModel (xs.filter p) ∧
    filterEltype Int f = Int ∧
    filterIteratorSize = .sizeUnknown ∧
    filterIteratorEltype (fun i => i.iteratorEltype) f = .hasEltype ∧
    rf.itr = xs.reverse

theorem filterSound : FilterSound := by
  intro xs p
  have hrev_emit : emitsExactly (filterAsIterator (listIterator xs.reverse) p) (xs.filter p).reverse := by
    rw [← List.filter_reverse]
    exact emitsExactly_filter xs.reverse p
  refine ⟨emitsExactly_filter xs p, hrev_emit, ?_, rfl, rfl, rfl, rfl⟩
  unfold lastFilter reverseFilter sourceMethod576
  dsimp only
  rw [firstIterModel_of_emitsExactly _ _ hrev_emit, head_reverse_eq_listLastModel]

def AccumulateSound : Prop :=
  AccumulateCorrect ∧
  (∀ (f : Int → Int → Int) (init : Option Int) (xs : List Int),
    let acc := accumulateModel f (listIterator xs) init
    accumulateLength (fun i => i.length) acc = .ok xs.length ∧
    accumulateSize (fun i => i.size) acc = .ok [xs.length] ∧
    accumulateIteratorSize (fun i => i.iteratorSize) acc = .hasLength ∧
    accumulateIteratorEltype = .eltypeUnknown)

theorem accumulateSound : AccumulateSound :=
  ⟨accumulateCorrect, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem collectPrefix_rest_at {α : Type} (xs : List α) (st fuel i : Nat)
    (hf : (xs.drop i).length < fuel) :
    collectPrefix (restAsIterator (restWithState (listIterator xs) st)) fuel (some i) =
      .ok (xs.drop i) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    have hrun : (restAsIterator (restWithState (listIterator xs) st)).run (some i) =
        (listIterator xs).run (some i) := rfl
    simp only [collectPrefix, hrun, listIterator_run_some]
    cases hd : xs.drop i with
    | nil => rfl
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hlen : (xs.drop (i + 1)).length < fuel := by rw [hdrop]; simp [hd] at hf; omega
      simp only [ok_bind, pure_jl, ih (i + 1) hlen, hdrop]

theorem emitsExactly_rest {α : Type} (xs : List α) (i : Nat) :
    emitsExactly (restAsIterator (restWithState (listIterator xs) i)) (xs.drop i) := by
  unfold emitsExactly
  have h0 : collectPrefix (restAsIterator (restWithState (listIterator xs) i)) ((xs.drop i).length + 1) none =
      collectPrefix (restAsIterator (restWithState (listIterator xs) i)) ((xs.drop i).length + 1) (some i) := rfl
  rw [h0]
  exact collectPrefix_rest_at xs i ((xs.drop i).length + 1) i (Nat.lt_succ_self _)

def RestSound : Prop :=
  (∀ (xs : List Int) (i : Nat),
    emitsExactly (restAsIterator (restWithState (listIterator xs) i)) (xs.drop i)) ∧
  (∀ {I S α : Type} (itr : Rest I S)
    (iterate : I → Option S → Jl (Option (α × S))),
      iterateRest iterate itr none = iterate itr.itr (some itr.st) ∧
      (∀ s, iterateRest iterate itr (some s) = iterate itr.itr (some s))) ∧
  (∀ {I S T : Type} (itr : I) (s : S) (t : T),
    restOnRest (restWithState itr s) t = restWithState itr t ∧
    restIdentity itr = itr) ∧
  (∀ {I S : Type} (r : Rest I S) (tag : IteratorSizeTag),
    (sourceMethod739 tag r = .isInfinite ↔ tag = .isInfinite) ∧
    (tag ≠ .isInfinite → sourceMethod739 tag r = .sizeUnknown) ∧
    sourceMethod738 tag = .isInfinite ∧
    sourceMethod737 tag = .sizeUnknown)

theorem restSound : RestSound := by
  refine ⟨emitsExactly_rest, fun _ _ => ⟨rfl, fun _ => rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  intro I S r tag
  cases tag <;> simp [sourceMethod739, sourceMethod738, sourceMethod737]

def WhileSound : Prop :=
  TakeWhileDropWhile ∧
  (∀ (p : Int → Bool) (xs : List Int),
    let tw := takewhileModel p (listIterator xs)
    let dw := dropwhileModel p (listIterator xs)
    takewhileIteratorSize = .sizeUnknown ∧
    takewhileIteratorEltype (fun i => i.iteratorEltype) tw = .hasEltype ∧
    dropwhileIteratorSize = .sizeUnknown ∧
    dropwhileIteratorEltype (fun i => i.iteratorEltype) dw = .hasEltype)

theorem whileSound : WhileSound :=
  ⟨takeWhileDropWhile, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem collectPrefix_reverseEnumerate_at {α : Type} (xs : List α) :
    ∀ (k fuel : Nat), k ≤ xs.length → k < fuel →
      collectPrefix (reverseEnumerateAsIterator xs) fuel
        (some (k, reverseListAsIterator xs, (k : Int))) =
      .ok (((enumerateNatFrom 1 (xs.take k)).reverse).map fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)) := by
  intro k
  induction k with
  | zero =>
    intro fuel _ hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [collectPrefix, reverseEnumerateAsIterator, sourceMethod228,
        reverseListAsIterator_run_zero, enumerateNatFrom]
  | succ m ih =>
    intro fuel hm hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
      have hrev := enumerateNatFrom_take_succ xs 1 m x hx (by omega)
      have h1m : 1 + m = m + 1 := by omega
      rw [h1m] at hrev
      have hrun : (reverseEnumerateAsIterator xs).run
          (some (m + 1, reverseListAsIterator xs, ((m + 1 : Nat) : Int))) =
          .ok (some ((JInt.lit .i64 (Int.ofNat (m + 1)), x), (m, reverseListAsIterator xs, (m : Int)))) := by
        unfold reverseEnumerateAsIterator sourceMethod228
        dsimp only
        rw [reverseListAsIterator_run_succ xs m x hx, ok_bind, pure_jl]
        rfl
      rw [collectPrefix_succ, hrun, collectAfterStep_some]
      simp only [ih fuel (by omega) (by omega), ok_bind, pure_jl, hrev, List.map_cons]

theorem emitsExactly_reverseEnumerate {α : Type} (xs : List α) :
    emitsExactly (reverseEnumerateAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)) := by
  unfold emitsExactly
  have hlen : (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)).length = xs.length := by
    rw [List.length_map, List.length_reverse, enumerateNatFrom_length]
  have h0 : (reverseEnumerateAsIterator xs).run none =
      (reverseEnumerateAsIterator xs).run (some (xs.length, reverseListAsIterator xs, (xs.length : Int))) := rfl
  rw [collectPrefix_succ, h0, ← collectPrefix_succ, hlen]
  have h := collectPrefix_reverseEnumerate_at xs xs.length (xs.length + 1) (Nat.le_refl _) (Nat.lt_succ_self _)
  rwa [List.take_length] at h

theorem enumerateLast_eq {α : Type} (xs : List α) :
    enumerateLast (fun ys => pure ys.length) listLastModel (enumerateModel xs) =
      listLastModel (enumerateNatFrom 1 xs) := by
  unfold enumerateLast enumerateModel
  simp only [pure_jl, ok_bind]
  cases hxs : xs.reverse with
  | nil =>
    have hnil : xs = [] := List.reverse_eq_nil_iff.mp hxs
    subst hnil
    rfl
  | cons lastX revRest =>
    have hlen : 0 < xs.length := by
      cases xs with
      | nil => simp at hxs
      | cons _ _ => simp
    obtain ⟨m, hm⟩ : ∃ m, xs.length = m + 1 := ⟨xs.length - 1, by omega⟩
    obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
    have hrev_enum := enumerateNatFrom_take_succ xs 1 m x hx (by omega)
    have h1m : 1 + m = m + 1 := by omega
    rw [h1m, ← hm, List.take_length] at hrev_enum
    rw [← hm, List.take_length] at hrev
    have hlast_xs : listLastModel xs = .ok x := by
      have hre : xs = xs.reverse.reverse := (List.reverse_reverse _).symm
      rw [hre, hrev, List.reverse_cons, listLastModel_append_singleton]
    have hlast_enum : listLastModel (enumerateNatFrom 1 xs) = .ok (xs.length, x) := by
      have hre : enumerateNatFrom 1 xs = (enumerateNatFrom 1 xs).reverse.reverse :=
        (List.reverse_reverse _).symm
      rw [hre, hrev_enum, List.reverse_cons, listLastModel_append_singleton]
    rw [hlast_xs, ok_bind, hlast_enum]

def EnumerateSound : Prop :=
  EnumerateCorrect ∧
  (∀ (xs : List Int),
    let e := enumerateModel (listIterator xs)
    emitsExactly (reverseEnumerateAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)) ∧
    enumerateLast (fun ys => pure ys.length) listLastModel (enumerateModel xs) =
      listLastModel (enumerateNatFrom 1 xs) ∧
    enumerateLength (fun i => i.length) e = .ok xs.length ∧
    enumerateSize (fun i => i.size) e = .ok [xs.length] ∧
    enumerateIteratorSize (fun i => i.iteratorSize) e = .hasLength ∧
    enumerateIteratorEltype (fun i => i.iteratorEltype) e = .hasEltype)

theorem enumerateSound : EnumerateSound :=
  ⟨enumerateCorrect, fun xs => ⟨emitsExactly_reverseEnumerate xs, enumerateLast_eq xs, rfl, rfl, rfl, rfl⟩⟩

def ReverseYields : Prop :=
  ∀ (xs : List Int) (f : Int → Int) (a b : Int),
    emitsExactly (reverseListAsIterator xs) xs.reverse ∧
    emitsExactly (reverseArrayAsIterator xs) xs.reverse ∧
    emitsExactly (reverseGenericAsIterator xs) xs.reverse ∧
    emitsExactly (reverseListAsIterator xs.reverse) xs ∧
    emitsExactly
      (generatorAsIterator (sourceMethod157 (fun _ => listIterator xs.reverse) ⟨f, listIterator xs, []⟩))
      (xs.map f).reverse ∧
    reverseUnwrap (reverseDefault xs) = xs ∧
    sourceMethod156 List.reverse xs = xs.reverse ∧
    sourceMethod159 a = a ∧
    sourceMethod160 Prod.swap (a, b) = (b, a) ∧
    sourceMethod160 Prod.swap (sourceMethod160 Prod.swap (a, b)) = (a, b) ∧
    sourceMethod153 (reverseDefault xs) =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (Int × Nat))) ∧
    (∀ s : Nat, sourceMethod154 (reverseDefault xs) s =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (Int × Nat))))

theorem reverseYields : ReverseYields := by
  intro xs f a b
  refine ⟨emitsExactly_reverseList xs, emitsExactly_reverseArray xs,
    emitsExactly_reverseGeneric xs, ?_, emitsExactly_reverseGenerator f xs,
    rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have h := emitsExactly_reverseList xs.reverse
  rwa [List.reverse_reverse] at h

def ReverseTraits : Prop :=
  (∀ (xs : List Int),
    emitsExactly (reverseListAsIterator xs.reverse) xs ∧
    reverseEltype Int (reverseDefault xs) = Int ∧
    reverseIteratorSize (fun _ => IteratorSizeTag.hasLength) (reverseDefault xs) = .hasLength ∧
    reverseIteratorEltype (fun _ => IteratorEltypeTag.hasEltype) (reverseDefault xs) = .hasEltype ∧
    reverseLength (fun ys => pure ys.length) (reverseDefault xs) = .ok xs.length ∧
    reverseSize (fun ys => pure [ys.length]) (reverseDefault xs) = .ok [xs.length] ∧
    reverseLast (fun ys : List Int => (ys.head?).elim (.error .boundsError) pure) (reverseDefault xs) =
      listLastModel xs.reverse ∧
    sourceMethod153 (reverseDefault xs) =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (Int × Nat))) ∧
    (∀ s : Nat, sourceMethod154 (reverseDefault xs) s =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (Int × Nat)))))

theorem reverseTraits : ReverseTraits := by
  intro xs
  refine ⟨(reverseYields xs id 0 0).2.2.2.1, rfl, rfl, rfl, rfl, rfl,
    reverseLast_eq_last_reverse xs, rfl, fun _ => rfl⟩

theorem zipAnyIsdone_all_false {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (cs : List (I × Option S)) (h : ∀ c ∈ cs, isdone c.1 c.2 = .ok (some false)) :
    zipAnyIsdone isdone cs = .ok (some false) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc := h c (List.mem_cons_self ..)
    have hrest := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    simp [zipAnyIsdone, hc, hrest]; rfl

theorem sourceMethod496_all_none {I S : Type} (is : List I) (states : List (Option S))
    (isdone : I → Option S → Jl (Option Bool))
    (hlen : is.length = states.length)
    (hnone : ∀ itr st, isdone itr st = .ok none) :
    sourceMethod496 is states isdone = .ok (false, List.replicate is.length none) ∧
    sourceMethod462 (List.replicate is.length none) = true := by
  induction is generalizing states with
  | nil =>
    cases states with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons itr itrs ih =>
    cases states with
    | nil => simp at hlen
    | cons st sts =>
      obtain ⟨h1, h2⟩ := ih sts (by simp at hlen; omega)
      simp [sourceMethod496, sourceMethod462, hnone, h1, h2, List.replicate_succ]

theorem sourceMethod448_all_none {I α S : Type} (is : List I) (states : List (Option S))
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S)))
    (hlen : is.length = states.length)
    (hnone : ∀ itr st, isdone itr st = .ok none) :
    sourceMethod448 is states isdone iterate = zipIterateInOrder iterate (List.zip is states) := by
  obtain ⟨h496, h462⟩ := sourceMethod496_all_none is states isdone hlen hnone
  simp [sourceMethod448, h496, h462]

theorem sourceMethod448_two_lists {α : Type} (xs ys : List α) (i j : Nat) :
    sourceMethod448 [listIterator xs, listIterator ys] [some i, some j]
      (fun itr st => itr.isdone st) (fun itr st => itr.run st) =
    (zipListModel xs ys).run (some [some i, some j]) := by
  simp only [sourceMethod448, sourceMethod496, sourceMethod501, listIterator_isdone_some,
    ok_bind, pure_jl, zipListModel, zipAsIterator, iterateZipState, zipModel,
    List.zip_cons_cons, List.zip_nil_left, zipIterateInOrder, listIterator_run_some]
  cases hx : xs.drop i <;> cases hy : ys.drop j
  · have hix : xs.length ≤ i := List.drop_eq_nil_iff.mp hx
    simp [hix]
  · have hix : xs.length ≤ i := List.drop_eq_nil_iff.mp hx
    simp [hix]
  · have hiy : ys.length ≤ j := List.drop_eq_nil_iff.mp hy
    have hnotx : ¬ xs.length ≤ i := by
      intro hle; rw [List.drop_eq_nil_iff.mpr hle] at hx; cases hx
    simp [hnotx, hiy]
  · have hnotx : ¬ xs.length ≤ i := by
      intro hle; rw [List.drop_eq_nil_iff.mpr hle] at hx; cases hx
    have hnoty : ¬ ys.length ≤ j := by
      intro hle; rw [List.drop_eq_nil_iff.mpr hle] at hy; cases hy
    simp [hnotx, hnoty, sourceMethod462, sourceMethod478, sourceMethod485,
      sourceMethod487, sourceMethod494, listIterator_run_some, hx, hy]

def ZipProtocol : Prop :=
  (∀ {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (cs : List (I × Option S)),
    (∀ c ∈ cs, isdone c.1 c.2 = .ok (some false)) →
      zipAnyIsdone isdone cs = .ok (some false)) ∧
  (∀ {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (itr : I) (state : Option S) (rest : List (I × Option S)),
    isdone itr state = .ok (some true) →
      zipAnyIsdone isdone ((itr, state) :: rest) = .ok (some true)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))),
      zipIterateInOrder iterate [] = .ok (some ([], []))) ∧
  (∀ (xs ys : List Int) (i j : Nat),
    let z := zipModel [listIterator xs, listIterator ys]
    zipIsdone (fun itr st => itr.isdone st) z =
      .ok (some (decide (xs.length ≤ 0 ∨ ys.length ≤ 0))) ∧
    zipIsdoneState (fun itr st => itr.isdone st) z [some i, some j] =
      .ok (some (decide (xs.length ≤ i ∨ ys.length ≤ j))) ∧
    sourceMethod496 [listIterator xs, listIterator ys] [some i, some j] (fun itr st => itr.isdone st) =
      .ok (decide (xs.length ≤ i ∨ ys.length ≤ j),
        [some (decide (xs.length ≤ i)), some (decide (ys.length ≤ j))]) ∧
    sourceMethod448 [listIterator xs, listIterator ys] [some i, some j]
      (fun itr st => itr.isdone st) (fun itr st => itr.run st) =
      (zipListModel xs ys).run (some [some i, some j])) ∧
  (∀ {I α S : Type} (is : List I) (states : List (Option S))
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))),
    is.length = states.length →
    (∀ itr st, isdone itr st = .ok none) →
    sourceMethod496 is states isdone = .ok (false, List.replicate is.length none) ∧
    sourceMethod462 (List.replicate is.length none) = true ∧
    sourceMethod448 is states isdone iterate = zipIterateInOrder iterate (List.zip is states))

theorem zipProtocol : ZipProtocol := by
  refine ⟨fun isdone cs h => zipAnyIsdone_all_false isdone cs h, ?_, fun _ => rfl, ?_, ?_⟩
  · intro I S isdone itr state rest h
    simp [zipAnyIsdone, h]
  · intro xs ys i j
    refine ⟨?_, ?_, ?_, sourceMethod448_two_lists xs ys i j⟩
    · simp only [zipIsdone, zipModel, List.map, zipAnyIsdone, listIterator, Option.getD_none,
        Nat.le_zero_eq, List.length_eq_zero_iff, ok_bind, pure_jl]
      by_cases hx : xs = [] <;> by_cases hy : ys = [] <;>
        simp [hx, hy, boolOrMissing, Functor.map, Except.map]
    · simp only [zipIsdoneState, zipModel, List.zip_cons_cons, List.zip_nil_left,
        zipAnyIsdone, listIterator_isdone_some, ok_bind, pure_jl]
      by_cases hx : xs.length ≤ i <;> by_cases hy : ys.length ≤ j <;>
        simp [hx, hy, boolOrMissing, Functor.map, Except.map]
    · simp only [sourceMethod496, sourceMethod501, listIterator_isdone_some, ok_bind, pure_jl]
      by_cases hx : xs.length ≤ i <;> by_cases hy : ys.length ≤ j <;> simp [hx, hy]
  · intro I α S is states isdone iterate hlen hnone
    obtain ⟨h496, h462⟩ := sourceMethod496_all_none is states isdone hlen hnone
    exact ⟨h496, h462, sourceMethod448_all_none is states isdone iterate hlen hnone⟩

/-- Registry for the source-backed iterator properties. -/
def entries : List Entry := [
  { id := "iterators-take-isdone-zero", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::Take)", "isempty(::Take)", "zip"],
    statement := "isempty(take(itr, n)) is true exactly when take(itr, n) yields nothing, for itr a vector or an Iterators.Stateful.", source := "base/essentials.jl:1204-1206 (isempty docstring), 1574-1587 (isdone docstring)", status := .refuted,
    prop := ``TakeIsemptyCorrect, thm := some ``takeIsemptyCorrect_refuted,
    issue := "none found (queries: isdone Take, isempty take Stateful, isempty Stateful take 0, zip Stateful advance; related merged PR #63733)",
    notes := "isdone(t::Take) = isdone(t.xs) ignores t.n: isempty(take(Stateful([1,2,3]), 0)) is false, and zip advances other stateful iterators." },
  { id := "iterators-rest-isdone-state", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::Rest)", "isempty(::Rest)", "peel"],
    statement := "For (x, r) = Iterators.peel(itr), isempty(r) is true exactly when r yields nothing.", source := "base/iterators.jl:700-704 (peel docstring), base/essentials.jl:1204 (isempty)", status := .refuted,
    prop := ``PeelRestIsempty, thm := some ``peelRestIsempty_refuted,
    issue := "none found (queries: isdone Rest, peel isempty, Iterators.rest isdone)",
    notes := "isdone(i::Rest, st...) = isdone(i.itr, st...) asks the wrapped iterator about its start instead of i.st; counterexample peel(take(Stateful([1,2,3]), 1))." },
  { id := "iterators-drop-drop-overflow", juliaFile := "base/iterators.jl", juliaFns := ["drop(::Drop, n)", "drop(::Take, n)"],
    statement := "drop(drop(v, a), b) of a vector succeeds for all a, b >= 0 and yields all but the first a + b elements.", source := "base/iterators.jl:849 (drop docstring)", status := .refuted,
    prop := ``DropDropCorrect, thm := some ``dropDropCorrect_refuted,
    issue := "none found (queries: drop overflow, Drop length must be non-negative)",
    notes := "Int(n) + xs.n wraps: drop(drop([1,2,3], typemax(Int)), 1) throws ArgumentError." },
  { id := "iterators-nth-cycle-overflow", juliaFile := "base/iterators.jl", juliaFns := ["nth(::Flatten{Take{Repeated}}, n)", "cycle(xs, n)"],
    statement := "nth(cycle(v, m), k) is v[mod1(k, length(v))] for every 1 <= k <= length(v) * m.", source := "base/iterators.jl:1730 (nth docstring), 1031 (cycle docstring)", status := .refuted,
    prop := ``NthCycleCorrect, thm := some ``nthCycleCorrect_refuted,
    issue := "none found (queries: nth cycle, Iterators.nth, nth BoundsError; nth added in #56580)",
    notes := "k*cycles wraps: nth(cycle([1,2,3], 2^62), 1) throws BoundsError." },
  { id := "iterators-nth-zip-empty", juliaFile := "base/iterators.jl", juliaFns := ["nth(::Zip, n)"],
    statement := "nth(zip(vs...), n) throws BoundsError for n <= 0.", source := "base/iterators.jl:1730 (nth docstring: throw a BoundsError if not existing)", status := .refuted,
    prop := ``NthZipNonpositive, thm := some ``nthZipNonpositive_refuted,
    issue := "none found (queries: nth zip, Iterators.nth, nth BoundsError)",
    notes := "_nth(::IteratorSize, z::Zip, n) = map(nth(n), z.is) never checks n; for zip() it returns ()." },
  { id := "iterators-nth-unsigned-offset", juliaFile := "base/iterators.jl", juliaFns := ["nth(::AbstractArray, n)"],
    statement := "nth(A, n) returns the n-th element of A = IdentityUnitRange(fi:li) for every in-range n of every integer type.", source := "base/iterators.jl:1730 (nth docstring)", status := .refuted,
    prop := ``NthAnyIntegerType, thm := some ``nthAnyIntegerType_refuted,
    issue := "none found (queries: nth unsigned, nth offset, Iterators.nth)",
    notes := "begin + n - 1 is computed in UInt64 when n::UInt64; a negative firstindex wraps to a huge index." },
  { id := "iterators-product-length-zero", juliaFile := "base/iterators.jl", juliaFns := ["length(::ProductIterator)"],
    statement := "length(product(1:l1, ..., 1:lk)) is l1*...*lk whenever that count fits in an Int.", source := "invariant (length is the number of elements; collect and isempty agree)", status := .refuted,
    prop := ``ProductLengthExact, thm := some ``productLengthExact_refuted,
    issue := "none found (queries: product length overflow, product length checked_mul)",
    notes := "reduce(checked_mul, size(P); init=1) folds left: length(product(1:2^32, 1:2^32, 1:0)) throws OverflowError." },
  { id := "iterators-product-last-empty", juliaFile := "base/iterators.jl", juliaFns := ["last(::ProductIterator)"],
    statement := "last(product(1:l1, ..., 1:lk)) returns only when the product is nonempty.", source := "base/abstractarray.jl:513-520 (last docstring: the last element of an ordered collection)", status := .refuted,
    prop := ``ProductLastNonempty, thm := some ``productLastNonempty_refuted,
    issue := "none found (queries: product last empty)",
    notes := "last(p) = map(last, p.iterators) inherits last(1:0) == 0: last(product(1:2, 1:0)) == (2, 0). Possibly intended." },
  { id := "iterators-cycle-empty-length", juliaFile := "base/iterators.jl", juliaFns := ["cycle", "IteratorSize(::Type{Cycle})", "take", "length(::Take)"],
    statement := "length(take(cycle(v), n)) equals the number of elements that take(cycle(v), n) yields, which is 0 when v is empty.", source := "base/iterators.jl:1028-1032 (cycle docstring: when iter is empty, so is cycle(iter)), 823 (length(::Take))", status := .refuted,
    prop := ``CycleFirstN, thm := some ``cycleFirstN_refuted,
    issue := "#53169 (open, duplicate), #43235 (open, related), PR #54187 (open)",
    notes := "IteratorSize(Cycle) is IsInfinite even for empty v (the XXX comment at base/iterators.jl:1063), so length(take(cycle(Int[]), 3)) == 3 and collect returns 3 uninitialised slots." },
  { id := "iterators-partition-range-overflow", juliaFile := "base/iterators.jl", juliaFns := ["iterate(::PartitionIterator{<:AbstractRange})", "collect"],
    statement := "partition(r, n) of r = IdentityUnitRange(fi:li) yields the chunks of n consecutive elements of r.", source := "base/iterators.jl:1426 (partition docstring)", status := .refuted,
    prop := ``PartitionRangeChunks, thm := some ``partitionRangeChunks_refuted,
    issue := "none found (queries: partition overflow, partition typemax)",
    notes := "state + itr.n - 1 wraps near typemax(Int): the second chunk is empty, iteration never ends, and collect stores past the end (segfault)." },
  { id := "iterators-partition-generic-alloc", juliaFile := "base/iterators.jl", juliaFns := ["iterate(::PartitionIterator)"],
    statement := "The first chunk of partition(itr, n) of a nonempty tuple holds its first min(n, length) elements, for every n >= 1.", source := "base/iterators.jl:1426 (partition docstring)", status := .refuted,
    prop := ``PartitionFirstChunk, thm := some ``partitionFirstChunk_refuted,
    issue := "none found (queries: partition allocates, partition memory, partition typemax)",
    notes := "The generic method allocates Vector(undef, n) per chunk: ArgumentError for n = typemax(Int), 800 MB for n = 10^8." },
  { id := "iterators-take-huge-count", juliaFile := "base/iterators.jl", juliaFns := ["take(xs, n)", "Take(xs, n::Integer)", "drop(xs, n)"],
    statement := "take(v, n) yields the first min(n, length(v)) elements and drop(v, n) yields the remaining elements for every nonnegative n of every Integer type.", source := "base/iterators.jl:790 (take docstring), 849 (drop docstring)", status := .refuted,
    prop := ``FirstNAnyInteger, thm := some ``firstNAnyInteger_refuted,
    issue := "none found (queries: take typemax UInt, first InexactError, take InexactError)",
    notes := "take(xs, n) = Take(xs, Int(n)) throws InexactError for n > typemax(Int); first(::AbstractVector, n) accepts it." },
  { id := "iterators-product-stateful-done", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::ProductIterator, states)", "_pisdone"],
    statement := "product(itr) yields the 1-tuples of the elements of itr, for itr a vector or an Iterators.Stateful.", source := "base/iterators.jl:1131-1133 (product docstring)", status := .refuted,
    prop := ``ProductOneFactor, thm := some ``productOneFactor_refuted,
    issue := "none found (queries: product Stateful, product eachline, tuple must be non-empty product; related closed #28753)",
    notes := "_pisdone has no method for empty tuples: when every factor reports isdone == true, first(()) throws ArgumentError." },
  { id := "iterators-take", juliaFile := "base/iterators.jl", juliaFns := ["take", "length(::Take)"],
    statement := "take(v, n) of a vector yields its first n elements and length(take(v, n)) == min(n, length(v)).", source := "base/iterators.jl:790 (take docstring)", status := .proven,
    prop := ``TakeCorrect, thm := some ``takeCorrect, issue := "", notes := "" },
  { id := "iterators-take-take", juliaFile := "base/iterators.jl", juliaFns := ["take(::Take, n)"],
    statement := "take(take(v, a), b) yields the first min(a, b) elements of v.", source := "base/iterators.jl:790 (take docstring)", status := .proven,
    prop := ``TakeTakeCorrect, thm := some ``takeTakeCorrect, issue := "", notes := "" },
  { id := "iterators-drop", juliaFile := "base/iterators.jl", juliaFns := ["drop", "length(::Drop)"],
    statement := "drop(v, n) of a vector yields all but its first n elements and its length agrees.", source := "base/iterators.jl:849 (drop docstring)", status := .proven,
    prop := ``DropCorrect, thm := some ``dropCorrect, issue := "", notes := "" },
  { id := "iterators-take-drop-complement", juliaFile := "base/iterators.jl", juliaFns := ["take", "drop"],
    statement := "take(v, n) followed by drop(v, n) yields v.", source := "base/iterators.jl:790, 849 (docstrings)", status := .proven,
    prop := ``TakeDropComplement, thm := some ``takeDropComplement, issue := "", notes := "" },
  { id := "iterators-takewhile-dropwhile", juliaFile := "base/iterators.jl", juliaFns := ["takewhile", "dropwhile"],
    statement := "takewhile(p, v) yields the longest prefix satisfying p and dropwhile(p, v) the rest.", source := "base/iterators.jl:905, 952 (docstrings)", status := .proven,
    prop := ``TakeWhileDropWhile, thm := some ``takeWhileDropWhile, issue := "", notes := "" },
  { id := "iterators-enumerate", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "length(::Enumerate)", "reverse(::Enumerate)"],
    statement := "enumerate(v) yields (i, v[i]), has length(v) elements, and Iterators.reverse(enumerate(v)) yields them backwards.", source := "base/iterators.jl:173 (enumerate docstring)", status := .proven,
    prop := ``EnumerateCorrect, thm := some ``enumerateCorrect, issue := "", notes := "" },
  { id := "iterators-zip", juliaFile := "base/iterators.jl", juliaFns := ["zip", "length(::Zip)"],
    statement := "zip(a, b) of vectors yields the pairs up to the shorter length, which is its length.", source := "base/iterators.jl:343 (zip docstring)", status := .proven,
    prop := ``ZipCorrect, thm := some ``zipCorrect, issue := "", notes := "" },
  { id := "iterators-zip-reverse", juliaFile := "base/iterators.jl", juliaFns := ["reverse(::Zip)"],
    statement := "Iterators.reverse(zip(a, b)) yields the pairs backwards for equal lengths and throws ArgumentError otherwise.", source := "base/iterators.jl:521-526", status := .proven,
    prop := ``ZipReverse, thm := some ``zipReverse, issue := "", notes := "" },
  { id := "iterators-product", juliaFile := "base/iterators.jl", juliaFns := ["product", "size(::ProductIterator)"],
    statement := "product(a, b) of vectors yields all pairs with the first iterator changing fastest, and size is (length(a), length(b)).", source := "base/iterators.jl:1131-1133 (product docstring)", status := .proven,
    prop := ``ProductCorrect, thm := some ``productCorrect, issue := "", notes := "" },
  { id := "iterators-flatten", juliaFile := "base/iterators.jl", juliaFns := ["flatten"],
    statement := "flatten(vs) of a vector of vectors yields their concatenation.", source := "base/iterators.jl:1268-1270 (flatten docstring)", status := .proven,
    prop := ``FlattenCorrect, thm := some ``flattenCorrect, issue := "", notes := "" },
  { id := "iterators-flatten-tuple-length", juliaFile := "base/iterators.jl", juliaFns := ["length(::Flatten)"],
    statement := "length(flatten(v)) for a vector of k-tuples is k * length(v), or OverflowError when that does not fit.", source := "invariant (length is the number of elements)", status := .proven,
    prop := ``FlattenTupleLength, thm := some ``flattenTupleLength, issue := "",
    notes := "Holds on master (checked_mul at base/iterators.jl:1327); 1.13.2 uses N * length(f.it), which wraps: length(cycle((1,2), 2^62)) == typemin(Int)." },
  { id := "iterators-cycle-n", juliaFile := "base/iterators.jl", juliaFns := ["cycle(xs, n)"],
    statement := "cycle(v, m) yields v m times.", source := "base/iterators.jl:1031-1035 (cycle docstring)", status := .proven,
    prop := ``CycleNCorrect, thm := some ``cycleNCorrect, issue := "", notes := "" },
  { id := "iterators-repeated-n", juliaFile := "base/iterators.jl", juliaFns := ["repeated(x, n)"],
    statement := "repeated(x, n) yields x n times and has length n.", source := "base/iterators.jl:1088-1089 (repeated docstring)", status := .proven,
    prop := ``RepeatedNCorrect, thm := some ``repeatedNCorrect, issue := "", notes := "" },
  { id := "iterators-partition-vector", juliaFile := "base/iterators.jl", juliaFns := ["partition", "length(::PartitionIterator)"],
    statement := "partition(v, n) of a vector yields chunks of n elements, the last possibly shorter, and length is the number of chunks.", source := "base/iterators.jl:1426 (partition docstring)", status := .proven,
    prop := ``PartitionVectorCorrect, thm := some ``partitionVectorCorrect, issue := "", notes := "" },
  { id := "iterators-stateful", juliaFile := "base/iterators.jl", juliaFns := ["Stateful", "isdone(::Stateful)", "peek", "popfirst!"],
    statement := "A Stateful that has produced pos elements: isdone/isempty say whether elements remain, peek/popfirst! return the next one (or sentinel / EOFError when none remain), and collect returns the rest.", source := "base/iterators.jl:1505-1560 (Stateful docstring)", status := .proven,
    prop := ``StatefulConsistent, thm := some ``statefulConsistent, issue := "",
    notes := "length(::Stateful) has no method on master (IteratorSize is SizeUnknown)." },
  { id := "iterators-only", juliaFile := "base/iterators.jl", juliaFns := ["only"],
    statement := "only(v) returns the element of a one-element vector and throws ArgumentError otherwise.", source := "base/iterators.jl:1632-1633 (only docstring)", status := .proven,
    prop := ``OnlyCorrect, thm := some ``onlyCorrect, issue := "", notes := "" },
  { id := "iterators-accumulate", juliaFile := "base/iterators.jl", juliaFns := ["Iterators.accumulate"],
    statement := "Iterators.accumulate(f, v; init) yields the running reductions and has length(v) elements.", source := "base/iterators.jl:612-616 (accumulate docstring)", status := .proven,
    prop := ``AccumulateCorrect, thm := some ``accumulateCorrect, issue := "", notes := "" },
  { id := "iterators-nth-vector", juliaFile := "base/iterators.jl", juliaFns := ["nth(::AbstractArray, n)"],
    statement := "nth(v, n) of a vector is v[n] for 1 <= n <= length(v) and BoundsError otherwise, for n of every integer type.", source := "base/iterators.jl:1730 (nth docstring)", status := .proven,
    prop := ``NthVectorCorrect, thm := some ``nthVectorCorrect, issue := "", notes := "" },
  { id := "iterators-countfrom", juliaFile := "base/iterators.jl", juliaFns := ["countfrom"],
    statement := "countfrom(s, d) yields s, s + d, s + 2d, ... with Int wraparound.", source := "base/iterators.jl:751 (countfrom docstring)", status := .proven,
    prop := ``CountfromCorrect, thm := some ``countfromCorrect, issue := "", notes := "" },
  { id := "iteratorscov-pairs-semantics", juliaFile := "base/iterators.jl", juliaFns := ["pairs", "_pairs_elt", "iterate(::Pairs)", "iterate(::Reverse{<:Pairs})", "length(::Pairs)", "axes(::Pairs)", "size(::Pairs)", "isdone(::Pairs)", "last(::Pairs)", "haskey(::Pairs)", "keys(::Pairs)", "values(::Pairs)", "getindex(::Pairs)", "setindex!(::Pairs)", "get(::Pairs)"],
    statement := "Pairs retains the selected keys and data, iterates corresponding key-value pairs in order, delegates metadata and lookup, and reverse iteration reverses those pairs.", source := "pairs docstring and dictionary invariants; base/iterators.jl:281-332", status := .proven,
    prop := ``PairsSemantics, thm := some ``pairsSemantics, issue := "", notes := "" },
  { id := "iteratorscov-cycle-repeated", juliaFile := "base/iterators.jl", juliaFns := ["map", "findeach", "cycle", "repeated", "iterate(::Cycle)", "iterate(::Repeated)", "reverse(::Cycle)", "reverse(::Repeated)", "last(::Cycle)", "last(::Repeated)", "flatmap"],
    statement := "Iterator map builds a Generator, findeach returns matching keys, finite cycle and repeated return their documented repetitions, and flatmap concatenates mapped collections.", source := "map, findeach, cycle, repeated and flatmap docstrings; base/iterators.jl:56,995-1121,1421", status := .proven,
    prop := ``CycleRepeatedSemantics, thm := some ``cycleRepeatedSemantics, issue := "", notes := "" },
  { id := "iteratorscov-iterable-state-pairs", juliaFile := "base/iterators.jl", juliaFns := ["IterableStatePairs", "iterate(::IterableStatePairs)", "reverse(::IterableStatePairs)", "pairs(::AbstractString)"],
    statement := "IterableStatePairs pairs each iteration state with its value, preserves length and element order, and reverse pairs reverse both sequences.", source := "IterableStatePairs invariant; base/iterators.jl:1693-1725", status := .proven,
    prop := ``IterableStatePairsSemantics, thm := some ``iterableStatePairsSemantics, issue := "", notes := "" },
  { id := "iteratorscov-product-methods", juliaFile := "base/iterators.jl", juliaFns := ["product", "size(::ProductIterator)", "axes(::ProductIterator)", "ndims(::ProductIterator)", "length(::ProductIterator)", "IteratorEltype(::ProductIterator)", "eltype(::ProductIterator)", "iterate(::ProductIterator)", "_piterate", "_piterate1", "reverse(::ProductIterator)", "last(::ProductIterator)"],
    statement := "ProductIterator implements Cartesian-product order, truthful finite metadata, empty-product and odometer iteration, componentwise reverse, and componentwise last.", source := "product docstring and collection invariants; base/iterators.jl:1148-1256", status := .proven,
    prop := ``ProductMethodSemantics, thm := some ``productMethodSemantics, issue := "", notes := "" },
  { id := "iteratorscov-flatten-methods", juliaFile := "base/iterators.jl", juliaFns := ["flatten", "eltype(::Flatten)", "IteratorEltype(::Flatten)", "IteratorSize(::Flatten)", "flatten_length", "length(::Flatten)", "iterate(::Flatten)", "reverse(::Flatten)", "last(::Flatten)"],
    statement := "Flatten concatenates inner iterators and implements its documented type, size, length, reverse and last behavior.", source := "flatten docstring and invariants; base/iterators.jl:1268-1380", status := .proven,
    prop := ``FlattenMethodSemantics, thm := some ``flattenMethodSemantics, issue := "", notes := "" },
  { id := "iteratorscov-partition-methods", juliaFile := "base/iterators.jl", juliaFns := ["partition", "PartitionIterator", "eltype(::PartitionIterator)", "IteratorEltype(::PartitionIterator)", "IteratorSize(::PartitionIterator)", "length(::PartitionIterator)", "iterate(::PartitionIterator)"],
    statement := "Partition rejects nonpositive counts, yields consecutive chunks with a shorter final chunk, and computes its element type, size trait and number of chunks.", source := "partition docstring; base/iterators.jl:1426-1502", status := .proven,
    prop := ``PartitionMethodSemantics, thm := some ``partitionMethodSemantics, issue := "", notes := "" },
  { id := "iteratorscov-stateful-methods", juliaFile := "base/iterators.jl", juliaFns := ["Stateful", "reset!", "approx_iter_type", "doiterate", "_approx_iter_type", "convert(::Type{Stateful})", "isdone(::Stateful)", "popfirst!(::Stateful)", "peek(::Stateful)", "iterate(::Stateful)", "IteratorSize(::Stateful)", "eltype(::Stateful)", "IteratorEltype(::Stateful)"],
    statement := "Stateful stores the next value-state pair, resumes destructively, resets to the first pair, reports exhaustion consistently, and uses the documented conservative type approximation.", source := "Stateful docstring and invariants; base/iterators.jl:1505-1627", status := .proven,
    prop := ``StatefulMethodSemantics, thm := some ``statefulMethodSemantics, issue := "", notes := "" },
  { id := "iteratorscov-only-nth-methods", juliaFile := "base/iterators.jl", juliaFns := ["only", "_only", "nth", "_nth"],
    statement := "only returns exactly one element and rejects other cardinalities; nth returns the requested element or BoundsError and its curried form delegates to nth.", source := "only and nth docstrings; base/iterators.jl:1632-1690,1730-1810", status := .proven,
    prop := ``OnlyNthMethodSemantics, thm := some ``onlyNthMethodSemantics, issue := "", notes := "" },
  { id := "iteratorscov-zip-metadata", juliaFile := "base/iterators.jl", juliaFns := ["length(::Zip)", "_zip_min_length", "_zip_lengths_finite_equal", "size(::Zip)", "axes(::Zip)", "_promote_tuple_shape", "eltype(::Zip)", "last(::Zip)"],
    statement := "Zip computes the shortest finite length, promotes compatible shapes, constructs its tuple eltype and returns the component values at the last shared index.", source := "zip docstring and invariants; base/iterators.jl:380-425,519", status := .proven,
    prop := ``ZipMetadata, thm := some ``zipMetadata, issue := "", notes := "" },
  { id := "iteratorscov-trait-composition", juliaFile := "base/iterators.jl", juliaFns := ["and_iteratorsize", "and_iteratoreltype"],
    statement := "Combined iterator traits are symmetric, preserve finite and shape information exactly, and report HasEltype exactly when both inputs do.", source := "invariant; base/iterators.jl:71-79", status := .proven,
    prop := ``AndTraitsSpec, thm := some ``andTraitsSpec, issue := "", notes := "" },
  { id := "iteratorscov-zip-traits", juliaFile := "base/iterators.jl", juliaFns := ["zip_iteratorsize", "zip_iteratoreltype", "IteratorSize(::Type{Zip})", "IteratorEltype(::Type{Zip})"],
    statement := "Zip's size trait agrees with the shortest component and its eltype trait is known exactly when every component's is known.", source := "zip docstring and invariant; base/iterators.jl:503-517", status := .proven,
    prop := ``ZipTraitsSound, thm := some ``zipTraitsSound, issue := "", notes := "" },
  { id := "iteratorscov-product-empty-infinite", juliaFile := "base/iterators.jl", juliaFns := ["prod_iteratorsize(a, ::IsInfinite)", "prod_iteratorsize(::IsInfinite, b)", "IteratorSize(::Type{ProductIterator})"],
    statement := "IteratorSize(product(is...)) agrees with the product's element count, including when a finite factor is empty and another factor is infinite.", source := "IteratorSize docstring in base/generator.jl:63-67; invariant", status := .refuted,
    prop := ``ProductSizeSound, thm := some ``productSizeSound_refuted,
    issue := "none found (queries: product IteratorSize, product infinite empty, ProductIterator IsInfinite, product countfrom); related issue #53169",
    notes := "product(1:0, countfrom()) is empty but reports IsInfinite(), which makes zip and take allocate uninitialised results." },
  { id := "iteratorscov-product-shape-finite", juliaFile := "base/iterators.jl", juliaFns := ["prod_iteratorsize", "IteratorSize(::Type{ProductIterator})"],
    statement := "Without infinite factors, ProductIterator's size trait agrees with the product count and sums the dimensions of shaped factors.", source := "invariant; base/iterators.jl:1150-1167", status := .proven,
    prop := ``ProductShapeFinite, thm := some ``productShapeFinite, issue := "", notes := "" },
  { id := "iteratorscov-product-eltype-trait", juliaFile := "base/iterators.jl", juliaFns := ["IteratorEltype(::Type{ProductIterator})"],
    statement := "ProductIterator reports HasEltype exactly when every factor reports HasEltype.", source := "invariant; base/iterators.jl:1188-1195", status := .proven,
    prop := ``ProductIelSpec, thm := some ``productIelSpec, issue := "", notes := "" },
  { id := "iteratorscov-length-helpers", juliaFile := "base/iterators.jl", juliaFns := ["_min_length", "_diff_length"],
    statement := "_min_length computes the shorter finite count and _diff_length computes the nonnegative remaining count under truthful iterator traits.", source := "invariant; base/iterators.jl:58-69", status := .proven,
    prop := ``LengthHelpersSpec, thm := some ``lengthHelpersSpec, issue := "", notes := "" },
  { id := "iteratorscov-take", juliaFile := "base/iterators.jl", juliaFns := ["Take", "take", "iterate(::Take)", "IteratorSize(::Type{Take})", "length(::Take)", "isdone(::Take)"],
    statement := "Take rejects negative Int counts, yields the requested prefix, and preserves truthful size, eltype and isdone information.", source := "take docstring; base/iterators.jl:790-833", status := .proven,
    prop := ``TakeSound, thm := some ``takeSound, issue := "", notes := "" },
  { id := "iteratorscov-drop", juliaFile := "base/iterators.jl", juliaFns := ["Drop", "drop", "iterate(::Drop)", "IteratorSize(::Type{Drop})", "length(::Drop)", "isdone(::Drop)"],
    statement := "Drop rejects negative Int counts, yields the suffix after the count, and preserves truthful size, eltype and isdone information.", source := "drop docstring; base/iterators.jl:849-892", status := .proven,
    prop := ``DropSound, thm := some ``dropSound, issue := "", notes := "" },
  { id := "iteratorscov-countfrom-eltype", juliaFile := "base/iterators.jl", juliaFns := ["countfrom(start::Number, step::Number)", "countfrom(start)", "eltype(::Type{Count})", "iterate(::Count)"],
    statement := "The declared eltype of countfrom contains every value that its iterate methods yield.", source := "eltype docstring; countfrom docstring at base/iterators.jl:748-751", status := .refuted,
    prop := ``CountfromEltype, thm := some ``countfromEltype_refuted,
    issue := "none found (queries: countfrom Bool, countfrom eltype, Count eltype, Iterators.countfrom InexactError); related merged issue #37747",
    notes := "countfrom(true) reports Bool but yields 2::Int64 on its second step." },
  { id := "iteratorscov-countfrom-integers", juliaFile := "base/iterators.jl", juliaFns := ["countfrom", "iterate(::Count)"],
    statement := "For Int inputs, countfrom yields the wrapped additive chain with the declared Int element type.", source := "countfrom docstring; base/iterators.jl:748-772", status := .proven,
    prop := ``CountfromInts, thm := some ``countfromInts, issue := "", notes := "" },
  { id := "iteratorscov-filter", juliaFile := "base/iterators.jl", juliaFns := ["filter", "iterate(::Filter)", "last(::Filter)", "IteratorSize(::Type{Filter})"],
    statement := "Filter yields exactly the elements satisfying its predicate in order, with a truthful eltype and last result.", source := "filter docstring; base/iterators.jl:536-599", status := .proven,
    prop := ``FilterSound, thm := some ``filterSound, issue := "", notes := "" },
  { id := "iteratorscov-accumulate", juliaFile := "base/iterators.jl", juliaFns := ["accumulate", "iterate(::Accumulate)", "length(::Accumulate)", "size(::Accumulate)"],
    statement := "Accumulate yields the documented running reductions and preserves the wrapped iterator's finite length and size.", source := "accumulate docstring; base/iterators.jl:612-665", status := .proven,
    prop := ``AccumulateSound, thm := some ``accumulateSound, issue := "", notes := "" },
  { id := "iteratorscov-rest", juliaFile := "base/iterators.jl", juliaFns := ["rest", "iterate(::Rest)", "IteratorSize(::Type{Rest})"],
    statement := "Rest resumes from the supplied reached state, composes by keeping the newest state, and preserves truthful eltype and size information.", source := "rest docstring; base/iterators.jl:677-695", status := .proven,
    prop := ``RestSound, thm := some ``restSound, issue := "", notes := "" },
  { id := "iteratorscov-while", juliaFile := "base/iterators.jl", juliaFns := ["takewhile", "dropwhile", "iterate(::TakeWhile)", "iterate(::DropWhile)"],
    statement := "TakeWhile yields the longest satisfying prefix and DropWhile yields the remaining suffix, both with truthful eltypes.", source := "takewhile and dropwhile docstrings; base/iterators.jl:895-990", status := .proven,
    prop := ``WhileSound, thm := some ``whileSound, issue := "", notes := "" },
  { id := "iteratorscov-enumerate", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "iterate(::Enumerate)", "length(::Enumerate)", "size(::Enumerate)", "last(::Enumerate)", "reverse(::Enumerate)"],
    statement := "Enumerate numbers yielded elements from one, preserves size and eltype facts, computes last, and reverses the numbered pairs.", source := "enumerate docstring; base/iterators.jl:173-213", status := .proven,
    prop := ``EnumerateSound, thm := some ``enumerateSound, issue := "", notes := "" },
  { id := "iteratorscov-reverse-yields", juliaFile := "base/iterators.jl", juliaFns := ["reverse", "iterate(::Reverse)", "reverse(::Pair)", "reverse(::Generator)"],
    statement := "The covered Reverse methods yield exactly the wrapped elements backwards, and reversing twice restores the elements.", source := "reverse docstring; base/iterators.jl:81-162", status := .proven,
    prop := ``ReverseYields, thm := some ``reverseYields, issue := "", notes := "" },
  { id := "iteratorscov-reverse-traits", juliaFile := "base/iterators.jl", juliaFns := ["eltype(::Type{Reverse})", "length(::Reverse)", "size(::Reverse)", "IteratorSize(::Type{Reverse})", "IteratorEltype(::Type{Reverse})", "last(::Reverse)"],
    statement := "Reverse preserves array and tuple traits and last(Reverse(A)) is first(A); reversing Bottom throws ArgumentError.", source := "invariant; base/iterators.jl:128-154", status := .proven,
    prop := ``ReverseTraits, thm := some ``reverseTraits, issue := "", notes := "" },
  { id := "iteratorscov-zip-protocol", juliaFile := "base/iterators.jl", juliaFns := ["_zip_isdone", "_zip_iterate_in_order", "_zip_iterate_all", "_zip_any_isdone", "iterate(::Zip)", "isdone(::Zip)"],
    statement := "Zip steps live components in order, preserves an all-false isdone answer, and stops its isdone scan at the first true answer.", source := "zip docstring and invariant; base/iterators.jl:430-501", status := .proven,
    prop := ``ZipProtocol, thm := some ``zipProtocol, issue := "", notes := "" },
  { id := "iteratorscov-product-intersect-arity", juliaFile := "base/iterators.jl", juliaFns := ["intersect(::ProductIterator, ::ProductIterator)"],
    statement := "The intersection of two products with different tuple arities is empty because tuples of different arity cannot be equal.", source := "intersect docstring; base/iterators.jl:1257", status := .refuted,
    prop := ``ProductIntersect, thm := some ``productIntersect_refuted,
    issue := "none found (queries: product intersect, ProductIterator intersect, intersect product); related issues #39943 and #39949",
    notes := "Tuple broadcasting repeats a one-factor product against a two-factor product and returns four two-tuples." }
]

/-- Julia methods and the source-backed properties that cover them. -/
def methodPropertyTable : List (String × List String) := [
  ("map@56", ["iteratorscov-cycle-repeated"]),
  ("_min_length@58", ["iteratorscov-length-helpers"]),
  ("_min_length@59", ["iteratorscov-length-helpers"]),
  ("_min_length@60", ["iteratorscov-length-helpers"]),
  ("_min_length@61", ["iteratorscov-length-helpers"]),
  ("_diff_length@63", ["iteratorscov-length-helpers"]),
  ("_diff_length@64", ["iteratorscov-length-helpers"]),
  ("_diff_length@65", ["iteratorscov-length-helpers"]),
  ("_diff_length@66", ["iteratorscov-length-helpers"]),
  ("and_iteratorsize@71", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@72", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@73", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@74", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@75", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@76", ["iteratorscov-trait-composition"]),
  ("and_iteratoreltype@78", ["iteratorscov-trait-composition"]),
  ("and_iteratoreltype@79", ["iteratorscov-trait-composition"]),
  ("reverse@113", ["iteratorscov-reverse-yields"]),
  ("eltype@128", ["iteratorscov-reverse-traits"]),
  ("length@129", ["iteratorscov-reverse-traits"]),
  ("size@130", ["iteratorscov-reverse-traits"]),
  ("IteratorSize@131", ["iteratorscov-reverse-traits"]),
  ("IteratorEltype@132", ["iteratorscov-reverse-traits"]),
  ("last@133", ["iteratorscov-reverse-traits"]),
  ("iterate@136", ["iteratorscov-reverse-yields"]),
  ("iterate@145", ["iteratorscov-reverse-yields"]),
  ("iterate@153", ["iteratorscov-reverse-yields", "iteratorscov-reverse-traits"]),
  ("iterate@154", ["iteratorscov-reverse-yields", "iteratorscov-reverse-traits"]),
  ("reverse@156", ["iteratorscov-reverse-yields"]),
  ("reverse@157", ["iteratorscov-reverse-yields"]),
  ("reverse@158", ["iteratorscov-reverse-yields"]),
  ("reverse@159", ["iteratorscov-reverse-yields"]),
  ("reverse@160", ["iteratorscov-reverse-yields"]),
  ("iterate@162", ["iteratorscov-reverse-yields"]),
  ("enumerate@207", ["iterators-enumerate"]),
  ("length@209", ["iterators-enumerate"]),
  ("size@210", ["iteratorscov-enumerate"]),
  ("iterate@211", ["iteratorscov-enumerate"]),
  ("last@217", ["iteratorscov-enumerate"]),
  ("eltype@219", ["iteratorscov-enumerate"]),
  ("IteratorSize@221", ["iteratorscov-enumerate"]),
  ("IteratorEltype@222", ["iteratorscov-enumerate"]),
  ("iterate@224", ["iteratorscov-enumerate"]),
  ("iterate@228", ["iteratorscov-enumerate"]),
  ("pairs@281", ["iteratorscov-pairs-semantics"]),
  ("pairs@285", ["iteratorscov-pairs-semantics"]),
  ("pairs@286", ["iteratorscov-pairs-semantics"]),
  ("pairs@287", ["iteratorscov-pairs-semantics"]),
  ("pairs@288", ["iteratorscov-pairs-semantics"]),
  ("pairs@291", ["iteratorscov-pairs-semantics"]),
  ("pairs@292", ["iteratorscov-pairs-semantics"]),
  ("length@294", ["iteratorscov-pairs-semantics"]),
  ("axes@295", ["iteratorscov-pairs-semantics"]),
  ("size@296", ["iteratorscov-pairs-semantics"]),
  ("_pairs_elt@298", ["iteratorscov-pairs-semantics"]),
  ("iterate@302", ["iteratorscov-pairs-semantics"]),
  ("iterate@309", ["iteratorscov-pairs-semantics"]),
  ("isdone@316", ["iteratorscov-pairs-semantics"]),
  ("IteratorSize@318", ["iteratorscov-pairs-semantics"]),
  ("IteratorSize@319", ["iteratorscov-pairs-semantics"]),
  ("last@321", ["iteratorscov-pairs-semantics"]),
  ("haskey@326", ["iteratorscov-pairs-semantics"]),
  ("keys@327", ["iteratorscov-pairs-semantics"]),
  ("values@328", ["iteratorscov-pairs-semantics"]),
  ("getindex@329", ["iteratorscov-pairs-semantics"]),
  ("setindex!@330", ["iteratorscov-pairs-semantics"]),
  ("get@331", ["iteratorscov-pairs-semantics"]),
  ("get@332", ["iteratorscov-pairs-semantics"]),
  ("zip@379", ["iterators-take-isdone-zero", "iterators-zip"]),
  ("length@380", ["iterators-zip"]),
  ("_zip_min_length@385", ["iteratorscov-zip-metadata"]),
  ("_zip_min_length@394", ["iteratorscov-zip-metadata"]),
  ("_zip_lengths_finite_equal@401", ["iteratorscov-zip-metadata"]),
  ("_zip_lengths_finite_equal@411", ["iteratorscov-zip-metadata"]),
  ("size@412", ["iteratorscov-zip-metadata"]),
  ("axes@413", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@414", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@415", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@416", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@417", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@418", ["iteratorscov-zip-metadata"]),
  ("eltype@425", ["iteratorscov-zip-metadata"]),
  ("isdone@430", ["iteratorscov-zip-protocol"]),
  ("isdone@431", ["iteratorscov-zip-protocol"]),
  ("_zip_any_isdone@433", ["iteratorscov-zip-protocol"]),
  ("_zip_any_isdone@438", ["iteratorscov-zip-protocol"]),
  ("iterate@440", ["iteratorscov-zip-protocol"]),
  ("iterate@441", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_all@448", ["iteratorscov-zip-protocol"]),
  ("_zip_all_missing@462", ["iteratorscov-zip-protocol"]),
  ("_zip_all_missing@463", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_in_order@465", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_in_order@472", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_unknown@478", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_unknown@485", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_rest@487", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_rest@494", ["iteratorscov-zip-protocol"]),
  ("_zip_isdone@496", ["iteratorscov-zip-protocol"]),
  ("_zip_isdone@501", ["iteratorscov-zip-protocol"]),
  ("IteratorSize@503", ["iteratorscov-zip-traits"]),
  ("IteratorEltype@504", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@506", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@507", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@508", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@509", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@510", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@511", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@512", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@513", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@515", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@516", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@517", ["iteratorscov-zip-traits"]),
  ("last@519", ["iteratorscov-zip-metadata"]),
  ("reverse@521", ["iterators-zip-reverse"]),
  ("filter@576", ["iteratorscov-filter"]),
  ("iterate@578", ["iteratorscov-filter"]),
  ("eltype@594", ["iteratorscov-filter"]),
  ("IteratorEltype@595", ["iteratorscov-filter"]),
  ("IteratorSize@596", ["iteratorscov-filter"]),
  ("reverse@598", ["iteratorscov-filter"]),
  ("last@599", ["iteratorscov-filter"]),
  ("accumulate@641", ["iterators-accumulate"]),
  ("iterate@643", ["iteratorscov-accumulate"]),
  ("iterate@652", ["iteratorscov-accumulate"]),
  ("length@661", ["iteratorscov-accumulate"]),
  ("size@662", ["iteratorscov-accumulate"]),
  ("IteratorSize@664", ["iteratorscov-accumulate"]),
  ("IteratorEltype@665", ["iteratorscov-accumulate"]),
  ("rest@696", ["iteratorscov-rest"]),
  ("rest@697", ["iteratorscov-rest"]),
  ("rest@698", ["iteratorscov-rest"]),
  ("peel@725", ["iterators-rest-isdone-state"]),
  ("iterate@732", ["iteratorscov-rest"]),
  ("isdone@733", ["iterators-rest-isdone-state"]),
  ("eltype@735", ["iteratorscov-rest"]),
  ("IteratorEltype@736", ["iteratorscov-rest"]),
  ("rest_iteratorsize@737", ["iteratorscov-rest"]),
  ("rest_iteratorsize@738", ["iteratorscov-rest"]),
  ("IteratorSize@739", ["iteratorscov-rest"]),
  ("countfrom@764", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@765", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@766", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@767", ["iteratorscov-countfrom-eltype"]),
  ("eltype@770", ["iteratorscov-countfrom-eltype"]),
  ("iterate@772", ["iteratorscov-countfrom-eltype"]),
  ("IteratorSize@774", ["iteratorscov-countfrom-eltype"]),
  ("Take@781", ["iteratorscov-take"]),
  ("take@815", ["iteratorscov-take"]),
  ("take@816", ["iteratorscov-take"]),
  ("eltype@818", ["iteratorscov-take"]),
  ("IteratorEltype@819", ["iteratorscov-take"]),
  ("take_iteratorsize@820", ["iteratorscov-take"]),
  ("take_iteratorsize@821", ["iteratorscov-take"]),
  ("IteratorSize@822", ["iteratorscov-take"]),
  ("length@823", ["iterators-cycle-empty-length", "iterators-take"]),
  ("isdone@824", ["iteratorscov-take"]),
  ("isdone@825", ["iteratorscov-take"]),
  ("iterate@827", ["iteratorscov-take"]),
  ("Drop@840", ["iteratorscov-drop"]),
  ("drop@871", ["iteratorscov-drop"]),
  ("drop@872", ["iteratorscov-drop"]),
  ("drop@873", ["iteratorscov-drop"]),
  ("eltype@875", ["iteratorscov-drop"]),
  ("IteratorEltype@876", ["iteratorscov-drop"]),
  ("drop_iteratorsize@877", ["iteratorscov-drop"]),
  ("drop_iteratorsize@878", ["iteratorscov-drop"]),
  ("drop_iteratorsize@879", ["iteratorscov-drop"]),
  ("IteratorSize@880", ["iteratorscov-drop"]),
  ("length@881", ["iterators-drop"]),
  ("iterate@883", ["iteratorscov-drop"]),
  ("iterate@891", ["iteratorscov-drop"]),
  ("isdone@892", ["iteratorscov-drop"]),
  ("takewhile@928", ["iterators-takewhile-dropwhile"]),
  ("iterate@930", ["iteratorscov-while"]),
  ("IteratorSize@937", ["iteratorscov-while"]),
  ("eltype@938", ["iteratorscov-while"]),
  ("IteratorEltype@939", ["iteratorscov-while"]),
  ("dropwhile@976", ["iterators-takewhile-dropwhile"]),
  ("iterate@978", ["iteratorscov-while"]),
  ("iterate@979", ["iteratorscov-while"]),
  ("IteratorSize@988", ["iteratorscov-while"]),
  ("eltype@989", ["iteratorscov-while"]),
  ("IteratorEltype@990", ["iteratorscov-while"]),
  ("findeach@1016", ["iteratorscov-cycle-repeated"]),
  ("findeach@1018", ["iteratorscov-cycle-repeated"]),
  ("cycle@1058", ["iterators-cycle-n", "iterators-nth-cycle-overflow"]),
  ("cycle@1059", ["iteratorscov-cycle-repeated"]),
  ("eltype@1061", ["iteratorscov-cycle-repeated"]),
  ("IteratorEltype@1062", ["iteratorscov-cycle-repeated"]),
  ("IteratorSize@1063", ["iteratorscov-cycle-repeated"]),
  ("iterate@1065", ["iteratorscov-cycle-repeated"]),
  ("isdone@1066", ["iteratorscov-cycle-repeated"]),
  ("isdone@1067", ["iteratorscov-cycle-repeated"]),
  ("iterate@1068", ["iteratorscov-cycle-repeated"]),
  ("reverse@1074", ["iteratorscov-cycle-repeated"]),
  ("last@1075", ["iteratorscov-cycle-repeated"]),
  ("repeated@1083", ["iterators-repeated-n"]),
  ("repeated@1111", ["iteratorscov-cycle-repeated"]),
  ("eltype@1113", ["iteratorscov-cycle-repeated"]),
  ("iterate@1115", ["iteratorscov-cycle-repeated"]),
  ("IteratorSize@1117", ["iteratorscov-cycle-repeated"]),
  ("IteratorEltype@1118", ["iteratorscov-cycle-repeated"]),
  ("reverse@1120", ["iteratorscov-cycle-repeated"]),
  ("last@1121", ["iteratorscov-cycle-repeated"]),
  ("product@1148", ["iterators-product"]),
  ("IteratorSize@1150", ["iteratorscov-product-empty-infinite"]),
  ("IteratorSize@1151", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1154", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1155", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1157", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1158", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1159", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1160", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1163", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1164", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1165", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1166", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1167", ["iteratorscov-product-empty-infinite"]),
  ("size@1169", ["iterators-product"]),
  ("_prod_size@1170", ["iteratorscov-product-methods"]),
  ("_prod_size@1171", ["iteratorscov-product-methods"]),
  ("_prod_size1@1172", ["iteratorscov-product-methods"]),
  ("_prod_size1@1173", ["iteratorscov-product-methods"]),
  ("_prod_size1@1174", ["iteratorscov-product-methods"]),
  ("axes@1177", ["iteratorscov-product-methods"]),
  ("_prod_indices@1178", ["iteratorscov-product-methods"]),
  ("_prod_indices@1179", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1180", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1181", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1182", ["iteratorscov-product-methods"]),
  ("ndims@1185", ["iteratorscov-product-methods"]),
  ("length@1186", ["iterators-product-length-zero"]),
  ("IteratorEltype@1188", ["iteratorscov-product-methods"]),
  ("IteratorEltype@1189", ["iteratorscov-product-methods"]),
  ("IteratorEltype@1191", ["iteratorscov-product-methods"]),
  ("eltype@1197", ["iteratorscov-product-methods"]),
  ("_prod_eltype@1198", ["iteratorscov-product-methods"]),
  ("_prod_eltype@1199", ["iteratorscov-product-methods"]),
  ("iterate@1201", ["iteratorscov-product-methods"]),
  ("iterate@1202", ["iteratorscov-product-methods"]),
  ("isdone@1204", ["iteratorscov-product-methods"]),
  ("_pisdone@1205", ["iterators-product-stateful-done"]),
  ("isdone@1213", ["iteratorscov-product-methods"]),
  ("isdone@1214", ["iteratorscov-product-methods"]),
  ("_piterate@1216", ["iteratorscov-product-methods"]),
  ("_piterate@1217", ["iteratorscov-product-methods"]),
  ("iterate@1226", ["iteratorscov-product-methods"]),
  ("_piterate1@1233", ["iteratorscov-product-methods"]),
  ("_piterate1@1234", ["iteratorscov-product-methods"]),
  ("iterate@1248", ["iteratorscov-product-methods"]),
  ("reverse@1255", ["iteratorscov-product-methods"]),
  ("last@1256", ["iterators-product-last-empty"]),
  ("intersect@1257", ["iteratorscov-product-intersect-arity"]),
  ("flatten@1291", ["iterators-flatten"]),
  ("eltype@1293", ["iteratorscov-flatten-methods"]),
  ("eltype@1298", ["iteratorscov-flatten-methods"]),
  ("eltype@1301", ["iteratorscov-flatten-methods"]),
  ("IteratorEltype@1305", ["iteratorscov-flatten-methods"]),
  ("IteratorEltype@1306", ["iteratorscov-flatten-methods"]),
  ("_flatteneltype@1307", ["iteratorscov-flatten-methods"]),
  ("_flatteneltype@1308", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1310", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1311", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1313", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1314", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1315", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1316", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1318", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1319", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1320", ["iteratorscov-flatten-methods"]),
  ("IteratorSize@1322", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1324", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1325", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1326", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1329", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1330", ["iteratorscov-flatten-methods"]),
  ("length@1332", ["iteratorscov-flatten-methods"]),
  ("length@1333", ["iteratorscov-flatten-methods"]),
  ("iterate@1335", ["iteratorscov-flatten-methods"]),
  ("iterate@1354", ["iteratorscov-flatten-methods"]),
  ("reverse@1379", ["iteratorscov-flatten-methods"]),
  ("last@1380", ["iteratorscov-flatten-methods"]),
  ("flatmap@1421", ["iteratorscov-cycle-repeated"]),
  ("partition@1436", ["iterators-partition-vector"]),
  ("PartitionIterator@1446", ["iteratorscov-partition-methods"]),
  ("PartitionIterator@1447", ["iteratorscov-partition-methods"]),
  ("eltype@1449", ["iteratorscov-partition-methods"]),
  ("eltype@1451", ["iteratorscov-partition-methods"]),
  ("eltype@1453", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1455", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1456", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1457", ["iteratorscov-partition-methods"]),
  ("partition_iteratorsize@1459", ["iteratorscov-partition-methods"]),
  ("partition_iteratorsize@1460", ["iteratorscov-partition-methods"]),
  ("IteratorSize@1461", ["iteratorscov-partition-methods"]),
  ("length@1465", ["iterators-partition-vector"]),
  ("iterate@1470", ["iterators-partition-range-overflow", "iteratorscov-partition-methods"]),
  ("iterate@1476", ["iteratorscov-partition-methods"]),
  ("iterate@1484", ["iterators-partition-generic-alloc", "iteratorscov-partition-methods"]),
  ("Stateful{<:Any, Any}@1566", ["iteratorscov-stateful-methods"]),
  ("Stateful@1569", ["iteratorscov-stateful-methods"]),
  ("reset!@1575", ["iteratorscov-stateful-methods"]),
  ("reset!@1579", ["iteratorscov-stateful-methods"]),
  ("approx_iter_type@1589", ["iteratorscov-stateful-methods"]),
  ("doiterate@1592", ["iteratorscov-stateful-methods"]),
  ("_approx_iter_type@1597", ["iteratorscov-stateful-methods"]),
  ("Stateful@1605", ["iteratorscov-stateful-methods"]),
  ("convert@1606", ["iteratorscov-stateful-methods"]),
  ("isdone@1607", ["iterators-stateful"]),
  ("popfirst!@1609", ["iterators-stateful"]),
  ("peek@1620", ["iterators-stateful"]),
  ("iterate@1624", ["iteratorscov-stateful-methods"]),
  ("IteratorSize@1625", ["iteratorscov-stateful-methods"]),
  ("eltype@1626", ["iteratorscov-stateful-methods"]),
  ("IteratorEltype@1627", ["iteratorscov-stateful-methods"]),
  ("only@1659", ["iteratorscov-only-nth-methods"]),
  ("_only@1661", ["iteratorscov-only-nth-methods"]),
  ("_only@1673", ["iteratorscov-only-nth-methods"]),
  ("only@1680", ["iteratorscov-only-nth-methods"]),
  ("only@1683", ["iteratorscov-only-nth-methods"]),
  ("only@1684", ["iteratorscov-only-nth-methods"]),
  ("only@1687", ["iteratorscov-only-nth-methods"]),
  ("only@1688", ["iteratorscov-only-nth-methods"]),
  ("IteratorSize@1704", ["iteratorscov-iterable-state-pairs"]),
  ("length@1705", ["iteratorscov-iterable-state-pairs"]),
  ("Base.eltype@1706", ["iteratorscov-iterable-state-pairs"]),
  ("iterate@1708", ["iteratorscov-iterable-state-pairs"]),
  ("reverse@1714", ["iteratorscov-iterable-state-pairs"]),
  ("reverse@1715", ["iteratorscov-iterable-state-pairs"]),
  ("iterate@1717", ["iteratorscov-iterable-state-pairs"]),
  ("pairs@1725", ["iteratorscov-iterable-state-pairs"]),
  ("nth@1753", ["iteratorscov-only-nth-methods"]),
  ("nth@1754", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("nth@1755", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("nth@1756", ["iterators-nth-vector", "iterators-nth-unsigned-offset"]),
  ("_nth@1758", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("_nth@1767", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("_nth@1777", ["iteratorscov-only-nth-methods"]),
  ("_nth@1789", ["iterators-nth-zip-empty", "iteratorscov-only-nth-methods"]),
  ("nth@1810", ["iteratorscov-only-nth-methods"])
]

end JuliaLean.Proofs.base.iterators
