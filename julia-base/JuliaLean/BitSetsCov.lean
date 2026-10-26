import JuliaLean.BitSetsCov.BitArrayRows
import JuliaLean.Registry.Types

namespace JuliaLean.BitSetsCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "bitsetscov-bitset-build", juliaFile := "base/bitset.jl"
    juliaFns := ["BitSet()", "BitSet(itr)", "union!(::BitSet, itr)",
      "empty(::BitSet)", "emptymutable(::BitSet)", "push!(::BitSet, ::Integer...)" ]
    statement := "BitSet construction is empty, and iterable construction, union!, and variadic push! add exactly the convertible Int elements."
    source := "BitSet docstring, base/bitset.jl:25-41; AbstractSet invariant", status := .proven
    prop := ``BitSetBuildSpec, thm := some ``bitSetBuildSpec },
  { id := "bitsetscov-bitset-copy", juliaFile := "base/bitset.jl"
    juliaFns := ["copy!(::BitSet, ::BitSet)", "copy(::BitSet)", "copymutable(::BitSet)"]
    statement := "The three BitSet copy methods preserve every stored chunk and the offset."
    source := "copy invariant; base/bitset.jl:48-56", status := .proven
    prop := ``BitSetCopySpec, thm := some ``bitSetCopySpec },
  { id := "bitsetscov-bitset-sizehint", juliaFile := "base/bitset.jl"
    juliaFns := ["sizehint!(::BitSet, ::Integer)"]
    statement := "sizehint! changes capacity only and either preserves the BitSet or reports an Int conversion failure for a 128-bit chunk count."
    source := "sizehint! invariant; base/bitset.jl:58-61", status := .proven
    prop := ``BitSetSizehintSpec, thm := some ``bitSetSizehintSpec },
  { id := "bitsetscov-bitset-in", juliaFile := "base/bitset.jl"
    juliaFns := ["_bits_getindex", "_is_convertible_Int", "in(::Integer, ::BitSet)"]
    statement := "BitSet membership reads the selected chunk and rejects Integer values outside Int without changing the answer."
    source := "BitSet set invariant; base/bitset.jl:63-68,279,331", status := .proven
    prop := ``BitSetInSpec, thm := some ``bitSetInSpec },
  { id := "bitsetscov-bitset-delete-pop", juliaFile := "base/bitset.jl"
    juliaFns := ["delete!(::BitSet, ::Int)", "delete!(::BitSet, ::Integer)",
      "pop!(::BitSet, ::Integer)", "pop!(::BitSet, ::Integer, default)"]
    statement := "delete! removes exactly its key; keyed pop! removes and returns a present key, throws without a default, and returns the default when absent."
    source := "AbstractSet delete!/pop! contract; base/bitset.jl:261-281", status := .proven
    prop := ``BitSetDeleteSpec, thm := some ``bitSetDeleteSpec },
  { id := "bitsetscov-bitset-empty", juliaFile := "base/bitset.jl"
    juliaFns := ["empty!(::BitSet)", "isempty(::BitSet)", "_check0"]
    statement := "empty! removes all members and resets the offset; isempty and _check0 hold exactly when the relevant chunks are zero."
    source := "empty!/isempty contract; base/bitset.jl:285-291,368-373", status := .proven
    prop := ``BitSetEmptySpec, thm := some ``bitSetEmptySpec },
  { id := "bitsetscov-bitset-grow", juliaFile := "base/bitset.jl"
    juliaFns := ["_growend0!", "_growbeg0!"]
    statement := "The two growth helpers preserve existing chunks and initialize every new chunk to zero."
    source := "representation invariant; base/bitset.jl:116-129", status := .proven
    prop := ``BitSetGrowSpec, thm := some ``bitSetGrowSpec },
  { id := "bitsetscov-bitset-union-range", juliaFile := "base/bitset.jl"
    juliaFns := ["union!(::BitSet, ::AbstractUnitRange{<:Integer})"]
    statement := "Range union adds exactly every Int in a nonempty range, leaves empty ranges unchanged, and checks conversion of both bounds."
    source := "union contract; base/bitset.jl:131-167", status := .proven
    prop := ``BitSetUnionRangeSpec, thm := some ``bitSetUnionRangeSpec },
  { id := "bitsetscov-bitset-matched-map", juliaFile := "base/bitset.jl"
    juliaFns := ["_matched_map!(f, ::BitSet, ::BitSet)", "_matched_map!(f, ::Bits, ...)",
      "union!(::BitSet, ::BitSet)", "intersect(::BitSet, ::BitSet)",
      "intersect!(::BitSet, ::BitSet)", "setdiff!(::BitSet, ::BitSet)",
      "symdiff!(::BitSet, ::BitSet)"]
    statement := "The matched chunk loop implements memberwise union, intersection, difference, and symmetric difference and preserves the BitSet invariant."
    source := "set-operation contracts; base/bitset.jl:169-253,296-326", status := .proven
    prop := ``BitSetMatchedSpec, thm := some ``bitSetMatchedSpec },
  { id := "bitsetscov-bitset-union", juliaFile := "base/bitset.jl"
    juliaFns := ["union(::BitSet, sets...)"]
    statement := "union copies the first BitSet and adds exactly the members of every following argument."
    source := "union contract; base/bitset.jl:295", status := .proven
    prop := ``BitSetUnionSpec, thm := some ``bitSetUnionSpec },
  { id := "bitsetscov-bitset-symdiff-set", juliaFile := "base/bitset.jl"
    juliaFns := ["symdiff!(::BitSet, ::AbstractSet)"]
    statement := "Symmetric difference with an AbstractSet toggles each distinct convertible Int member exactly once."
    source := "symdiff! docstring; base/bitset.jl:312-317", status := .proven
    prop := ``BitSetSymdiffSetSpec, thm := some ``bitSetSymdiffSetSpec },
  { id := "bitsetscov-bitset-filter-invariant", juliaFile := "base/bitset.jl"
    juliaFns := ["filter!(f, ::BitSet)"]
    statement := "The in-place filter loop preserves the BitSet representation invariant while deleting from the set it iterates."
    source := "representation invariant; base/bitset.jl:328 and base/abstractset.jl:633-641", status := .proven
    prop := ``BitSetFilterSpec, thm := some ``bitSetFilterSpec },
  { id := "bitsetscov-bitset-find", juliaFile := "base/bitset.jl"
    juliaFns := ["_bits_findnext", "_bits_findprev"]
    statement := "The BitSet search helpers return the first set position at or after the start and the last at or before it, or -1."
    source := "search invariant; base/bitset.jl:70-84", status := .proven
    prop := ``BitSetFindSpec, thm := some ``bitSetFindSpec },
  { id := "bitsetscov-bitset-iteration", juliaFile := "base/bitset.jl"
    juliaFns := ["intoffset", "iterate(::BitSet)", "_throw_bitset_notempty_error",
      "first(::BitSet)", "last(::BitSet)", "length(::BitSet)", "show(::IO, ::BitSet)",
      "pop!(::BitSet)", "popfirst!(::BitSet)", "minimum(::BitSet)",
      "maximum(::BitSet)", "extrema(::BitSet)", "issorted(::BitSet)"]
    statement := "BitSet iteration lists every member in increasing order; its extrema, length, pop methods, and printed form agree with that sequence."
    source := "BitSet sorted-set docstring and iteration invariant; base/bitset.jl:43,259,283,333-366,423-426", status := .proven
    prop := ``BitSetIterSpec, thm := some ``bitSetIterSpec },
  { id := "bitsetscov-bitset-equality", juliaFile := "base/bitset.jl"
    juliaFns := ["==(::BitSet, ::BitSet)"]
    statement := "Two BitSets compare equal exactly when they have the same integer members."
    source := "AbstractSet equality invariant; base/bitset.jl:375-407", status := .proven
    prop := ``BitSetEqSpec, thm := some ``bitSetEqSpec },
  { id := "bitsetscov-bitset-subset", juliaFile := "base/bitset.jl"
    juliaFns := ["f(a,b)", "issubset(::BitSet, ::BitSet)", "⊊(::BitSet, ::BitSet)"]
    statement := "The chunk predicate and BitSet subset methods implement member inclusion, with ⊊ requiring a strict difference."
    source := "subset contracts; base/bitset.jl:409-420", status := .proven
    prop := ``BitSetSubsetSpec, thm := some ``bitSetSubsetSpec },
  { id := "bitsetscov-replace-generic-set", juliaFile := "base/set.jl"
    juliaFns := ["replace(::Callable, ::AbstractSet)", "_replace!(::Callable, ::AbstractSet, ::AbstractSet, ::Int)"]
    statement := "Replacing every original member of an AbstractSet with f(x) yields the set of mapped original members."
    source := "replace docstring; base/set.jl:895-896,909-943", status := .refuted
    prop := ``ReplaceGenericSetSpec, thm := some ``replaceGenericSetSpec_refuted
    issue := "#64235 (open, duplicate)"
    notes := "replace(x -> x + 1, BitSet([1,2])) returns BitSet([3]); the distinct destination loses a newly inserted value when the next old value is removed." },
  { id := "bitsetscov-isdisjoint-zero-step", juliaFile := "base/abstractset.jl"
    juliaFns := ["_overlapping_range_isdisjoint(::AbstractRange{<:Integer}, ::AbstractRange{<:Integer})"]
    statement := "isdisjoint on two valid integer ranges returns a Bool, including zero-step StepRangeLen inputs."
    source := "isdisjoint docstring; base/abstractset.jl:612-618", status := .refuted
    prop := ``RangeIsdisjointSpec, thm := some ``rangeIsdisjointSpec_refuted
    issue := "related #47796; none found for zero-step isdisjoint"
    notes := "Equal zero steps take mod(minimum(a), step(a)) and throw DivideError." },
  { id := "bitsetscov-isdisjoint-threshold", juliaFile := "base/abstractset.jl"
    juliaFns := ["isdisjoint(a, b)", "_isdisjoint(a, b)"]
    statement := "Adding irrelevant nonmatching elements to one input cannot change whether two collections are disjoint."
    source := "isdisjoint docstring; base/abstractset.jl:572-584", status := .refuted
    prop := ``IsdisjointSizeIndependent, thm := some ``isdisjointSizeIndependent_refuted
    issue := "related #61893"
    notes := "At 70 elements the implementation converts b to Set and switches signed-zero and NaN comparison from == to isequal." },
  { id := "bitsetscov-allunique-idset", juliaFile := "base/set.jl"
    juliaFns := ["allunique(::Union{AbstractSet,AbstractDict})", "allequal(::Union{AbstractSet,AbstractDict})"]
    statement := "allunique and allequal inspect the iterated values under isequal, including identity collections."
    source := "allunique and allequal docstrings; base/set.jl:544,658", status := .refuted
    prop := ``AlluniqueSetSpec, thm := some ``alluniqueSetSpec_refuted
    issue := "related #61893; none found for IdSet/IdDict"
    notes := "IdSet{Any}([1, 1.0]) contains two identity-distinct but isequal values, yet allunique returns true." },
  { id := "bitsetscov-sizehint-bitvector-integer", juliaFile := "base/bitarray.jl"
    juliaFns := ["sizehint!(::BitVector, ::Integer)"]
    statement := "sizehint! on a BitVector accepts every nonnegative Integer value documented by its signature."
    source := "signature and sizehint! contract; base/bitarray.jl:798-801", status := .refuted
    prop := ``BitSizehintSpec, thm := some ``bitSizehintSpec_refuted
    issue := "none found (queries: sizehint! BitVector; sizehint! BitArray; num_bit_chunks)"
    notes := "The computed chunk count keeps the argument's integer type and misses _resize_int!(..., ::Int) for Int32 and BigInt." },
  { id := "bitsetscov-replace-set-singleton", juliaFile := "base/set.jl"
    juliaFns := ["replace(::AbstractSet, ::Pair...)", "subtract_singletontype"]
    statement := "Replacing a singleton-typed value in a Set returns a Set containing the replaced and all unreplaced members."
    source := "replace docstring; base/set.jl:842-866", status := .refuted
    prop := ``ReplaceSetSingletonSpec, thm := some ``replaceSetSingletonSpec_refuted
    issue := "none found (queries: replace missing Set; replace Set missing; replace singleton type Set)"
    notes := "replace(Set([1, missing]), missing => 0) narrows the temporary Set to Int and then throws while copying missing." },
  { id := "bitsetscov-abstractset-basic", juliaFile := "base/abstractset.jl"
    juliaFns := ["eltype(::Type{<:AbstractSet})", "sizehint!(::AbstractSet, n)", "copy!(::AbstractSet, ::AbstractSet)"]
    statement := "AbstractSet eltype, no-op sizehint!, and copy! follow their dispatch and empty-then-union bodies."
    source := "source-body invariant; base/abstractset.jl:3-9", status := .proven
    prop := ``Coll.AbstractBasicSpec, thm := some ``Coll.abstractBasicSpec },
  { id := "bitsetscov-abstractset-union", juliaFile := "base/abstractset.jl"
    juliaFns := ["union(s, sets...)", "union(::AbstractSet)", "union!(::AbstractSet, sets...)",
      "union!(::AbstractSet{T}, itr)", "max_values"]
    statement := "Generic union methods insert each input in order, stop only at the finite type cardinality, and saturate max_values addition."
    source := "union docstrings and source-body invariant; base/abstractset.jl:57-112", status := .proven
    prop := ``Coll.AbstractUnionSpec, thm := some ``Coll.abstractUnionSpec },
  { id := "bitsetscov-abstractset-intersect", juliaFile := "base/abstractset.jl"
    juliaFns := ["intersect(::AbstractSet, itr, itrs...)", "intersect(s)",
      "intersect(::AbstractSet, itr)", "intersect!(::AbstractSet, itrs...)",
      "intersect!(::AbstractSet, ::AbstractSet)", "intersect!(::AbstractSet, itr)"]
    statement := "Generic intersection follows the shortest-input branch and keeps exactly values present in every argument."
    source := "intersect docstrings and source-body invariant; base/abstractset.jl:155-200", status := .proven
    prop := ``Coll.AbstractIntersectSpec, thm := some ``Coll.abstractIntersectSpec },
  { id := "bitsetscov-abstractset-setdiff", juliaFile := "base/abstractset.jl"
    juliaFns := ["setdiff(::AbstractSet, itrs...)", "setdiff(s)",
      "setdiff!(::AbstractSet, itrs...)", "setdiff!(::AbstractSet, itr)"]
    statement := "Generic set difference copies when needed and deletes every iterated element from each right-hand input."
    source := "setdiff docstrings and source-body invariant; base/abstractset.jl:222-255", status := .proven
    prop := ``Coll.AbstractSetdiffSpec, thm := some ``Coll.abstractSetdiffSpec },
  { id := "bitsetscov-abstractset-symdiff", juliaFile := "base/abstractset.jl"
    juliaFns := ["symdiff(s, sets...)", "symdiff(s)", "symdiff!(::AbstractSet, itrs...)",
      "symdiff!(::AbstractSet, itr)", "symdiff!(::AbstractSet, ::AbstractSet)"]
    statement := "Generic symmetric difference converts non-set iterables to sets and toggles each distinct member."
    source := "symdiff docstrings and source-body invariant; base/abstractset.jl:278-304", status := .proven
    prop := ``Coll.AbstractSymdiffSpec, thm := some ``Coll.abstractSymdiffSpec },
  { id := "bitsetscov-abstractset-subset", juliaFile := "base/abstractset.jl"
    juliaFns := ["issubset(a,b)", "hasfastin", "⊇(a,b)", "issubset(a)", "⊇(a)",
      "⊊ overloads", "⊋ overloads", "⊈ overloads", "⊉ overloads"]
    statement := "Subset, strict-subset, negated-subset, reversed operators, and their Fix2 wrappers follow the source dispatch and conversion branches."
    source := "subset docstrings and source-body invariant; base/abstractset.jl:335-500", status := .proven
    prop := ``Coll.AbstractCompareSpec, thm := some ``Coll.abstractCompareSpec },
  { id := "bitsetscov-abstractset-issetequal", juliaFile := "base/abstractset.jl"
    juliaFns := ["issetequal overloads", "issetequal(a)"]
    statement := "issetequal uses direct set equality or converts the generic side to a Set after its length check."
    source := "issetequal docstring and source-body invariant; base/abstractset.jl:521-549", status := .proven
    prop := ``Coll.AbstractSetequalSpec, thm := some ``Coll.abstractSetequalSpec },
  { id := "bitsetscov-abstractset-disjoint-filter", juliaFile := "base/abstractset.jl"
    juliaFns := ["isdisjoint overloads", "_overlapping_range_isdisjoint", "<", "<=", "filter", "unsafe_filter!", "mapfilter"]
    statement := "Disjointness, range dispatch, containment ordering, and filtering follow their threshold, range, and mutation loops."
    source := "source-body invariant; base/abstractset.jl:572-641", status := .proven
    prop := ``Coll.AbstractDisjointFilterSpec, thm := some ``Coll.abstractDisjointFilterSpec },
  { id := "bitsetscov-set-basic", juliaFile := "base/set.jl"
    juliaFns := ["_Set", "Set constructors", "empty", "emptymutable", "_similar_for"]
    statement := "Set constructors canonicalize iterable keys, copy key sets, and create empty mutable results of the requested element type."
    source := "Set docstring and source-body invariant; base/set.jl:42-73", status := .proven
    prop := ``Coll.SetBasicSpec, thm := some ``Coll.setBasicSpec },
  { id := "bitsetscov-set-mutable", juliaFile := "base/set.jl"
    juliaFns := ["show(::IO,::Set)", "isempty", "length", "in", "in!", "push!", "pop!",
      "delete!", "copy", "copymutable", "sizehint!", "empty!", "rehash!", "iterate", "Iterators.only", "setdiff!"]
    statement := "Mutable Set methods delegate to the backing dictionary and implement the documented membership and mutation results."
    source := "Set and mutation docstrings; base/set.jl:75-198", status := .proven
    prop := ``Coll.SetMutableSpec, thm := some ``Coll.setMutableSpec },
  { id := "bitsetscov-set-unique", juliaFile := "base/set.jl"
    juliaFns := ["unique", "_unique_from", "unique_from", "unique(f,...)", "_unique!", "unique!", "_groupedunique!"]
    statement := "Unique methods retain the first value for each mapped isequal class, with the grouped fast path retaining each group head."
    source := "unique docstrings and source-body invariant; base/set.jl:203-478", status := .proven
    prop := ``Coll.SetUniqueSpec, thm := some ``Coll.setUniqueSpec },
  { id := "bitsetscov-set-predicates", juliaFile := "base/set.jl"
    juliaFns := ["allunique overloads", "_hashed_allunique", "_indexed_allunique", "allequal overloads", "_allequal_loop"]
    statement := "Generic allunique and allequal paths implement isequal-based distinctness and equality, including tuple and string cutoffs."
    source := "allunique and allequal docstrings; base/set.jl:515-693", status := .proven
    prop := ``Coll.SetPredicatesSpec, thm := some ``Coll.setPredicatesSpec },
  { id := "bitsetscov-set-helpers", juliaFile := "base/set.jl"
    juliaFns := ["filter!(::Set)", "hash(::AbstractSet)", "convert(::AbstractSet)", "check_count", "_copy_oftype", "_similar_or_copy"]
    statement := "Set filter, unordered hash, conversion, count validation, and copy-selection helpers follow their source bodies."
    source := "source-body invariant; base/set.jl:695-731", status := .proven
    prop := ``Coll.SetHelpersSpec, thm := some ``Coll.setHelpersSpec },
  { id := "bitsetscov-set-replace", juliaFile := "base/set.jl"
    juliaFns := ["replace! overloads", "replace_pairs!", "new", "replace overloads", "promote_valuetype",
      "subtract_singletontype", "askey", "_replace! overloads", "_replace tuple"]
    statement := "Replacement helpers scan pairs in order, enforce the shared count, choose copy types, and use the container-specific mutation loops."
    source := "replace and replace! docstrings and source-body invariant; base/set.jl:762-1046", status := .proven
    prop := ``Coll.SetReplaceSpec, thm := some ``Coll.setReplaceSpec },
  { id := "bitsetscov-idset-basic", juliaFile := "base/idset.jl"
    juliaFns := ["IdSet constructors", "copymutable", "emptymutable", "copy", "haskey", "isempty"]
    statement := "IdSet constructors, copies, and lookups preserve identity-keyed membership."
    source := "IdSet docstring and source-body invariant; base/idset.jl:34-45", status := .proven
    prop := ``Coll.IdSetBasicSpec, thm := some ``Coll.idSetBasicSpec },
  { id := "bitsetscov-idset-pop", juliaFile := "base/idset.jl"
    juliaFns := ["_pop!(::IdSet,x)", "pop!(::IdSet,x)", "pop!(::IdSet,x,default)"]
    statement := "Identity-set pop removes the matching identity, returns the supplied object, and distinguishes throwing from default overloads."
    source := "source-body invariant; base/idset.jl:71-82", status := .proven
    prop := ``Coll.IdSetPopSpec, thm := some ``Coll.idSetPopSpec },
  { id := "bitsetscov-idset-memory", juliaFile := "base/idset.jl"
    juliaFns := ["_zero!(::Memory{<:BitInteger})", "filter!(::IdSet)"]
    statement := "_zero! clears every memory element and IdSet filter retains exactly identities whose values satisfy the predicate."
    source := "source-body invariant; base/idset.jl:99-119", status := .proven
    prop := ``Coll.IdSetMemorySpec, thm := some ``Coll.idSetMemorySpec },
  { id := "bitsetscov-bitarray-construct", juliaFile := "base/bitarray.jl"
    juliaFns := ["BitArray undef constructors", "BitVector()", "BitVector(::Tuple)",
      "length(::BitArray)", "size(::BitArray)", "isassigned", "IndexStyle", "dataids"]
    statement := "BitArray constructors allocate the required packed length, and basic shape and storage queries return their fields."
    source := "BitArray representation and source-body invariant; base/bitarray.jl:28-110", status := .proven
    prop := ``BARows.ConstructSpec, thm := some ``BARows.constructSpec },
  { id := "bitsetscov-bitarray-chunks", juliaFile := "base/bitarray.jl"
    juliaFns := ["_div64", "_mod64", "_blsr", "_msk_end", "num_bit_chunks", "get_chunks_id",
      "glue_src_bitchunks", "fill_chunks!", "copy_to_bitarray_chunks!", "pack8bools", "dumpbitcache", "iterate(::BitArray)"]
    statement := "Chunk addressing, masks, gluing, Boolean packing, copying, filling, and iteration follow the UInt64 packed representation."
    source := "representation invariant and source-body invariant; base/bitarray.jl:115-355", status := .proven
    prop := ``BARows.ChunkSpec, thm := some ``BARows.chunkSpec },
  { id := "bitsetscov-bitarray-shape", juliaFile := "base/bitarray.jl"
    juliaFns := ["similar(::BitArray)", "falses", "trues", "one(::BitMatrix)", "reshape(::BitArray)",
      "Array(::BitArray)", "BitArray(::AbstractArray)", "convert(::Type{<:BitArray}, ::AbstractArray)"]
    statement := "Shape constructors allocate the product of dimensions, reshape preserves shared data when lengths agree, and conversions preserve Boolean elements."
    source := "source-body invariant; base/bitarray.jl:359-536", status := .proven
    prop := ``BARows.ShapeSpec, thm := some ``BARows.shapeSpec },
  { id := "bitsetscov-bitarray-copy-generate", juliaFile := "base/bitarray.jl"
    juliaFns := ["copyto! overloads", "unsafe_copyto!", "_copyto_int!", "_copyto_bitarray!",
      "BitArray iterator constructors", "gen_bitarray", "gen_bitarrayN", "gen_bitarray_from_itr",
      "fill_bitarray_from_itr!", "indexoffset", "setindex! range", "empty!(::BitVector)"]
    statement := "BitArray copy and iterator construction preserve order, shape and checked lengths; range assignment writes the selected packed span."
    source := "source-body invariant; base/bitarray.jl:429-699,1137-1141", status := .proven
    prop := ``BARows.CopyGenerateSpec, thm := some ``BARows.copyGenerateSpec },
  { id := "bitsetscov-bitarray-mutation", juliaFile := "base/bitarray.jl"
    juliaFns := ["deleteat!(::BitVector, inds)", "deleteat!(::BitVector, ::AbstractVector{Bool})",
      "keepat! overloads", "splice! overloads", "_splice_int!"]
    statement := "BitVector bulk deletion validates increasing indices, Boolean masks select positions, and splice returns the removed segment while inserting replacements."
    source := "source-body invariant; base/bitarray.jl:979-1134", status := .proven
    prop := ``BARows.MutationSpec, thm := some ``BARows.mutationSpec },
  { id := "bitsetscov-bitarray-arithmetic", juliaFile := "base/bitarray.jl"
    juliaFns := ["-(::BitArray)", "bitwise binary overloads", "/(::BitArray,::Number)",
      "/(::Number,::BitArray)", "==(::BitArray,::BitArray)"]
    statement := "BitArray arithmetic maps Boolean values elementwise, binary bit operations zip matching shapes, and equality checks shape and packed data."
    source := "source-body invariant; base/bitarray.jl:1145-1209", status := .proven
    prop := ``BARows.ArithmeticSpec, thm := some ``BARows.arithmeticSpec },
  { id := "bitsetscov-bitarray-reduce-map", juliaFile := "base/bitarray.jl"
    juliaFns := ["findmax(::BitArray)", "findmin(::BitArray)", "allindices!", "_overflowind", "_toind",
      "findall(::BitArray)", "_sum(::BitArray)", "minimum", "maximum", "map overloads", "map! overloads",
      "bit_map", "bit_map_constant!", "bit_map!", "filter(::BitArray)"]
    statement := "BitArray reductions, index collection, extrema, map specializations and filter operate on the packed Boolean sequence in linear index order."
    source := "source-body invariant; base/bitarray.jl:1611-1833", status := .proven
    prop := ``BARows.ReduceMapSpec, thm := some ``BARows.reduceMapSpec },
  { id := "bitsetscov-bitarray-cat", juliaFile := "base/bitarray.jl"
    juliaFns := ["hcat(::BitVector...)", "vcat(::BitVector...)", "hcat(::BitArray...)",
      "vcat(::BitMatrix...)", "_cat", "sizeof(::BitArray)"]
    statement := "BitArray concatenation appends packed element sequences along the requested dimension, and sizeof counts eight bytes per UInt64 chunk."
    source := "source-body invariant; base/bitarray.jl:1838-1930", status := .proven
    prop := ``BARows.CatSpec, thm := some ``BARows.catSpec }
]

end JuliaLean.BitSetsCov
