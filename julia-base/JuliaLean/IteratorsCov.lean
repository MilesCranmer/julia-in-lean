import JuliaLean.Registry.Types
import JuliaLean.IteratorsCov.Count
import JuliaLean.IteratorsCov.Wrappers
import JuliaLean.IteratorsCov.Reverse
import JuliaLean.IteratorsCov.Product
import JuliaLean.IteratorsCov.Metadata
import JuliaLean.IteratorsCov.AnyAll
import JuliaLean.IteratorsCov.SimdLoop

namespace JuliaLean.IteratorsCov

open JuliaLean.Registry

/-- Registry entries for the four iterator implementation files. -/
def entries : List Entry := [
  { id := "iteratorscov-generator-semantics", juliaFile := "base/generator.jl"
    juliaFns := ["Generator", "iterate(::Generator)", "length(::Generator)", "size(::Generator)",
      "axes(::Generator)", "ndims(::Generator)", "keys(::Generator)", "last(::Generator)",
      "isempty(::Generator)", "isdone(::Generator)", "IteratorSize", "IteratorEltype", "haslength"]
    statement := "Generator maps each yielded value, delegates collection metadata, and implements the documented IteratorSize and IteratorEltype defaults and special cases."
    source := "Generator, IteratorSize and IteratorEltype docstrings; base/generator.jl:37-134"
    status := .proven, prop := ``GeneratorSemantics, thm := some ``generatorSemantics },
  { id := "iteratorscov-anyall-semantics", juliaFile := "base/anyall.jl"
    juliaFns := ["any", "_any", "_any_tuple", "all", "_all", "_all_tuple"]
    statement := "Every any/all loop and tuple specialization implements documented short-circuiting three-valued logic and throws TypeError for a non-boolean predicate result."
    source := "any and all docstrings; base/anyall.jl:41-257"
    status := .proven, prop := ``AnyAllSemantics, thm := some ``anyAllSemantics },
  { id := "iteratorscov-simdloop-semantics", juliaFile := "base/simdloop.jl"
    juliaFns := ["parse_iteration_space", "check_body!", "simd_outer_range", "simd_inner_length",
      "simd_index", "compile", "@simd"]
    statement := "The SIMD parser validates the loop shape, rejects nested forbidden control flow, constructs the documented indexed loop expansion, and accepts only the ivdep option."
    source := "@simd docstring and invariant; base/simdloop.jl:17-137"
    status := .proven, prop := ``SimdLoopSemantics, thm := some ``simdLoopSemantics },
  { id := "iteratorscov-pairs-semantics", juliaFile := "base/iterators.jl"
    juliaFns := ["pairs", "_pairs_elt", "iterate(::Pairs)", "iterate(::Reverse{<:Pairs})",
      "length(::Pairs)", "axes(::Pairs)", "size(::Pairs)", "isdone(::Pairs)",
      "last(::Pairs)", "haskey(::Pairs)", "keys(::Pairs)", "values(::Pairs)",
      "getindex(::Pairs)", "setindex!(::Pairs)", "get(::Pairs)"]
    statement := "Pairs retains the selected keys and data, iterates corresponding key-value pairs in order, delegates metadata and lookup, and reverse iteration reverses those pairs."
    source := "pairs docstring and dictionary invariants; base/iterators.jl:281-332"
    status := .proven, prop := ``PairsSemantics, thm := some ``pairsSemantics },
  { id := "iteratorscov-cycle-repeated", juliaFile := "base/iterators.jl"
    juliaFns := ["map", "findeach", "cycle", "repeated", "iterate(::Cycle)",
      "iterate(::Repeated)", "reverse(::Cycle)", "reverse(::Repeated)", "last(::Cycle)",
      "last(::Repeated)", "flatmap"]
    statement := "Iterator map builds a Generator, findeach returns matching keys, finite cycle and repeated return their documented repetitions, and flatmap concatenates mapped collections."
    source := "map, findeach, cycle, repeated and flatmap docstrings; base/iterators.jl:56,995-1121,1421"
    status := .proven, prop := ``CycleRepeatedSemantics, thm := some ``cycleRepeatedSemantics },
  { id := "iteratorscov-iterable-state-pairs", juliaFile := "base/iterators.jl"
    juliaFns := ["IterableStatePairs", "iterate(::IterableStatePairs)",
      "reverse(::IterableStatePairs)", "pairs(::AbstractString)"]
    statement := "IterableStatePairs pairs each iteration state with its value, preserves length and element order, and reverse pairs reverse both sequences."
    source := "IterableStatePairs invariant; base/iterators.jl:1693-1725"
    status := .proven, prop := ``IterableStatePairsSemantics, thm := some ``iterableStatePairsSemantics },
  { id := "iteratorscov-product-methods", juliaFile := "base/iterators.jl"
    juliaFns := ["product", "size(::ProductIterator)", "axes(::ProductIterator)",
      "ndims(::ProductIterator)", "length(::ProductIterator)", "IteratorEltype(::ProductIterator)",
      "eltype(::ProductIterator)", "iterate(::ProductIterator)", "_piterate", "_piterate1",
      "reverse(::ProductIterator)", "last(::ProductIterator)"]
    statement := "ProductIterator implements Cartesian-product order, truthful finite metadata, empty-product and odometer iteration, componentwise reverse, and componentwise last."
    source := "product docstring and collection invariants; base/iterators.jl:1148-1256"
    status := .proven, prop := ``ProductMethodSemantics, thm := some ``productMethodSemantics },
  { id := "iteratorscov-flatten-methods", juliaFile := "base/iterators.jl"
    juliaFns := ["flatten", "eltype(::Flatten)", "IteratorEltype(::Flatten)",
      "IteratorSize(::Flatten)", "flatten_length", "length(::Flatten)", "iterate(::Flatten)",
      "reverse(::Flatten)", "last(::Flatten)"]
    statement := "Flatten concatenates inner iterators and implements its documented type, size, length, reverse and last behavior."
    source := "flatten docstring and invariants; base/iterators.jl:1268-1380"
    status := .proven, prop := ``FlattenMethodSemantics, thm := some ``flattenMethodSemantics },
  { id := "iteratorscov-partition-methods", juliaFile := "base/iterators.jl"
    juliaFns := ["partition", "PartitionIterator", "eltype(::PartitionIterator)",
      "IteratorEltype(::PartitionIterator)", "IteratorSize(::PartitionIterator)",
      "length(::PartitionIterator)", "iterate(::PartitionIterator)"]
    statement := "Partition rejects nonpositive counts, yields consecutive chunks with a shorter final chunk, and computes its element type, size trait and number of chunks."
    source := "partition docstring; base/iterators.jl:1426-1502"
    status := .proven, prop := ``PartitionMethodSemantics, thm := some ``partitionMethodSemantics },
  { id := "iteratorscov-stateful-methods", juliaFile := "base/iterators.jl"
    juliaFns := ["Stateful", "reset!", "approx_iter_type", "doiterate", "_approx_iter_type",
      "convert(::Type{Stateful})", "isdone(::Stateful)", "popfirst!(::Stateful)",
      "peek(::Stateful)", "iterate(::Stateful)", "IteratorSize(::Stateful)",
      "eltype(::Stateful)", "IteratorEltype(::Stateful)"]
    statement := "Stateful stores the next value-state pair, resumes destructively, resets to the first pair, reports exhaustion consistently, and uses the documented conservative type approximation."
    source := "Stateful docstring and invariants; base/iterators.jl:1505-1627"
    status := .proven, prop := ``StatefulMethodSemantics, thm := some ``statefulMethodSemantics },
  { id := "iteratorscov-only-nth-methods", juliaFile := "base/iterators.jl"
    juliaFns := ["only", "_only", "nth", "_nth"]
    statement := "only returns exactly one element and rejects other cardinalities; nth returns the requested element or BoundsError and its curried form delegates to nth."
    source := "only and nth docstrings; base/iterators.jl:1632-1690,1730-1810"
    status := .proven, prop := ``OnlyNthMethodSemantics, thm := some ``onlyNthMethodSemantics },
  { id := "iteratorscov-zip-metadata", juliaFile := "base/iterators.jl"
    juliaFns := ["length(::Zip)", "_zip_min_length", "_zip_lengths_finite_equal",
      "size(::Zip)", "axes(::Zip)", "_promote_tuple_shape", "eltype(::Zip)", "last(::Zip)"]
    statement := "Zip computes the shortest finite length, promotes compatible shapes, constructs its tuple eltype and returns the component values at the last shared index."
    source := "zip docstring and invariants; base/iterators.jl:380-425,519"
    status := .proven, prop := ``ZipMetadata, thm := some ``zipMetadata },

  { id := "iteratorscov-trait-composition", juliaFile := "base/iterators.jl"
    juliaFns := ["and_iteratorsize", "and_iteratoreltype"]
    statement := "Combined iterator traits are symmetric, preserve finite and shape information exactly, and report HasEltype exactly when both inputs do."
    source := "invariant; base/iterators.jl:71-79", status := .proven
    prop := ``AndTraitsSpec, thm := some ``andTraitsSpec },
  { id := "iteratorscov-zip-traits", juliaFile := "base/iterators.jl"
    juliaFns := ["zip_iteratorsize", "zip_iteratoreltype", "IteratorSize(::Type{Zip})", "IteratorEltype(::Type{Zip})"]
    statement := "Zip's size trait agrees with the shortest component and its eltype trait is known exactly when every component's is known."
    source := "zip docstring and invariant; base/iterators.jl:503-517", status := .proven
    prop := ``ZipTraitsSound, thm := some ``zipTraitsSound },
  { id := "iteratorscov-product-empty-infinite", juliaFile := "base/iterators.jl"
    juliaFns := ["prod_iteratorsize(a, ::IsInfinite)", "prod_iteratorsize(::IsInfinite, b)", "IteratorSize(::Type{ProductIterator})"]
    statement := "IteratorSize(product(is...)) agrees with the product's element count, including when a finite factor is empty and another factor is infinite."
    source := "IteratorSize docstring in base/generator.jl:63-67; invariant", status := .refuted
    prop := ``ProductSizeSound, thm := some ``productSizeSound_refuted
    issue := "none found (queries: product IteratorSize, product infinite empty, ProductIterator IsInfinite, product countfrom); related issue #53169"
    notes := "product(1:0, countfrom()) is empty but reports IsInfinite(), which makes zip and take allocate uninitialised results." },
  { id := "iteratorscov-product-shape-finite", juliaFile := "base/iterators.jl"
    juliaFns := ["prod_iteratorsize", "IteratorSize(::Type{ProductIterator})"]
    statement := "Without infinite factors, ProductIterator's size trait agrees with the product count and sums the dimensions of shaped factors."
    source := "invariant; base/iterators.jl:1150-1167", status := .proven
    prop := ``ProductShapeFinite, thm := some ``productShapeFinite },
  { id := "iteratorscov-product-eltype-trait", juliaFile := "base/iterators.jl"
    juliaFns := ["IteratorEltype(::Type{ProductIterator})"]
    statement := "ProductIterator reports HasEltype exactly when every factor reports HasEltype."
    source := "invariant; base/iterators.jl:1188-1195", status := .proven
    prop := ``ProductIelSpec, thm := some ``productIelSpec },
  { id := "iteratorscov-length-helpers", juliaFile := "base/iterators.jl"
    juliaFns := ["_min_length", "_diff_length"]
    statement := "_min_length computes the shorter finite count and _diff_length computes the nonnegative remaining count under truthful iterator traits."
    source := "invariant; base/iterators.jl:58-69", status := .proven
    prop := ``LengthHelpersSpec, thm := some ``lengthHelpersSpec },
  { id := "iteratorscov-take", juliaFile := "base/iterators.jl"
    juliaFns := ["Take", "take", "iterate(::Take)", "IteratorSize(::Type{Take})", "length(::Take)", "isdone(::Take)"]
    statement := "Take rejects negative Int counts, yields the requested prefix, and preserves truthful size, eltype and isdone information."
    source := "take docstring; base/iterators.jl:790-833", status := .proven
    prop := ``TakeSound, thm := some ``takeSound },
  { id := "iteratorscov-drop", juliaFile := "base/iterators.jl"
    juliaFns := ["Drop", "drop", "iterate(::Drop)", "IteratorSize(::Type{Drop})", "length(::Drop)", "isdone(::Drop)"]
    statement := "Drop rejects negative Int counts, yields the suffix after the count, and preserves truthful size, eltype and isdone information."
    source := "drop docstring; base/iterators.jl:849-892", status := .proven
    prop := ``DropSound, thm := some ``dropSound },
  { id := "iteratorscov-countfrom-eltype", juliaFile := "base/iterators.jl"
    juliaFns := ["countfrom(start::Number, step::Number)", "countfrom(start)", "eltype(::Type{Count})", "iterate(::Count)"]
    statement := "The declared eltype of countfrom contains every value that its iterate methods yield."
    source := "eltype docstring; countfrom docstring at base/iterators.jl:748-751", status := .refuted
    prop := ``CountfromEltype, thm := some ``countfromEltype_refuted
    issue := "none found (queries: countfrom Bool, countfrom eltype, Count eltype, Iterators.countfrom InexactError); related merged issue #37747"
    notes := "countfrom(true) reports Bool but yields 2::Int64 on its second step." },
  { id := "iteratorscov-countfrom-integers", juliaFile := "base/iterators.jl"
    juliaFns := ["countfrom", "iterate(::Count)"]
    statement := "For Int inputs, countfrom yields the wrapped additive chain with the declared Int element type."
    source := "countfrom docstring; base/iterators.jl:748-772", status := .proven
    prop := ``CountfromInts, thm := some ``countfromInts },
  { id := "iteratorscov-filter", juliaFile := "base/iterators.jl"
    juliaFns := ["filter", "iterate(::Filter)", "last(::Filter)", "IteratorSize(::Type{Filter})"]
    statement := "Filter yields exactly the elements satisfying its predicate in order, with a truthful eltype and last result."
    source := "filter docstring; base/iterators.jl:536-599", status := .proven
    prop := ``FilterSound, thm := some ``filterSound },
  { id := "iteratorscov-accumulate", juliaFile := "base/iterators.jl"
    juliaFns := ["accumulate", "iterate(::Accumulate)", "length(::Accumulate)", "size(::Accumulate)"]
    statement := "Accumulate yields the documented running reductions and preserves the wrapped iterator's finite length and size."
    source := "accumulate docstring; base/iterators.jl:612-665", status := .proven
    prop := ``AccumulateSound, thm := some ``accumulateSound },
  { id := "iteratorscov-rest", juliaFile := "base/iterators.jl"
    juliaFns := ["rest", "iterate(::Rest)", "IteratorSize(::Type{Rest})"]
    statement := "Rest resumes from the supplied reached state, composes by keeping the newest state, and preserves truthful eltype and size information."
    source := "rest docstring; base/iterators.jl:677-695", status := .proven
    prop := ``RestSound, thm := some ``restSound },
  { id := "iteratorscov-while", juliaFile := "base/iterators.jl"
    juliaFns := ["takewhile", "dropwhile", "iterate(::TakeWhile)", "iterate(::DropWhile)"]
    statement := "TakeWhile yields the longest satisfying prefix and DropWhile yields the remaining suffix, both with truthful eltypes."
    source := "takewhile and dropwhile docstrings; base/iterators.jl:895-990", status := .proven
    prop := ``WhileSound, thm := some ``whileSound },
  { id := "iteratorscov-enumerate", juliaFile := "base/iterators.jl"
    juliaFns := ["enumerate", "iterate(::Enumerate)", "length(::Enumerate)", "size(::Enumerate)", "last(::Enumerate)", "reverse(::Enumerate)"]
    statement := "Enumerate numbers yielded elements from one, preserves size and eltype facts, computes last, and reverses the numbered pairs."
    source := "enumerate docstring; base/iterators.jl:173-213", status := .proven
    prop := ``EnumerateSound, thm := some ``enumerateSound },
  { id := "iteratorscov-reverse-yields", juliaFile := "base/iterators.jl"
    juliaFns := ["reverse", "iterate(::Reverse)", "reverse(::Pair)", "reverse(::Generator)"]
    statement := "The covered Reverse methods yield exactly the wrapped elements backwards, and reversing twice restores the elements."
    source := "reverse docstring; base/iterators.jl:81-162", status := .proven
    prop := ``ReverseYields, thm := some ``reverseYields },
  { id := "iteratorscov-reverse-traits", juliaFile := "base/iterators.jl"
    juliaFns := ["eltype(::Type{Reverse})", "length(::Reverse)", "size(::Reverse)", "IteratorSize(::Type{Reverse})", "IteratorEltype(::Type{Reverse})", "last(::Reverse)"]
    statement := "Reverse preserves array and tuple traits and last(Reverse(A)) is first(A); reversing Bottom throws ArgumentError."
    source := "invariant; base/iterators.jl:128-154", status := .proven
    prop := ``ReverseTraits, thm := some ``reverseTraits },
  { id := "iteratorscov-zip-protocol", juliaFile := "base/iterators.jl"
    juliaFns := ["_zip_isdone", "_zip_iterate_in_order", "_zip_iterate_all", "_zip_any_isdone", "iterate(::Zip)", "isdone(::Zip)"]
    statement := "Zip steps live components in order, preserves an all-false isdone answer, and stops its isdone scan at the first true answer."
    source := "zip docstring and invariant; base/iterators.jl:430-501", status := .proven
    prop := ``ZipProtocol, thm := some ``zipProtocol },
  { id := "iteratorscov-product-intersect-arity", juliaFile := "base/iterators.jl"
    juliaFns := ["intersect(::ProductIterator, ::ProductIterator)"]
    statement := "The intersection of two products with different tuple arities is empty because tuples of different arity cannot be equal."
    source := "intersect docstring; base/iterators.jl:1257", status := .refuted
    prop := ``ProductIntersect, thm := some ``productIntersect_refuted
    issue := "none found (queries: product intersect, ProductIterator intersect, intersect product); related issues #39943 and #39949"
    notes := "Tuple broadcasting repeats a one-factor product against a two-factor product and returns four two-tuples." }
]

end JuliaLean.IteratorsCov
