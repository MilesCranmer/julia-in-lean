import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Iterators.Model
import JuliaLean.Iterators.Funs
import JuliaLean.Iterators.Props
import JuliaLean.Iterators.Spec
import JuliaLean.Iterators.Proofs

namespace JuliaLean.Iterators

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "iterators-take-isdone-zero", juliaFile := "base/iterators.jl"
    juliaFns := ["isdone(::Take)", "isempty(::Take)", "zip"]
    statement := "isempty(take(itr, n)) is true exactly when take(itr, n) yields nothing, for itr a vector or an Iterators.Stateful."
    source := "base/essentials.jl:1204-1206 (isempty docstring), 1574-1587 (isdone docstring)", status := .refuted
    prop := ``TakeIsemptyCorrect, thm := some ``takeIsemptyCorrect_refuted
    issue := "none found (queries: isdone Take, isempty take Stateful, isempty Stateful take 0, zip Stateful advance; related merged PR #63733)"
    notes := "isdone(t::Take) = isdone(t.xs) ignores t.n: isempty(take(Stateful([1,2,3]), 0)) is false, and zip advances other stateful iterators." },
  { id := "iterators-rest-isdone-state", juliaFile := "base/iterators.jl"
    juliaFns := ["isdone(::Rest)", "isempty(::Rest)", "peel"]
    statement := "For (x, r) = Iterators.peel(itr), isempty(r) is true exactly when r yields nothing."
    source := "base/iterators.jl:700-704 (peel docstring), base/essentials.jl:1204 (isempty)", status := .refuted
    prop := ``PeelRestIsempty, thm := some ``peelRestIsempty_refuted
    issue := "none found (queries: isdone Rest, peel isempty, Iterators.rest isdone)"
    notes := "isdone(i::Rest, st...) = isdone(i.itr, st...) asks the wrapped iterator about its start instead of i.st; counterexample peel(take(Stateful([1,2,3]), 1))." },
  { id := "iterators-drop-drop-overflow", juliaFile := "base/iterators.jl"
    juliaFns := ["drop(::Drop, n)", "drop(::Take, n)"]
    statement := "drop(drop(v, a), b) of a vector succeeds for all a, b >= 0 and yields all but the first a + b elements."
    source := "base/iterators.jl:849 (drop docstring)", status := .refuted
    prop := ``DropDropCorrect, thm := some ``dropDropCorrect_refuted
    issue := "none found (queries: drop overflow, Drop length must be non-negative)"
    notes := "Int(n) + xs.n wraps: drop(drop([1,2,3], typemax(Int)), 1) throws ArgumentError." },
  { id := "iterators-nth-cycle-overflow", juliaFile := "base/iterators.jl"
    juliaFns := ["nth(::Flatten{Take{Repeated}}, n)", "cycle(xs, n)"]
    statement := "nth(cycle(v, m), k) is v[mod1(k, length(v))] for every 1 <= k <= length(v) * m."
    source := "base/iterators.jl:1730 (nth docstring), 1031 (cycle docstring)", status := .refuted
    prop := ``NthCycleCorrect, thm := some ``nthCycleCorrect_refuted
    issue := "none found (queries: nth cycle, Iterators.nth, nth BoundsError; nth added in #56580)"
    notes := "k*cycles wraps: nth(cycle([1,2,3], 2^62), 1) throws BoundsError." },
  { id := "iterators-nth-zip-empty", juliaFile := "base/iterators.jl"
    juliaFns := ["nth(::Zip, n)"]
    statement := "nth(zip(vs...), n) throws BoundsError for n <= 0."
    source := "base/iterators.jl:1730 (nth docstring: throw a BoundsError if not existing)", status := .refuted
    prop := ``NthZipNonpositive, thm := some ``nthZipNonpositive_refuted
    issue := "none found (queries: nth zip, Iterators.nth, nth BoundsError)"
    notes := "_nth(::IteratorSize, z::Zip, n) = map(nth(n), z.is) never checks n; for zip() it returns ()." },
  { id := "iterators-nth-unsigned-offset", juliaFile := "base/iterators.jl"
    juliaFns := ["nth(::AbstractArray, n)"]
    statement := "nth(A, n) returns the n-th element of A = IdentityUnitRange(fi:li) for every in-range n of every integer type."
    source := "base/iterators.jl:1730 (nth docstring)", status := .refuted
    prop := ``NthAnyIntegerType, thm := some ``nthAnyIntegerType_refuted
    issue := "none found (queries: nth unsigned, nth offset, Iterators.nth)"
    notes := "begin + n - 1 is computed in UInt64 when n::UInt64; a negative firstindex wraps to a huge index." },
  { id := "iterators-product-length-zero", juliaFile := "base/iterators.jl"
    juliaFns := ["length(::ProductIterator)"]
    statement := "length(product(1:l1, ..., 1:lk)) is l1*...*lk whenever that count fits in an Int."
    source := "invariant (length is the number of elements; collect and isempty agree)", status := .refuted
    prop := ``ProductLengthExact, thm := some ``productLengthExact_refuted
    issue := "none found (queries: product length overflow, product length checked_mul)"
    notes := "reduce(checked_mul, size(P); init=1) folds left: length(product(1:2^32, 1:2^32, 1:0)) throws OverflowError." },
  { id := "iterators-product-last-empty", juliaFile := "base/iterators.jl"
    juliaFns := ["last(::ProductIterator)"]
    statement := "last(product(1:l1, ..., 1:lk)) returns only when the product is nonempty."
    source := "base/abstractarray.jl:513-520 (last docstring: the last element of an ordered collection)", status := .refuted
    prop := ``ProductLastNonempty, thm := some ``productLastNonempty_refuted
    issue := "none found (queries: product last empty)"
    notes := "last(p) = map(last, p.iterators) inherits last(1:0) == 0: last(product(1:2, 1:0)) == (2, 0). Possibly intended." },
  { id := "iterators-cycle-empty-length", juliaFile := "base/iterators.jl"
    juliaFns := ["IteratorSize(::Type{Cycle})", "length(::Take)", "first(itr, n)"]
    statement := "first(cycle(v), n) returns the first n elements of the repetition of v, which is empty when v is."
    source := "base/iterators.jl:1028-1032 (cycle docstring: when iter is empty, so is cycle(iter)), base/generator.jl:79", status := .refuted
    prop := ``CycleFirstN, thm := some ``cycleFirstN_refuted
    issue := "#53169 (open, duplicate), #43235 (open, related), PR #54187 (open)"
    notes := "IteratorSize(Cycle) is IsInfinite even for empty v (the XXX comment at base/iterators.jl:1063), so length(take(cycle(Int[]), 3)) == 3 and collect returns 3 uninitialised slots." },
  { id := "iterators-partition-range-overflow", juliaFile := "base/iterators.jl"
    juliaFns := ["iterate(::PartitionIterator{<:AbstractRange})", "collect"]
    statement := "partition(r, n) of r = IdentityUnitRange(fi:li) yields the chunks of n consecutive elements of r."
    source := "base/iterators.jl:1426 (partition docstring)", status := .refuted
    prop := ``PartitionRangeChunks, thm := some ``partitionRangeChunks_refuted
    issue := "none found (queries: partition overflow, partition typemax)"
    notes := "state + itr.n - 1 wraps near typemax(Int): the second chunk is empty, iteration never ends, and collect stores past the end (segfault)." },
  { id := "iterators-partition-generic-alloc", juliaFile := "base/iterators.jl"
    juliaFns := ["iterate(::PartitionIterator)"]
    statement := "The first chunk of partition(itr, n) of a nonempty tuple holds its first min(n, length) elements, for every n >= 1."
    source := "base/iterators.jl:1426 (partition docstring)", status := .refuted
    prop := ``PartitionFirstChunk, thm := some ``partitionFirstChunk_refuted
    issue := "none found (queries: partition allocates, partition memory, partition typemax)"
    notes := "The generic method allocates Vector(undef, n) per chunk: ArgumentError for n = typemax(Int), 800 MB for n = 10^8." },
  { id := "iterators-take-huge-count", juliaFile := "base/iterators.jl"
    juliaFns := ["take(xs, n)", "first(itr, n)", "last(itr, n)", "drop(xs, n)"]
    statement := "first(itr, n) returns the first min(n, length(itr)) elements for a nonnegative n of any integer type."
    source := "base/abstractarray.jl:481-484 (first(itr, n) docstring)", status := .refuted
    prop := ``FirstNAnyInteger, thm := some ``firstNAnyInteger_refuted
    issue := "none found (queries: take typemax UInt, first InexactError, take InexactError)"
    notes := "take(xs, n) = Take(xs, Int(n)) throws InexactError for n > typemax(Int); first(::AbstractVector, n) accepts it." },
  { id := "iterators-product-stateful-done", juliaFile := "base/iterators.jl"
    juliaFns := ["isdone(::ProductIterator, states)", "_pisdone"]
    statement := "product(itr) yields the 1-tuples of the elements of itr, for itr a vector or an Iterators.Stateful."
    source := "base/iterators.jl:1131-1133 (product docstring)", status := .refuted
    prop := ``ProductOneFactor, thm := some ``productOneFactor_refuted
    issue := "none found (queries: product Stateful, product eachline, tuple must be non-empty product; related closed #28753)"
    notes := "_pisdone has no method for empty tuples: when every factor reports isdone == true, first(()) throws ArgumentError." },
  -- proven
  { id := "iterators-take", juliaFile := "base/iterators.jl", juliaFns := ["take", "length(::Take)"]
    statement := "take(v, n) of a vector yields its first n elements and length(take(v, n)) == min(n, length(v))."
    source := "base/iterators.jl:790 (take docstring)", status := .proven
    prop := ``TakeCorrect, thm := some ``takeCorrect },
  { id := "iterators-take-take", juliaFile := "base/iterators.jl", juliaFns := ["take(::Take, n)"]
    statement := "take(take(v, a), b) yields the first min(a, b) elements of v."
    source := "base/iterators.jl:790 (take docstring)", status := .proven
    prop := ``TakeTakeCorrect, thm := some ``takeTakeCorrect },
  { id := "iterators-drop", juliaFile := "base/iterators.jl", juliaFns := ["drop", "length(::Drop)"]
    statement := "drop(v, n) of a vector yields all but its first n elements and its length agrees."
    source := "base/iterators.jl:849 (drop docstring)", status := .proven
    prop := ``DropCorrect, thm := some ``dropCorrect },
  { id := "iterators-take-drop-complement", juliaFile := "base/iterators.jl", juliaFns := ["take", "drop"]
    statement := "take(v, n) followed by drop(v, n) yields v."
    source := "base/iterators.jl:790, 849 (docstrings)", status := .proven
    prop := ``TakeDropComplement, thm := some ``takeDropComplement },
  { id := "iterators-takewhile-dropwhile", juliaFile := "base/iterators.jl", juliaFns := ["takewhile", "dropwhile"]
    statement := "takewhile(p, v) yields the longest prefix satisfying p and dropwhile(p, v) the rest."
    source := "base/iterators.jl:905, 952 (docstrings)", status := .proven
    prop := ``TakeWhileDropWhile, thm := some ``takeWhileDropWhile },
  { id := "iterators-enumerate", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "length(::Enumerate)", "reverse(::Enumerate)"]
    statement := "enumerate(v) yields (i, v[i]), has length(v) elements, and Iterators.reverse(enumerate(v)) yields them backwards."
    source := "base/iterators.jl:173 (enumerate docstring)", status := .proven
    prop := ``EnumerateCorrect, thm := some ``enumerateCorrect },
  { id := "iterators-zip", juliaFile := "base/iterators.jl", juliaFns := ["zip", "length(::Zip)"]
    statement := "zip(a, b) of vectors yields the pairs up to the shorter length, which is its length."
    source := "base/iterators.jl:343 (zip docstring)", status := .proven
    prop := ``ZipCorrect, thm := some ``zipCorrect },
  { id := "iterators-zip-reverse", juliaFile := "base/iterators.jl", juliaFns := ["reverse(::Zip)"]
    statement := "Iterators.reverse(zip(a, b)) yields the pairs backwards for equal lengths and throws ArgumentError otherwise."
    source := "base/iterators.jl:521-526", status := .proven
    prop := ``ZipReverse, thm := some ``zipReverse },
  { id := "iterators-product", juliaFile := "base/iterators.jl", juliaFns := ["product", "size(::ProductIterator)"]
    statement := "product(a, b) of vectors yields all pairs with the first iterator changing fastest, and size is (length(a), length(b))."
    source := "base/iterators.jl:1131-1133 (product docstring)", status := .proven
    prop := ``ProductCorrect, thm := some ``productCorrect },
  { id := "iterators-flatten", juliaFile := "base/iterators.jl", juliaFns := ["flatten"]
    statement := "flatten(vs) of a vector of vectors yields their concatenation."
    source := "base/iterators.jl:1268-1270 (flatten docstring)", status := .proven
    prop := ``FlattenCorrect, thm := some ``flattenCorrect },
  { id := "iterators-flatten-tuple-length", juliaFile := "base/iterators.jl", juliaFns := ["length(::Flatten)"]
    statement := "length(flatten(v)) for a vector of k-tuples is k * length(v), or OverflowError when that does not fit."
    source := "invariant (length is the number of elements)", status := .proven
    prop := ``FlattenTupleLength, thm := some ``flattenTupleLength
    notes := "Holds on master (checked_mul at base/iterators.jl:1327); 1.13.2 uses N * length(f.it), which wraps: length(cycle((1,2), 2^62)) == typemin(Int)." },
  { id := "iterators-cycle-n", juliaFile := "base/iterators.jl", juliaFns := ["cycle(xs, n)"]
    statement := "cycle(v, m) yields v m times."
    source := "base/iterators.jl:1031-1035 (cycle docstring)", status := .proven
    prop := ``CycleNCorrect, thm := some ``cycleNCorrect },
  { id := "iterators-repeated-n", juliaFile := "base/iterators.jl", juliaFns := ["repeated(x, n)"]
    statement := "repeated(x, n) yields x n times and has length n."
    source := "base/iterators.jl:1088-1089 (repeated docstring)", status := .proven
    prop := ``RepeatedNCorrect, thm := some ``repeatedNCorrect },
  { id := "iterators-partition-vector", juliaFile := "base/iterators.jl", juliaFns := ["partition", "length(::PartitionIterator)"]
    statement := "partition(v, n) of a vector yields chunks of n elements, the last possibly shorter, and length is the number of chunks."
    source := "base/iterators.jl:1426 (partition docstring)", status := .proven
    prop := ``PartitionVectorCorrect, thm := some ``partitionVectorCorrect },
  { id := "iterators-stateful", juliaFile := "base/iterators.jl", juliaFns := ["Stateful", "isdone(::Stateful)", "peek", "popfirst!"]
    statement := "A Stateful that has produced pos elements: isdone/isempty say whether elements remain, peek/popfirst! return the next one, collect returns the rest."
    source := "base/iterators.jl:1505-1560 (Stateful docstring)", status := .proven
    prop := ``StatefulConsistent, thm := some ``statefulConsistent
    notes := "length(::Stateful) has no method on master (IteratorSize is SizeUnknown)." },
  { id := "iterators-only", juliaFile := "base/iterators.jl", juliaFns := ["only"]
    statement := "only(v) returns the element of a one-element vector and throws ArgumentError otherwise."
    source := "base/iterators.jl:1632-1633 (only docstring)", status := .proven
    prop := ``OnlyCorrect, thm := some ``onlyCorrect },
  { id := "iterators-accumulate", juliaFile := "base/iterators.jl", juliaFns := ["Iterators.accumulate"]
    statement := "Iterators.accumulate(f, v; init) yields the running reductions and has length(v) elements."
    source := "base/iterators.jl:612-616 (accumulate docstring)", status := .proven
    prop := ``AccumulateCorrect, thm := some ``accumulateCorrect },
  { id := "iterators-nth-vector", juliaFile := "base/iterators.jl", juliaFns := ["nth(::AbstractArray, n)"]
    statement := "nth(v, n) of a vector is v[n] for 1 <= n <= length(v) and BoundsError otherwise, for n of every integer type."
    source := "base/iterators.jl:1730 (nth docstring)", status := .proven
    prop := ``NthVectorCorrect, thm := some ``nthVectorCorrect },
  { id := "iterators-first-last-vector", juliaFile := "base/abstractarray.jl", juliaFns := ["first(::AbstractVector, n)", "last(::AbstractVector, n)"]
    statement := "first(v, n) and last(v, n) of a vector return its first and last min(n, length(v)) elements for n >= 0 of every integer type."
    source := "base/abstractarray.jl:481-484, 533-536 (docstrings)", status := .proven
    prop := ``FirstLastVector, thm := some ``firstLastVector },
  { id := "iterators-first-n-tuple", juliaFile := "base/abstractarray.jl", juliaFns := ["first(itr, n)"]
    statement := "first(t, n) of a tuple with an Int count returns its first min(n, length(t)) elements."
    source := "base/abstractarray.jl:481-484 (first docstring)", status := .proven
    prop := ``FirstNTupleInt, thm := some ``firstNTupleInt },
  { id := "iterators-countfrom", juliaFile := "base/iterators.jl", juliaFns := ["countfrom"]
    statement := "countfrom(s, d) yields s, s + d, s + 2d, ... with Int wraparound."
    source := "base/iterators.jl:751 (countfrom docstring)", status := .proven
    prop := ``CountfromCorrect, thm := some ``countfromCorrect }
]

end JuliaLean.Iterators
