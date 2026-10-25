import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IdDicts.Value
import JuliaLean.IdDicts.IdDict
import JuliaLean.IdDicts.IdSet
import JuliaLean.IdDicts.Weak
import JuliaLean.IdDicts.Props
import JuliaLean.IdDicts.ProofTable
import JuliaLean.IdDicts.ProofIdDict
import JuliaLean.IdDicts.ProofIdSet
import JuliaLean.IdDicts.Refutations

namespace JuliaLean.IdDicts

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "iddicts-ops-agree", juliaFile := "base/iddict.jl"
    juliaFns := ["setindex!(::IdDict, v, k)", "delete!(::IdDict, k)", "pop!(::IdDict, k)",
      "pop!(::IdDict, k, default)", "empty!(::IdDict)", "sizehint!(::IdDict, n)", "get(::IdDict, k, default)",
      "length(::IdDict)", "iterate(::IdDict)"]
    statement := "For IdDict{K,V} and any sequence of setindex!/delete!/pop!/empty!/sizehint! calls, get(d, q, default) returns the value of a reference === map (KeyTypeError for keys not of type K, convert(V, v) for values), length(d) is its number of keys, and iteration yields pairwise non-=== keys with the reference lookups."
    source := "IdDict docstring base/iddict.jl:6-8 (objectid hash, === equality, keys of type K, values of type V); setindex! base/iddict.jl:79-92", status := .proven
    prop := ``IdDictOpsAgree, thm := some ``idDictOpsAgree_proven
    notes := "jl_eqtable_* modelled as a primitive === map; the ndel rehash trigger and sizehint! only replace the array. Checked against Julia on 120 random call sequences (IdDict{Any,Any} and IdDict{Int,Float64}), both versions identical." },
  { id := "iddicts-length-live", juliaFile := "base/iddict.jl"
    juliaFns := ["length(::IdDict)", "iterate(::IdDict)", "get!(::IdDict, k, default)", "get!(f, ::IdDict, k)", "pop!(::IdDict, k)"]
    statement := "After any sequence of IdDict calls (including get! and pop! on stored sentinels), length(d) equals the number of pairs iteration yields, the keys are pairwise non-===, and iteration never throws."
    source := "invariant (length of an iterable equals the number of elements it yields); base/iddict.jl:90,111-112,147", status := .proven
    prop := ``IdDictLengthLive, thm := some ``idDictLengthLive_proven },
  { id := "iddicts-getbang-absent", juliaFile := "base/iddict.jl"
    juliaFns := ["get!(::IdDict, k, default)"]
    statement := "get!(d, k, default) for an absent key of type K whose default converts to w stores k => w, returns w, and increases length by one."
    source := "get! docstring base/dict.jl:393-394", status := .proven
    prop := ``IdDictGetBangAbsent, thm := some ``idDictGetBangAbsent_proven },
  { id := "iddicts-idset-ops-agree", juliaFile := "base/idset.jl"
    juliaFns := ["push!(::IdSet, x)", "pop!(::IdSet, x)", "pop!(::IdSet, x, default)", "delete!(::IdSet, x)",
      "empty!(::IdSet)", "sizehint!(::IdSet, n)", "union!(::IdSet, itr)", "setdiff!(::IdSet, itr)",
      "iterate(::IdSet)", "length(::IdSet)", "in(x, ::IdSet)", "jl_idset_put_key"]
    statement := "For IdSet{Any} and any call sequence mentioning fewer than 2^62 elements, iteration yields the elements of a reference === set exactly once each, in insertion order, length is their number, in agrees with membership, and no @assert in push! fires."
    source := "IdSet docstring base/idset.jl:7-8 (a set using ===); union!/setdiff! docstrings base/abstractset.jl:62-84, 225-243", status := .proven
    prop := ``IdSetOpsAgree, thm := some ``idSetOpsAgree_proven
    notes := "s.list is modelled slot by slot with the max scan and jl_idset_put_key's compaction and growth; the hash index idxs is a primitive. Checked against Julia on 60 random call sequences (up to 600 calls, up to 40 elements): identical iteration order on both versions." },
  -- refuted
  { id := "iddicts-token-lookup", juliaFile := "base/iddict.jl"
    juliaFns := ["haskey(::IdDict, k)", "in(k, ::KeySet{<:Any,<:IdDict})", "getindex(::IdDict, k)"]
    statement := "For every key k present in an IdDict (iteration yields k => v), haskey(d, k) is true and d[k] returns v."
    source := "haskey docstring base/dict.jl:537; KeyError docstring base/abstractdict.jl:5-9", status := .refuted
    prop := ``LookupFindsPresent, thm := some ``lookupFindsPresent_refuted
    issue := "none found (queries: secret_table_token, IdDict sentinel, IdDict KeyError, IdDict haskey, IdDict getindex)"
    notes := "d[\"k\"] = Base.secret_table_token: haskey is false and d[\"k\"] throws KeyError on both versions; (k => T) in d and mergewith! are affected too. P2." },
  { id := "iddicts-token-pop", juliaFile := "base/iddict.jl"
    juliaFns := ["pop!(::IdDict, k)"]
    statement := "pop!(d, k) returns the stored value of every present key."
    source := "pop! docstring base/dict.jl:594-595", status := .refuted
    prop := ``PopReturnsPresent, thm := some ``popReturnsPresent_refuted
    issue := "none found (queries: secret_table_token, IdDict pop! KeyError, IdDict sentinel, pop! removes throws)"
    notes := "With the sentinel stored, pop!(d, k) removes the entry and then throws KeyError. P2." },
  { id := "iddicts-token-getbang", juliaFile := "base/iddict.jl"
    juliaFns := ["get!(::IdDict, k, default)", "get!(f, ::IdDict, k)"]
    statement := "get!(d, k, default) on a present key returns the stored value and leaves the contents unchanged."
    source := "get! docstring base/dict.jl:393-394", status := .refuted
    prop := ``GetBangKeepsPresent, thm := some ``getBangKeepsPresent_refuted
    issue := "none found (queries: secret_table_token, IdDict get!, get! overwrites, IdDict sentinel)"
    notes := "With the sentinel stored, get! overwrites it with the default. P2." },
  { id := "iddicts-idset-eltype", juliaFile := "base/idset.jl"
    juliaFns := ["push!(::IdSet, x)", "iterate(::IdSet)", "union!(::IdSet, itr)"]
    statement := "Every element of an IdSet{T} has type T, so iteration never throws."
    source := "IdSet docstring base/idset.jl:7-8 (values of type T); iterate base/idset.jl:125 (::S cast)", status := .refuted
    prop := ``IdSetElemsHaveEltype, thm := some ``idSetElemsHaveEltype_refuted
    issue := "none found (queries: IdSet push convert, IdSet eltype, IdSet TypeError, IdSet convert check, IdSet)"
    notes := "push!(IdSet{Int}(), \"a string\") is accepted; collect throws TypeError. IdSet{Bool}(Any[1, 2, true, false]) stops after 1 and 2 (max_values). P2." },
  { id := "iddicts-idset-symdiff", juliaFile := "base/abstractset.jl"
    juliaFns := ["symdiff!(::AbstractSet, itr)", "symdiff(::IdSet, itr)"]
    statement := "symdiff!(s::IdSet{Any}, itr): x is in the result exactly when x is in s or === an element of itr, but not both."
    source := "symdiff! docstring base/abstractset.jl:284; IdSet docstring base/idset.jl:7-8", status := .refuted
    prop := ``IdSetSymdiffIdentity, thm := some ``idSetSymdiffIdentity_refuted
    issue := "related #61893 (open); none found (queries: IdSet symdiff, symdiff Set itr, symdiff IdSet, symdiff, IdSet)"
    notes := "symdiff!(IdSet{Any}(), [a, b]) with a = [1], b = [1] holds only b: base/abstractset.jl:297 converts itr to a Set. P2." },
  { id := "iddicts-idset-issetequal", juliaFile := "base/abstractset.jl"
    juliaFns := ["issetequal(::AbstractSet, itr)", "issetequal(itr, ::AbstractSet)", "==(::AbstractSet, ::AbstractSet)"]
    statement := "issetequal(a, b) == (a ⊆ b && b ⊆ a) for an IdSet{Any} a and a vector b, in both argument orders."
    source := "issetequal docstring base/abstractset.jl:507-508", status := .refuted
    prop := ``IdSetIssetequalSubsets, thm := some ``idSetIssetequalSubsets_refuted
    issue := "related #61893 (open), #41748 (closed); none found (queries: IdSet issetequal, issetequal IdSet, issetequal length, issetequal, IdSet ==)"
    notes := "issetequal(IdSet{Any}(Any[1, 1.0]), Any[1, 1.0]) is false while both inclusions hold: the length comparison in ==(::AbstractSet, ::AbstractSet). P2." },
  { id := "iddicts-idset-issubset", juliaFile := "base/abstractset.jl"
    juliaFns := ["issubset(a, b)"]
    statement := "issubset(a, b) == all(x -> x in b, a) for an IdSet{Any} a and a Set or vector b."
    source := "issubset docstring base/abstractset.jl:315", status := .refuted
    prop := ``IdSetIssubsetIn, thm := some ``idSetIssubsetIn_refuted
    issue := "related #61893 (open); none found (queries: issubset IdSet, IdSet issubset, issubset AbstractSet length, issubset length shortcut, issubset)"
    notes := "IdSet{Any}(Any[1, 1.0]) ⊆ Set([1]) is false although every element is in Set([1]): the length(a) > length(b) shortcut at base/abstractset.jl:339-341. P2." },
  { id := "iddicts-weakkeydict-length", juliaFile := "base/weakdict.jl"
    juliaFns := ["setindex!(::WeakKeyDict, v, k)", "length(::WeakKeyDict)", "iterate(::WeakKeyDict)"]
    statement := "After any realistic sequence of setindex!, delete! and garbage collections, length(wkh) equals the number of pairs iteration yields."
    source := "invariant; WeakKeyDict docstring base/weakdict.jl:14-16; length base/weakdict.jl:190-195", status := .refuted
    prop := ``WeakKeyLengthLive, thm := some ``weakKeyLengthLive_refuted
    issue := "related #24721 (closed); none found (queries: WeakKeyDict finalizer, WeakKeyDict length, WeakKeyDict isequal key, WeakKeyDict replace key, WeakKeyDict dirty, WeakKeyDict stale entry)"
    notes := "Re-setting an isequal key retargets the WeakRef without registering a finalizer (base/weakdict.jl:97-103); once the new key is collected, length counts a dead entry. 1.13.2 has the same code in base/weakkeydict.jl. P2." },
  { id := "iddicts-weakvalue-eltype", juliaFile := "base/weakdict.jl"
    juliaFns := ["setindex!(::WeakValueIdDict, v, k)", "getindex(::WeakValueIdDict, k)", "get(::WeakValueIdDict, k, default)", "get!(::WeakValueIdDict, k, default)"]
    statement := "After h[k] = v succeeds on a WeakValueIdDict{K,V}(), h[k], get(h, k, default) and get!(h, k, default) do not throw TypeError."
    source := "WeakValueIdDict docstring base/weakdict.jl:227 (like IdDict); IdDict setindex! converts values base/iddict.jl:81-83", status := .refuted
    prop := ``WeakValueReadsTyped, thm := some ``weakValueReadsTyped_refuted
    issue := "related #62831 (merged, adds the type); none found (queries: WeakValueIdDict, WeakValueIdDict TypeError, weak value dict convert)"
    notes := "Master only (the type is not in 1.13.2). WeakValueIdDict{Any,Vector{Int}}()[:k] = [1.0] is accepted; every read throws TypeError. P2." }
]

end JuliaLean.IdDicts
