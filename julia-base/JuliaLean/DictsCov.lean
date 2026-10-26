import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.DictsCov.DictIterProofs
import JuliaLean.DictsCov.IdMapBug
import JuliaLean.DictsCov.AbsBugs
import JuliaLean.DictsCov.DeepcopyRows
import JuliaLean.DictsCov.HamtRows
import JuliaLean.DictsCov.IdDictRows
import JuliaLean.DictsCov.AbstractDictRows
import JuliaLean.DictsCov.DictRows
import JuliaLean.DictsCov.WeakDictRows
import JuliaLean.DictsCov.DictSplitRows

namespace JuliaLean.DictsCov

open JuliaLean.Registry

def DeepcopyWeakRegistered : Prop := DeepcopyRows.DeepcopyWeakRegistered

theorem deepcopyWeakRegistered_refuted : ¬ DeepcopyWeakRegistered :=
  DeepcopyRows.deepcopyWeakRegistered_refuted

/-- Registry entries of this area. -/
def coreEntries : List Entry := [
  { id := "dictscov-dict-construct", juliaFile := "base/dict.jl"
    juliaFns := ["Dict{K,V}()", "Dict{K,V}(d::Dict{K,V})", "Dict{K,V}(slots, keys, vals, ...)", "Dict{K,V}(kv)",
      "Dict{K,V}(p::Pair)", "Dict{K,V}(ps::Pair...)", "Dict()", "Dict(kv::Tuple{})", "copy(d::Dict)",
      "Dict(ps::Pair{K,V}...)"]
    statement := "Each Dict constructor builds a table agreeing with the reference map of its pairs (later pairs win), copy keeps the contents, and the inner constructor stores its fields."
    source := "Dict docstring base/dict.jl:31-64", status := .proven
    prop := ``DictConstructSpec, thm := some ``dictConstructSpec_proven },
  { id := "dictscov-dict-slots", juliaFile := "base/dict.jl"
    juliaFns := ["_shorthash7(hsh::UInt)", "hashindex(key, sz::Integer)", "isslotempty", "isslotfilled", "isslotmissing"]
    statement := "_shorthash7 is a filled slot byte holding the top seven hash bits, hashindex is hash mod sz plus one for power-of-two sizes, and the slot tests classify 0x00, 0x7f and 0x80-0xff."
    source := "invariant: base/dict.jl:66,123-137", status := .proven
    prop := ``DictSlotSpec, thm := some ``dictSlotSpec_proven },
  { id := "dictscov-dict-keyindex", juliaFile := "base/dict.jl"
    juliaFns := ["ht_keyindex(h::Dict, key)", "ht_keyindex2_shorthash!(h::Dict, key)", "ht_keyindex2!(h::Dict, key)",
      "_setindex!(h::Dict, v, key, index, sh)"]
    statement := "On every reachable table, ht_keyindex finds the slot of the stored key isequal to a key of any lawful type or returns -1; ht_keyindex2! returns a present key's slot or a free slot on its probe sequence, and _setindex! there stores the new pair."
    source := "invariant: base/dict.jl:241-345", status := .proven
    prop := ``DictKeyindexSpec, thm := some ``dictKeyindexSpec_proven },
  { id := "dictscov-dict-setindex", juliaFile := "base/dict.jl"
    juliaFns := ["setindex!(h::Dict{K,V}, v0, key0)", "setindex!(h::Dict{K,V}, v0, key::K)", "setindex!(h::Dict{K,Any}, v, key::K)"]
    statement := "setindex! converts the value to V and stores it under the key; the Dict{K,Any} method stores it unconverted; a key of another type is converted and must stay isequal, else KeyTypeError."
    source := "setindex! docstring; base/dict.jl:347-387", status := .proven
    prop := ``DictSetindexSpec, thm := some ``dictSetindexSpec_proven },
  { id := "dictscov-dict-getbang", juliaFile := "base/dict.jl"
    juliaFns := ["get!(default::Callable, h::Dict{K,V}, key0)", "get!(default::Callable, h::Dict{K,V}, key::K)"]
    statement := "get!(f, h, key) returns a stored value without calling f, or stores and returns convert(V, f()); a foreign key goes through the setindex! key conversion."
    source := "get! docstring base/dict.jl:416-442", status := .proven
    prop := ``DictGetBangSpec, thm := some ``dictGetBangSpec_proven },
  { id := "dictscov-dict-lookup", juliaFile := "base/dict.jl"
    juliaFns := ["getindex(h::Dict, key)", "get(h::Dict, key, default)", "get(default::Callable, h::Dict, key)",
      "haskey(h::Dict, key)", "in(key, v::KeySet{<:Any,<:Dict})", "getkey(h::Dict, key, default)"]
    statement := "Lookups with a key of any lawful type agree with the reference map: getindex (or KeyError), get, get(f, ...), haskey, in(keys) and getkey."
    source := "docstrings base/dict.jl:485-575", status := .proven
    prop := ``DictLookupSpec, thm := some ``dictLookupSpec_proven },
  { id := "dictscov-dict-pop", juliaFile := "base/dict.jl"
    juliaFns := ["_pop!(h::Dict, index)", "pop!(h::Dict, key)", "pop!(h::Dict, key, default)", "_delete!(h::Dict, index)"]
    statement := "pop!(h, key) returns the stored value and removes the key or throws KeyError; pop!(h, key, default) returns default instead; _delete!/_pop! remove exactly their slot's pair."
    source := "pop! docstring base/dict.jl:591-612", status := .proven
    prop := ``DictPopSpec, thm := some ``dictPopSpec_proven },
  { id := "dictscov-dict-iterate", juliaFile := "base/dict.jl"
    juliaFns := ["skip_deleted(h::Dict, i)", "skip_deleted_floor!(h::Dict)", "_iterate_dict", "iterate(t::Dict)",
      "iterate(t::Dict, i)", "isempty(t::Dict)", "Iterators.only(t::Dict)", "iterate(v::KeySet/ValueIterator{<:Dict}, i)"]
    statement := "skip_deleted returns the first filled slot at or after i (or 0), iteration yields each stored pair once, keys/values iterate in the same order, isempty tests for no pairs and only returns the single pair or throws ArgumentError."
    source := "keys docstring base/abstractdict.jl:86-91; base/dict.jl:689-723", status := .proven
    prop := ``DictIterSpec, thm := some ``dictIterSpec_proven },
  { id := "dictscov-dict-map-reduce", juliaFile := "base/dict.jl"
    juliaFns := ["map!(f, iter::ValueIterator{<:Dict})", "reduce(::typeof(merge), items::Vector{<:Dict})"]
    statement := "map!(f, values(d)) replaces each value v by f(v); reduce(merge, items) is the left fold of merge and throws ArgumentError for no items."
    source := "map! docstring base/abstractdict.jl:650-660; base/dict.jl:735-739", status := .proven
    prop := ``DictMapReduceSpec, thm := some ``dictMapReduceSpec_proven },
  { id := "dictscov-show-limit-ellipsis", juliaFile := "base/dict.jl"
    juliaFns := ["show(io::IO, t::AbstractDict{K,V})"]
    statement := "With :limit => true, show prints an ellipsis only when some pair is not shown."
    source := ":limit IOContext docstring base/show.jl:397-398", status := .refuted
    prop := ``ShowEllipsisOmits, thm := some ``showEllipsisOmits_refuted
    issue := "none found (queries: Dict show limit ellipsis, show Dict limit 10 entries, show dict truncation, ellipsis in:title, show Dict in:title)"
    notes := "Both versions: repr(Dict(i => i for i in 1:10); context = :limit => true) shows all 10 pairs followed by …: base/dict.jl:19 tests n >= 10 after printing the n-th pair. P3." },
  { id := "dictscov-immutable-filter-copy", juliaFile := "base/abstractdict.jl"
    juliaFns := ["filter(f, d::AbstractDict)", "copy(a::AbstractDict)"]
    statement := "filter(f, d) and copy(d) return a dictionary for every AbstractDict, including ImmutableDict."
    source := "filter docstring base/abstractdict.jl:464; copy docstring", status := .refuted
    prop := ``FilterCopyNothrow, thm := some ``filterCopyNothrow_refuted
    issue := "none found (queries: ImmutableDict filter, ImmutableDict copy, PersistentDict filter, filter AbstractDict setindex, ImmutableDict)"
    notes := "Both versions: filter(p -> true, ImmutableDict(:a => 1)) and copy(ImmutableDict(:a => 1)) throw MethodError(setindex!): empty(::ImmutableDict) is an ImmutableDict (base/dict.jl:866). Same for PersistentDict (base/dict.jl:1067). P2." },
  { id := "dictscov-merge-iddict", juliaFile := "base/abstractdict.jl"
    juliaFns := ["merge(d::AbstractDict, others::AbstractDict...)", "mergewith(combine, d::AbstractDict, others::AbstractDict...)",
      "_typeddict(d::AbstractDict, others::AbstractDict...)"]
    statement := "merge(d) of an IdDict keeps every ===-distinct key of d."
    source := "merge docstring base/abstractdict.jl:330-333", status := .refuted
    prop := ``MergeKeepsIdKeys, thm := some ``mergeKeepsIdKeys_refuted
    issue := "#22738"
    notes := "Both versions: merge(IdDict{Any,Any}(1 => :a, 1.0 => :b)) is Dict(1.0 => :b) with one entry: _typeddict (base/abstractdict.jl:413-417) always builds a Dict, which compares keys with isequal. Open issue #22738 asks whether merge should always return a Dict. P2." },
  { id := "dictscov-iddict-map-rehash", juliaFile := "base/abstractdict.jl"
    juliaFns := ["map!(f, iter::ValueIterator)", "mergewith!(combine, d1::AbstractDict, d2::AbstractDict)"]
    statement := "map!(f, values(d)) on an IdDict replaces every value exactly once, and mergewith!(f, d, d) combines every value once."
    source := "map! docstring base/abstractdict.jl:653; mergewith! docstring base/abstractdict.jl:243-244", status := .refuted
    prop := ``IdDictMapOnce, thm := some ``idDictMapOnce_refuted
    issue := "none found (queries: IdDict map, map! values, IdDict mergewith, IdDict rehash, IdDict iterate setindex, ValueIterator map, mergewith IdDict)"
    notes := "Both versions: with enough tombstones (ndel >= 3*length(ht)/4), the first setindex! inside the loop rehashes (base/iddict.jl:84-87) and the live pairs move below the iteration index, so later values are skipped. P1." },
  { id := "dictscov-deepcopy-weakref", juliaFile := "base/deepcopy.jl"
    juliaFns := ["deepcopy(@nospecialize x)", "deepcopy_internal(@nospecialize(x), stackdict::IdDict)"]
    statement := "deepcopy of a WeakRef returns a registered weak reference whose value is cleared when its copied referent is collected."
    source := "deepcopy docstring base/deepcopy.jl:11-17; WeakRef docstring base/gcutils.jl:9-10"
    status := .refuted, prop := ``DeepcopyWeakRegistered,
    thm := some ``deepcopyWeakRegistered_refuted, issue := "#62597"
    notes := "Both versions: the generic mutable-object path allocates an unregistered WeakRef, so GC frees the copied referent without clearing the copied WeakRef field. P0." }
]

def entries : List Entry :=
  coreEntries ++ DeepcopyRows.entries ++ HamtRows.entries ++ IdDictRows.entries
    ++ AbstractDictRows.entries
    ++ DictRows.entries
    ++ WeakDictRows.entries
    ++ DictSplitRows.entries

end JuliaLean.DictsCov
