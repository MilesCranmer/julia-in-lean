import JuliaLean.base.namedtuple
import JuliaLean.Proofs.base.tuple.sort_tuple
/-!
Value-level methods of `base/namedtuple.jl` (master `bbfa0ce4150`) that the
`Tuples` area does not register: constructors and conversions, indexing and
iteration, comparisons, `map`/`filter`, the iterator forms of `merge`,
`delete`, `show`, and the `@NamedTuple`/`@Kwargs` macros.

A named tuple is the `Tuples.NT α` list of `(name, value)` fields. Field types
are an opaque universe `T`; `conv T x` is `x isa T ? x : convert(T, x)` (which may
throw). A `NamedTuple` type `NamedTuple{names, Tuple{types...}}` is the pair of
its names and field types.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds argErr liftJ Idx NT ntNames ntValues lookup
  selectNames symIn mergeNames diffNames restTuple Ops)

namespace NTup

variable {α T : Type}

end NTup

open NTup

/-- Construction and conversion of named tuples (`base/namedtuple.jl:115-157,
178-196`): `NamedTuple{names,T}(args)` throws `ArgumentError` for a length
mismatch and otherwise converts each argument to its field type;
`NamedTuple{names,T}(nt)` takes the field of each name (`FieldError` when
missing) and converts it; `NamedTuple{names}(itr)` pairs the names with the
values (`ErrorException` for a length mismatch or repeated names);
`NamedTuple{names,T}(itr)` converts the first values (`ArgumentError` when there
are too few and the conversions succeed); `NamedTuple(itr)` keeps
each key once at its first position with its last value; `_new_NamedTuple`
does not convert; `convert` to the same type returns the argument and
otherwise converts fieldwise; `Tuple(nt)` is the values and `T(nt)` converts
them (`MethodError` for a length mismatch). -/
def NTConstructCorrect : Prop :=
  ∀ (α T : Type) (conv : T → α → R α),
    (∀ names tys (args : List α), tys.length = names.length →
      ofTuple conv names tys args =
        if args.length ≠ names.length then argErr "Wrong number of arguments to named tuple constructor."
        else ((tys.zip args).mapM fun p => conv p.1 p.2).map names.zip) ∧
    (∀ names tys (nt : NT α), tys.length = names.length →
      (fieldsAt nt names = none → ∃ e, ofNT conv names tys nt = .error e) ∧
      ∀ xs, fieldsAt nt names = some xs →
        ofNT conv names tys nt = ((tys.zip xs).mapM fun p => conv p.1 p.2).map names.zip) ∧
    (∀ names (vals : List α), names.Nodup → names.length = vals.length →
      ofNamesItr names vals = .ok (names.zip vals)) ∧
    (∀ names (vals : List α), (¬ names.Nodup ∨ names.length ≠ vals.length) →
      ofNamesItr names vals = .error .errorException) ∧
    (∀ (tys : List T) (itr : List α), itr.length < tys.length → (∀ ty x, ∃ y, conv ty x = .ok y) →
      ∃ msg, totupleFixed conv tys itr = argErr msg) ∧
    (∀ (tys : List T) (itr : List α), tys.length ≤ itr.length →
      totupleFixed conv tys itr = (tys.zip itr).mapM fun p => conv p.1 p.2) ∧
    (∀ names (args : List α), newNamedTuple names args = names.zip args) ∧
    (∀ (nt : NT α), convertSame nt = nt ∧ toTuple nt = ntValues nt) ∧
    (∀ (tys : List T) (nt : NT α), tys.length ≠ nt.length →
      toTupleType conv tys nt = .error (.jl (.methodError "convert")))

/-- Access to named tuples (`base/namedtuple.jl:159-176,382-389`): `length`,
`firstindex`, `lastindex` describe `1:length`; `iterate` yields the values in
order then `nothing`; `t[i]` is the `i`-th value (`BoundsError` outside);
`t[s]` the field `s` (`FieldError` when missing); `t[:]` is `t`; `keys` and
`values` are the names and values; `isempty`/`empty`; `tail`, `front` and
`reverse` drop the first or last field or reverse the fields, and throw
`ArgumentError` on the empty named tuple (`tail`/`front`). -/
def NTAccessCorrect : Prop :=
  ∀ (α : Type) (t : NT α), (ntNames t).Nodup →
    length t = t.length ∧ firstindex t = 1 ∧ lastindex t = t.length ∧
    (∀ i : Int, 1 ≤ i → i ≤ t.length →
      ∃ x, (ntValues t)[(i - 1).toNat]? = some x ∧ iterate t i = .ok (some (x, i + 1)) ∧
        getindexInt t i = .ok x ∧ indexedIterate t i = .ok (x, i + 1)) ∧
    (∀ i : Int, i > t.length → iterate t i = .ok none) ∧
    (∀ i : Int, ¬ (1 ≤ i ∧ i ≤ t.length) → getindexInt t i = bounds) ∧
    (∀ s, getindexSym t s = match lookup t s with | some x => .ok x | none => .error .fieldError) ∧
    getindexColon t = t ∧ keys t = ntNames t ∧ values t = ntValues t ∧
    isempty t = t.isEmpty ∧ empty t = [] ∧ restAll t = t ∧
    tail t = (if t = [] then argErr "Cannot call tail on an empty tuple." else .ok t.tail) ∧
    front t = (if t = [] then argErr "Cannot call front on an empty tuple." else .ok t.dropLast) ∧
    reverse t = .ok t.reverse

/-- Comparisons of named tuples (`base/namedtuple.jl:241-256`): `==`, `isequal`,
`<` and `isless` compare the values when the names agree (in order), `==` and
`isequal` are `false` otherwise, and `<`/`isless` have no method otherwise;
`same_names` tests that all names agree. -/
def NTCompareCorrect : Prop :=
  ∀ (α : Type) (o : Ops α) (a b : NT α),
    eq o a b = (if ntNames a = ntNames b then JuliaLean.Tuples.eq o (ntValues a) (ntValues b)
      else some false) ∧
    isequal o a b = (ntNames a == ntNames b && JuliaLean.Tuples.isequal o (ntValues a) (ntValues b)) ∧
    isequal o a b = JuliaLean.Tuples.isequalNT o a b ∧
    (ntNames a ≠ ntNames b → lt o a b = .error (.jl (.methodError "isless")) ∧
      isless o a b = .error (.jl (.methodError "isless"))) ∧
    (ntNames a = ntNames b → isless o a b = .ok (JuliaLean.Tuples.isless o (ntValues a) (ntValues b))) ∧
    (∀ nts : List (NT α), sameNames (a :: nts) = nts.all (fun b => ntNames b == ntNames a)) ∧
    ntNamesOf a = ntNames a

/-- `map(f, nt, nts...)` and `filter(f, nt)` (`base/namedtuple.jl:258-266`):
`map` throws `ArgumentError` unless all names agree and otherwise applies `f`
to the values field by field; `filter` keeps the fields whose value satisfies
`f`, in order. -/
def NTMapFilterCorrect : Prop :=
  ∀ (α β : Type) (f : List α → β) (g : α → Bool) (nt : NT α) (nts : List (NT α)),
    (ntNames nt).Nodup →
    (sameNames (nt :: nts) = false → ∃ msg, map f nt nts = argErr msg) ∧
    (sameNames (nt :: nts) = true →
      map f nt nts = .ok ((ntNames nt).zip ((Tup.zipN ((nt :: nts).map ntValues) nt.length).map f))) ∧
    filter g nt = .ok (nt.filter fun p => g p.2)

/-- The `merge` methods for iterators and several arguments, and `delete`
(`base/namedtuple.jl:346-380,437-440`): `merge(a, itr)` merges the named tuple
of the pairs of `itr`, which has each key once, at its first position, with
the value of its last pair (`TypeError` for a non-`Symbol` key);
`merge(a, pairs(nt))` is `merge(a, nt)`; `merge(a, b, cs...)` merges left to
right; `merge(a) = a`; `delete(a, k)` drops the field `k`. -/
def NTMergeItrCorrect : Prop :=
  ∀ (α : Type) (a data : NT α) (itr : List (KV α)) (bs : List (NT α)),
    (ntNames a).Nodup →
    mergePairs a data = JuliaLean.Tuples.merge a data ∧
    mergeMany a [] = a ∧
    mergeMany a bs = bs.foldl JuliaLean.Tuples.merge a ∧
    ((∀ kv ∈ itr, kv.isSym = true) →
      ∃ acc, mergeItrLoop [] itr = .ok acc ∧ acc.map Prod.fst = firstKeys itr ∧
        (∀ k, lookup acc k = lastVal itr k) ∧
        mergeItr a itr = .ok (JuliaLean.Tuples.merge a acc)) ∧
    ((∃ kv ∈ itr, kv.isSym = false) → mergeItr a itr = .error .typeError) ∧
    (∀ k, delete a k = .ok (a.filter fun p => p.1 != k))

/-- `merge(a, zip(ks, vs))` agrees with the generic `merge(a, itr)` on the
iterated pairs `zip(ks, vs)` (`merge` docstring, `base/namedtuple.jl:354-357`). -/
def MergeZipAgrees : Prop :=
  ∀ (α : Type) (a : NT α) (ks : List String) (vs : List α),
    mergeZip a ks vs = mergeItr a ((ks.zip vs).map fun (k, v) => ⟨k, true, v⟩)

end JuliaLean.SortTuplesCov
