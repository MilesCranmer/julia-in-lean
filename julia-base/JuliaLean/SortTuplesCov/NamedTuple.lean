import JuliaLean.SortTuplesCov.Tuple

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

/-- `NamedTuple{names,T}(args::Tuple)`, `base/namedtuple.jl:115-122`: a length
mismatch throws `ArgumentError`; otherwise `T(args)` converts each argument to
its field type. -/
def ofTuple (conv : T → α → R α) (names : List String) (tys : List T) (args : List α) :
    R (NT α) :=
  if args.length ≠ names.length then argErr "Wrong number of arguments to named tuple constructor."
  else do
    let vs ← (tys.zip args).mapM fun p => conv p.1 p.2
    pure (names.zip vs)

/-- `NamedTuple{names,T}(nt::NamedTuple)`, `base/namedtuple.jl:124-134`
(generated branch): for each name in order, `getfield(nt, name)` (`FieldError`
when missing) converted to the field type. -/
def ofNTField (conv : T → α → R α) (nt : NT α) (p : String × T) : R α := do
  let x ← match lookup nt p.1 with
    | some x => pure x
    | none => .error .fieldError
  conv p.2 x
def ofNT (conv : T → α → R α) (names : List String) (tys : List T) (nt : NT α) : R (NT α) := do
  let vs ← (names.zip tys).mapM (ofNTField conv nt)
  pure (names.zip vs)

/-- `NamedTuple{names}(t::Tuple)` (the builtin constructor of `boot.jl`): the
lengths must agree (`ErrorException`) and the names must be distinct. -/
def ofNamesTuple (names : List String) (vals : List α) : R (NT α) :=
  if names.length ≠ vals.length then .error .errorException
  else if names.Nodup then .ok (names.zip vals) else .error .errorException

/-- `NamedTuple{names}(itr) = NT(Tuple(itr))`, `base/namedtuple.jl:149`, for the
values `itr` produces. -/
def ofNamesItr (names : List String) (itr : List α) : R (NT α) := ofNamesTuple names itr

/-- `T(itr)` for the fixed tuple type `Tuple{tys...}` (`_totuple`,
`base/tuple.jl:475-495`): the first `length(tys)` values, each converted;
`ArgumentError` when there are fewer. -/
def totupleFixed (conv : T → α → R α) : List T → List α → R (List α)
  | [], _ => .ok []
  | _ :: _, [] => argErr "too few elements for tuple type"
  | ty :: tys, x :: xs => do
    let y ← conv ty x
    let ys ← totupleFixed conv tys xs
    pure (y :: ys)

/-- `NamedTuple{names,T}(itr) = NT(T(itr))`, `base/namedtuple.jl:148`. -/
def ofNamesTypesItr (conv : T → α → R α) (names : List String) (tys : List T) (itr : List α) :
    R (NT α) := do
  let t ← totupleFixed conv tys itr
  ofTuple conv names tys t

/-- `_new_NamedTuple(T, args)`, `base/namedtuple.jl:155-157`: the fields without conversion. -/
def newNamedTuple (names : List String) (args : List α) : NT α := names.zip args

/-- The pairs `k => v` of a `merge` iterator: the key, and whether it is a `Symbol`. -/
structure KV (α : Type) where
  key : String
  isSym : Bool
  val : α

/-- The loop of `merge(a::NamedTuple, itr)`, `base/namedtuple.jl:365-378`: `k::Symbol`
(`TypeError` otherwise); a repeated key overwrites the value at the position of
its first occurrence (`IdDict` of indices). -/
def mergeItrLoop : List (String × α) → List (KV α) → R (List (String × α))
  | acc, [] => .ok acc
  | acc, kv :: rest =>
    if !kv.isSym then .error .typeError
    else if acc.any (·.1 == kv.key) then
      mergeItrLoop (acc.map fun p => if p.1 == kv.key then (p.1, kv.val) else p) rest
    else mergeItrLoop (acc ++ [(kv.key, kv.val)]) rest

/-- `merge(a::NamedTuple, itr)`, `base/namedtuple.jl:364-380`: collect the names
and values, then `merge(a, NamedTuple{(names...,)}((vals...,)))`. -/
def mergeItr (a : NT α) (itr : List (KV α)) : R (NT α) := do
  let acc ← mergeItrLoop [] itr
  let b ← ofNamesTuple (acc.map Prod.fst) (acc.map Prod.snd)
  pure (JuliaLean.Tuples.merge a b)

/-- `NamedTuple(itr) = (; itr...)`, `base/namedtuple.jl:151`: the lowering of
`(; itr...)` is `merge(NamedTuple(), itr)`. -/
def ofItr (itr : List (KV α)) : R (NT α) := mergeItr [] itr

/-- `merge(a, b::Iterators.Pairs{<:Any,<:Any,Nothing,<:NamedTuple}) =
merge(a, getfield(b, :data))`, `base/namedtuple.jl:346`: `b` wraps the named tuple `data`. -/
def mergePairs (a data : NT α) : NT α := JuliaLean.Tuples.merge a data

/-- `merge(a, b::Iterators.Zip{<:Tuple{Any,Any}}) = merge(a, NamedTuple{Tuple(b.is[1])}(b.is[2]))`,
`base/namedtuple.jl:348`: all keys and all values of the two zipped collections. -/
def mergeZip (a : NT α) (ks : List String) (vs : List α) : R (NT α) := do
  let b ← ofNamesItr ks vs
  pure (JuliaLean.Tuples.merge a b)

/-- `merge(a, b, cs...) = merge(merge(a, b), cs...)` (`base/namedtuple.jl:350`)
and `merge(a) = a` (`base/namedtuple.jl:352`). -/
def mergeMany (a : NT α) : List (NT α) → NT α
  | [] => a
  | b :: cs => mergeMany (JuliaLean.Tuples.merge a b) cs

/-- `length(t) = nfields(t)`, `firstindex(t) = 1`, `lastindex(t) = nfields(t)`,
`base/namedtuple.jl:159,163-164`. -/
def length (t : NT α) : Nat := t.length
def firstindex (_ : NT α) : Int := 1
def lastindex (t : NT α) : Int := t.length

/-- `iterate(t::NamedTuple, iter=1) = iter > nfields(t) ? nothing : (getfield(t, iter), iter + 1)`,
`base/namedtuple.jl:160`. -/
def iterate (t : NT α) (i : Int := 1) : R (Option (α × Int)) :=
  if i > t.length then .ok none else do
    let x ← getfield (ntValues t) i
    pure (some (x, i + 1))

/-- `rest(t::NamedTuple) = t` (`base/namedtuple.jl:161`) and
`rest(t::NamedTuple{names}, i) = NamedTuple{rest(names, i::Int)}(t)` (`:162`). -/
def restAll (t : NT α) : NT α := t
def rest (t : NT α) (i : JInt .i64) : R (NT α) := do
  let names ← restTuple (ntNames t) i
  selectNames t names

/-- `getindex(t, i::Int) = getfield(t, i)`, `getindex(t, i::Symbol) = getfield(t, i)`,
`getindex(t, ::Colon) = t`, `getindex(t, idxs::AbstractVector{Symbol}) =
NamedTuple{Tuple(idxs)}(t)`, `base/namedtuple.jl:165-169`. -/
def getindexInt (t : NT α) (i : Int) : R α := getfield (ntValues t) i
def getindexSym (t : NT α) (s : String) : R α :=
  match lookup t s with
  | some x => .ok x
  | none => .error .fieldError
def getindexColon (t : NT α) : NT α := t
def getindexSymVec (t : NT α) (idxs : List String) : R (NT α) := selectNames t idxs

/-- `indexed_iterate(t::NamedTuple, i::Int, state=1) = (getfield(t, i), i+1)`,
`base/namedtuple.jl:170`. -/
def indexedIterate (t : NT α) (i : Int) : R (α × Int) := do
  let x ← getfield (ntValues t) i
  pure (x, i + 1)

/-- `isempty(::NamedTuple{()}) = true`, `isempty(::NamedTuple) = false`,
`empty(::NamedTuple) = NamedTuple()`, `base/namedtuple.jl:171-173`. -/
def isempty : NT α → Bool
  | [] => true
  | _ :: _ => false
def empty (_ : NT α) : NT α := []

/-- `prevind(t, i::Integer) = Int(i)-1`, `nextind(t, i::Integer) = Int(i)+1`,
`base/namedtuple.jl:175-176`. -/
def prevind (_ : NT α) (i : Idx) : R (JInt .i64) := do
  let j ← Tup.idxToInt i
  pure (j - JInt.lit .i64 1)
def nextind (_ : NT α) (i : Idx) : R (JInt .i64) := do
  let j ← Tup.idxToInt i
  pure (j + JInt.lit .i64 1)

/-- `convert(::Type{NT}, nt::NT) = nt` for the same type (`base/namedtuple.jl:178-179`). -/
def convertSame (nt : NT α) : NT α := nt

/-- `convert(::Type{NT}, t::Tuple) = NT(t)`, `base/namedtuple.jl:180`, for
`NT = NamedTuple{names, Tuple{tys...}}`. -/
def convertTuple (conv : T → α → R α) (names : List String) (tys : List T) (t : List α) :
    R (NT α) := ofTuple conv names tys t

/-- `convert(::Type{NamedTuple{names,T}}, nt::NamedTuple{names}) = NT(nt)`
(`base/namedtuple.jl:182-185`), and the abstract-target method
`NT1(T1(nt))` with `T1 = Tuple{fieldtype(NT, i)...}` (`:187-193`): both convert
each field of `nt` (whose names are `names`) to its field type. -/
def convertNT (conv : T → α → R α) (tys : List T) (nt : NT α) : R (NT α) :=
  ofNT conv (ntNames nt) tys nt
def convertNTAbstract (conv : T → α → R α) (tys : List T) (nt : NT α) : R (NT α) := do
  let t1 ← totupleFixed conv tys (ntValues nt)
  ofTuple conv (ntNames nt) tys t1

/-- `Tuple(nt) = (nt...,)` (`base/namedtuple.jl:195`) and
`(::Type{T})(nt::NamedTuple) = (t = Tuple(nt); t isa T ? t : convert(T, t)::T)`
(`:196`) for `T = Tuple{tys...}`: a length mismatch is a `MethodError`
("Cannot convert"). -/
def toTuple (nt : NT α) : List α := ntValues nt
def toTupleType (conv : T → α → R α) (tys : List T) (nt : NT α) : R (List α) :=
  if tys.length ≠ nt.length then .error (.jl (.methodError "convert"))
  else (tys.zip (ntValues nt)).mapM fun p => conv p.1 p.2

/-- `==(a::NamedTuple{n}, b::NamedTuple{n}) = Tuple(a) == Tuple(b)`,
`==(a::NamedTuple, b::NamedTuple) = false`, `base/namedtuple.jl:241-242`. -/
def eq (o : Ops α) (a b : NT α) : Option Bool :=
  if ntNames a = ntNames b then JuliaLean.Tuples.eq o (ntValues a) (ntValues b) else some false

/-- `isequal` on named tuples, `base/namedtuple.jl:244-245`. -/
def isequal (o : Ops α) (a b : NT α) : Bool :=
  if ntNames a = ntNames b then JuliaLean.Tuples.isequal o (ntValues a) (ntValues b) else false

/-- `_nt_names(::NamedTuple{names}) = names` and the type method,
`base/namedtuple.jl:247-248`. -/
def ntNamesOf (nt : NT α) : List String := ntNames nt

/-- `(<)(a::NamedTuple{n}, b::NamedTuple{n}) = Tuple(a) < Tuple(b)` and
`isless(a::NamedTuple{n}, b::NamedTuple{n})`, `base/namedtuple.jl:252-253`;
named tuples with different names have no method (`MethodError`). -/
def lt (o : Ops α) (a b : NT α) : R (Option Bool) :=
  if ntNames a = ntNames b then .ok (JuliaLean.Tuples.lt o (ntValues a) (ntValues b))
  else .error (.jl (.methodError "isless"))
def isless (o : Ops α) (a b : NT α) : R Bool :=
  if ntNames a = ntNames b then .ok (JuliaLean.Tuples.isless o (ntValues a) (ntValues b))
  else .error (.jl (.methodError "isless"))

/-- `same_names(::NamedTuple{names}...) = true`, `same_names(::NamedTuple...) = false`,
`base/namedtuple.jl:255-256`. -/
def sameNames (nts : List (NT α)) : Bool :=
  match nts with
  | [] => true
  | a :: rest => rest.all fun b => ntNames b == ntNames a

/-- `map(f, nt::NamedTuple{names}, nts::NamedTuple...)`, `base/namedtuple.jl:259-264`:
`ArgumentError` unless all names agree, then `NamedTuple{names}` of the tuple
`map` of the values (elementwise). -/
def map {β : Type} (f : List α → β) (nt : NT α) (nts : List (NT α)) : R (NT β) :=
  if !sameNames (nt :: nts) then argErr "Named tuple names do not match."
  else .ok ((ntNames nt).zip ((Tup.zipN ((nt :: nts).map ntValues) nt.length).map f))

/-- `filter(f, xs::NamedTuple) = xs[filter(k -> f(xs[k]), keys(xs))]`,
`base/namedtuple.jl:266`. -/
def filter (f : α → Bool) (xs : NT α) : R (NT α) :=
  selectNames xs ((ntNames xs).filter fun k => (lookup xs k).any f)

/-- `keys(nt) = names`, `values(nt) = Tuple(nt)`, `base/namedtuple.jl:382-383`. -/
def keys (nt : NT α) : List String := ntNames nt
def values (nt : NT α) : List α := ntValues nt

/-- `get(f::Callable, nt, key::Union{Integer, Symbol}) = isdefined(nt, key) ?
getfield(nt, key) : f()`, `base/namedtuple.jl:386`. -/
def getF (f : Unit → R α) (nt : NT α) (k : JuliaLean.Tuples.Key) : R α := do
  if ← JuliaLean.Tuples.isdefinedNT nt k then JuliaLean.Tuples.getfieldKey nt k else f ()

/-- `tail(t::NamedTuple{names}) = NamedTuple{tail(names)}(t)`,
`front(t::NamedTuple{names}) = NamedTuple{front(names)}(t)`,
`reverse(nt) = NamedTuple{reverse(keys(nt))}(reverse(values(nt)))`,
`base/namedtuple.jl:387-389`. -/
def tail (t : NT α) : R (NT α) := do
  let names ← JuliaLean.Tuples.tail (ntNames t)
  selectNames t names
def front (t : NT α) : R (NT α) := do
  let names ← JuliaLean.Tuples.front (ntNames t)
  selectNames t names
def reverse (nt : NT α) : R (NT α) :=
  ofNamesTuple (JuliaLean.Tuples.revargs (ntNames nt)) (JuliaLean.Tuples.revargs (ntValues nt))

/-- `delete(a::NamedTuple{an}, field::Symbol)`, `base/namedtuple.jl:437-440`:
`NamedTuple{diff_names(an, (field,))}(a)`. -/
def delete (a : NT α) (field : String) : R (NT α) := selectNames a (diffNames (ntNames a) [field])

end NTup

open NTup

/-! ## Properties -/

/-- The fields of a named tuple with the given names, in the given order. -/
def fieldsAt {α : Type} (nt : NT α) (names : List String) : Option (List α) :=
  names.mapM (lookup nt)

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

/-- The step of `firstKeys`: append a key not yet seen. -/
def keyStep {α : Type} (ks : List String) (kv : KV α) : List String :=
  if kv.key ∈ ks then ks else ks ++ [kv.key]

/-- The keys of `itr` in the order of their first occurrence. -/
def firstKeys {α : Type} (itr : List (KV α)) : List String := itr.foldl keyStep []

/-- The value of the last pair of `itr` with key `k`, if any. -/
def lastVal {α : Type} (itr : List (KV α)) (k : String) : Option α :=
  (itr.reverse.find? (·.key == k)).map KV.val

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
