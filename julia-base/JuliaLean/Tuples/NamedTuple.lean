import JuliaLean.Tuples.Model

/-!
Model of `NamedTuple` (`base/namedtuple.jl`). A named tuple is the list of its
`(name, value)` fields; names are `Symbol`s, written as strings. A named tuple
that Julia can build has distinct names.
-/

namespace JuliaLean.Tuples

abbrev NT (α : Type) := List (String × α)

variable {α : Type}

def ntNames (nt : NT α) : List String := nt.map Prod.fst
def ntValues (nt : NT α) : List α := nt.map Prod.snd

/-- The field called `k`, if any. -/
def lookup (nt : NT α) (k : String) : Option α := (nt.find? (·.1 == k)).map Prod.snd

/-- `sym_in`, `base/tuple.jl:696-703`. -/
def symIn (x : String) (itr : List String) : Bool := itr.any (· == x)

/-- `NamedTuple{names}(nt)`, `base/namedtuple.jl:136-146`: `fieldindex` of each
requested name (`FieldError` for a missing one), then the type
`NamedTuple{names, types}`, which rejects duplicate names (`ErrorException`). -/
def selectNames (nt : NT α) (names : List String) : R (NT α) :=
  match names.mapM (fun k => (lookup nt k).map (k, ·)) with
  | none => .error .fieldError
  | some fields => if names.Nodup then .ok fields else .error .errorException

/-- `getindex(t::NamedTuple, idxs::Tuple{Vararg{Symbol}}) = NamedTuple{idxs}(t)`,
`base/namedtuple.jl:168`. -/
def getindexNames (nt : NT α) (idxs : List String) : R (NT α) := selectNames nt idxs

/-- `merge_names`, `base/namedtuple.jl:268-278`. -/
def mergeNames (an bn : List String) : List String :=
  an ++ bn.filter (fun n => !symIn n an)

/-- `merge(a::NamedTuple, b::NamedTuple)`, `base/namedtuple.jl:331-344`: each
merged name takes its value from `b` when `sym_in(name, bn)`, else from `a`
(`merge_fallback`, `base/namedtuple.jl:287-300`). -/
def merge (a b : NT α) : NT α :=
  if b = [] then a
  else if a = [] then b
  else (mergeNames (ntNames a) (ntNames b)).filterMap fun n =>
    (if symIn n (ntNames b) then lookup b n else lookup a n).map (n, ·)

/-- `diff_names`, `base/namedtuple.jl:391-401`. -/
def diffNames (an bn : List String) : List String := an.filter (fun n => !symIn n bn)

/-- `structdiff(a, b)`, `base/namedtuple.jl:448-461`. -/
def structdiff (a : NT α) (bn : List String) : NT α :=
  if ntNames a = bn then []
  else (diffNames (ntNames a) bn).filterMap fun n => (lookup a n).map (n, ·)

/-- `delete(a, field)`, `base/namedtuple.jl:437-440`. -/
def delete (a : NT α) (field : String) : R (NT α) := selectNames a (diffNames (ntNames a) [field])

/-- `setindex(nt, v, idx::Symbol) = merge(nt, (; idx => v))`, `base/namedtuple.jl:483-485`. -/
def setindexNT (nt : NT α) (v : α) (k : String) : NT α := merge nt [(k, v)]

/-- A `haskey`/`get` key: a `Symbol` or an `Integer`. -/
inductive Key where
  | sym (s : String)
  | int (i : Idx)

/-- The builtin `isdefined(nt, key)`: a `Symbol` names a field, an `Int` is a
field position; any other key type is a `TypeError`. -/
def isdefinedNT (nt : NT α) : Key → R Bool
  | .sym s => .ok (symIn s (ntNames nt))
  | .int (.int .i64 v) => .ok (decide (1 ≤ v.val ∧ v.val ≤ nt.length))
  | .int _ => .error .typeError

/-- `haskey(nt, key::Union{Integer, Symbol}) = isdefined(nt, key)`, `base/namedtuple.jl:384`. -/
def haskeyNT (nt : NT α) (k : Key) : R Bool := isdefinedNT nt k

/-- `getfield(nt, key)` for a defined key. -/
def getfieldKey (nt : NT α) : Key → R α
  | .sym s => match lookup nt s with
    | some a => .ok a
    | none => .error .fieldError
  | .int i => getfield (ntValues nt) i.val

/-- `get(nt, key, default)`, `base/namedtuple.jl:385`. -/
def getNT (nt : NT α) (k : Key) (d : α) : R α := do
  if ← isdefinedNT nt k then getfieldKey nt k else pure d

/-- `isequal` on named tuples, `base/namedtuple.jl:244-245`. -/
def isequalNT (o : Ops α) (a b : NT α) : Bool :=
  ntNames a == ntNames b && isequal o (ntValues a) (ntValues b)

/-- `hash(x::NamedTuple, h) = xor(objectid(_nt_names(x)), hash(Tuple(x), h))`,
`base/namedtuple.jl:250`; `objectid` of the names tuple is `oid`. -/
def hashNT (o : Ops α) (oid : List String → Nat) (x : NT α) (h : Nat) : Nat :=
  oid (ntNames x) ^^^ hash o (ntValues x) h

/-- `split_rest(t::NamedTuple, n, st...)`, `base/namedtuple.jl:585-589`. -/
def splitRestNT (t : NT α) (n i : JInt .i64) : R (NT α × NT α) := do
  checkLengthSplitRest t.length n
  let (f, l) ← splitRestTuple (ntNames t) n i
  let a ← selectNames t f
  let b ← selectNames t l
  pure (a, b)

end JuliaLean.Tuples
