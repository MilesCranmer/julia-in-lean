import JuliaLean.Dicts.Table

/-!
# `Set`, `base/set.jl` and `base/abstractset.jl` (master `bbfa0ce4150`)

`struct Set{T}; dict::Dict{T,Nothing}; end` (`base/set.jl:39-43`): a set is
the table of its `dict` field, with `Unit` for `Nothing` values.

Elements of another type `Q` (e.g. a `Float64` pushed into a `Set{Float32}`)
go through a `Conv Q K`: the type test `x isa K`, `convert(K, x)`, `hash(x)`
and `isequal(x, k)`.
-/

namespace JuliaLean.Dicts

variable {K Q E : Type}

/-- `Set{K}`: the `dict::Dict{K,Nothing}` field. -/
abbrev SetT (K : Type) := Table K Unit

/-- How a value of type `Q` meets keys of type `K`. -/
structure Conv (Q K : Type) where
  /-- `x isa K` (with the value as a `K`) -/
  isa : Q → Option K
  /-- `convert(K, x)` -/
  convert : Q → DR K
  /-- `hash(x)` -/
  hash : Q → JInt .u64
  /-- `x === k || isequal(x, k)` -/
  iseq : Q → K → Bool

/-- Elements that already have the key type. -/
def Conv.self (o : KeyOps K) : Conv K K := ⟨some, pure, o.hash, o.eq⟩

/-- `setindex!(h, v0, key0)`, `base/dict.jl:347-357`: convert a foreign key and
throw `KeyTypeError` unless `isequal(key, key0)`. -/
def setindexConv {V : Type} (o : KeyOps K) (c : Conv Q K) (t : Table K V) (v : V) (key0 : Q) :
    DR (Table K V) :=
  match c.isa key0 with
  | some k => setindex o t v k
  | none => do
    let k ← c.convert key0
    if !(c.iseq key0 k) then throw .keyTypeError
    setindex o t v k

/-- `push!(s::Set, x) = (s.dict[x] = nothing; s)`, `base/set.jl:137`. -/
def pushConv (o : KeyOps K) (c : Conv Q K) (s : SetT K) (x : Q) : DR (SetT K) :=
  setindexConv o c s () x

/-- `push!` of an element of the key type. -/
def push (o : KeyOps K) (s : SetT K) (x : K) : DR (SetT K) := setindex o s () x

/-- `in(x, s::Set) = haskey(s.dict, x)`, `base/set.jl:92`, for `x::Q`. -/
def inConv (c : Conv Q K) (s : SetT K) (x : Q) : DR Bool := do
  let index ← htKeyindex s (c.hash x) (c.iseq x)
  pure (index ≥ 0)

/-- `in(x, s::Set)` for `x::K`. -/
def setIn (o : KeyOps K) (s : SetT K) (x : K) : DR Bool := haskey o s x

/-- `delete!(s::Set, x)`, `base/set.jl:164`. -/
def setDelete (o : KeyOps K) (s : SetT K) (x : K) : DR (SetT K) := dictDelete o s x

/-- `in!(x, s::Set)`, `base/set.jl:129-135`. -/
def inBang (o : KeyOps K) (c : Conv Q K) (s : SetT K) (x : Q) : DR (Bool × SetT K) := do
  let xT ← c.convert x
  let (idx, sh, s) ← keyindex2 o s (o.hash xT) (o.eq xT)
  if idx > 0 then pure (true, s)
  else
    let s ← setindexAt o s () xT (-idx).toNat sh
    pure (false, s)

/-- The loop of `union!(s::AbstractSet{T}, itr)`, `base/abstractset.jl:107-110`:
push each element and stop once `length(s) == max_values(T)`. -/
def unionLoop (o : KeyOps K) (c : Conv Q K) : SetT K → List Q → DR (SetT K)
  | s, [] => pure s
  | s, x :: xs => do
    let s ← pushConv o c s x
    if (s.count : Int) == o.maxValues.val then pure s else unionLoop o c s xs

/-- `union!(s::AbstractSet{T}, itr)`, `base/abstractset.jl:105-112`, for an
iterator with a length (a vector or a set, listed in iteration order). -/
def unionBang (o : KeyOps K) (c : Conv Q K) (s : SetT K) (itr : List Q) : DR (SetT K) := do
  let s ← sizehint o s (JInt.lit .i64 (s.count + itr.length)) false
  unionLoop o c s itr

/-- `Set{T}(itr) = union!(Set{T}(), itr)`, `base/set.jl:47`. -/
def setOf (o : KeyOps K) (c : Conv Q K) (itr : List Q) : DR (SetT K) :=
  unionBang o c Table.empty itr

/-- Elements of a set in iteration order (`base/set.jl:176`, KeySet iteration
`base/dict.jl:717-723`, which visits the same slots as `iterate(::Dict)`). -/
def elems (s : SetT K) : DR (List K) := do
  let xs ← iterList s
  pure (xs.map (·.1))

/-- `union!(s, t::Set)`. -/
def unionSet (o : KeyOps K) (s t : SetT K) : DR (SetT K) := do
  unionBang o (Conv.self o) s (← elems t)

/-- `for x in s; (!keep(x)) && delete!(s, x); end`: the iteration of
`mapfilter(!pred, delete!, s, s)` (`base/abstractset.jl:633-641`) over a set
that is mutated inside the loop. The iteration state is the slot index,
`base/dict.jl:717-723`; `left` bounds the steps (each strictly increases it). -/
def filterLoop (o : KeyOps K) (keep : K → DR Bool) : Nat → SetT K → Nat → DR (SetT K)
  | 0, s, _ => pure s
  | left + 1, s, i =>
    let j := skipDeleted s i
    if j == 0 then pure s else
    match s.keys j with
    | none => throw .undefRef
    | some x => do
      let k ← keep x
      let s ← if !k then setDelete o s x else pure s
      filterLoop o keep left s (j + 1)

/-- `filter!(f, s::Set) = unsafe_filter!(f, s)`, `base/set.jl:695`, `base/abstractset.jl:633`. -/
def setFilterBang (o : KeyOps K) (keep : K → DR Bool) (s : SetT K) : DR (SetT K) :=
  filterLoop o keep (s.size + 1) s s.idxfloor

/-- `intersect!(s::AbstractSet, s2::AbstractSet) = filter!(in(s2), s)`, `base/abstractset.jl:198`. -/
def intersectBang (o : KeyOps K) (s t : SetT K) : DR (SetT K) :=
  setFilterBang o (fun x => setIn o t x) s

/-- `setdiff!(s::Set, t::Set)`, `base/set.jl:187-198`. -/
def setdiffBang (o : KeyOps K) (s t : SetT K) : DR (SetT K) := do
  if 2 * s.count < t.count then
    setFilterBang o (fun x => do pure (!(← setIn o t x))) s
  else
    (← elems t).foldlM (fun s x => setDelete o s x) s

/-- `symdiff!(s::AbstractSet, itr::AbstractSet)`, `base/abstractset.jl:299-304`. -/
def symdiffBang (o : KeyOps K) (s t : SetT K) : DR (SetT K) := do
  (← elems t).foldlM (fun s x => do
    if ← setIn o s x then setDelete o s x else push o s x) s

/-- The loop `for elt in a; elt in b || return false; end`, `base/abstractset.jl:348-351`. -/
def allIn (o : KeyOps K) (b : SetT K) : List K → DR Bool
  | [] => pure true
  | x :: xs => do
    if ← setIn o b x then allIn o b xs else pure false

/-- `issubset(a::Set, b::Set)`, `base/abstractset.jl:335-352`: `b` has a length
and `a` is an `AbstractSet`, so `length(a) > length(b)` returns early;
`hasfastin(b)` holds, so `b` is not converted. -/
def issubsetSet (o : KeyOps K) (a b : SetT K) : DR Bool := do
  if a.count > b.count then return false
  allIn o b (← elems a)

/-- `==(a::AbstractSet, b::AbstractSet)`, `base/abstractset.jl:622`. -/
def setEq (o : KeyOps K) (a b : SetT K) : DR Bool := do
  if a.count == b.count then issubsetSet o a b else pure false

/-- `issubset(a::Vector, b::Vector)`, `base/abstractset.jl:335-352`. A vector has
a length and no fast `in` (`hasfastin(::Type{<:Vector}) = false`,
`base/abstractset.jl:367`), so for `length(b) > FASTIN_SET_THRESHOLD = 70` the
call becomes `issubset(a, Set(b))`; otherwise each `elt in b` is
`any(y -> y == elt, b)` with the element `==` (`eqeq`). -/
def issubsetVec (o : KeyOps E) (eqeq : E → E → Bool) (a b : List E) : DR Bool := do
  if b.length > 70 then
    let sb ← setOf o (Conv.self o) b
    -- issubset(a, Set(b)): hasfastin(Set) holds, so straight to the loop
    allIn o sb a
  else
    pure (a.all fun x => b.any fun y => eqeq y x)

end JuliaLean.Dicts
