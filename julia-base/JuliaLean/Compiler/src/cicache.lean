/-!
Model of `Compiler/src/cicache.jl`: world ranges and the code-instance cache view.

Worlds are `UInt` in Julia. They are `Nat`s here, and every operation keeps them at most
`typemaxUInt`; the one place where Julia's arithmetic wraps (`b.min_world - 1` in `union`) is
modelled with the wrap.

The pinned file has no `WorldView`: the cache view is `InternalCodeCache`, whose lookups go
through `jl_rettype_inferred` (`src/gf.c:4272-4292`), modelled here over an explicit cache chain.
-/

namespace JuliaLean.Compiler.CICache

/-- `typemax(UInt)` on 64-bit Julia. -/
def typemaxUInt : Nat := 2 ^ 64 - 1

/-- `struct WorldRange`

Julia source: Compiler/src/cicache.jl:3-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct WorldRange
    min_world::UInt
    max_world::UInt
end
```
-/
structure WorldRange where
  minWorld : Nat
  maxWorld : Nat
  deriving Inhabited, BEq, DecidableEq, Repr

/-- `WorldRange()`, `WorldRange(w::UInt)`, `WorldRange(r::UnitRange)`

Julia source: Compiler/src/cicache.jl:7-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
WorldRange() = WorldRange(typemin(UInt), typemax(UInt))
WorldRange(w::UInt) = WorldRange(w, w)
WorldRange(r::UnitRange) = WorldRange(first(r), last(r))
```
Only ranges of `UInt` endpoints are modelled. A `UnitRange` built from `start` and `stop`
has `last` equal to `stop`, or to `start - 1` when `stop < start` (`base/range.jl`, the
`UnitRange` inner constructor's `unitrange_last`).
-/
def WorldRange.all : WorldRange := ⟨0, typemaxUInt⟩
def WorldRange.single (w : Nat) : WorldRange := ⟨w, w⟩
def WorldRange.ofUnitRange (start stop : Nat) : WorldRange :=
  ⟨start, if stop ≥ start then stop else start - 1⟩

/-- `first`, `last`, `in`, `min_world`, `max_world`

Julia source: Compiler/src/cicache.jl:10-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(wr::WorldRange) = wr.min_world
last(wr::WorldRange) = wr.max_world
in(world::UInt, wr::WorldRange) = wr.min_world <= world <= wr.max_world
min_world(wr::WorldRange) = first(wr)
max_world(wr::WorldRange) = last(wr)
```
-/
def WorldRange.first (wr : WorldRange) : Nat := wr.minWorld
def WorldRange.last (wr : WorldRange) : Nat := wr.maxWorld
def WorldRange.contains (wr : WorldRange) (world : Nat) : Bool :=
  wr.minWorld ≤ world && world ≤ wr.maxWorld

/-- A failed `@assert` (`AssertionError`). -/
def assertionError {α : Type} (msg : String) : Except String α :=
  throw s!"julia:AssertionError: {msg}"

/-- `intersect(a::WorldRange, b::WorldRange)`

Julia source: Compiler/src/cicache.jl:16-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function intersect(a::WorldRange, b::WorldRange)
    ret = WorldRange(max(a.min_world, b.min_world), min(a.max_world, b.max_world))
    @assert ret.min_world <= ret.max_world
    return ret
end
```
-/
def intersect (a b : WorldRange) : Except String WorldRange := do
  let ret : WorldRange := ⟨max a.minWorld b.minWorld, min a.maxWorld b.maxWorld⟩
  if !(ret.minWorld ≤ ret.maxWorld) then
    assertionError "ret.min_world <= ret.max_world"
  return ret

/-- `x - 1` on `UInt`, which wraps at zero. -/
def uintPred (x : Nat) : Nat := if x = 0 then typemaxUInt else x - 1

/-- `union(a::WorldRange, b::WorldRange)`

Julia source: Compiler/src/cicache.jl:22-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function union(a::WorldRange, b::WorldRange)
    if b.min_world < a.min_world
        (b, a) = (a, b)
    end
    @assert a.max_world >= b.min_world - 1
    return WorldRange(a.min_world, b.max_world)
end
```
-/
def union (a b : WorldRange) : Except String WorldRange := do
  let (a, b) := if b.minWorld < a.minWorld then (b, a) else (a, b)
  if !(a.maxWorld ≥ uintPred b.minWorld) then
    assertionError "a.max_world >= b.min_world - 1"
  return ⟨a.minWorld, b.maxWorld⟩

/-- One entry of a method instance's cache chain (`mi.cache`, then `ci.next`): the code
instance id, its world range, its owner (an object identity class: owners are compared with
`jl_egal`) and whether `ci.inferred` is set (not C `NULL`). -/
structure CacheEntry where
  ci : Nat
  minWorld : Nat
  maxWorld : Nat
  owner : Nat
  hasInferred : Bool
  /-- `ci.inferred` and `ci.invoke` are both set (`hasinvoke` of `jl_mi_cache_insert`). -/
  hasInvoke : Bool := false
  deriving Inhabited, BEq, Repr

/-- `struct InternalCodeCache`

Julia source: Compiler/src/cicache.jl:37-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InternalCodeCache
    owner::Any # `jl_egal` is used for comparison
    worlds::WorldRange
    InternalCodeCache(@nospecialize(owner), wr::WorldRange) = new(owner, wr)
    InternalCodeCache(@nospecialize(owner), args...) = new(owner, WorldRange(args...))
end
```
-/
structure InternalCodeCache where
  owner : Nat
  worlds : WorldRange
  deriving Inhabited, BEq, Repr

/-- The argument tuples `InternalCodeCache(owner, args...)` forwards to `WorldRange(args...)`:
none, one `UInt`, one `UnitRange` (by its `start` and `stop`), or the two fields. -/
inductive WorldRangeArgs where
  | none
  | single (w : Nat)
  | unitRange (start stop : Nat)
  | fields (minWorld maxWorld : Nat)
  deriving Inhabited, BEq, Repr

/-- `WorldRange(args...)` for the argument tuples of `WorldRangeArgs`. -/
def WorldRange.ofArgs : WorldRangeArgs → WorldRange
  | .none => WorldRange.all
  | .single w => WorldRange.single w
  | .unitRange a b => WorldRange.ofUnitRange a b
  | .fields a b => ⟨a, b⟩

/-- `InternalCodeCache(owner, args...) = new(owner, WorldRange(args...))`
(`Compiler/src/cicache.jl:41`). -/
def InternalCodeCache.ofArgs (owner : Nat) (args : WorldRangeArgs) : InternalCodeCache :=
  ⟨owner, WorldRange.ofArgs args⟩

/-- `_jl_rettype_inferred(owner, mi, min_world, max_world)` over the cache chain `chain`.

It walks the chain and returns the first code instance whose world range contains
`[min_world, max_world]`, whose owner is `jl_egal` to `owner` and whose `inferred` is set
(`src/gf.c:4272-4287`).
-/
def jlRettypeInferred (owner : Nat) (chain : List CacheEntry) (minWorld maxWorld : Nat) :
    Option Nat :=
  match chain with
  | [] => none
  | c :: rest =>
    if c.minWorld ≤ minWorld && maxWorld ≤ c.maxWorld && c.owner == owner && c.hasInferred then
      some c.ci
    else jlRettypeInferred owner rest minWorld maxWorld

/-- `haskey(wvc::InternalCodeCache, mi)`

Julia source: Compiler/src/cicache.jl:54-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function haskey(wvc::InternalCodeCache, mi::MethodInstance)
    return ccall(:jl_rettype_inferred, Any, (Any, Any, UInt, UInt), wvc.owner, mi, first(wvc.worlds), last(wvc.worlds)) !== nothing
end
```
-/
def InternalCodeCache.haskey (wvc : InternalCodeCache) (chain : List CacheEntry) : Bool :=
  (jlRettypeInferred wvc.owner chain wvc.worlds.first wvc.worlds.last).isSome

/-- `get(wvc::InternalCodeCache, mi, default)`: the code instance found, or `none` for the
default.

Julia source: Compiler/src/cicache.jl:58-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(wvc::InternalCodeCache, mi::MethodInstance, default)
    r = ccall(:jl_rettype_inferred, Any, (Any, Any, UInt, UInt), wvc.owner, mi, first(wvc.worlds), last(wvc.worlds))
    if r === nothing
        return default
    end
    return r::CodeInstance
end
```
-/
def InternalCodeCache.get (wvc : InternalCodeCache) (chain : List CacheEntry) : Option Nat :=
  jlRettypeInferred wvc.owner chain wvc.worlds.first wvc.worlds.last

/-- `getindex(wvc::InternalCodeCache, mi)`

Julia source: Compiler/src/cicache.jl:66-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(wvc::InternalCodeCache, mi::MethodInstance)
    r = get(wvc, mi, nothing)
    r === nothing && throw(KeyError(mi))
    return r::CodeInstance
end
```
-/
def InternalCodeCache.getindex (wvc : InternalCodeCache) (chain : List CacheEntry) :
    Except String Nat :=
  match wvc.get chain with
  | some c => pure c
  | none => throw "julia:KeyError: mi"

/-- `jl_mi_cache_insert(mi, ci)` (`src/gf.c:803-857`) on the cache chain of `mi`, for the
entry `e` of `ci`. The walk stops at `ci` itself (then nothing moves) or before the first entry
that `ci` should precede: `ci` has `invoke` and it does not, `ci` has `inferred` and it does not,
or `ci` has no `next` and the entry's `max_world` is smaller. `ci` is linked in there, and an
older place of `ci` further down the chain is unlinked (its `next` takes `ci`'s old `next`).
`ci` has no `next` when it is not in the chain or is its last entry. The `native_cache_valid`
flag it sets is not part of the entry. -/
def cacheNextNull (chain : List CacheEntry) (e : CacheEntry) : Bool :=
  match chain.dropWhile (·.ci != e.ci) with
  | _ :: _ :: _ => false
  | _ => true

/-- Where the walk of `jl_mi_cache_insert` stops. -/
def cacheInsertStop (nextNull : Bool) (e old : CacheEntry) : Bool :=
  old.ci == e.ci || (e.hasInvoke && !old.hasInvoke) || (e.hasInferred && !old.hasInferred) ||
    (nextNull && old.maxWorld < e.maxWorld)

/-- Link `e` in before the first entry where `stop` holds, unless that entry is `e` itself. -/
def cacheInsertAt (chain : List CacheEntry) (e : CacheEntry) (stop : CacheEntry → Bool) :
    List CacheEntry :=
  match chain.dropWhile (fun o => !stop o) with
  | o :: post =>
    if o.ci == e.ci then chain
    else chain.takeWhile (fun o => !stop o) ++ e :: (o :: post).filter (·.ci != e.ci)
  | [] => chain ++ [e]

def jlMiCacheInsert (chain : List CacheEntry) (e : CacheEntry) : List CacheEntry :=
  cacheInsertAt chain e (cacheInsertStop (cacheNextNull chain e) e)

/-- `setindex!(cache::InternalCodeCache, ci, mi)`: checks the owner, then hands `ci` to
`jl_push_newly_inferred` (when `mi.def` is a method) and `jl_mi_cache_insert` on `mi`'s cache
chain. Returns whether the push happened, and the new chain.

Julia source: Compiler/src/cicache.jl:44-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(cache::InternalCodeCache, ci::CodeInstance, mi::MethodInstance)
    @assert ci.owner === cache.owner
    m = mi.def
    if isa(m, Method)
        ccall(:jl_push_newly_inferred, Cvoid, (Any,), ci)
    end
    ccall(:jl_mi_cache_insert, Cvoid, (Any, Any), mi, ci)
    return cache
end
```
-/
def InternalCodeCache.setindex (cache : InternalCodeCache) (ci : CacheEntry) (miDefIsMethod : Bool)
    (chain : List CacheEntry) : Except String (Bool × List CacheEntry) := do
  if ci.owner != cache.owner then assertionError "ci.owner === cache.owner"
  return (miDefIsMethod, jlMiCacheInsert chain ci)

end JuliaLean.Compiler.CICache
