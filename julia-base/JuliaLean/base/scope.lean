import JuliaLean.Core
import JuliaLean.base.dict

/-!
# Model of `base/scope.jl`

`Key` represents the erased Julia `AbstractScopedValue{T}` object key. The persistent
scope storage uses `dict.PersistentDict`; `H`, `HS`, and `S` carry its HAMT handle,
hash state, and iteration state.
-/

namespace JuliaLean.base.scope

open JuliaLean

/--
Julia source: base/scope.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractScopedValue{T} end
```
-/
abbrev AbstractScopedValue (Key : Type) := Key

/--
Julia source: base/scope.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ScopeStorage = PersistentDict{AbstractScopedValue, Any}
```
-/
abbrev ScopeStorage (Key Any H : Type) :=
  JuliaLean.base.dict.PersistentDict (AbstractScopedValue Key) Any H

/--
Julia source: base/scope.jl:24-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Scope
    values::ScopeStorage
end
```
-/
structure Scope (Key Any H : Type) where
  values : ScopeStorage Key Any H

/-- Persistent dictionary operations, value conversion, and source error mapping for `Scope`. -/
structure ScopeOps (Key Any H HS S TypeRep Error : Type) where
  persistent : JuliaLean.base.dict.PersistentOps
    (AbstractScopedValue Key) Any (AbstractScopedValue Key) Any H HS S
  valueType : AbstractScopedValue Key → TypeRep
  convertValue : TypeRep → Any → Except Error Any
  keyConv : JuliaLean.base.dict.KeyConv (AbstractScopedValue Key) (AbstractScopedValue Key)
  valueConv : JuliaLean.base.dict.ValueConv Any Any
  mapDictError : JuliaLean.base.dict.DictError → Error

/-- Convert the value before building a scope, then use the existing persistent-dictionary model. -/
def scopeWithValue {Key Any H HS S TypeRep Error : Type}
    (ops : ScopeOps Key Any H HS S TypeRep Error)
    (parent : Option (Scope Key Any H)) (key : AbstractScopedValue Key) (value : Any) :
    Option (Except Error (Scope Key Any H)) :=
  match ops.convertValue (ops.valueType key) value with
  | .error error => some (.error error)
  | .ok converted =>
      match parent with
      | none =>
          match JuliaLean.base.dict.persistentTypedPair ops.persistent (key, converted) with
          | .error error => some (.error (ops.mapDictError error))
          | .ok values => some (.ok ⟨values⟩)
      | some parent =>
          match JuliaLean.base.dict.persistentTypedExtendPair ops.persistent
              ops.keyConv ops.valueConv parent.values (key, converted) with
          | none => none
          | some (.error error) => some (.error (ops.mapDictError error))
          | some (.ok values) => some (.ok ⟨values⟩)

/--
Julia source: base/scope.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Scope(scope::Scope) = scope
```
-/
def scopeIdentity {Key Any H : Type} (scope : Scope Key Any H) : Scope Key Any H := scope

/--
Julia source: base/scope.jl:30-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Scope(parent::Union{Nothing, Scope}, key::AbstractScopedValue{T}, value) where T
    val = convert(T, value)
    if parent === nothing
        return Scope(ScopeStorage(key=>val))
    end
    return Scope(ScopeStorage(parent.values, key=>val))
end
```
-/
def scopeWithValueConstructor {Key Any H HS S TypeRep Error : Type}
    (ops : ScopeOps Key Any H HS S TypeRep Error)
    (parent : Option (Scope Key Any H)) (key : AbstractScopedValue Key) (value : Any) :
    Option (Except Error (Scope Key Any H)) :=
  scopeWithValue ops parent key value

/--
Julia source: base/scope.jl:38-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Scope(scope, pair::Pair{<:AbstractScopedValue})
    return Scope(scope, pair...)
end
```
-/
def scopeWithPair {Key Any H HS S TypeRep Error : Type}
    (ops : ScopeOps Key Any H HS S TypeRep Error)
    (parent : Option (Scope Key Any H)) (pair : AbstractScopedValue Key × Any) :
    Option (Except Error (Scope Key Any H)) :=
  scopeWithValue ops parent pair.1 pair.2

/--
Julia source: base/scope.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Scope(scope, pair1::Pair{<:AbstractScopedValue}, pair2::Pair{<:AbstractScopedValue}, pairs::Pair{<:AbstractScopedValue}...)
    # Unroll this loop through recursion to make sure that
    # our compiler optimization support works
    return Scope(Scope(scope, pair1...), pair2, pairs...)
end
```
-/
def scopeWithPairs {Key Any H HS S TypeRep Error : Type}
    (ops : ScopeOps Key Any H HS S TypeRep Error)
    (parent : Option (Scope Key Any H)) (first : AbstractScopedValue Key × Any) :
    List (AbstractScopedValue Key × Any) → Option (Except Error (Scope Key Any H))
  | [] => scopeWithPair ops parent first
  | pair :: rest =>
      match scopeWithPair ops parent first with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok next) => scopeWithPairs ops (some next) pair rest

/--
Julia source: base/scope.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Scope(::Nothing) = nothing
```
-/
def scopeNothing {Key Any H : Type} : Option (Scope Key Any H) := none

end JuliaLean.base.scope

namespace JuliaLean.MiscCov.Scope

/-- A scoped value: an identity and `convert(T, ·)` for its type `T`. -/
structure Key (V : Type) where
  id : Nat
  conv : V → M V

variable {V : Type}

/-- `ScopeStorage = PersistentDict{AbstractScopedValue, Any}`: a persistent map, as an
association list in which the first binding of a key wins; `PersistentDict(d, k => v)`
is the map `d` with `k` bound to `v`. -/
abbrev Storage (V : Type) := List (Nat × V)

def Storage.get : Storage V → Nat → Option V
  | [], _ => none
  | (k', v) :: d, k => if k' = k then some v else Storage.get d k

/-- `struct Scope values::ScopeStorage end`. -/
structure Scope (V : Type) where
  values : Storage V

/-- `Scope(scope::Scope) = scope`, `base/scope.jl:28`. -/
def ofScope (s : Scope V) : Scope V := s

/-- `Scope(parent::Union{Nothing, Scope}, key::AbstractScopedValue{T}, value)`,
`base/scope.jl:30-36`. -/
def mk (parent : Option (Scope V)) (key : Key V) (value : V) : M (Scope V) := do
  let val ← key.conv value
  match parent with
  | none => pure ⟨[(key.id, val)]⟩
  | some p => pure ⟨(key.id, val) :: p.values⟩

/-- `Scope(scope, pair::Pair{<:AbstractScopedValue}) = Scope(scope, pair...)`,
`base/scope.jl:38-40`. -/
def mkPair (scope : Option (Scope V)) (pair : Key V × V) : M (Scope V) := mk scope pair.1 pair.2

/-- `Scope(scope, pair1, pair2, pairs...) = Scope(Scope(scope, pair1...), pair2, pairs...)`,
`base/scope.jl:42-46`, unrolled over the pairs after the first. -/
def mkPairs (scope : Option (Scope V)) (pair1 : Key V × V) : List (Key V × V) → M (Scope V)
  | [] => mkPair scope pair1
  | pair2 :: pairs => do
    let s ← mk scope pair1.1 pair1.2
    mkPairs (some s) pair2 pairs

/-- `Scope(::Nothing) = nothing`, `base/scope.jl:47`. -/
def ofNothing : Option (Scope V) := none

end JuliaLean.MiscCov.Scope
