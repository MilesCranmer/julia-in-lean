import JuliaLean.Core
import JuliaLean.base.dict
import JuliaLean.base.scope
import JuliaLean.base.show

/-!
# Model of `base/scopedvalues.jl`

Typed source model of scoped values and dynamic-scope helpers at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Identity keys, `OncePerProcess`
forcing, conversion, current-scope access, dynamic-scope restoration, and
user-extensible display calls are explicit interfaces. Scope construction uses
the installed `dict.PersistentDict` model through `scope.ScopeOps`. Julia AST
macros remain visible as untranslated compile-time transformations.
-/

namespace JuliaLean.base.scopedvalues

open JuliaLean

/-- A world-passing IO computation; `none` represents divergence. -/
abbrev M (Error World A : Type) := World → Option (Except (Error × World) (A × World))

instance {Error World : Type} : Monad (M Error World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world =>
    match action world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (value, world)) => next value world

instance {Error World : Type} : MonadExceptOf Error (M Error World) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

/-- Source while-loop semantics for iterators whose termination is not structural. -/
def whileLoop {Error World State Result : Type}
    (step : State → M Error World (Sum Result State)) (state : State) : M Error World Result :=
  fun world =>
    match step state world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (.inl result, world)) => some (.ok (result, world))
    | some (.ok (.inr next, world)) => whileLoop step next world
partial_fixpoint

def liftExceptMap {Error World A : Type} (mapError : Error → JuliaLean.base.show.ShowError)
    (result : Except Error A) : M JuliaLean.base.show.ShowError World A :=
  match result with
  | .error error => fun world => some (.error (mapError error, world))
  | .ok value => pure value


/--
Julia source: base/scopedvalues.jl:39-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct LazyScopedValue{T} <: AbstractScopedValue{T}
    const getdefault::OncePerProcess{T}
end
```
-/
structure LazyScopedValueModel (Key Once T : Type) where
  key : Key
  getdefault : Once

/--
Julia source: base/scopedvalues.jl:79-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct ScopedValue{T} <: AbstractScopedValue{T}
    # NOTE this struct must be defined as mutable one since it's used as a key of
    #      `ScopeStorage` dictionary and thus needs object identity
    const hasdefault::Bool # this field is necessary since isbitstype `default` field may be initialized with undefined value
    const default::T
    ScopedValue{T}() where T = new{T}(false)
    ScopedValue{T}(val) where T = new{T}(true, val)
    ScopedValue(val::T) where T = new{T}(true, val)
end
```
-/
structure ScopedValueModel (Key T : Type) where
  key : Key
  hasdefault : Bool
  default : Option T

/--
Julia source: base/scopedvalues.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ScopedValue{T}() where T = new{T}(false)
```
-/
def scopedValueNoDefault {Key T : Type} (key : Key) : ScopedValueModel Key T :=
  ⟨key, false, none⟩

/--
Julia source: base/scopedvalues.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ScopedValue{T}(val) where T = new{T}(true, val)
```
-/
def scopedValueTyped {Key T A Error : Type} (key : Key) (convert : A → Except Error T)
    (value : A) : Except Error (ScopedValueModel Key T) := do
  let value ← convert value
  pure ⟨key, true, some value⟩

/--
Julia source: base/scopedvalues.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ScopedValue(val::T) where T = new{T}(true, val)
```
-/
def scopedValueInferred {Key T : Type} (key : Key) (value : T) : ScopedValueModel Key T :=
  ⟨key, true, some value⟩

/-- A value paired with the `T` parameter of `AbstractScopedValue{T}`. -/
structure AbstractScopedValueRef (T Value : Type) where
  value : Value
/--
Julia source: base/scopedvalues.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.eltype(::AbstractScopedValue{T}) where {T} = T
```
-/
def eltypeAbstractScopedValue {T Value : Type} (_value : AbstractScopedValueRef T Value) : Type := T

/--
Julia source: base/scopedvalues.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasdefault(val::ScopedValue) = val.hasdefault
```
-/
def hasdefaultScopedValue {Key T : Type} (value : ScopedValueModel Key T) : Bool :=
  value.hasdefault
/--
Julia source: base/scopedvalues.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasdefault(val::LazyScopedValue) = true
```
-/

def hasdefaultLazyScopedValue {Key Once T : Type} (_value : LazyScopedValueModel Key Once T) : Bool :=
  true

/--
Julia source: base/scopedvalues.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasdefault(val::Base.CancelTokenKey) = true
```
-/
def hasdefaultCancelTokenKey {Key : Type} (_key : Key) : Bool := true

/--
Julia source: base/scopedvalues.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getdefault(val::ScopedValue) = val.hasdefault ? val.default : throw(KeyError(val))
```
-/
def getdefaultScopedValue {Key T Error : Type} (keyError : Key → Error)
    (value : ScopedValueModel Key T) : Except Error T :=
  if value.hasdefault then
    match value.default with
    | some default => .ok default
    | none => .error (keyError value.key)
  else
    .error (keyError value.key)

/--
Julia source: base/scopedvalues.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getdefault(val::LazyScopedValue) = val.getdefault()
```
-/
def getdefaultLazyScopedValue {Key Once T Error : Type} (force : Once → Except Error T)
    (value : LazyScopedValueModel Key Once T) : Except Error T :=
  force value.getdefault

/--
Julia source: base/scopedvalues.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getdefault(val::Base.CancelTokenKey) = nothing
```
-/
def getdefaultCancelTokenKey {Key : Type} (_key : Key) : Unit := ()

/--
Julia source: base/scopedvalues.jl:119-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.isassigned(val::AbstractScopedValue)
    hasdefault(val) && return true
    scope = Core.current_scope()::Union{Scope, Nothing}
    scope === nothing && return false
    return haskey((scope::Scope).values, val)
end
```
-/
def isassigned {Key Any H HS S TypeRep Error : Type}
    (ops : JuliaLean.base.scope.ScopeOps Key Any H HS S TypeRep Error)
    (key : Key) (hasdefault : Bool)
    (currentScope : Unit → Option (JuliaLean.base.scope.Scope Key Any H)) : Bool :=
  if hasdefault then true else
    match currentScope () with
    | none => false
    | some scope => JuliaLean.base.dict.persistentHasKey ops.persistent scope.values key

structure ScopeDisplayOps (Key Any H HS S TypeRep ScopeError World Io V : Type) where
  scopeOps : JuliaLean.base.scope.ScopeOps Key Any H HS S TypeRep ScopeError
  stream : JuliaLean.base.show.IOPrims (M JuliaLean.base.show.ShowError World) Io V
  printScopeType : JuliaLean.base.show.JIO Io V → M JuliaLean.base.show.ShowError World Unit
  isScopedValue : Key → Bool
  typeOfKey : Key → TypeRep
  elementType : Key → TypeRep
  scopedValueType : TypeRep → TypeRep
  printType : JuliaLean.base.show.JIO Io V → TypeRep → M JuliaLean.base.show.ShowError World Unit
  objectId : Key → JInt .u64
  showObjectId : JuliaLean.base.show.JIO Io V → JInt .u64 →
    M JuliaLean.base.show.ShowError World Unit
  showValueWithTypeInfo : JuliaLean.base.show.JIO Io V → TypeRep → Any →
    M JuliaLean.base.show.ShowError World Unit

def showScopeLoop {Key Any H HS S TypeRep ScopeError World Io V : Type}
    (ops : ScopeDisplayOps Key Any H HS S TypeRep ScopeError World Io V)
    (io : JuliaLean.base.show.JIO Io V) (scope : JuliaLean.base.scope.Scope Key Any H) :
    M JuliaLean.base.show.ShowError World Unit :=
  whileLoop (fun state : Option S × Bool => do
    match ops.scopeOps.persistent.iterate scope.values.trie state.1 with
    | none => pure (.inl ())
    | some ((key, value), next) => do
        if state.2 then pure () else JuliaLean.base.show.printStr ops.stream io ", "
        let printedType :=
          if ops.isScopedValue key then ops.scopedValueType (ops.elementType key)
          else ops.typeOfKey key
        JuliaLean.base.show.printAll ops.stream io [
          ops.printType io printedType,
          JuliaLean.base.show.printStr ops.stream io "@"
        ]
        ops.showObjectId io (ops.objectId key)
        JuliaLean.base.show.printStr ops.stream io " => "
        ops.showValueWithTypeInfo io (ops.elementType key) value
        pure (.inr (some next, false))) (none, true)

/--
Julia source: base/scopedvalues.jl:126-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, scope::Scope)
    print(io, Scope, "(")
    first = true
    for (key, value) in scope.values
        if first
            first = false
        else
            print(io, ", ")
        end
        print(io, isa(key, ScopedValue) ? ScopedValue{eltype(key)} : typeof(key), "@")
        show(io, Base.objectid(key))
        print(io, " => ")
        show(IOContext(io, :typeinfo => eltype(key)), value)
    end
    print(io, ")")
end
```
-/
def showScope {Key Any H HS S TypeRep ScopeError World Io V : Type}
    (ops : ScopeDisplayOps Key Any H HS S TypeRep ScopeError World Io V)
    (io : JuliaLean.base.show.JIO Io V) (scope : JuliaLean.base.scope.Scope Key Any H) :
    M JuliaLean.base.show.ShowError World Unit := do
  JuliaLean.base.show.printAll ops.stream io [
    ops.printScopeType io,
    JuliaLean.base.show.printStr ops.stream io "("
  ]
  showScopeLoop ops io scope
  JuliaLean.base.show.printStr ops.stream io ")"
/-- `convert`, typed dictionary retrieval, and `KeyError` construction for a scoped value. -/
structure ScopedValueAccessOps (Key Any H HS S TypeRep Error T : Type) where
  scopeOps : JuliaLean.base.scope.ScopeOps Key Any H HS S TypeRep Error
  castAny : Any → Except Error T
  toAny : T → Any
  keyError : Key → Error

/--
Julia source: base/scopedvalues.jl:166-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(val::AbstractScopedValue{T}) where {T}
    scope = Core.current_scope()::Union{Scope, Nothing}
    if scope === nothing
        !hasdefault(val) && return nothing
        return Some{T}(getdefault(val))
    end
    scope = scope::Scope
    if hasdefault(val)
        return Some{T}(Base.get(Base.Fix1(getdefault, val), scope.values, val)::T)
    else
        v = Base.KeyValue.get(scope.values, val)
        v === nothing && return nothing
        return Some{T}(something(v)::T)
    end
end
```
-/
def get {Key Any H HS S TypeRep Error T : Type}
    (ops : ScopedValueAccessOps Key Any H HS S TypeRep Error T)
    (key : Key) (hasdefault : Bool) (getdefault : Unit → Except Error T)
    (currentScope : Unit → Option (JuliaLean.base.scope.Scope Key Any H)) :
    Except Error (Option T) := do
  match currentScope () with
  | none =>
      if hasdefault then pure (some (← getdefault ())) else pure none
  | some scope =>
      if hasdefault then
        match JuliaLean.base.dict.persistentKeyGet ops.scopeOps.persistent scope.values key with
        | some value => pure (some (← ops.castAny value))
        | none => pure (some (← getdefault ()))
      else
        match JuliaLean.base.dict.persistentKeyGet ops.scopeOps.persistent scope.values key with
        | none => pure none
        | some value => pure (some (← ops.castAny value))

/--
Julia source: base/scopedvalues.jl:182-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getindex(val::AbstractScopedValue{T})::T where T
    maybe = get(val)
    maybe === nothing && throw(KeyError(val))
    return something(maybe)::T
end
```
-/
def getindex {Key Any H HS S TypeRep Error T : Type}
    (ops : ScopedValueAccessOps Key Any H HS S TypeRep Error T)
    (key : Key) (hasdefault : Bool) (getdefault : Unit → Except Error T)
    (currentScope : Unit → Option (JuliaLean.base.scope.Scope Key Any H)) : Except Error T := do
  match ← get ops key hasdefault getdefault currentScope with
  | none => throw (ops.keyError key)
  | some value => pure value

/-- Display callbacks for the source `show(io, scopedValue)` method. -/
structure ScopedValueDisplayOps (Key Any TypeRep Error World Io V : Type) where
  stream : JuliaLean.base.show.IOPrims (M JuliaLean.base.show.ShowError World) Io V
  mapError : Error → JuliaLean.base.show.ShowError
  isScopedValue : Key → Bool
  typeOfKey : Key → TypeRep
  elementType : Key → TypeRep
  scopedValueType : TypeRep → TypeRep
  printScopedValueType : JuliaLean.base.show.JIO Io V →
    M JuliaLean.base.show.ShowError World Unit
  printType : JuliaLean.base.show.JIO Io V → TypeRep →
    M JuliaLean.base.show.ShowError World Unit
  printChar : JuliaLean.base.show.JIO Io V → Char →
    M JuliaLean.base.show.ShowError World Unit
  showValueWithTypeInfo : JuliaLean.base.show.JIO Io V → TypeRep → Any →
    M JuliaLean.base.show.ShowError World Unit

/--
Julia source: base/scopedvalues.jl:188-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, val::AbstractScopedValue)
    if isa(val, ScopedValue)
        print(io, ScopedValue)
        print(io, '{', eltype(val), '}')
    else
        print(io, typeof(val))
    end
    print(io, '(')
    v = get(val)
    if v !== nothing
        show(IOContext(io, :typeinfo => eltype(val)), something(v))
    end
    print(io, ')')
end
```
-/
def showAbstractScopedValue {Key Any H HS S TypeRep Error T World Io V : Type}
    (access : ScopedValueAccessOps Key Any H HS S TypeRep Error T)
    (display : ScopedValueDisplayOps Key Any TypeRep Error World Io V)
    (io : JuliaLean.base.show.JIO Io V) (key : Key) (hasdefault : Bool)
    (getdefault : Unit → Except Error T)
    (currentScope : Unit → Option (JuliaLean.base.scope.Scope Key Any H)) :
    M JuliaLean.base.show.ShowError World Unit := do
  if display.isScopedValue key then
    display.printScopedValueType io
    JuliaLean.base.show.printAll display.stream io [
      display.printChar io '{',
      display.printType io (display.elementType key),
      display.printChar io '}'
    ]
  else
    display.printType io (display.typeOfKey key)
  display.printChar io '('
  let value ← liftExceptMap display.mapError (get access key hasdefault getdefault currentScope)
  match value with
  | none => pure ()
  | some value =>
      display.showValueWithTypeInfo io (display.elementType key) (access.toAny value)
  display.printChar io ')'

-- UNTRANSLATED
-- Source: base/scopedvalues.jl:231-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro with(exprs...)
--     if length(exprs) > 1
--         ex = last(exprs)
--         exprs = exprs[1:end-1]
--     elseif length(exprs) == 1
--         ex = only(exprs)
--         exprs = ()
--     else
--         error("@with expects at least one argument")
--     end
--     exprs = map(esc, exprs)
--     Expr(:tryfinally, esc(ex), nothing, :(Scope(Core.current_scope()::Union{Nothing, Scope}, $(exprs...))))
-- end
-- /Source
-- Reason: This macro constructs and escapes Julia AST nodes at compile time rather than evaluating a typed runtime method.

/--
Julia source: base/scopedvalues.jl:285-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function with(f, pair::Pair{<:AbstractScopedValue}, rest::Pair{<:AbstractScopedValue}...)
    @with(pair, rest..., f())
end
```
-/
def withPairs {Key Any H HS S TypeRep Error A : Type}
    (ops : JuliaLean.base.scope.ScopeOps Key Any H HS S TypeRep Error)
    (currentScope : Unit → Option (JuliaLean.base.scope.Scope Key Any H))
    (runInScope : Option (JuliaLean.base.scope.Scope Key Any H) →
      (Unit → Except Error A) → Except Error A)
    (first : Key × Any) (rest : List (Key × Any)) (f : Unit → Except Error A) :
    Option (Except Error A) :=
  match JuliaLean.base.scope.scopeWithPairs ops (currentScope ()) first rest with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok child) => some (runInScope (some child) f)

/--
Julia source: base/scopedvalues.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
with(@nospecialize(f)) = f()
```
-/
def withNoPairs {Error A : Type} (f : Unit → Except Error A) : Except Error A := f ()

-- UNTRANSLATED
-- Source: base/scopedvalues.jl:290-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro enter_scope(scope, expr)
--     Expr(:tryfinally, esc(expr), nothing, :(Scope($(esc(scope))::Union{Nothing, Scope})))
-- end
-- /Source
-- Reason: This macro emits a Julia try/finally AST to restore Core.current_scope after the expression.

/--
Julia source: base/scopedvalues.jl:301-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ScopedThunk{F}
    f::F
    scope::Union{Nothing, Scope}

    ScopedThunk{F}(f) where {F} = new{F}(f, Core.current_scope())
end
```
-/
structure ScopedThunkModel (F Key Any H : Type) where
  f : F
  scope : Option (JuliaLean.base.scope.Scope Key Any H)

/--
Julia source: base/scopedvalues.jl:305-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ScopedThunk{F}(f) where {F} = new{F}(f, Core.current_scope())
```
-/
def scopedThunkCapture {F Key Any H : Type} (currentScope : Unit →
    Option (JuliaLean.base.scope.Scope Key Any H)) (f : F) : ScopedThunkModel F Key Any H :=
  ⟨f, currentScope ()⟩

/--
Julia source: base/scopedvalues.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ScopedThunk(f) = ScopedThunk{typeof(f)}(f)
```
-/
def scopedThunk {F Key Any H : Type} (currentScope : Unit →
    Option (JuliaLean.base.scope.Scope Key Any H)) (f : F) : ScopedThunkModel F Key Any H :=
  scopedThunkCapture currentScope f

/--
Julia source: base/scopedvalues.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(sf::ScopedThunk)() = @enter_scope sf.scope sf.f()
```
-/
def callScopedThunk {F Key Any H Error A : Type}
    (runInScope : Option (JuliaLean.base.scope.Scope Key Any H) →
      (Unit → Except Error A) → Except Error A)
    (invoke : F → Except Error A) (thunk : ScopedThunkModel F Key Any H) : Except Error A :=
  runInScope thunk.scope (fun _ => invoke thunk.f)

end JuliaLean.base.scopedvalues

namespace JuliaLean.Tasks



abbrev Scope := Nat → Option Int
abbrev Bindings := List (Nat × Int)
/-- One `Scope(parent, bindings...)`, `base/scopedvalues.jl:231-243`.
The first binding for a key wins, matching the constructed scope storage. -/
def enterScope (parent : Scope) (bindings : Bindings) : Scope := fun key =>
  match bindings.find? (fun binding => binding.1 == key) with
  | some binding => some binding.2
  | none => parent key
/-- `@with` installs the child scope only while evaluating the body. The
runtime's `tryfinally` scope operand restores `parent` for both outcomes. -/
def withScope (parent : Scope) (bindings : Bindings)
    (body : Scope → Except Nat Nat) :
    Except Nat Nat × Scope :=
  (body (enterScope parent bindings), parent)
/-- A new task captures `Core.current_scope()` at construction. -/
def createTaskScope (current : Scope) : Scope := current

end JuliaLean.Tasks

namespace JuliaLean.Tasks



/-! ## base/scopedvalues.jl:79-201, defaults, lookup, and display decisions -/

structure ScopedCell where
  hasDefault : Bool
  defaultValue : Int := 0
  deriving Repr, DecidableEq

def scopedDefault (cell : ScopedCell) : Option Int :=
  if cell.hasDefault then some cell.defaultValue else none

def scopedGet (scope : Scope) (cell : ScopedCell) (key : Nat) : Option Int :=
  match scope key with
  | some value => some value
  | none => scopedDefault cell

def scopedAssigned (scope : Scope) (cell : ScopedCell) (key : Nat) : Bool :=
  cell.hasDefault || (scope key).isSome

/-! ## base/scopedvalues.jl:231-308, dynamic scope and ScopedThunk -/

structure CoverageScopedThunk where
  captured : Scope
  result : Nat

def scopedThunkCall (thunk : CoverageScopedThunk) : Nat × Scope :=
  (thunk.result, thunk.captured)

end JuliaLean.Tasks
