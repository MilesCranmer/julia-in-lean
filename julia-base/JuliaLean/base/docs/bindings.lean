import JuliaLean.base.meta
import JuliaLean.Core
import JuliaLean.base.expr


section

/-!
# `base/docs/core.jl`, `base/docs/utils.jl`, `base/docs/bindings.jl`, `base/docs/basedocs.jl`

Models of the bootstrap docsystem (`Core.CoreDocs`), the `HTML`/`Text` wrappers,
`Docs.Binding` and the `kw"..."` keyword literal, master `bbfa0ce4150`.
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `base/docs/bindings.jl` -/

/-- The module system as `Binding` sees it. Modules are named by strings. -/
structure ModEnv where
  /-- `nameof(m)`. -/
  nameof : String → String
  /-- `parentmodule(m)`. -/
  parent : String → String
  /-- `isdefinedglobal(m, v)` in the current world. -/
  isdefined : String → String → Bool
  /-- The target of an explicit by-name import binding `(m, v)`, if it is one:
  `partition_restriction(bpart).globalref`. -/
  imported : String → String → Option (String × String)
  /-- `Base.binding_module(m, v)`. -/
  bindingModule : String → String → String
  /-- `getglobal(m, v)`. -/
  value : String → String → JV
  /-- `Base.active_module()`. -/
  active : String

/-- `Docs.Binding`: a module and a variable name. -/
structure Binding where
  mod : String
  var : String
  deriving Repr, DecidableEq

/-- The import-following loop of `Binding(m, v)`, `base/docs/bindings.jl:16-23`. -/
def bindingLoop (env : ModEnv) : Nat → String → String → String × String
  | 0, m, v => (m, v)
  | n + 1, m, v =>
    if env.isdefined m v then
      match env.imported m v with
      | none => (m, v)
      | some (m', v') => if m' == m && v' == v then (m, v) else bindingLoop env n m' v'
    else (m, v)

/-- `Binding(m, v)`, `base/docs/bindings.jl:7-25`; `fuel` bounds the import chain. -/
def mkBinding (env : ModEnv) (fuel : Nat) (m v : String) : Binding :=
  let m := if env.nameof m == v then env.parent m else m
  let (m, v) := bindingLoop env fuel m v
  ⟨env.bindingModule m v, v⟩

/-- The function object `Docs.Binding` inside generated expressions. -/
def bindingFn : JV := .val "Base.Docs.Binding"

/-- `:($Base.@__MODULE__)`: a macro call of `Base.@__MODULE__`. -/
def atModuleExpr : JV :=
  .expr "macrocall" [.expr "." [.val "Base", .qn (.sym "@__MODULE__")], .lnn 0 ""]

/-- `splitexpr(x)` for all four methods, `base/docs/bindings.jl:33-38`. -/
def splitexpr (x : JV) : DJ (JV × JV) :=
  match x with
  | .expr h as =>
    if h == "." then
      match as with
      | a :: b :: _ => pure (a, b)
      | _ => .error .boundsError
    else .error (DErr.errorException "Could not find something to document")
  | .sym s => pure (atModuleExpr, quot (.sym s))
  | .gref m n => pure (.val m, quot (.sym n))
  | _ => .error (DErr.errorException "Could not find something to document")

/-- `bindingexpr(x) = Expr(:call, Binding, splitexpr(x)...)`, `base/docs/bindings.jl:28`. -/
def bindingexpr (x : JV) : DJ JV := do
  let (a, b) ← splitexpr x
  pure (.expr "call" [bindingFn, a, b])

/-- `defined(b)`, `base/docs/bindings.jl:30`. -/
def defined (env : ModEnv) (b : Binding) : Bool := env.isdefined b.mod b.var

/-- `resolve(b)`, `base/docs/bindings.jl:31`. -/
def resolve (env : ModEnv) (b : Binding) : DJ JV :=
  if env.isdefined b.mod b.var then pure (env.value b.mod b.var)
  else .error (.undefVarError b.var)

/-- `show(io, b::Binding)`, `base/docs/bindings.jl:40-53`. `isoperator` is
`Base.isoperator` and `showSym` is `show(io, ::Symbol)`. -/
def showBinding (env : ModEnv) (isoperator : String → Bool) (showSym : String → String)
    (b : Binding) : String :=
  if b.mod == env.active then b.var
  else b.mod ++ "." ++ (if isoperator b.var then showSym b.var else b.var)

/-- What `aliasof` dispatches on: a resolved value's type. -/
inductive ValKind where
  | dataType (parent name : String)
  | function (parent name : String)
  | module (name : String)
  | other

/-- `aliasof(d::DataType, b)`, `aliasof(λ::Function, b)`, `aliasof(m::Module, b)` and
`aliasof(other, b)`, `base/docs/bindings.jl:56-59`. -/
def aliasofVal (env : ModEnv) (fuel : Nat) (k : ValKind) (b : Binding) : Binding :=
  match k with
  | .dataType p n => mkBinding env fuel p n
  | .function p n => mkBinding env fuel p n
  | .module m => mkBinding env fuel m (env.nameof m)
  | .other => b

/-- `aliasof(b::Binding)`, `base/docs/bindings.jl:55`. `kind` classifies `resolve(b)`. -/
def aliasof (env : ModEnv) (fuel : Nat) (kind : JV → ValKind) (b : Binding) : Binding :=
  if defined env b then
    let a := aliasofVal env fuel (kind (env.value b.mod b.var)) b
    if defined env a then a else b
  else b

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/docs/bindings.jl`

Typed model of `Base.Docs.Binding` and its helpers at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Each modelled method is a Lean definition whose
docstring carries the method's verbatim source; its body follows the Julia body call by call.

* Modules, world ages, binding partitions and binding kinds are type parameters. The runtime's
  binding tables (`isdefinedglobal`, `getglobal`, `lookup_binding_partition`, `binding_module`)
  are the callees of `BindingOps`; methods run in a monad `m` with the `BindingError` exceptions.
* Expressions are the `Value L` ASTs of the `base/expr.jl` model.
-/

namespace JuliaLean.base.docs.bindings
open JuliaLean
open JuliaLean.base.expr (Value LeafOps isexpr)

abbrev Sym := String

/-- Exceptions thrown by the modelled methods. -/
inductive BindingError where
  /-- `error(msg)`: an `ErrorException`. -/
  | errorException (msg : String)
  | boundsError
  /-- A failed type assertion `x::T`. -/
  | typeError
  deriving Repr, DecidableEq

-- UNTRANSLATED
-- license header; no method
-- Source: base/docs/bindings.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /Source

/--
Julia source: base/docs/bindings.jl:3-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Binding
    mod::Module
    var::Symbol

    function Binding(m::Module, v::Symbol)
        # Normalise the binding module for module symbols so that:
        #   Binding(Base, :Base) === Binding(Main, :Base)
        m = nameof(m) === v ? parentmodule(m) : m
        # Walk every explicit by-name import to recover the canonical `(mod, name)` pair,
        # threading `as`-renames through chained re-exports.
        # `partition_restriction` only walks one hop; `binding_module` walks all hops
        # but drops the name.
        world = Base.get_world_counter()
        while Base.invoke_in_world(world, isdefinedglobal, m, v)
            bpart = Base.lookup_binding_partition(world, GlobalRef(m, v))
            Base.is_some_explicit_imported(Base.binding_kind(bpart)) || break
            imported = Base.partition_restriction(bpart)::Core.Binding
            next_m, next_v = imported.globalref.mod, imported.globalref.name
            (next_m === m && next_v === v) && break
            m, v = next_m, next_v
        end
        new(Base.binding_module(m, v), v)
    end
end

```
-/
/- A `Binding`: a module and a variable name. -/
structure Binding (Mod : Type) where
  mod : Mod
  var : Sym

/-- The world's binding tables over a monad `n`: modules `Mod`, world ages `W`, binding
partitions `BP`, binding kinds `K` and objects `Obj`. -/
structure BindingOps (n : Type → Type) (Mod W BP K Obj : Type) where
  /-- `nameof(m::Module)`, `parentmodule(m::Module)`, `===` on modules. -/
  nameof : Mod → Sym
  parentmodule : Mod → Mod
  egalMod : Mod → Mod → Bool
  /-- `Base.get_world_counter()`. -/
  get_world_counter : n W
  /-- `Base.invoke_in_world(world, isdefinedglobal, m, v)`. -/
  isdefinedglobal_in_world : W → Mod → Sym → n Bool
  /-- `Base.lookup_binding_partition(world, GlobalRef(m, v))`, `Base.binding_kind(bpart)`,
  `Base.is_some_explicit_imported(kind)`. -/
  lookup_binding_partition : W → Mod → Sym → n BP
  binding_kind : BP → K
  is_some_explicit_imported : K → Bool
  /-- `Base.partition_restriction(bpart)` when it is a `Core.Binding`: its
  `globalref.mod` and `globalref.name`; `none` for another value. -/
  partition_restriction : BP → n (Option (Mod × Sym))
  /-- `Base.binding_module(m, v)`. -/
  binding_module : Mod → Sym → n Mod
  /-- `invokelatest(isdefinedglobal, m, v)` and `invokelatest(getglobal, m, v)`. -/
  isdefinedglobal : Mod → Sym → n Bool
  getglobal : Mod → Sym → n Obj

section
variable {m : Type → Type} [Monad m] [MonadExceptOf BindingError m] {Mod W BP K Obj : Type}

def throwB {α : Type} (e : BindingError) : m α := throwThe BindingError e

/-- The `while` loop of the inner constructor: follow explicit by-name imports. -/
def binding_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BindingOps m Mod W BP K Obj)
    (world : W) (md : Mod) (v : Sym) : m (Mod × Sym) := do
  if ← o.isdefinedglobal_in_world world md v then
    let bpart ← o.lookup_binding_partition world md v
    if !o.is_some_explicit_imported (o.binding_kind bpart) then return (md, v)
    let some (next_m, next_v) ← o.partition_restriction bpart | throwB .typeError
    if o.egalMod next_m md && next_v == v then return (md, v)
    binding_loop o world next_m next_v
  else return (md, v)
partial_fixpoint

/-- `Binding(m, v)`. -/
def mkBinding [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BindingOps m Mod W BP K Obj)
    (md : Mod) (v : Sym) : m (Binding Mod) := do
  -- Normalise the binding module for module symbols so that:
  --   Binding(Base, :Base) === Binding(Main, :Base)
  let md := if o.nameof md == v then o.parentmodule md else md
  let world ← o.get_world_counter
  let (md, v) ← binding_loop o world md v
  return ⟨← o.binding_module md v, v⟩

/--
Julia source: base/docs/bindings.jl:30-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defined(b::Binding) = invokelatest(isdefinedglobal, b.mod, b.var)
resolve(b::Binding) = invokelatest(getglobal, b.mod, b.var)

```
-/
/- `defined(b::Binding)`. -/
def defined (o : BindingOps m Mod W BP K Obj) (b : Binding Mod) : m Bool := o.isdefinedglobal b.mod b.var

/-- `resolve(b::Binding)`. -/
def resolve (o : BindingOps m Mod W BP K Obj) (b : Binding Mod) : m Obj := o.getglobal b.mod b.var

end

/--
Julia source: base/docs/bindings.jl:33-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splitexpr(x::Expr)
    isexpr(x, :.) ? (x.args[1], x.args[2]) : error("Could not find something to document in `$x`.")
end
splitexpr(s::Symbol) = :($Base.@__MODULE__), quot(s) # this somewhat complex form allows deferring resolving the Module for module docstring until after the module is created
splitexpr(r::GlobalRef) = r.mod, quot(r.name)
splitexpr(other)     = error("Could not find something to document in `$other`.")

```
-/
/- `splitexpr(x)`: the module and quoted name expressions. `str` is the string interpolation
`"$x"`, and `lineNode` the `LineNumberNode` of the quoted macro call at `bindings.jl:36`. -/
def splitexpr {L : Type} (lo : LeafOps L) (str : Value L → String) (lineNode : Value L) :
    Value L → Except BindingError (Value L × Value L)
  | .expr h args =>
    if h == "." then
      match args with
      | a1 :: a2 :: _ => .ok (a1, a2)
      | _ => .error .boundsError
    else .error (.errorException ("Could not find something to document in `" ++ str (.expr h args) ++ "`."))
  -- `:($Base.@__MODULE__)`, `quot(s)`
  | .symbol s => .ok (.expr "macrocall" [.expr "." [.leaf lo.base, .quoteNode (.symbol "@__MODULE__")], lineNode],
      .quoteNode (.symbol s))
  | .globalRef md name => .ok (.leaf md, .quoteNode (.symbol name))
  | other => .error (.errorException ("Could not find something to document in `" ++ str other ++ "`."))

/--
Julia source: base/docs/bindings.jl:28-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bindingexpr(x) = Expr(:call, Binding, splitexpr(x)...)

```
-/
/- `bindingexpr(x) = Expr(:call, Binding, splitexpr(x)...)`; `bindingType` is the `Binding` type
object. -/
def bindingexpr {L : Type} (lo : LeafOps L) (str : Value L → String) (lineNode : Value L) (bindingType : L)
    (x : Value L) : Except BindingError (Value L) := do
  let (a, b) ← splitexpr lo str lineNode x
  return .expr "call" [.leaf bindingType, a, b]

section
variable {m : Type → Type} [Monad m] [MonadExceptOf BindingError m] {Mod W BP K Obj : Type}

/--
Julia source: base/docs/bindings.jl:40-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, b::Binding)
    if b.mod === Base.active_module()
        print(io, b.var)
    else
        print(io, b.mod, '.')
        if Base.isoperator(b.var)
            # ensures symbols are quoted right, so e.g.  :(==), :(:), :+ or :-
            show(io, b.var)
        else
            # print ordinary identifiers without any quoting
            print(io, b.var)
        end
    end
end

```
-/
/- Printing callees of `show(io, b::Binding)` over a stream `Io`. -/
structure ShowOps (n : Type → Type) (Io Mod : Type) where
  active_module : n Mod
  /-- `print(io, s::Symbol)`, `print(io, m::Module, '.')`, `show(io, s::Symbol)`. -/
  printSym : Io → Sym → n Unit
  printModuleDot : Io → Mod → n Unit
  showSym : Io → Sym → n Unit
  /-- `Base.isoperator(s)`. -/
  isoperator : Sym → Bool

def show_Binding {Io : Type} (o : BindingOps m Mod W BP K Obj) (s : ShowOps m Io Mod) (io : Io)
    (b : Binding Mod) : m Unit := do
  if o.egalMod b.mod (← s.active_module) then
    s.printSym io b.var
  else
    s.printModuleDot io b.mod
    if s.isoperator b.var then
      -- ensures symbols are quoted right, so e.g.  :(==), :(:), :+ or :-
      s.showSym io b.var
    else
      -- print ordinary identifiers without any quoting
      s.printSym io b.var

/--
Julia source: base/docs/bindings.jl:55-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
aliasof(b::Binding)     = defined(b) ? (a = aliasof(resolve(b), b); defined(a) ? a : b) : b
aliasof(d::DataType, b) = Binding(parentmodule(d), nameof(d))
aliasof(λ::Function, b) = Binding(parentmodule(λ), nameof(λ))
aliasof(m::Module,   b) = Binding(m, nameof(m))
aliasof(other,       b) = b
```
-/
/- The object kinds `aliasof(x, b)` dispatches on, with `parentmodule(x)` and `nameof(x)` of a
`DataType` or `Function`. -/
inductive ObjKind (Mod : Type) where
  | dataType (parent : Mod) (name : Sym)
  | function (parent : Mod) (name : Sym)
  | module (md : Mod)
  | other

/-- `aliasof(x, b)` for a non-`Binding` `x`. -/
def aliasof_obj [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BindingOps m Mod W BP K Obj)
    (kind : ObjKind Mod) (b : Binding Mod) : m (Binding Mod) :=
  match kind with
  | .dataType p n => mkBinding o p n
  | .function p n => mkBinding o p n
  | .module md => mkBinding o md (o.nameof md)
  | .other => pure b

/-- `aliasof(b::Binding)`; `objKind` classifies the resolved object. -/
def aliasof [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BindingOps m Mod W BP K Obj)
    (objKind : Obj → ObjKind Mod) (b : Binding Mod) : m (Binding Mod) := do
  if ← defined o b then
    let a ← aliasof_obj o (objKind (← resolve o b)) b
    if ← defined o a then return a else return b
  else return b

end

end JuliaLean.base.docs.bindings
