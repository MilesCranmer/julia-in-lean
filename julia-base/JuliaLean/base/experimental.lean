import JuliaLean.Core
import JuliaLean.base.channels
import JuliaLean.base.condition
import JuliaLean.base.park
import JuliaLean.base.opaque_closure
import JuliaLean.base.checked
import JuliaLean.base.libuv
import JuliaLean.base.expr

/-!
# Model of `base/experimental.jl`

Typed models for the executable helpers in Julia's experimental Base API at
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Array storage, exception-hint registries, compiler
state, task clocks, native caches, and runtime effects are explicit interfaces. Compiler AST
rewrites construct `base.expr.Value` trees with their quoted source positions. Scheduler
arbitration remains an explicit runtime interface.
-/

namespace JuliaLean.base.experimental

open JuliaLean
open JuliaLean.base.expr

-- Source: base/experimental.jl:1-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     Experimental
-- 
-- !!! warning
--     Types, methods, or macros defined in this module are experimental and subject
--     to change and will not have deprecations. Caveat emptor.
-- """
-- module Experimental
-- 
-- using Base: Threads, ScopedValues, sync_varname, is_function_def
-- using Base: GenericCondition
-- using Base.Meta
-- /Source
-- Reason: The Lean namespace and imports represent the Julia module declaration.
/--
Julia source: base/experimental.jl:17-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Const(A::Array)

Mark an Array as constant/read-only. The invariant guaranteed is that you will not
modify an Array (through another reference) within an `@aliasscope` scope.

!!! warning
    Experimental API. Subject to change without deprecation.
"""
struct Const{T,N} <: DenseArray{T,N}
    a::Array{T,N}
end
```
-/
structure Const (Element : Type) (Rank : Nat) (Array : Type) where
  a : Array

inductive IndexStyle where
  | linear

/--
Julia source: base/experimental.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.IndexStyle(::Type{<:Const}) = IndexLinear()
```
-/
def constIndexStyle : IndexStyle := .linear

/--
Julia source: base/experimental.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.size(C::Const) = size(C.a)
```
-/
def constSize {Element : Type} {Rank : Nat} {Array Size : Type}
    (size : Array → Size) (array : Const Element Rank Array) : Size :=
  size array.a

/--
Julia source: base/experimental.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.axes(C::Const) = axes(C.a)
```
-/
def constAxes {Element : Type} {Rank : Nat} {Array Axes : Type}
    (axes : Array → Axes) (array : Const Element Rank Array) : Axes :=
  axes array.a

structure ConstArrayOps (Array Ref Value Size Axes Error : Type) where
  size : Array → Size
  axes : Array → Axes
  checkBoundsOne : Array → JInt .i64 → Except Error Unit
  memoryRefNew : Array → JInt .i64 → Ref
  constMemoryRefGet : Ref → Except Error Value
  checkBoundsMany : Array → List (JInt .i64) → Except Error Unit
  toLinearIndex : Array → List (JInt .i64) → Except Error (JInt .i64)
  /-- The dynamically dispatched `@inbounds getindex(Const(array), index)`. -/
  getLinearIndex : Array → JInt .i64 → Except Error Value

/--
Julia source: base/experimental.jl:32-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :noub_if_noinbounds function Base.getindex(A::Const, i::Int)
    @inline
    @boundscheck Base.checkbounds(A.a, i)
    return Core.const_memoryrefget(Core.memoryrefnew(getfield(A.a, :ref), i, false), :not_atomic, false)
end
```
-/
def constGetIndex {Element : Type} {Rank : Nat} {Array Ref Value Size Axes Error : Type}
    (ops : ConstArrayOps Array Ref Value Size Axes Error)
    (array : Const Element Rank Array) (index : JInt .i64) : Except Error Value := do
  ops.checkBoundsOne array.a index
  let reference := ops.memoryRefNew array.a index
  ops.constMemoryRefGet reference

/--
Julia source: base/experimental.jl:37-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getindex(A::Const, i1::Int, i2::Int, I::Int...)
    @inline
    @boundscheck Base.checkbounds(A.a, i1, i2, I...) # generally _to_linear_index requires bounds checking
    return @inbounds A[Base._to_linear_index(A.a, i1, i2, I...)]
end
```
-/
def constGetIndexManyNative {Element : Type} {Rank : Nat} {Array Ref Value Size Axes Error : Type}
    (ops : ConstArrayOps Array Ref Value Size Axes Error)
    (array : Const Element Rank Array) (i1 i2 : JInt .i64)
    (rest : List (JInt .i64)) : Except Error Value := do
  let indices := i1 :: i2 :: rest
  ops.checkBoundsMany array.a indices
  let linearIndex ← ops.toLinearIndex array.a indices
  ops.getLinearIndex array.a linearIndex

def constGetIndexMany {Element : Type} {Rank : Nat} {Array Ref Value Size Axes Error : Type}
    (ops : ConstArrayOps Array Ref Value Size Axes Error)
    (array : Const Element Rank Array) (i1 i2 : JInt .i64) (rest : List (JInt .i64)) : Except Error Value :=
  constGetIndexManyNative ops array i1 i2 rest

-- Source: base/experimental.jl:43-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @aliasscope expr
-- 
-- Allow the compiler to assume that all `Const`s are not being modified through stores
-- within this scope, even if the compiler can't prove this to be the case.
-- 
-- !!! warning
--     Experimental API. Subject to change without deprecation.
-- """
-- macro aliasscope(body)
--     sym = :aliasscope_result
--     quote
--         $(Expr(:aliasscope))
--         $sym = $(esc(body))
--         $(Expr(:popaliasscope))
--         $sym
--     end
-- end
-- /Source
inductive SyncEndEvent (Event : Type) where
  | completion
  | waitOn (event : Event)

structure SyncEndOps (E W C Cond Lock Task Waiter Token Event Source Request Ref Pool : Type) where
  channel : JuliaLean.base.channels.Runtime E W C Cond Lock Task Waiter Token (SyncEndEvent Event)
  tasks : JuliaLean.base.channels.TaskRuntime (E := E) (Task := Task) (W := W) Ref Pool
  waitEvent : Event → JuliaLean.base.io.CancelArg Token →
    JuliaLean.base.channels.M E Task W Unit
  cancellationRequest : JuliaLean.base.channels.Error E Task → Option Request
  cancelSource : Source → JuliaLean.base.channels.M E Task W Unit
  cancelSourceWith : Source → Request → JuliaLean.base.channels.M E Task W Unit
  isException : JuliaLean.base.channels.Error E Task → Bool
  errorException : String → JuliaLean.base.channels.Error E Task
  closeException : C → JuliaLean.base.channels.Error E Task → JuliaLean.base.channels.M E Task W Unit
/-- Julia source: base/experimental.jl:63-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sync_end(c::Channel{Any}, src::Union{Nothing, Base.CancellationTokenSource}=nothing)
    if !isready(c)
        # there must be at least one item to begin with
        close(c)
        return
    end
    nremaining::Int = 0
    try
        while true
            event = take!(c)
            if event === :__completion__
                nremaining -= 1
                if nremaining == 0
                    break
                end
            else
                nremaining += 1
                # The watcher must survive cancellation of the enclosing
                # scope to deliver the completion (the `cancel` keyword is
                # part of the waitable interface).
                schedule(Task(()->begin
                    try
                        wait(event; cancel = nothing)
                        put!(c, :__completion__; cancel = nothing)
                    catch e
                        close(c, e)
                    end
                end))
            end
        end
    catch e
        # Per this macro's contract the exception (a child failure delivered
        # via `close(c, e)`, or a cancellation of this block's scope) is
        # rethrown immediately - we do not wait for the children to finish
        # dying, but we cancel the block's own source so that all children
        # observe the cancellation through the token tree.
        if src !== nothing
            e isa Base.CancellationRequest ? Base.cancel!(src, e) : Base.cancel!(src)
        end
        close(c, e isa Exception ? e : ErrorException("sync_end interrupted"))
        rethrow()
    end
    close(c)
    nothing
end
```
-/
def syncEnd
    {E W C Cond Lock Task Waiter Token Event Source Request Ref Pool : Type}
    (ops : SyncEndOps E W C Cond Lock Task Waiter Token Event Source Request Ref Pool)
    (channel : C) (source : Option Source := none) :
    JuliaLean.base.channels.M E Task W Unit := do
  if !(← JuliaLean.base.channels.isready ops.channel channel) then
    JuliaLean.base.channels.closeDefault ops.channel channel
    return
  let loop := JuliaLean.base.channels.loop (fun remaining => do
    let event ← JuliaLean.base.channels.take ops.channel channel
    match event with
    | .completion =>
      let remaining := JInt.wrap .i64 (remaining.val - 1)
      if remaining.val == 0 then
        pure (.inl ())
      else
        pure (.inr remaining)
    | .waitOn event => do
      let worker ← ops.tasks.newTask (fun _ => do
        tryCatch (do
          let _ ← ops.waitEvent event (.explicit none)
          let _ ← JuliaLean.base.channels.put ops.channel
            (fun value => pure value) channel .completion (.explicit none)
          pure ())
          (fun error => ops.closeException channel error))
      ops.tasks.schedule worker
      pure (.inr (JInt.wrap .i64 (remaining.val + 1)))) (JInt.lit .i64 0)
  let _ ← tryCatch loop (fun error => do
    match source with
    | none => pure ()
    | some source =>
      match ops.cancellationRequest error with
      | some request => ops.cancelSourceWith source request
      | none => ops.cancelSource source
    let closeError :=
      if ops.isException error then error else ops.errorException "sync_end interrupted"
    ops.closeException channel closeError
    throw error)
  JuliaLean.base.channels.closeDefault ops.channel channel
  pure ()
-- Source: base/experimental.jl:109-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@sync
-- 
-- Wait until all lexically-enclosed uses of [`@async`](@ref), [`@spawn`](@ref Threads.@spawn),
-- `Distributed.@spawnat` and `Distributed.@distributed`
-- are complete, or at least one of them has errored. The first exception is immediately
-- rethrown; the block's cancellation scope is cancelled at the same time, so
-- still-running operations spawned within observe the failure through their
-- cancellation points rather than running unsupervised (they are not awaited).
-- 
-- !!! Note
--     This is different to [`@sync`](@ref) in that errors from wrapped tasks are thrown immediately,
--     potentially before all tasks have returned.
-- 
-- !!! Note
--     This interface is experimental and subject to change or removal without notice.
-- """
-- macro sync(block)
--     var = esc(sync_varname)
--     # like Base.@sync, the block runs in a new dynamic scope carrying the
--     # token of a fresh cancellation source; on the fail-fast path (and on
--     # cancellation from outside) the source is cancelled, reaching all
--     # children through the token tree without awaiting them
--     scoped_block = Expr(:tryfinally, esc(block), nothing,
--         :(Base.Scope(Core.current_scope()::Union{Nothing, Base.Scope},
--                      Base.CANCEL_TOKEN => Base.CancellationToken(var"#sync_src#"))))
--     quote
--         let var"#sync_src#" = Base.CancellationTokenSource(Base.default_cancel_token()),
--             $var = Channel(Inf)
--             v = $scoped_block
--             sync_end($var, var"#sync_src#")
--             v
--         end
--     end
-- end
-- /Source
-- Source: base/experimental.jl:145-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@optlevel n::Int
-- 
-- Set the optimization level (equivalent to the `-O` command line argument)
-- for code in the current module. Submodules inherit the setting of their
-- parent module.
-- 
-- Supported values are 0, 1, 2, and 3.
-- 
-- The effective optimization level is the minimum of that specified on the
-- command line and in per-module settings. If a `--min-optlevel` value is
-- set on the command line, that is enforced as a lower bound.
-- """
-- macro optlevel(n::Int)
--     return Expr(:meta, :optlevel, n)
-- end
-- /Source
-- Source: base/experimental.jl:162-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@max_methods n::Int
-- 
-- Set the maximum number of potentially-matching methods considered when running inference
-- for methods defined in the current module. This setting affects inference of calls with
-- incomplete knowledge of the argument types.
-- 
-- The benefit of this setting is to avoid excessive compilation and reduce invalidation risks
-- in poorly-inferred cases. For example, when `@max_methods 2` is set and there are two
-- potentially-matching methods returning different types inside a function body, then Julia
-- will compile subsequent calls for both types so that the compiled function body accounts
-- for both possibilities. Also the compiled code is vulnerable to invalidations that would
-- happen when either of the two methods gets invalidated. This speculative compilation and
-- these invalidations can be avoided by setting `@max_methods 1` and allowing the compiled
-- code to resort to runtime dispatch instead.
-- 
-- Supported values are `1`, `2`, `3`, `4`, and `default` (currently equivalent to `3`).
-- """
-- macro max_methods(n::Int)
--     1 <= n <= 4 || error("We must have that `1 <= max_methods <= 4`, but `max_methods = $n`.")
--     return Expr(:meta, :max_methods, n)
-- end
-- /Source
-- Source: base/experimental.jl:185-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@max_methods n::Int function fname end
-- 
-- Set the maximum number of potentially-matching methods considered when running inference
-- for the generic function `fname`. Overrides any module-level or global inference settings
-- for max_methods. This setting is global for the entire generic function (or more precisely
-- the MethodTable).
-- """
-- macro max_methods(n::Int, fdef::Expr)
--     1 <= n <= 255 || error("We must have that `1 <= max_methods <= 255`, but `max_methods = $n`.")
--     (fdef.head === :function && length(fdef.args) == 1) || error("Second argument must be a function forward declaration")
--     return :(typeof($(esc(fdef))).name.max_methods = $(UInt8(n)))
-- end
-- /Source
-- Source: base/experimental.jl:199-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@compiler_options optimize={0,1,2,3} compile={yes,no,all,min} infer={true,false} max_methods={default,1,2,3,4}
-- 
-- Set compiler options for code in the enclosing module. Options correspond directly to
-- command-line options with the same name, where applicable. The following options
-- are currently supported:
-- 
--   * `optimize`: Set optimization level.
--   * `compile`: Toggle native code compilation. Currently only `min` is supported, which
--     requests the minimum possible amount of compilation.
--   * `infer`: Enable or disable type inference. If disabled, implies [`@nospecialize`](@ref).
--   * `max_methods`: Maximum number of matching methods considered when running type inference.
-- """
-- macro compiler_options(args...)
--     opts = Expr(:block)
--     for ex in args
--         if isa(ex, Expr) && ex.head === :(=) && length(ex.args) == 2
--             if ex.args[1] === :optimize
--                 push!(opts.args, Expr(:meta, :optlevel, ex.args[2]::Int))
--             elseif ex.args[1] === :compile
--                 a = ex.args[2]
--                 a = #a === :no  ? 0 :
--                     #a === :yes ? 1 :
--                     #a === :all ? 2 :
--                     a === :min ? 3 : error("invalid argument to \"compile\" option")
--                 push!(opts.args, Expr(:meta, :compile, a))
--             elseif ex.args[1] === :infer
--                 a = ex.args[2]
--                 a = a === false || a === :no  ? 0 :
--                     a === true  || a === :yes ? 1 : error("invalid argument to \"infer\" option")
--                 push!(opts.args, Expr(:meta, :infer, a))
--             elseif ex.args[1] === :max_methods
--                 a = ex.args[2]
--                 a = a === :default ? 3 :
--                   a isa Int ? ((1 <= a <= 4) ? a : error("We must have that `1 <= max_methods <= 4`, but `max_methods = $a`.")) :
--                   error("invalid argument to \"max_methods\" option")
--                 push!(opts.args, Expr(:meta, :max_methods, a))
--             else
--                 error("unknown option \"$(ex.args[1])\"")
--             end
--         else
--             error("invalid option syntax")
--         end
--     end
--     return opts
-- end
-- /Source
-- Source: base/experimental.jl:246-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@force_compile
-- 
-- Force compilation of the block or function (Julia's built-in interpreter is blocked from executing it).
-- 
-- # Examples
-- 
-- ```
-- julia> occursin("interpreter", string(stacktrace(begin
--            # with forced compilation
--            Base.Experimental.@force_compile
--            backtrace()
--        end, true)))
-- false
-- 
-- julia> occursin("interpreter", string(stacktrace(begin
--            # without forced compilation
--            backtrace()
--        end, true)))
-- true
-- ```
-- """
-- macro force_compile() Expr(:meta, :force_compile) end
-- /Source
/--
Julia source: base/experimental.jl:270-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
# UI features for errors

"""
    Experimental.register_error_hint(handler, exceptiontype)

Register a "hinting" function `handler(io, exception)` that can
suggest potential ways for users to circumvent errors.  `handler`
should examine `exception` to see whether the conditions appropriate
for a hint are met, and if so generate output to `io`.
Packages should call `register_error_hint` from within their
`__init__` function.

For specific exception types, `handler` is required to accept additional arguments:

- `MethodError`: provide `handler(io, exc::MethodError, argtypes, kwargs)`,
  which splits the combined arguments into positional and keyword arguments.

When issuing a hint, the output should typically start with `\\n`.

If you define custom exception types, your `showerror` method can
support hints by calling [`Experimental.show_error_hints`](@ref).

# Examples

```
julia> module Hinter

       only_int(x::Int)      = 1
       any_number(x::Number) = 2

       function __init__()
           Base.Experimental.register_error_hint(MethodError) do io, exc, argtypes, kwargs
               if exc.f == only_int
                    # Color is not necessary, this is just to show it's possible.
                    print(io, "\\nDid you mean to call ")
                    printstyled(io, "`any_number`?", color=:cyan)
               end
           end
       end

       end
```

Then if you call `Hinter.only_int` on something that isn't an `Int` (thereby triggering a `MethodError`), it issues the hint:

```
julia> Hinter.only_int(1.0)
ERROR: MethodError: no method matching only_int(::Float64)
The function `only_int` exists, but no method is defined for this combination of argument types.
Did you mean to call `any_number`?
Closest candidates are:
    ...
```

!!! compat "Julia 1.5"
    Custom error hints are available as of Julia 1.5.
!!! warning
    This interface is experimental and subject to change or removal without notice.
    To insulate yourself against changes, consider putting any registrations inside an
    `if isdefined(Base.Experimental, :register_error_hint) ... end` block.
"""
function register_error_hint(@nospecialize(handler), @nospecialize(exct::Type))
    list = get!(Vector{Any}, _hint_handlers, Core.typename(exct))
    push!(list, (exct, handler))
    return nothing
end
````
-/
structure ErrorHintOps (m : Type → Type)
    (ExceptionType Handler IO Exception Argument : Type) where
  registerHint : ExceptionType → Handler → m Unit
  hintsDisabled : m Bool
  exceptionType : Exception → ExceptionType
  supertypesBeforeAny : ExceptionType → List ExceptionType
  isInstance : Exception → ExceptionType → Bool
  handlersFor : ExceptionType → m (List (ExceptionType × Handler))
  invokeLatest : Handler → IO → Exception → List Argument → m Unit
  handlerModule : Handler → String
  logHintFailure : Handler → ExceptionType → String → m Unit
  withHintsDisabled : m Unit → m Unit

structure ErrorHintRegistrationOps (m : Type → Type) (ExceptionType TypeName Handler ListRef : Type) where
  typename : ExceptionType → TypeName
  getOrInsertEmpty : TypeName → m ListRef
  pushPair : ListRef → ExceptionType → Handler → m Unit

/--
Julia source: base/experimental.jl:331-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function register_error_hint(@nospecialize(handler), @nospecialize(exct::Type))
    list = get!(Vector{Any}, _hint_handlers, Core.typename(exct))
    push!(list, (exct, handler))
    return nothing
end
```
-/
def registerErrorHintNative {m : Type → Type} [Monad m]
    {ExceptionType TypeName Handler ListRef : Type}
    (ops : ErrorHintRegistrationOps m ExceptionType TypeName Handler ListRef)
    (handler : Handler) (exceptionType : ExceptionType) : m Unit := do
  let list ← ops.getOrInsertEmpty (ops.typename exceptionType)
  ops.pushPair list exceptionType handler

def registerErrorHint {m : Type → Type} {ExceptionType Handler IO Exception Argument : Type}
    [Monad m] (ops : ErrorHintOps m ExceptionType Handler IO Exception Argument)
    (handler : Handler) (exceptionType : ExceptionType) : m Unit :=
  registerErrorHintNative {
    typename := id
    getOrInsertEmpty := pure
    pushPair := fun _ exct handler => ops.registerHint exct handler
  } handler exceptionType

/--
Julia source: base/experimental.jl:342-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Experimental.show_error_hints(io, ex, args...)

Invoke all handlers from [`Experimental.register_error_hint`](@ref) for the particular
exception type `typeof(ex)` and all of its supertypes. `args` must contain any other arguments expected by
the handler for that type.

!!! compat "Julia 1.5"
    Custom error hints are available as of Julia 1.5.
!!! warning
    This interface is experimental and subject to change or removal without notice.
"""
function show_error_hints(io, ex, args...)
    @nospecialize
    _hints_disabled[] && return
    ex_supertype = typeof(ex)
    while ex_supertype != Any
        hinters = get(_hint_handlers, Core.typename(ex_supertype), Any[])
        for (exct, handler) in hinters
            ex isa exct || continue
            try
                # TODO: deal with handlers accepting different signatures?
                @invokelatest handler(io, ex, args...)
            catch
                tn = typeof(handler).name
                ScopedValues.@with _hints_disabled => true begin
                    @error "Hint-handler $handler for $(ex_supertype) in $(tn.module) caused an error" exception=current_exceptions()
                end
            end
        end
        ex_supertype = supertype(ex_supertype)
    end
end
```
-/
def showErrorHints {m : Type → Type} {ExceptionType Handler IO Exception Argument : Type}
    [Monad m] [MonadExceptOf Exception m]
    (ops : ErrorHintOps m ExceptionType Handler IO Exception Argument)
    (io : IO) (exception : Exception) (args : List Argument) : m Unit := do
  if ← ops.hintsDisabled then
    pure ()
  else
    let concreteType := ops.exceptionType exception
    for supertype in ops.supertypesBeforeAny concreteType do
      let handlers ← ops.handlersFor supertype
      for (acceptedType, handler) in handlers do
        if ops.isInstance exception acceptedType then
          try
            ops.invokeLatest handler io exception args
          catch _ =>
            let moduleName := ops.handlerModule handler
            ops.withHintsDisabled (ops.logHintFailure handler supertype moduleName)

-- Source: base/experimental.jl:376-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # OpaqueClosure
-- include("opaque_closure.jl")
-- /Source
-- Reason: `import JuliaLean.base.opaque_closure` represents the included model.
-- Source: base/experimental.jl:379-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@overlay mt def
--     Base.Experimental.@overlay mt begin defs... end
-- 
-- Define a method and add it to the method table `mt` instead of to the global method table.
-- This can be used to implement a method override mechanism. Regular compilation will not
-- consider these methods, and you should customize the compilation flow to look in these
-- method tables (e.g., using [`Core.Compiler.OverlayMethodTable`](@ref)). The block form
-- overlays every definition in the block; definitions may carry docstrings and other macros.
-- 
-- !!! note
--     Please be aware that when defining overlay methods using `@overlay`, it is not necessary
--     to have an original method that corresponds exactly in terms of how the method dispatches.
--     This means that the method overlay mechanism enabled by `@overlay` is not implemented by
--     replacing the methods themselves, but through an additional and prioritized method
--     lookup during the method dispatch.
-- 
--     Considering this, it is important to understand that in compilations using an overlay
--     method table like the following, the method dispatched by `callx(x)` is not the regular
--     method `callx(::Float64)`, but the overlay method `callx(x::Real)`:
--     ```julia
--     callx(::Real) = :real
--     @overlay SOME_OVERLAY_MT callx(::Real) = :overlay_real
--     callx(::Float64) = :float64
-- 
--     # some overlay callsite
--     let x::Float64
--         callx(x) #> :overlay_real
--     end
--     ```
-- """
-- macro overlay(mt, def)
--     inner = Base.unwrap_macrocalls(def)
--     if isexpr(inner, :block)
--         # `@overlay mt begin ... end`: overlay every definition in the block
--         for arg in inner.args
--             isa(arg, LineNumberNode) && continue
--             innerarg = Base.unwrap_macrocalls(arg)
--             is_function_def(innerarg) || error("@overlay requires a function definition")
--             overlay_def!(mt, innerarg)
--         end
--     else
--         is_function_def(inner) || error("@overlay requires a function definition")
--         overlay_def!(mt, inner)
--     end
--     return esc(def)
-- end
-- /Source
-- Source: base/experimental.jl:427-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@consistent_overlay mt def
-- 
-- This macro operates almost identically to [`Base.Experimental.@overlay`](@ref), defining a
-- new overlay method. The key difference with this macro is that it informs the compiler that
-- the invocation of the overlay method it defines is `:consistent` with a regular,
-- non-overlayed method call.
-- 
-- More formally, when evaluating a generic function call ``f(x)`` at a specific world age
-- ``i``, if a regular method call ``fᵢ(x)`` is redirected to an overlay method call ``fᵢ′(x)``
-- defined by this macro, ``fᵢ(x)`` and ``fᵢ′(x)`` are considered `:consistent` if the following
-- conditions are met:
-- - If ``fᵢ(x)`` returns a value ``y``, then ``fᵢ′(x)`` also returns some value ``yᵢ``, and ``y ≡ yᵢ`` holds.
-- - If ``fᵢ(x)`` throws an exception, then ``fᵢ′(x)`` also throws some exception.
-- 
-- For a detailed definition of `:consistent`-cy, consult the corresponding section in
-- [`Base.@assume_effects`](@ref).
-- 
-- !!! note
--     Note that the requirements for `:consistent`-cy include not only that the return values
--     are egal, but also that the manner of termination is the same. However, it's important
--     to be aware that when they throw exceptions, the exceptions themselves don't necessarily
--     have to be egal. In other words, if ``fᵢ(x)`` throws an exception, ``fᵢ′(x)`` is
--     required to also throw one, but the exact exceptions may differ.
-- 
-- !!! note
--     Please note that the `:consistent`-cy requirement applies not to method itself but to
--     _method invocation_. This means that for the use of `@consistent_overlay`, it is
--     necessary for method invocations with the native regular compilation and those with
--     a compilation with overlay method table to be `:consistent`.
-- 
--     For example, it is important to understand that, `@consistent_overlay` can be used like
--     the following:
--     ```julia
--     callsin(x::Real) = x < 0 ? error(x) : sin(x)
--     @consistent_overlay SOME_OVERLAY_MT callsin(x::Float64) =
--         x < 0 ? error_somehow(x) : sin(x)
--     ```
--     However, be aware that this `@consistent_overlay` will immediately become invalid if a
--     new method for `callsin` is defined subsequently, such as:
--     ```julia
--     callsin(x::Float64) = cos(x)
--     ```
-- 
--     This specifically implies that the use of `@consistent_overlay` should be restricted as
--     much as possible to cases where a regular method with a concrete signature is replaced
--     by an overlay method with the same concrete signature.
-- 
--     This constraint is closely related to the note in [`Base.Experimental.@overlay`](@ref);
--     you are advised to consult that as well.
-- """
-- macro consistent_overlay(mt, def)
--     inner = Base.unwrap_macrocalls(def)
--     is_function_def(inner) || error("@consistent_overlay requires a function definition")
--     overlay_def!(mt, inner)
--     override = Base.EffectsOverride(; consistent_overlay=true)
--     Base.pushmeta!(def::Expr, Base.form_purity_expr(override))
--     return esc(def)
-- end
-- /Source
/--
Julia source: base/experimental.jl:487-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function overlay_def!(mt, @nospecialize ex)
    arg1 = ex.args[1]
    if isexpr(arg1, :call)
        arg1.args[1] = Expr(:overlay, mt, arg1.args[1])
    elseif isexpr(arg1, :(::))
        overlay_def!(mt, arg1)
    elseif isexpr(arg1, :where)
        overlay_def!(mt, arg1)
    else
        error("@overlay requires a function definition")
    end
    return ex
end
```
-/
def overlayDef {L : Type} (methodTable : Value L) : Value L → ExprResult (Value L)
  | .expr _ [] => .error (.jl .boundsError)
  | .expr head (.expr "call" (callee :: callRest) :: rest) =>
    .ok (.expr head (.expr "call" (.expr "overlay" [methodTable, callee] :: callRest) :: rest))
  | .expr _ (.expr "call" [] :: _) => .error (.jl .boundsError)
  | .expr head ((.expr "::" args) :: rest) => do
    let updatedArgument ← overlayDef methodTable (.expr "::" args)
    pure (.expr head (updatedArgument :: rest))
  | .expr head ((.expr "where" args) :: rest) => do
    let updatedArgument ← overlayDef methodTable (.expr "where" args)
    pure (.expr head (updatedArgument :: rest))
  | .expr _ (_ :: _) => .error (.errorException "@overlay requires a function definition")
  | _ => .error .typeError
termination_by expression => sizeOf expression
decreasing_by
  · have _hList : sizeOf (.expr "::" args : Value L) <
        sizeOf ((.expr "::" args : Value L) :: rest) :=
      List.sizeOf_lt_of_mem (by simp)
    simp_wf
    omega
  · have _hList : sizeOf (.expr "where" args : Value L) <
        sizeOf ((.expr "where" args : Value L) :: rest) :=
      List.sizeOf_lt_of_mem (by simp)
    simp_wf
    omega
structure MethodTableOps (m : Type → Type) (Module Symbol MethodTable : Type) where
  checkTopLevelEffect : Module → String → m Unit
  newMethodTable : Symbol → Module → m MethodTable

/--
Julia source: base/experimental.jl:501-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let new_mt(name::Symbol, mod::Module) = begin
        ccall(:jl_check_top_level_effect, Cvoid, (Any, Cstring), mod, "@MethodTable")
        ccall(:jl_new_method_table, Any, (Any, Any), name, mod)
    end
```
-/
def newMethodTable {m : Type → Type} {Module Symbol MethodTable : Type}
    [Monad m] (ops : MethodTableOps m Module Symbol MethodTable)
    (name : Symbol) (mod : Module) : m MethodTable := do
  ops.checkTopLevelEffect mod "@MethodTable"
  ops.newMethodTable name mod

-- Source: base/experimental.jl:505-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @eval macro MethodTable(name::Symbol)
--         esc(:(const $name = $$new_mt($(quot(name)), $(__module__))))
--     end
-- end
-- /Source
-- UNTRANSLATED
-- Source: base/experimental.jl:510-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@MethodTable name
-- 
-- Create a new MethodTable in the current module, bound to `name`. This method table can be
-- used with the [`Base.Experimental.@overlay`](@ref) macro to define methods for a function
-- without adding them to the global method table.
-- """
-- :@MethodTable
-- /Source
-- Reason: The exported `@MethodTable` macro documentation and registration expression have no runtime method body.
-- Source: base/experimental.jl:519-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Experimental.@make_all_arithmetic_checked
-- 
-- This macro defines methods that overwrite the base definition of basic arithmetic (`+`, `-`, `*`),
-- to use their checked variants instead. Explicitly overflowing arithmetic operators (`+%`, `-%`, `*%`)
-- are not affected.
-- 
-- !!! warning
--     This macro is temporary and will likely be replaced by a more complete mechanism in the
--     future. It is subject to change or removal without notice.
-- """
-- macro make_all_arithmetic_checked()
--     esc(quote
--         Base.:(-)(x::Base.BitInteger)                         = Base.Checked.checked_neg(x)
--         Base.:(-)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_sub(x, y)
--         Base.:(-)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_sub(x, y)
--         Base.:(+)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_add(x, y)
--         Base.:(+)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_add(x, y)
--         Base.:(*)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_mul(x, y)
--     end)
-- end
-- /Source
structure IOThreadOps (m : Type → Type)
    (ThreadIdCell ThreadWork Pointer Task ThreadSynchronizer Error : Type) where
  newThreadIdCell : m ThreadIdCell
  makeCFunction : (Pointer → m Unit) → m ThreadWork
  createThread : ThreadIdCell → ThreadWork → Pointer → m (JInt .i32)
  detachThread : ThreadIdCell → m (JInt .i32)
  currentTask : m Task
  makeThreadSynchronizer : m ThreadSynchronizer
  setDoneNotify : Task → ThreadSynchronizer → m Unit
  errorMonitor : Task → m Unit
  threadId : m (JInt .i64)
  toInt16 : JInt .i64 → m (JInt .i16)
  setIOLoopThreadId : JInt .i16 → m Unit
  wait : m Unit
  nullPointer : Pointer
  uvError : String → JInt .i32 → m Unit

/--
Julia source: base/experimental.jl:541-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.make_io_thread()

Create a new thread that will run the Julia IO loop. This can potentially reduce the latency of some
IO operations as they no longer depend on the main thread to run it. This does mean that code that uses
this as implicit synchronization needs to be checked for correctness.
"""
function make_io_thread()
    tid = UInt[0]
    threadwork = @cfunction function(arg::Ptr{Cvoid})
            current_task().donenotify = Base.ThreadSynchronizer() #TODO: Should this happen by default in adopt thread?
            Base.errormonitor(current_task()) # this may not go particularly well if the IO loop is dead, but try anyways
            @ccall jl_set_io_loop_tid((Threads.threadid() - 1)::Int16)::Cvoid
            wait() # spin uv_run as long as needed
            nothing
        end Cvoid (Ptr{Cvoid},)
    err = @ccall uv_thread_create(tid::Ptr{UInt}, threadwork::Ptr{Cvoid}, C_NULL::Ptr{Cvoid})::Cint
    err == 0 || Base.uv_error("uv_thread_create", err)
    @ccall uv_thread_detach(tid::Ptr{UInt})::Cint
    err == 0 || Base.uv_error("uv_thread_detach", err)
    # n.b. this does not wait for the thread to start or to take ownership of the event loop
end
```
-/
def makeIOThreadNative {m : Type → Type}
    {ThreadIdCell ThreadWork Pointer Task ThreadSynchronizer Error : Type}
    [Monad m]
    (ops : IOThreadOps m ThreadIdCell ThreadWork Pointer Task ThreadSynchronizer Error) : m (Option Bool) := do
  let threadIdCell ← ops.newThreadIdCell
  let work ← ops.makeCFunction (fun _ => do
    let task ← ops.currentTask
    let synchronizer ← ops.makeThreadSynchronizer
    ops.setDoneNotify task synchronizer
    ops.errorMonitor (← ops.currentTask)
    let threadId ← ops.threadId
    let osThreadId ← ops.toInt16 (JInt.wrap .i64 (threadId.val - 1))
    ops.setIOLoopThreadId osThreadId
    ops.wait
  )
  let createError ← ops.createThread threadIdCell work ops.nullPointer
  if createError.val != 0 then ops.uvError "uv_thread_create" createError
  let _ ← ops.detachThread threadIdCell
  if createError.val == 0 then
    pure (some true)
  else
    ops.uvError "uv_thread_detach" createError
    pure none

def makeIOThread {m : Type → Type}
    {ThreadIdCell ThreadWork Pointer Task ThreadSynchronizer Error : Type}
    [Monad m]
    (ops : IOThreadOps m ThreadIdCell ThreadWork Pointer Task ThreadSynchronizer Error) : m Unit := do
  let _ ← makeIOThreadNative ops
  pure ()

/-- Source: base/experimental.jl:548-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def makeIOThreadLibuv
    {Handle Request Object Ptr Io Options Runtime RuntimeError ThreadIdCell ThreadWork Task Sync : Type}
    (uv : JuliaLean.base.libuv.Ops Handle Request (JInt .i32) Object Ptr Io Options String Runtime RuntimeError)
    (ops : IOThreadOps
      (JuliaLean.base.libuv.M (JuliaLean.base.libuv.World Object Io Runtime) RuntimeError)
      ThreadIdCell ThreadWork Ptr Task Sync (JuliaLean.base.libuv.Error RuntimeError)) :
    JuliaLean.base.libuv.M (JuliaLean.base.libuv.World Object Io Runtime) RuntimeError (Option Bool) :=
  let uv := { uv with
    integerToCint := fun code => pure code
    integerLessThanZero := fun code => pure (decide (code.val < 0))
    textToString := fun text => pure text }
  makeIOThreadNative (Error := JuliaLean.base.libuv.Error RuntimeError)
    { ops with uvError := JuliaLean.base.libuv.uvErrorStringInteger uv }

structure EntrypointOps (m : Type → Type)
    (Function FunctionType ArgumentType Signature : Type) where
  functionType : Function → FunctionType
  tupleType : FunctionType → List ArgumentType → Signature
  entrypointType : Signature → m Unit
  generatingOutput : m Bool
  addCompilerEntrypoint : Signature → m Unit

/--
Julia source: base/experimental.jl:564-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.entrypoint(f, argtypes::Tuple)

Mark a method for inclusion when the `--trim` option is specified.
"""
function entrypoint(@nospecialize(f), @nospecialize(argtypes::Tuple))
    entrypoint(Tuple{Core.Typeof(f), argtypes...})
end
```
-/
def entrypointFunction {m : Type → Type} {Function FunctionType ArgumentType Signature : Type}
    [Monad m] (ops : EntrypointOps m Function FunctionType ArgumentType Signature)
    (f : Function) (argTypes : List ArgumentType) : m Unit :=
  ops.entrypointType (ops.tupleType (ops.functionType f) argTypes)

/--
Julia source: base/experimental.jl:573-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function entrypoint(@nospecialize(argt::Type))
    # Only add to entrypoint list if we're generating output and in trim mode
    if ccall(:jl_generating_output, Cint, ()) != 0
        Base.Compiler.add_entrypoint(argt)
    end
    nothing
end
```
-/
def entrypointType {m : Type → Type} {Function FunctionType ArgumentType Signature : Type}
    [Monad m] (ops : EntrypointOps m Function FunctionType ArgumentType Signature)
    (signature : Signature) : m Unit := do
  if ← ops.generatingOutput then ops.addCompilerEntrypoint signature

structure WorldAgeOps (m : Type → Type) where
  disableNewWorlds : m Unit

/--
Julia source: base/experimental.jl:581-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.disable_new_worlds()

Mark that no new worlds (methods additions, deletions, etc) are permitted to be created at
any future time, allowing for lower latencies for some operations and slightly lower memory
usage, by eliminating the tracking of those possible invalidation.
"""
disable_new_worlds() = ccall(:jl_disable_new_worlds, Cvoid, ())
```
-/
def disableNewWorlds {m : Type → Type} [Monad m] (ops : WorldAgeOps m) : m Unit :=
  ops.disableNewWorlds

structure TaskMetricsOps (m : Type → Type) where
  enableMetrics : m Unit
  disableMetrics : m Unit

/--
Julia source: base/experimental.jl:590-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
### Task metrics

"""
    Base.Experimental.task_metrics(::Bool)

Enable or disable the collection of per-task metrics.
A `Task` created when `Base.Experimental.task_metrics(true)` is in effect will have
[`Base.Experimental.task_running_time_ns`](@ref) and [`Base.Experimental.task_wall_time_ns`](@ref)
timing information available.

!!! note
    Task metrics can be enabled at start-up via the `--task-metrics=yes` command line option.
"""
function task_metrics(b::Bool)
    if b
        ccall(:jl_task_metrics_enable, Cvoid, ())
    else
        ccall(:jl_task_metrics_disable, Cvoid, ())
    end
    return nothing
end
```
-/
def taskMetrics {m : Type → Type} [Monad m] (ops : TaskMetricsOps m) (enabled : Bool) : m Unit := do
  if enabled then ops.enableMetrics else ops.disableMetrics

structure TaskTimeOps (m : Type → Type) (Task : Type) where
  currentTask : m Task
  metricsEnabled : Task → Bool
  sameTask : Task → Task → Bool
  runningTimeNs : Task → JInt .u64
  lastStartedRunningAt : Task → JInt .u64
  firstEnqueuedAt : Task → JInt .u64
  finishedAt : Task → JInt .u64
  timeNs : m (JInt .u64)

/--
Julia source: base/experimental.jl:612-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.task_running_time_ns(t::Task)::Union{UInt64, Nothing}

Return the total nanoseconds that the task `t` has spent running.
This metric is only updated when `t` yields or completes unless `t` is the current task, in
which it will be updated continuously.
See also [`Base.Experimental.task_wall_time_ns`](@ref).

Return `nothing` if task timings are not enabled.
See [`Base.Experimental.task_metrics`](@ref).

!!! note "This metric is from the Julia scheduler"
    A task may be running on an OS thread that is descheduled by the OS
    scheduler, this time still counts towards the metric.

!!! compat "Julia 1.12"
    This method was added in Julia 1.12.
"""
function task_running_time_ns(t::Task=current_task())
    t.metrics_enabled || return nothing
    if t == current_task()
        # These metrics fields can't update while we're running.
        # But since we're running we need to include the time since we last started running!
        return t.running_time_ns +% (time_ns() -% t.last_started_running_at)
    else
        return t.running_time_ns
    end
end
```
-/
def taskRunningTimeNs {m : Type → Type} {Task : Type} [Monad m]
    (ops : TaskTimeOps m Task) (requestedTask : Option Task := none) : m (Option (JInt .u64)) := do
  let task ← match requestedTask with
    | some task => pure task
    | none => ops.currentTask
  if !ops.metricsEnabled task then
    pure none
  else
    let current ← ops.currentTask
    if ops.sameTask task current then
      let now ← ops.timeNs
      let elapsed := JInt.wrap .u64 (now.val - (ops.lastStartedRunningAt task).val)
      pure (some (JInt.wrap .u64 ((ops.runningTimeNs task).val + elapsed.val)))
    else
      pure (some (ops.runningTimeNs task))

/--
Julia source: base/experimental.jl:641-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.task_wall_time_ns(t::Task)::Union{UInt64, Nothing}

Return the total nanoseconds that the task `t` was runnable.
This is the time since the task first entered the run queue until the time at which it
completed, or until the current time if the task has not yet completed.
See also [`Base.Experimental.task_running_time_ns`](@ref).

Return `nothing` if task timings are not enabled.
See [`Base.Experimental.task_metrics`](@ref).

!!! compat "Julia 1.12"
    This method was added in Julia 1.12.
"""
function task_wall_time_ns(t::Task=current_task())
    t.metrics_enabled || return nothing
    start_at = t.first_enqueued_at
    start_at == 0 && return UInt64(0)
    end_at = t.finished_at
    end_at == 0 && return time_ns() -% start_at
    return end_at -% start_at
end
```
-/
def taskWallTimeNs {m : Type → Type} {Task : Type} [Monad m]
    (ops : TaskTimeOps m Task) (requestedTask : Option Task := none) : m (Option (JInt .u64)) := do
  let task ← match requestedTask with
    | some task => pure task
    | none => ops.currentTask
  if !ops.metricsEnabled task then
    pure none
  else
    let startAt := ops.firstEnqueuedAt task
    if startAt.val == 0 then
      pure (some (JInt.lit .u64 0))
    else
      let endAt := ops.finishedAt task
      if endAt.val == 0 then
        let now ← ops.timeNs
        pure (some (JInt.wrap .u64 (now.val - startAt.val)))
      else
        pure (some (JInt.wrap .u64 (endAt.val - startAt.val)))

inductive WaitTimeoutOther (Condition Timeout : Type) where
  | condition (condition : Condition)
  | timeout (timeout : Timeout)

structure WaitWithTimeoutOps
    (E Task W Queue Lock Entry Token Source Timeout Real LockState Value : Type) where
  zeroTimeout : Real
  checkCancelArg : JuliaLean.base.io.CancelArg Token →
    JuliaLean.base.channels.M E Task W (Option Token)
  cancelSource : Option Token → Option Source
  currentTask : JuliaLean.base.channels.M E Task W Task
  timeoutPositive : Real → JuliaLean.base.channels.M E Task W Bool
  newTimeoutWait : Real → JuliaLean.base.channels.M E Task W Timeout
  acquireWaitEntry : Task →
    JuliaLean.base.park.Waitables Source (WaitTimeoutOther (JuliaLean.base.condition.GenericCondition Queue Lock) Timeout) →
    JuliaLean.base.channels.M E Task W Entry
  park : JuliaLean.base.park.Waitables Source
      (WaitTimeoutOther (JuliaLean.base.condition.GenericCondition Queue Lock) Timeout) →
    Entry → Bool → JuliaLean.base.channels.M E Task W Bool
  withdraw : JuliaLean.base.park.Waitables Source
      (WaitTimeoutOther (JuliaLean.base.condition.GenericCondition Queue Lock) Timeout) →
    Entry → JInt .u8 → JuliaLean.base.channels.M E Task W Unit
  checkCancel : Source → JuliaLean.base.channels.M E Task W Unit
  unlockAll : Lock → JuliaLean.base.channels.M E Task W LockState
  waitSafeInterrupt : JuliaLean.base.park.Waitables Source
      (WaitTimeoutOther (JuliaLean.base.condition.GenericCondition Queue Lock) Timeout) →
    Entry → JuliaLean.base.channels.M E Task W Value
  relockAll : Lock → LockState → JuliaLean.base.channels.M E Task W Unit
  wakeFired : JInt .u8
  wakeValue : JInt .u8
  errorException : String → JuliaLean.base.channels.Error E Task

def waitTimeoutWaitables {Queue Lock Source Timeout : Type}
    (condition : JuliaLean.base.condition.GenericCondition Queue Lock)
    (source : Option Source) (timeout : Option Timeout) :
    JuliaLean.base.park.Waitables Source
      (WaitTimeoutOther (JuliaLean.base.condition.GenericCondition Queue Lock) Timeout) :=
  match source, timeout with
  | none, none =>
    .tuple [.other (.condition condition)]
  | none, some timeout =>
    .tuple [.other (.condition condition), .other (.timeout timeout)]
  | some source, none =>
    .tuple [.other (.condition condition), .source source (JInt.lit .u8 0)]
  | some source, some timeout =>
    .tuple [.other (.condition condition), .source source (JInt.lit .u8 0),
      .other (.timeout timeout)]

/-- Julia source: base/experimental.jl:664-719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# wait_with_timeout
#
# A version of `wait(c::Condition)` that additionally allows the
# specification of a timeout. This is experimental as it will likely
# be dropped when a cancellation framework is added.
#
# Implemented as a `park!` over the condition, the governing cancellation
# source, and a `Base.TimeoutWait` deadline (see base/park.jl and
# base/asyncevent.jl): the deadline's claimer arbitrates against notifies
# and interrupters through the single wake-claim CAS on the waiting
# task's `waiting_on`, and the non-canonical waitable shape makes the
# entry cache hand out a fresh, single-use entry - which is exactly what
# makes the deadline's specific-wait claim sound.

"""
    wait_with_timeout(c::GenericCondition; first::Bool=false, timeout::Real=0.0)

Wait for [`notify`](@ref) on `c` and return the `val` parameter passed to `notify`.

If the keyword `first` is set to `true`, the waiter will be put _first_
in line to wake up on `notify`. Otherwise, `wait` has first-in-first-out (FIFO) behavior.

If `timeout` is specified, cancel the `wait` when it expires and return
`:timed_out`. The minimum value for `timeout` is 0.001 seconds, i.e. 1
millisecond.
"""
function wait_with_timeout(c::GenericCondition; first::Bool=false, timeout::Real=0.0,
                           cancel::Base.CancelTokenArg=Base.DEFAULT_CANCEL)
    tok = Base.check_cancel_arg(cancel)
    src = Base.cancel_source(tok)
    ct = current_task()
    if timeout > 0.0
        tw = Base.TimeoutWait(timeout)
        ws = src === nothing ? (c, tw) : (c, Base.SourceWait(src, 0x00), tw)
    else
        ws = src === nothing ? (c,) : (c, Base.SourceWait(src, 0x00))
    end
    # non-canonical shapes get a fresh entry - exactly what makes the
    # deadline claimer's specific-wait CAS sound
    w = Base.acquire_wait_entry!(ct, ws)
    if !Base.park!(ws, w, first)
        Base.withdraw!(ws, w, Base.WAKE_FIRED)
        src === nothing || Base.checkcancel(src)
        error("park fired without a cancelled source")
    end
    lockstate = Base.unlockall(c.lock)
    r = try
        Base.wait_safe_interrupt(ws, w)
    catch
        Base.relockall(c.lock, lockstate)
        rethrow()
    end
    Base.relockall(c.lock, lockstate)
    Base.withdraw!(ws, w, Base.WAKE_VALUE)   # closes the timer, retires
    return r
end
```
-/
def waitWithTimeout
    {E Task W Queue Lock Entry Token Source Timeout Real LockState Value : Type}
    (ops : WaitWithTimeoutOps E Task W Queue Lock Entry Token Source Timeout Real LockState Value)
    (condition : JuliaLean.base.condition.GenericCondition Queue Lock)
    (first : Bool := false) (timeout : Real := ops.zeroTimeout)
    (cancel : JuliaLean.base.io.CancelArg Token := .default) :
    JuliaLean.base.channels.M E Task W Value := do
  let token ← ops.checkCancelArg cancel
  let source := ops.cancelSource token
  let currentTask ← ops.currentTask
  let timeoutWait ← if ← ops.timeoutPositive timeout then do
    let timeoutWait ← ops.newTimeoutWait timeout
    pure (some timeoutWait)
  else
    pure none
  let waitables := waitTimeoutWaitables condition source timeoutWait
  let waitEntry ← ops.acquireWaitEntry currentTask waitables
  if !(← ops.park waitables waitEntry first) then
    ops.withdraw waitables waitEntry ops.wakeFired
    match source with
    | none => pure ()
    | some source => ops.checkCancel source
    throw (ops.errorException "park fired without a cancelled source")
  let lockState ← ops.unlockAll condition.lock
  let value ← tryCatch (ops.waitSafeInterrupt waitables waitEntry) (fun error => do
    ops.relockAll condition.lock lockState
    throw error)
  ops.relockAll condition.lock lockState
  ops.withdraw waitables waitEntry ops.wakeValue
  pure value
-- Source: base/experimental.jl:721-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@reexport using Module
-- 
-- Automatically re-export all exported names from a module when using it.
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> module A
--            export foo
--            foo() = "foo from A"
--        end
-- A
-- 
-- julia> module B
--            using Base.Experimental: @reexport
--            @reexport using ..A
--            # Now B exports foo, even though it's defined in A
--        end
-- B
-- 
-- julia> using .B
-- 
-- julia> foo()
-- "foo from A"
-- ```
-- 
-- !!! warning
--     This interface is experimental and subject to change or removal without notice.
-- """
-- macro reexport(ex)
--     if !Meta.isexpr(ex, :using) || isempty(ex.args)
--         error("@reexport must be used with a `using` statement, e.g., `@reexport using MyModule`")
--     end
-- 
--     # Check for `using Foo: x, y` syntax (not supported)
--     if any(arg -> Meta.isexpr(arg, :(:)), ex.args)
--         error("@reexport does not support `using Module: names` syntax")
--     end
-- 
--     # Generate _eval_using calls for each module in the using statement
--     calls = Expr(:block)
--     for mod_path in ex.args
--         push!(calls.args, :($(Core._eval_using)($(__module__), $(QuoteNode(mod_path)), $(Base.JL_MODULE_USING_REEXPORT))))
--     end
--     push!(calls.args, Expr(:latestworld))
--     push!(calls.args, :nothing)
-- 
--     return esc(calls)
-- end
-- /Source
structure SyntaxVersionOps (m : Type → Type) (Module Version Edition Parser : Type) where
  versionedParse : Edition → m Parser
  declareInternalParser : Module → String → Parser → m Unit
  editionNumber : Version → m Edition

/--
Julia source: base/experimental.jl:772-776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.set_syntax_version(m::Module, edition::Tuple{Int, Int})
    parser = Base.VersionedParse(edition)
    Core.declare_const(m, Symbol("#_internal_julia_parse"), parser)
    nothing
end
```
-/
def setSyntaxVersionEdition {m : Type → Type} {Module Version Edition Parser : Type} [Monad m]
    (ops : SyntaxVersionOps m Module Version Edition Parser) (mod : Module) (edition : Edition) : m Unit := do
  let parser ← ops.versionedParse edition
  ops.declareInternalParser mod "#_internal_julia_parse" parser

/--
Julia source: base/experimental.jl:777-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.set_syntax_version(mod, e::VersionNumber) =
    Base.set_syntax_version(mod, Base.EditionNumber(e))
```
-/
def setSyntaxVersionNumber {m : Type → Type} {Module Version Edition Parser : Type} [Monad m]
    (ops : SyntaxVersionOps m Module Version Edition Parser) (mod : Module) (version : Version) : m Unit := do
  let edition ← ops.editionNumber version
  setSyntaxVersionEdition ops mod edition

-- Source: base/experimental.jl:780-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@set_syntax_version ver
-- 
-- Sets the syntax version of the current module to `ver`. This overrides settings of `syntax.julia_version` or
-- `compat.julia` from Project.toml.
-- 
-- !!! compat "Julia 1.14"
--     This macro was added in Julia 1.14.
-- 
-- !!! warning
--     The new syntax version will take effect only for code parsed after the *invocation* of the result of the macro
--     expansion. This may be unintuitive if the macro is used inside a module body, as the entire module will be parsed
--     before any statements therein are executed, e.g. consider.
-- 
--     ```
--     @set_syntax_version v"1.13"
--     module ChangeSyntax
--         @set_syntax_version v"1.14"
--         expr1 # Parsed with syntax version 1.13
--      # The call itself is parsed with syntax version 1.13, but the included code is parsed with syntax version 1.14
--         include_string(ChangeSyntax, "expr2")
--         expr3 # Parsed with syntax version 1.13
--     end
--     ```
-- 
--     For this reason, the Project.toml mechanism is strongly preferred for packages.
--     However, this macro may be useful for scripts or the REPL.
-- 
-- !!! warning
--     This interface is experimental and subject to change or removal without notice.
-- """
-- macro set_syntax_version(ver)
--     Expr(:call, Base.set_syntax_version, __module__, esc(ver))
-- end
-- /Source
-- Source: base/experimental.jl:815-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Experimental.@VERSION ver
-- 
-- This macro provides access to parser (and possibly in the future other frontend component) language version
-- information. In particular, `(@VERSION).syntax` provides the syntax version used to parse the location where the macro is invoked.
-- 
-- !!! compat "Julia 1.14"
--     This macro was added in Julia 1.14.
-- 
-- !!! note
--     Calls to this macro have special handling in the parser and the name `@VERSION` is mandatory. At this time, other macros do not
--     have access to source syntax version information.
-- """
-- function var"@VERSION"(__source__::Union{LineNumberNode, Core.MacroSource}, __module__::Module)
--     # This macro has special handling in the parser, which puts the current syntax
--     # version into __source__.
--     if isa(__source__, LineNumberNode)
--         return :((; syntax = v"1.13", runtime = VERSION))
--     else
--         return :((; syntax = $(__source__.syntax_ver), runtime = VERSION))
--     end
-- end
-- /Source
structure ObjectCacheOps (m : Type → Type) (Directory Age Pointer Error : Type) where
  defaultAge : Age
  cacheEnabled : m (JInt .i32)
  time : m Age
  subtractAge : Age → Age → Age
  floorToInt64 : Age → m (JInt .i64)
  pruneBefore : JInt .i64 → m (JInt .i64)
  compact : Directory → m Pointer
  showDirectory : Directory → m String
  isNull : Pointer → Bool
  unsafeString : Pointer → m String
  errorException : String → Error

/--
Julia source: base/experimental.jl:838-861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Experimental.prune_objcache(dir::AbstractString; age::Real=7*24*60*60) -> Int

Remove the entries of the native code cache that were not used within the last `age`
seconds, then write a copy of the cache without its free space to `dir`, which must not
already hold a cache. Return the number of entries removed, or `nothing` if the cache is
disabled.

The cache file never shrinks by itself. To save a small cache, for example between CI jobs,
save the copy in `dir`, either directly as a `JULIA_OBJCACHE_PATH` directory or with its
`data.mdb` moved over the one in the cache once no Julia process is using it.

!!! warning
    This interface is experimental and subject to change or removal without notice.
"""
function prune_objcache(dir::AbstractString; age::Real=7*24*60*60)
    ccall(:jl_objcache_kv_enabled, Cint, ()) == 0 && return nothing
    # waiting for the database's write lock and copying it can take a while, so let GC run
    removed = @ccall gc_safe=true jl_objcache_prune((floor(Int64, time() - age))::Int64)::Int64
    removed < 0 && error("could not prune the native code cache")
    err = @ccall gc_safe=true jl_objcache_compact(dir::Cstring)::Cstring
    err == C_NULL || error("could not copy the native code cache to ", dir, ": ", unsafe_string(err))
    return Int(removed)
end
```
-/
def pruneObjCache {m : Type → Type} {Directory Age Pointer Error : Type}
    [Monad m] [MonadExceptOf Error m]
    (ops : ObjectCacheOps m Directory Age Pointer Error)
    (directory : Directory) (requestedAge : Option Age := none) : m (Option (JInt .i64)) := do
  if (← ops.cacheEnabled).val == 0 then
    pure none
  else
    let age := match requestedAge with
      | some age => age
      | none => ops.defaultAge
    let now ← ops.time
    let cutoff ← ops.floorToInt64 (ops.subtractAge now age)
    let removed ← ops.pruneBefore cutoff
    if removed.val < 0 then
      throw (ops.errorException "could not prune the native code cache")
    let errorPointer ← ops.compact directory
    if !ops.isNull errorPointer then
      let shownDirectory ← ops.showDirectory directory
      let message ← ops.unsafeString errorPointer
      throw (ops.errorException ("could not copy the native code cache to " ++ shownDirectory ++ ": " ++ message))
    pure (some removed)

-- Source: base/experimental.jl:863-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module
-- /Source
-- Reason: The Lean namespace terminator closes the modeled Julia module.

structure MacroAtoms (L : Type) where
  leaf : LeafOps L
  asInt : L → Option JInt64
  ofUInt8 : JInt .u8 → L
  ofString : String → L
  showValue : Value L → String
  caller : L
  evalUsing : L
  usingReexport : L
  setSyntaxVersion : L
  newMethodTable : L
  sourceFile : Value L

/--
Julia source: base/experimental.jl:52-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro aliasscope(body)
    sym = :aliasscope_result
    quote
        $(Expr(:aliasscope))
        $sym = $(esc(body))
        $(Expr(:popaliasscope))
        $sym
    end
end
```
-/
def aliasscopeMacro {L : Type} (sourceFile body : Value L) : Value L :=
  .expr "block" [.lineNumberNode (JuliaLean.base.expr.i64 55) sourceFile, .expr "aliasscope" [],
    .lineNumberNode (JuliaLean.base.expr.i64 56) sourceFile,
    .expr "=" [.symbol "aliasscope_result", esc body],
    .lineNumberNode (JuliaLean.base.expr.i64 57) sourceFile, .expr "popaliasscope" [],
    .lineNumberNode (JuliaLean.base.expr.i64 58) sourceFile, .symbol "aliasscope_result"]

/--
Julia source: base/experimental.jl:158-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro optlevel(n::Int)
    return Expr(:meta, :optlevel, n)
end
```
-/
def optlevelMacro {L : Type} (lo : LeafOps L) (n : JInt64) : Value L :=
  .expr "meta" [.symbol "optlevel", .leaf (lo.ofInt n)]

/--
Julia source: base/experimental.jl:180-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro max_methods(n::Int)
    1 <= n <= 4 || error("We must have that `1 <= max_methods <= 4`, but `max_methods = $n`.")
    return Expr(:meta, :max_methods, n)
end
```
-/
def maxMethodsMacro {L : Type} (lo : LeafOps L) (n : JInt64) : ExprResult (Value L) := do
  if !(1 ≤ n.val ∧ n.val ≤ 4) then
    throw (.errorException s!"We must have that `1 <= max_methods <= 4`, but `max_methods = {n.val}`.")
  pure (.expr "meta" [.symbol "max_methods", .leaf (lo.ofInt n)])

/--
Julia source: base/experimental.jl:193-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro max_methods(n::Int, fdef::Expr)
    1 <= n <= 255 || error("We must have that `1 <= max_methods <= 255`, but `max_methods = $n`.")
    (fdef.head === :function && length(fdef.args) == 1) || error("Second argument must be a function forward declaration")
    return :(typeof($(esc(fdef))).name.max_methods = $(UInt8(n)))
end
```
-/
def maxMethodsFunctionMacro {L : Type} (a : MacroAtoms L) (n : JInt64)
    (fdef : Value L) : ExprResult (Value L) := do
  if !(1 ≤ n.val ∧ n.val ≤ 255) then
    throw (.errorException s!"We must have that `1 <= max_methods <= 255`, but `max_methods = {n.val}`.")
  if !(isexpr_n fdef "function" (JuliaLean.base.expr.i64 1)) then
    throw (.errorException "Second argument must be a function forward declaration")
  let typ : Value L := .expr "call" [.symbol "typeof", esc fdef]
  let name : Value L := .expr "." [typ, quoteSym "name"]
  pure (.expr "=" [.expr "." [name, quoteSym "max_methods"], .leaf (a.ofUInt8 (JInt.wrap .u8 n.val))])

/--
Julia source: base/experimental.jl:212-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro compiler_options(args...)
    opts = Expr(:block)
    for ex in args
        if isa(ex, Expr) && ex.head === :(=) && length(ex.args) == 2
            if ex.args[1] === :optimize
                push!(opts.args, Expr(:meta, :optlevel, ex.args[2]::Int))
            elseif ex.args[1] === :compile
                a = ex.args[2]
                a = #a === :no  ? 0 :
                    #a === :yes ? 1 :
                    #a === :all ? 2 :
                    a === :min ? 3 : error("invalid argument to \"compile\" option")
                push!(opts.args, Expr(:meta, :compile, a))
            elseif ex.args[1] === :infer
                a = ex.args[2]
                a = a === false || a === :no  ? 0 :
                    a === true  || a === :yes ? 1 : error("invalid argument to \"infer\" option")
                push!(opts.args, Expr(:meta, :infer, a))
            elseif ex.args[1] === :max_methods
                a = ex.args[2]
                a = a === :default ? 3 :
                  a isa Int ? ((1 <= a <= 4) ? a : error("We must have that `1 <= max_methods <= 4`, but `max_methods = $a`.")) :
                  error("invalid argument to \"max_methods\" option")
                push!(opts.args, Expr(:meta, :max_methods, a))
            else
                error("unknown option \"$(ex.args[1])\"")
            end
        else
            error("invalid option syntax")
        end
    end
    return opts
end
```
-/
def compilerOptionsMacro {L : Type} (a : MacroAtoms L) (args : List (Value L)) : ExprResult (Value L) := do
  let mut opts : List (Value L) := []
  for ex in args do
    let .expr "=" [key, value] := ex | throw (.errorException "invalid option syntax")
    let (tag, number) ← match key with
      | .symbol "optimize" => do
        let .leaf x := value | throw .typeError
        let some n := a.asInt x | throw .typeError
        pure ("optlevel", n)
      | .symbol "compile" => do
        let .symbol "min" := value | throw (.errorException "invalid argument to \"compile\" option")
        pure ("compile", JuliaLean.base.expr.i64 3)
      | .symbol "infer" => do
        let b := match value with | .leaf x => a.leaf.asBool x | _ => none
        if b == some false || isSymbol value "no" then pure ("infer", JuliaLean.base.expr.i64 0)
        else if b == some true || isSymbol value "yes" then pure ("infer", JuliaLean.base.expr.i64 1)
        else throw (.errorException "invalid argument to \"infer\" option")
      | .symbol "max_methods" => do
        if isSymbol value "default" then pure ("max_methods", JuliaLean.base.expr.i64 3)
        else
          let n := match value with | .leaf x => a.asInt x | _ => none
          let some n := n | throw (.errorException "invalid argument to \"max_methods\" option")
          if !(1 ≤ n.val ∧ n.val ≤ 4) then
            throw (.errorException s!"We must have that `1 <= max_methods <= 4`, but `max_methods = {n.val}`.")
          pure ("max_methods", n)
      | _ => throw (.errorException ("unknown option \"" ++ a.showValue key ++ "\""))
    opts := opts ++ [.expr "meta" [.symbol tag, .leaf (a.leaf.ofInt number)]]
  pure (.expr "block" opts)
where
  isSymbol (value : Value L) (name : String) : Bool :=
    match value with | .symbol s => s == name | _ => false

/--
Julia source: base/experimental.jl:268-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro force_compile() Expr(:meta, :force_compile) end
```
-/
def forceCompileMacro {L : Type} : Value L := .expr "meta" [.symbol "force_compile"]

/--
Julia source: base/experimental.jl:505-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval macro MethodTable(name::Symbol)
        esc(:(const $name = $$new_mt($(quot(name)), $(__module__))))
    end
```
-/
def methodTableMacro {L : Type} (a : MacroAtoms L) (name : Sym) : Value L :=
  esc (.expr "const" [.expr "=" [.symbol name,
    .expr "call" [.leaf a.newMethodTable, quoteSym name, .leaf a.caller]]])

/--
Julia source: base/experimental.jl:532-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(-)(x::Base.BitInteger)                         = Base.Checked.checked_neg(x)
```
-/
def arithmeticCheckedNeg {t : IntTy} (x : JInt t) := JuliaLean.base.checked.checkedNegBits x
/--
Julia source: base/experimental.jl:533-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(-)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_sub(x, y)
```
-/
def arithmeticCheckedSubInt (x y : JInt64) := JuliaLean.base.checked.checkedSubBits x y
/--
Julia source: base/experimental.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(-)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_sub(x, y)
```
-/
def arithmeticCheckedSub {t : IntTy} (x y : JInt t) := JuliaLean.base.checked.checkedSubBits x y
/--
Julia source: base/experimental.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(+)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_add(x, y)
```
-/
def arithmeticCheckedAddInt (x y : JInt64) := JuliaLean.base.checked.checkedAddBits x y
/--
Julia source: base/experimental.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(+)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_add(x, y)
```
-/
def arithmeticCheckedAdd {t : IntTy} (x y : JInt t) := JuliaLean.base.checked.checkedAddBits x y
/--
Julia source: base/experimental.jl:537-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        Base.:(*)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_mul(x, y)
```
-/
def arithmeticCheckedMul {t : IntTy} (x y : JInt t) := JuliaLean.base.checked.checkedMulBits x y

/--
Julia source: base/experimental.jl:751-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro reexport(ex)
    if !Meta.isexpr(ex, :using) || isempty(ex.args)
        error("@reexport must be used with a `using` statement, e.g., `@reexport using MyModule`")
    end

    # Check for `using Foo: x, y` syntax (not supported)
    if any(arg -> Meta.isexpr(arg, :(:)), ex.args)
        error("@reexport does not support `using Module: names` syntax")
    end

    # Generate _eval_using calls for each module in the using statement
    calls = Expr(:block)
    for mod_path in ex.args
        push!(calls.args, :($(Core._eval_using)($(__module__), $(QuoteNode(mod_path)), $(Base.JL_MODULE_USING_REEXPORT))))
    end
    push!(calls.args, Expr(:latestworld))
    push!(calls.args, :nothing)

    return esc(calls)
end
```
-/
def reexportMacro {L : Type} (a : MacroAtoms L) (ex : Value L) : ExprResult (Value L) := do
  let .expr "using" paths := ex
    | throw (.errorException "@reexport must be used with a `using` statement, e.g., `@reexport using MyModule`")
  if paths.isEmpty then
    throw (.errorException "@reexport must be used with a `using` statement, e.g., `@reexport using MyModule`")
  if paths.any (fun path => isexpr path ":") then
    throw (.errorException "@reexport does not support `using Module: names` syntax")
  let calls := paths.map (fun path => Value.expr "call"
    [.leaf a.evalUsing, .leaf a.caller, .quoteNode path, .leaf a.usingReexport])
  pure (esc (.expr "block" (calls ++ [.expr "latestworld" [], .symbol "nothing"])))

/--
Julia source: base/experimental.jl:811-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro set_syntax_version(ver)
    Expr(:call, Base.set_syntax_version, __module__, esc(ver))
end
```
-/
def setSyntaxVersionMacro {L : Type} (a : MacroAtoms L) (ver : Value L) : Value L :=
  .expr "call" [.leaf a.setSyntaxVersion, .leaf a.caller, esc ver]

/--
Julia source: base/experimental.jl:828-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function var"@VERSION"(__source__::Union{LineNumberNode, Core.MacroSource}, __module__::Module)
    # This macro has special handling in the parser, which puts the current syntax
    # version into __source__.
    if isa(__source__, LineNumberNode)
        return :((; syntax = v"1.13", runtime = VERSION))
    else
        return :((; syntax = $(__source__.syntax_ver), runtime = VERSION))
    end
end
```
-/
def versionMacro {L : Type} (a : MacroAtoms L) (syntaxVersion : Option L) : Value L :=
  let syntaxExpr : Value L := match syntaxVersion with
    | some version => .leaf version
    | none => .expr "macrocall" [.symbol "@v_str",
        .lineNumberNode (JuliaLean.base.expr.i64 832) a.sourceFile, .leaf (a.ofString "1.13")]
  .expr "tuple" [.expr "parameters"
    [.expr "kw" [.symbol "syntax", syntaxExpr], .expr "kw" [.symbol "runtime", .symbol "VERSION"]]]

/--
Julia source: base/experimental.jl:410-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro overlay(mt, def)
    inner = Base.unwrap_macrocalls(def)
    if isexpr(inner, :block)
        # `@overlay mt begin ... end`: overlay every definition in the block
        for arg in inner.args
            isa(arg, LineNumberNode) && continue
            innerarg = Base.unwrap_macrocalls(arg)
            is_function_def(innerarg) || error("@overlay requires a function definition")
            overlay_def!(mt, innerarg)
        end
    else
        is_function_def(inner) || error("@overlay requires a function definition")
        overlay_def!(mt, inner)
    end
    return esc(def)
end
```
-/
def overlayMacro {L : Type} (mt defn : Value L) : ExprResult (Value L) := do
  let (inner, path) ← unwrap_macrocalls_path defn
  let updated ← if isexpr inner "block" then do
      let .expr head args := inner | throw .typeError
      let args ← args.mapM (fun arg => do
        if let .lineNumberNode _ _ := arg then return arg
        let (innerArg, argPath) ← unwrap_macrocalls_path arg
        if !is_function_def innerArg then throw (.errorException "@overlay requires a function definition")
        modifyAt (overlayDef mt) argPath arg)
      pure (.expr head args)
    else do
      if !is_function_def inner then throw (.errorException "@overlay requires a function definition")
      overlayDef mt inner
  pure (esc (← modifyAt (fun _ => pure updated) path defn))

/--
Julia source: base/experimental.jl:478-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro consistent_overlay(mt, def)
    inner = Base.unwrap_macrocalls(def)
    is_function_def(inner) || error("@consistent_overlay requires a function definition")
    overlay_def!(mt, inner)
    override = Base.EffectsOverride(; consistent_overlay=true)
    Base.pushmeta!(def::Expr, Base.form_purity_expr(override))
    return esc(def)
end
```
-/
def consistentOverlayMacro {L : Type} (lo : LeafOps L) (mt defn : Value L) :
    ExprResult (Value L) := do
  let (inner, path) ← unwrap_macrocalls_path defn
  if !is_function_def inner then throw (.errorException "@consistent_overlay requires a function definition")
  let updated ← modifyAt (overlayDef mt) path defn
  let override := EffectsOverride.kw (consistent_overlay := true)
  pure (esc (← pushmeta! updated (form_purity_expr lo override)))

/--
Julia source: base/experimental.jl:126-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro sync(block)
    var = esc(sync_varname)
    # like Base.@sync, the block runs in a new dynamic scope carrying the
    # token of a fresh cancellation source; on the fail-fast path (and on
    # cancellation from outside) the source is cancelled, reaching all
    # children through the token tree without awaiting them
    scoped_block = Expr(:tryfinally, esc(block), nothing,
        :(Base.Scope(Core.current_scope()::Union{Nothing, Base.Scope},
                     Base.CANCEL_TOKEN => Base.CancellationToken(var"#sync_src#"))))
    quote
        let var"#sync_src#" = Base.CancellationTokenSource(Base.default_cancel_token()),
            $var = Channel(Inf)
            v = $scoped_block
            sync_end($var, var"#sync_src#")
            v
        end
    end
end
```
-/
def syncMacro {L : Type} (a : MacroAtoms L) (syncVarname : Sym) (block : Value L) : Value L :=
  let src : Value L := .symbol "#sync_src#"
  let channel := esc (.symbol syncVarname)
  let call (fn : Value L) (args : List (Value L)) := Value.expr "call" (fn :: args)
  let base (name : Sym) := Value.expr "." [.symbol "Base", quoteSym name]
  let scope := call (base "Scope")
    [.expr "::" [call (.expr "." [.symbol "Core", quoteSym "current_scope"]) [],
      .expr "curly" [.symbol "Union", .symbol "Nothing", base "Scope"]],
     call (.symbol "=>") [base "CANCEL_TOKEN", call (base "CancellationToken") [src]]]
  let scopedBlock := Value.expr "tryfinally" [esc block, .leaf a.leaf.nothing, scope]
  let line (n : Int) := Value.lineNumberNode (JuliaLean.base.expr.i64 n) a.sourceFile
  .expr "block" [line 136, .expr "let" [.expr "block"
    [.expr "=" [src, call (base "CancellationTokenSource") [call (base "default_cancel_token") []]],
     .expr "=" [channel, call (.symbol "Channel") [.symbol "Inf"]]],
    .expr "block" [line 138, .expr "=" [.symbol "v", scopedBlock],
      line 139, call (.symbol "sync_end") [channel, src], line 140, .symbol "v"]]]

/--
Julia source: base/experimental.jl:530-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro make_all_arithmetic_checked()
    esc(quote
        Base.:(-)(x::Base.BitInteger)                         = Base.Checked.checked_neg(x)
        Base.:(-)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_sub(x, y)
        Base.:(-)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_sub(x, y)
        Base.:(+)(x::Base.Int, y::Base.Int)                    = Base.Checked.checked_add(x, y)
        Base.:(+)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_add(x, y)
        Base.:(*)(x::T, y::T) where {T<:Base.BitInteger}       = Base.Checked.checked_mul(x, y)
    end)
end
```
-/
def makeAllArithmeticCheckedMacro {L : Type} (sourceFile : Value L) : Value L :=
  let base : Value L := .symbol "Base"
  let dot (value : Value L) (name : Sym) := Value.expr "." [value, quoteSym name]
  let arg (name : Sym) (typ : Value L) := Value.expr "::" [.symbol name, typ]
  let line (n : Int) := Value.lineNumberNode (JuliaLean.base.expr.i64 n) sourceFile
  let definition (op : Sym) (args : List (Value L)) (checked : Sym) (names : List Sym)
      (typeParam : Bool) (sourceLine : Int) :=
    let signature := Value.expr "call" (dot base op :: args)
    let signature := if typeParam then
      Value.expr "where" [signature, .expr "<:" [.symbol "T", dot base "BitInteger"]]
      else signature
    Value.expr "=" [signature, .expr "block"
      [line sourceLine, .expr "call" (dot (dot base "Checked") checked :: names.map Value.symbol)]]
  esc (.expr "block"
    [line 532, definition "-" [arg "x" (dot base "BitInteger")] "checked_neg" ["x"] false 532,
     line 533, definition "-" [arg "x" (dot base "Int"), arg "y" (dot base "Int")] "checked_sub" ["x", "y"] false 533,
     line 534, definition "-" [arg "x" (.symbol "T"), arg "y" (.symbol "T")] "checked_sub" ["x", "y"] true 534,
     line 535, definition "+" [arg "x" (dot base "Int"), arg "y" (dot base "Int")] "checked_add" ["x", "y"] false 535,
     line 536, definition "+" [arg "x" (.symbol "T"), arg "y" (.symbol "T")] "checked_add" ["x", "y"] true 536,
     line 537, definition "*" [arg "x" (.symbol "T"), arg "y" (.symbol "T")] "checked_mul" ["x", "y"] true 537])


end JuliaLean.base.experimental

namespace JuliaLean.MiscCov.Experimental

open JuliaLean
/-! ## `Const` -/

/-- `Const(A::Array)`: the wrapped array, as its dimensions and column-major elements. -/
structure Const (V : Type) where
  dims : List Nat
  elems : List V

variable {V : Type}

/-- `Base.IndexStyle(::Type{<:Const}) = IndexLinear()`, `base/experimental.jl:29`. -/
def indexStyleLinear : Bool := true

/-- `Base.size(C::Const) = size(C.a)` and `Base.axes(C::Const) = axes(C.a)` (`:30-31`):
the sizes and the ranges `1:n`, here by their lengths. -/
def size (C : Const V) : List Nat := C.dims
def axes (C : Const V) : List (Nat × Nat) := C.dims.map (fun n => (1, n))

/-- `getindex(A::Const, i::Int)`, `base/experimental.jl:32-36`: `checkbounds(A.a, i)`
under `@boundscheck`, then the unchecked load of element `i`. -/
def getindex1 (A : Const V) (i : Int) : M V :=
  if 1 ≤ i ∧ i ≤ A.elems.length then
    match A.elems[(i - 1).toNat]? with
    | some v => .ok v
    | none => .error .boundsError
  else .error .boundsError

/-- `_to_linear_index(A.a, i1, i2, I...)`: the column-major linear index of `(i1, i2, I...)`
in an array of size `dims`,
`1 + Σ (i_k - 1) * prod(dims[1:k-1])`. -/
def linearIndex : List Nat → List Int → Int
  | _, [] => 1
  | [], i :: _ => i
  | d :: ds, i :: is => i + d * (linearIndex ds is - 1)

/-- `checkbounds(A.a, i1, i2, I...)`: every index within its dimension (trailing
dimensions are 1, trailing indices must be 1). -/
def inBounds : List Nat → List Int → Bool
  | _, [] => true
  | [], i :: is => i == 1 && inBounds [] is
  | d :: ds, i :: is => decide (1 ≤ i ∧ i ≤ d) && inBounds ds is

/-- `getindex(A::Const, i1::Int, i2::Int, I::Int...)`, `base/experimental.jl:37-41`:
bounds check, then `A[_to_linear_index(A.a, i1, i2, I...)]`. -/
def getindexN (A : Const V) (i1 i2 : Int) (I : List Int) : M V :=
  if inBounds A.dims (i1 :: i2 :: I) then getindex1 A (linearIndex A.dims (i1 :: i2 :: I))
  else .error .boundsError


/-! ## Expression macros -/

/-- `@aliasscope body`, `base/experimental.jl:52-60`. -/
def aliasscope (body : Ex) : Ex :=
  .expr "block" [.expr "aliasscope" [], .expr "=" [.sym "aliasscope_result", Ex.esc body],
    .expr "popaliasscope" [], .sym "aliasscope_result"]

/-- `@optlevel n::Int`, `base/experimental.jl:158-160`: no range check. -/
def optlevel (n : Ex) : M Ex :=
  match n with
  | .int k => .ok (.expr "meta" [.sym "optlevel", .int k])
  | _ => .error .methodError

/-- `@max_methods n::Int`, `base/experimental.jl:180-183`. -/
def maxMethods1 (n : Ex) : M Ex :=
  match n with
  | .int k =>
    if 1 ≤ k ∧ k ≤ 4 then .ok (.expr "meta" [.sym "max_methods", .int k])
    else .error (.errorException "We must have that `1 <= max_methods <= 4`")
  | _ => .error .methodError

/-- `@max_methods n::Int fdef::Expr`, `base/experimental.jl:193-197`. -/
def maxMethods2 (n fdef : Ex) : M Ex :=
  match n, fdef with
  | .int k, .expr hd args =>
    if ¬ (1 ≤ k ∧ k ≤ 255) then .error (.errorException "We must have that `1 <= max_methods <= 255`")
    else if ¬ (hd = "function" ∧ args.length = 1) then
      .error (.errorException "Second argument must be a function forward declaration")
    else .ok (.expr "=" [.expr "." [.expr "." [.expr "call" [.sym "typeof", Ex.esc (.expr hd args)],
        .qn (.sym "name")], .qn (.sym "max_methods")], .val s!"UInt8({k})"])
  | _, _ => .error .methodError


/-- `@compiler_options args...`, `base/experimental.jl:212-244`. -/
def compilerOption (ex : Ex) : M Ex :=
  match ex with
  | .expr "=" [.sym name, a] =>
    if name = "optimize" then
      match a with
      | .int k => .ok (.expr "meta" [.sym "optlevel", .int k])
      | _ => .error .typeError
    else if name = "compile" then
      if a.isSym "min" then .ok (.expr "meta" [.sym "compile", .int 3])
      else .error (.errorException "invalid argument to \"compile\" option")
    else if name = "infer" then
      match a with
      | .bool false => .ok (.expr "meta" [.sym "infer", .int 0])
      | .bool true => .ok (.expr "meta" [.sym "infer", .int 1])
      | .sym "no" => .ok (.expr "meta" [.sym "infer", .int 0])
      | .sym "yes" => .ok (.expr "meta" [.sym "infer", .int 1])
      | _ => .error (.errorException "invalid argument to \"infer\" option")
    else if name = "max_methods" then
      match a with
      | .sym "default" => .ok (.expr "meta" [.sym "max_methods", .int 3])
      | .int k =>
        if 1 ≤ k ∧ k ≤ 4 then .ok (.expr "meta" [.sym "max_methods", .int k])
        else .error (.errorException "We must have that `1 <= max_methods <= 4`")
      | _ => .error (.errorException "invalid argument to \"max_methods\" option")
    else .error (.errorException "unknown option")
  | .expr "=" [_, _] => .error (.errorException "unknown option")
  | _ => .error (.errorException "invalid option syntax")

def compilerOptions : List Ex → M (List Ex)
  | [] => .ok []
  | ex :: rest =>
    match compilerOption ex with
    | .error e => .error e
    | .ok m =>
      match compilerOptions rest with
      | .error e => .error e
      | .ok ms => .ok (m :: ms)

/-- `@force_compile`, `base/experimental.jl:268`. -/
def forceCompile : Ex := .expr "meta" [.sym "force_compile"]


/-! ## `@make_all_arithmetic_checked` -/

open JuliaLean.IntArith.Checked in
/-- The six methods `@make_all_arithmetic_checked` defines, `base/experimental.jl:530-539`:
`-x`, `x - y` (for `Int` and for any same-type `BitInteger`), `x + y` (likewise) and
`x * y` call `checked_neg`, `checked_sub`, `checked_add`, `checked_mul`. -/
def checkedNegM {t : IntTy} (x : JInt t) : Jl (JInt t) := checkedNeg x
open JuliaLean.IntArith.Checked in
def checkedSubInt (x y : JInt .i64) : Jl (JInt .i64) := checkedSub x y
open JuliaLean.IntArith.Checked in
def checkedSubM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedSub x y
open JuliaLean.IntArith.Checked in
def checkedAddInt (x y : JInt .i64) : Jl (JInt .i64) := checkedAdd x y
open JuliaLean.IntArith.Checked in
def checkedAddM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedAdd x y
open JuliaLean.IntArith.Checked in
def checkedMulM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedMul x y




/-- External results of `prune_objcache`: the cutoff conversion may throw, the
prune call returns an Int64, and a non-null compact error carries its message.
The foreign calls themselves are outside the Julia-level model. -/
structure ObjCacheInputs where
  enabled : Bool
  cutoff : M Int
  removed : Int
  compactError : Option String

/-- `base/experimental.jl:853-861`. The action list records which foreign
operations were reached, including the argument passed to each operation. -/
def pruneObjcache (dir : String) (i : ObjCacheInputs) : List String × M (Option Int) :=
  if !i.enabled then (["enabled"], .ok none)
  else match i.cutoff with
    | .error e => (["enabled"], .error e)
    | .ok cutoff =>
      let calls := ["enabled", "prune:" ++ toString cutoff]
      if i.removed < 0 then (calls, .error (.errorException "could not prune the native code cache"))
      else match i.compactError with
        | some err => (calls ++ ["compact:" ++ dir],
            .error (.errorException ("could not copy the native code cache to " ++ dir ++ ": " ++ err)))
        | none => (calls ++ ["compact:" ++ dir], .ok (some i.removed))

end JuliaLean.MiscCov.Experimental

namespace JuliaLean.MiscCov.Experimental
/-! ## `sync_end`, `base/experimental.jl:63-107` -/

/-- What `take!(c)` returns or throws: a waitable registered by `@async`/`@spawn`, the
`:__completion__` token a watcher puts after its waitable finished, or an exception
(a child failure delivered by `close(c, e)`, or a cancellation of the scope). -/
inductive Event where
  | task
  | completion
  | fail (cancellation : Bool)
  deriving DecidableEq, Repr

/-- The outcome of `sync_end`: normal return after spawning `watchers` watcher tasks,
the exception rethrown (with whether the block's source was cancelled), or still
blocked in `take!` when the events run out. -/
inductive SyncResult where
  | ok (watchers : Nat)
  | rethrown (srcCancelled : Bool) (watchers : Nat)
  | blocked
  deriving DecidableEq, Repr

/-- The `while true` loop of `sync_end`, on the sequence of `take!` results. -/
def syncLoop (hasSrc : Bool) : Int → Nat → List Event → SyncResult
  | _, _, [] => .blocked
  | n, w, .task :: es => syncLoop hasSrc (n + 1) (w + 1) es
  | n, w, .completion :: es => if n - 1 = 0 then .ok w else syncLoop hasSrc (n - 1) w es
  | _, w, .fail _ :: _ => .rethrown hasSrc w

/-- `sync_end(c, src)`: an empty channel is closed at once; otherwise the loop. -/
def syncEnd (ready : Bool) (hasSrc : Bool) (events : List Event) : SyncResult :=
  if !ready then .ok 0 else syncLoop hasSrc 0 0 events


/-- `Experimental.@sync block`, `base/experimental.jl:126-143`: a `let` that creates the
cancellation source and the channel, runs the block in a scope carrying the source's
token, then calls `sync_end` and returns the block's value. -/
def syncMacro (block : Ex) : Ex :=
  let var := Ex.esc (.sym "##sync#48")
  let blk := .expr "tryfinally" [Ex.esc block, .nothing,
    .expr "call" [.gref "Base" "Scope", .val "current_scope", .val "CANCEL_TOKEN => token(#sync_src#)"]]
  .expr "let" [.expr "block" [.expr "=" [.sym "#sync_src#", .val "CancellationTokenSource(default_cancel_token())"],
      .expr "=" [var, .val "Channel(Inf)"]],
    .expr "block" [.expr "=" [.sym "v", blk],
      .expr "call" [.sym "sync_end", var, .sym "#sync_src#"], .sym "v"]]


/-! ## Error hints, `base/experimental.jl:331-374` -/

/-- A Julia type for the hint machinery: its `TypeName` and supertype (`none` for `Any`). -/
structure HTy where
  name : Nat
  super : Option Nat
  deriving DecidableEq, Repr

/-- A registered handler: the exception type it was registered for and what it writes
(or throws). -/
structure Handler where
  exct : Nat
  run : Except String (List String)

/-- `_hint_handlers`: the handlers of each `TypeName`, in registration order (an absent
key has none). -/
abbrev HintTable := Nat → List Handler

/-- `register_error_hint(handler, exct)`: `push!(get!(Vector{Any}, _hint_handlers,
typename(exct)), (exct, handler))`. `tn` is `Core.typename(exct)`. -/
def registerErrorHint (r : HintTable) (tn : Nat) (h : Handler) : HintTable :=
  fun n => if n = tn then r n ++ [h] else r n

/-- Run the handlers of one `TypeName` whose `exct` the exception is an instance of
(`isa` given as `isaT`); a throwing handler is logged and the loop continues. -/
def runHandlers (isaT : Nat → Bool) : List Handler → List String
  | [] => []
  | h :: hs =>
    (if isaT h.exct then
      match h.run with
      | .ok out => out
      | .error _ => ["@error Hint-handler caused an error"]
    else []) ++ runHandlers isaT hs

/-- `show_error_hints(io, ex, args...)`: nothing while `_hints_disabled[]`; otherwise the
handlers of `typeof(ex)` and of each supertype below `Any`, most specific first.
`chain` lists the `TypeName`s from `typeof(ex)` up to (excluding) `Any`. -/
def showErrorHints (disabled : Bool) (r : HintTable) (isaT : Nat → Bool) (chain : List Nat) : List String :=
  if disabled then [] else chain.flatMap (fun tn => runHandlers isaT (r tn))


/-- `overlay_def!(mt, ex)`: in the first argument of `ex`, replace the called function of
the signature `f(args...)` by `Expr(:overlay, mt, f)`, looking through `::` and `where`. -/
def overlayDef (mt : Ex) : Nat → Ex → M Ex
  | 0, _ => .error (.other "fuel")
  | n + 1, .expr hd (arg1 :: rest) =>
    match arg1 with
    | .expr "call" (f :: cargs) => .ok (.expr hd (.expr "call" (.expr "overlay" [mt, f] :: cargs) :: rest))
    | .expr "::" _ | .expr "where" _ => do
      let a ← overlayDef mt n arg1
      pure (.expr hd (a :: rest))
    | _ => .error (.errorException "@overlay requires a function definition")
  | _, _ => .error .boundsError

/-- Apply `f` to the definition inside nested macro calls, rebuilding them. -/
def mapUnwrapped (f : Ex → M Ex) : Nat → Ex → M Ex
  | 0, ex => f ex
  | n + 1, .expr "macrocall" args =>
    match args.getLast? with
    | some a => do
      let a' ← mapUnwrapped f n a
      pure (.expr "macrocall" (args.dropLast ++ [a']))
    | none => f (.expr "macrocall" args)
  | _, ex => f ex

def overlayOne (mt : Ex) (ex : Ex) : M Ex :=
  if isFunctionDef ex then overlayDef mt 100 ex
  else .error (.errorException "@overlay requires a function definition")

/-- `@overlay mt def`, `base/experimental.jl:410-425`. -/
def overlay (mt def_ : Ex) : M Ex := do
  let inner := unwrapMacrocalls 100 def_
  if inner.isExpr "block" then
    let args := inner.args?.getD []
    let args' ← args.mapM (fun arg =>
      if arg.isLnn then pure arg else mapUnwrapped (overlayOne mt) 100 arg)
    let rebuilt ← mapUnwrapped (fun _ => pure (.expr "block" args')) 100 def_
    pure (Ex.esc rebuilt)
  else do
    let d ← mapUnwrapped (overlayOne mt) 100 def_
    pure (Ex.esc d)

/-- `@consistent_overlay mt def`, `base/experimental.jl:478-485`: one definition, plus
the `:consistent_overlay` purity `:meta` pushed into its body. -/
def consistentOverlay (mt def_ : Ex) : M Ex := do
  let d ← mapUnwrapped (overlayOne mt) 100 def_
  pure (Ex.esc (.expr "pushmeta" [d, .val "purity(consistent_overlay=true)"]))


/-! ## `@MethodTable`, `base/experimental.jl:501-509` -/

/-- `new_mt(name, mod)`: `jl_check_top_level_effect` (which may throw), then a fresh
method table named `name` owned by `mod`. -/
def newMt (checkTopLevel : M Unit) (name mod : String) : M (String × String) := do
  checkTopLevel
  pure (name, mod)

/-- `@MethodTable name` expands to `const name = new_mt(:name, __module__)`. -/
def methodTableMacro (name mod : String) : Ex :=
  Ex.esc (.expr "const" [.expr "=" [.sym name, .expr "call" [.val "new_mt", .qn (.sym name), .val mod]]])


/-! ## `make_io_thread`, `entrypoint`, `disable_new_worlds`, `task_metrics` -/

/-- `make_io_thread()`, `base/experimental.jl:548-562`: `createErr` and `detachErr` are
the return codes of `uv_thread_create` and `uv_thread_detach`. The check after the
detach call tests `err`, which still holds the create result. -/
def makeIoThread (createErr detachErr : Int) : M Unit :=
  if createErr ≠ 0 then .error (.other "IOError: uv_thread_create")
  else
    let _ := detachErr
    if createErr ≠ 0 then .error (.other "IOError: uv_thread_detach") else .ok ()

/-- Runtime flags touched by `entrypoint`, `disable_new_worlds` and `task_metrics`. -/
structure RtFlags where
  entrypoints : List String
  newWorldsDisabled : Bool
  metricsEnabled : Bool
  deriving DecidableEq, Repr

/-- `entrypoint(argt::Type)`, `base/experimental.jl:573-579`. -/
def entrypointT (generatingOutput : Bool) (s : RtFlags) (argt : String) : RtFlags :=
  if generatingOutput then { s with entrypoints := s.entrypoints ++ [argt] } else s

/-- `entrypoint(f, argtypes::Tuple) = entrypoint(Tuple{Core.Typeof(f), argtypes...})`,
`base/experimental.jl:569-571`. -/
def entrypointF (generatingOutput : Bool) (s : RtFlags) (typeofF : String) (argtypes : List String) : RtFlags :=
  entrypointT generatingOutput s ("Tuple{" ++ String.intercalate ", " (typeofF :: argtypes) ++ "}")

/-- `disable_new_worlds()`, `base/experimental.jl:588`. -/
def disableNewWorlds (s : RtFlags) : RtFlags := { s with newWorldsDisabled := true }

/-- `task_metrics(b::Bool)`, `base/experimental.jl:603-610`. -/
def taskMetrics (s : RtFlags) (b : Bool) : RtFlags := { s with metricsEnabled := b }

/-- A `Task`'s metric fields (`UInt64` nanoseconds). -/
structure TaskM where
  id : Nat
  metricsEnabled : Bool
  runningTimeNs : Nat
  lastStartedRunningAt : Nat
  firstEnqueuedAt : Nat
  finishedAt : Nat

/-- `x -% y` and `x +% y` on `UInt64`. -/
def subW (x y : Nat) : Nat := (x + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64
def addW (x y : Nat) : Nat := (x + y) % 2 ^ 64

/-- `task_running_time_ns(t)`, `base/experimental.jl:630-639`; `current` is
`current_task()` and `now` is `time_ns()`. -/
def taskRunningTimeNs (t current : TaskM) (now : Nat) : Option Nat :=
  if !t.metricsEnabled then none
  else if t.id = current.id then some (addW t.runningTimeNs (subW now t.lastStartedRunningAt))
  else some t.runningTimeNs

/-- `task_wall_time_ns(t)`, `base/experimental.jl:655-662`. -/
def taskWallTimeNs (t : TaskM) (now : Nat) : Option Nat :=
  if !t.metricsEnabled then none
  else if t.firstEnqueuedAt = 0 then some 0
  else if t.finishedAt = 0 then some (subW now t.firstEnqueuedAt)
  else some (subW t.finishedAt t.firstEnqueuedAt)


/-! ## `wait_with_timeout`, `base/experimental.jl:690-719` -/

/-- The waitables `wait_with_timeout` parks on. -/
inductive Waitable where
  | cond | source | timeout
  deriving DecidableEq, Repr

/-- Observable steps: park, withdraw with a wake reason, lock depth changes, and the
outcome. -/
inductive Step where
  | park (ws : List Waitable)
  | withdrawFired
  | withdrawValue
  | unlock
  | relock
  deriving DecidableEq, Repr

inductive WaitOutcome (V : Type) where
  | value (v : V)
  | throws (e : Err)

/-- `wait_with_timeout(c; first, timeout, cancel)`: `parked` is the result of `park!`,
`cancelled` whether `checkcancel(src)` throws, and `wait` the result of
`wait_safe_interrupt`. -/
def waitWithTimeout {V : Type} (timeout : Int) (hasSrc parked cancelled : Bool) (wait : Except Err V) :
    List Step × WaitOutcome V :=
  let ws := if timeout > 0 then (if hasSrc then [.cond, .source, .timeout] else [.cond, .timeout])
    else (if hasSrc then [.cond, .source] else [.cond])
  if !parked then
    ([.park ws, .withdrawFired],
      if hasSrc && cancelled then .throws (.other "CancellationRequest")
      else .throws (.errorException "park fired without a cancelled source"))
  else
    match wait with
    | .error e => ([.park ws, .unlock, .relock], .throws e)
    | .ok v => ([.park ws, .unlock, .relock, .withdrawValue], .value v)





/-! ## `@reexport`, `set_syntax_version`, `@VERSION` -/

/-- `@reexport ex`, `base/experimental.jl:751-770`. -/
def reexport (mod : String) (ex : Ex) : M Ex :=
  match ex with
  | .expr "using" (a :: as) =>
    if (a :: as).any (·.isExpr ":") then .error (.errorException "@reexport does not support `using Module: names` syntax")
    else .ok (Ex.esc (.expr "block" (((a :: as).map fun p =>
      .expr "call" [.val "Core._eval_using", .val mod, .qn p, .val "JL_MODULE_USING_REEXPORT"]) ++
      [.expr "latestworld" [], .sym "nothing"])))
  | _ => .error (.errorException "@reexport must be used with a `using` statement")

/-- `Base.set_syntax_version(m, edition::Tuple{Int,Int})` declares the constant
`#_internal_julia_parse` of `m` as `VersionedParse(edition)`, `base/experimental.jl:772-776`;
`set_syntax_version(mod, e::VersionNumber)` uses `EditionNumber(e)`, the major and
minor version (`:777-778`). The module is the list of its declared constants. -/
def setSyntaxVersion (m : List (String × (Int × Int))) (edition : Int × Int) : List (String × (Int × Int)) :=
  m ++ [("#_internal_julia_parse", edition)]

def setSyntaxVersionV (m : List (String × (Int × Int))) (major minor patch : Int) : List (String × (Int × Int)) :=
  let _ := patch
  setSyntaxVersion m (major, minor)

/-- `@set_syntax_version ver`, `base/experimental.jl:811-813`. -/
def setSyntaxVersionMacro (mod : String) (ver : Ex) : Ex :=
  .expr "call" [.gref "Base" "set_syntax_version", .val mod, Ex.esc ver]

/-- `@VERSION`, `base/experimental.jl:828-836`: the parser puts the syntax version into a
`MacroSource`; a plain `LineNumberNode` means 1.13. -/
def versionMacro (source : Option String) : Ex :=
  match source with
  | none => .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val "v\"1.13\""],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]]
  | some v => .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val v],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]]

end JuliaLean.MiscCov.Experimental
