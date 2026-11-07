import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.Core
import JuliaLean.Runtime.Collections
import JuliaLean.base.hashing
import JuliaLean.base.locks_mt

/-!
# Model of `base/gcutils.jl`

Typed wrappers for weak references, finalization, and garbage-collection calls at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Julia's weak-reference values and finalizer/runtime
operations are typed interfaces. C-runtime GC behavior and object lifetime are not inferred.
`GC.@preserve` expansion remains visible because it creates a compiler-specific expression.
-/

namespace JuliaLean.base.gcutils

open JuliaLean

-- UNTRANSLATED
-- Source: base/gcutils.jl:1-1 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- /Source
-- Reason: The file license header has no executable behavior.
/--
Julia source: base/gcutils.jl:4-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    WeakRef(x)

`w = WeakRef(x)` constructs a mutable [weak reference](https://en.wikipedia.org/wiki/Weak_reference)
to the Julia value `x`: although `w` contains a reference to `x`, it does not prevent `x` from being
garbage collected. The referenced value can be accessed or replaced with `w.value`. If the referenced
value gets garbage-collected, `w.value` will be set to `nothing`.

```jldoctest
julia> x = "one string"
"one string"

julia> w = WeakRef(x)
WeakRef("one string")

julia> x2 = "another string"; w.value = x2
"another string"

julia> GC.gc()

julia> w           # a reference is maintained via `x2`
WeakRef("another string")

julia> x2 = nothing # clear reference

julia> GC.gc()

julia> w
WeakRef(nothing)
```
"""
WeakRef
````
-/
abbrev WeakRef (Value : Type) := JuliaLean.base.hashing.WeakRef (Option Value)

structure WeakRefEqualityOps (Value : Type) where
  isequalWeakWeak : Option Value → Option Value → Bool
  isequalWeakValue : {Other : Type} → Option Value → Other → Bool
  isequalValueWeak : {Other : Type} → Other → Option Value → Bool

/--
Julia source: base/gcutils.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(w::WeakRef, v::WeakRef) = isequal(w.value, v.value)
```
-/
def weakRefEqualWeak {Value : Type} (ops : WeakRefEqualityOps Value)
    (w v : WeakRef Value) : Bool := ops.isequalWeakWeak w.value v.value

/--
Julia source: base/gcutils.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(w::WeakRef, v) = isequal(w.value, v)
```
-/
def weakRefEqualValue {Value Other : Type} (ops : WeakRefEqualityOps Value)
    (w : WeakRef Value) (v : Other) : Bool := ops.isequalWeakValue w.value v

/--
Julia source: base/gcutils.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(w, v::WeakRef) = isequal(w, v.value)
```
-/
def valueEqualWeakRef {Value Other : Type} (ops : WeakRefEqualityOps Other)
    (w : Value) (v : WeakRef Other) : Bool := ops.isequalValueWeak w v.value

/--
Julia source: base/gcutils.jl:41-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Used by `Base.finalizer` to validate mutability of an object being finalized.
function _check_mutable(@nospecialize(o)) @noinline
    if !ismutable(o)
        error("objects of type ", typeof(o), " cannot be finalized because they are not mutable")
    end
end
```
-/
structure GcOps (m : Type → Type)
    (Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type) where
  isMutable : Object → Bool
  typeName : Object → String
  errorException : String → Error
  registerFinalizer : Finalizer → Object → m Unit
  currentThreadState : m ThreadState
  registerPointerFinalizer : ThreadState → Object → Finalizer → m Unit
  currentTask : m Task
  finalizeObject : Task → Object → m Unit
  collect : JInt .i32 → m Unit
  setEnabled : JInt .i32 → m (JInt .i32)
  enableFinalizersInternal : m Unit
  pendingFinalizers : MemoryOrder → m (JInt .i32)
  runPendingFinalizers : Pointer → m Unit
  disableFinalizersInternal : m Unit
  inFinalizer : m (JInt .i8)
  safepoint : m Unit
  setLogging : JInt .i32 → m Unit
  loggingEnabled : m (JInt .i32)
  activeImplementation : m Pointer
  unsafeString : Pointer → m String
  nullPointer : Pointer
  monotonicOrder : MemoryOrder
  preserveRoots : {A : Type} → List Object → m A → m A

/-- The runtime root effect associated with `GC.@preserve` after macro expansion. -/
def withPreservedRoots {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error A : Type}
    (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (objects : List Object) (body : m A) : m A := ops.preserveRoots objects body

def checkMutable {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] [MonadExceptOf Error m]
    (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (object : Object) : m Unit := do
  if !ops.isMutable object then
    throw (ops.errorException ("objects of type " ++ ops.typeName object ++
      " cannot be finalized because they are not mutable"))

/--
Julia source: base/gcutils.jl:48-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    finalizer(f, x)

Register a function `f(x)` to be called when there are no program-accessible references to
`x`, and return `x`. The type of `x` must be a `mutable struct`, otherwise the function
will throw.

`f` must not cause a task switch, which excludes most I/O operations such as `println`.
Using the `@async` macro (to defer context switching to outside of the finalizer) or
`ccall` to directly invoke IO functions in C may be helpful for debugging purposes.

Note that there is no guaranteed world age for the execution of `f`. It may be
called in the world age in which the finalizer was registered or any later world age.

# Examples
```julia
finalizer(my_mutable_struct) do x
    @async println("Finalizing \$x.")
end

finalizer(my_mutable_struct) do x
    ccall(:jl_safe_printf, Cvoid, (Cstring, Cstring), "Finalizing %s.", repr(x))
end
```

A finalizer may be registered at object construction. In the following example note that
we implicitly rely on the finalizer returning the newly created mutable struct `x`.

```julia
mutable struct MyMutableStruct
    bar
    function MyMutableStruct(bar)
        x = new(bar)
        f(t) = @async println("Finalizing \$t.")
        finalizer(f, x)
    end
end
```
"""
function finalizer(@nospecialize(f), @nospecialize(o))
    _check_mutable(o)
    Core.finalizer(f, o)
    return o
end
````
-/
def finalizer {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] [MonadExceptOf Error m]
    (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (f : Finalizer) (object : Object) : m Object := do
  checkMutable ops object
  ops.registerFinalizer f object
  pure object

/--
Julia source: base/gcutils.jl:93-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function finalizer(f::Ptr{Cvoid}, o::T) where T @inline
    _check_mutable(o)
    ccall(:jl_gc_add_ptr_finalizer, Cvoid, (Ptr{Cvoid}, Any, Ptr{Cvoid}),
          Core.getptls(), o, f)
    return o
end
```
-/
def finalizerPointer {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] [MonadExceptOf Error m]
    (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (f : Finalizer) (object : Object) : m Object := do
  checkMutable ops object
  let threadState ← ops.currentThreadState
  ops.registerPointerFinalizer threadState object f
  pure object

/--
Julia source: base/gcutils.jl:100-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    finalize(x)

Immediately run finalizers registered for object `x`.
"""
finalize(@nospecialize(o)) = ccall(:jl_finalize_th, Cvoid, (Any, Any,),
                                   current_task(), o)
```
-/
def finalizeNow {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m]
    (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (object : Object) : m Unit := do
  let task ← ops.currentTask
  ops.finalizeObject task object

-- UNTRANSLATED
-- Source: base/gcutils.jl:108-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.GC
-- 
-- Module with garbage collection utilities.
-- """
-- module GC
-- 
-- public gc, enable, @preserve, safepoint, enable_logging, logging_enabled
-- /Source
-- Reason: The Julia submodule and its public-export declaration are represented by the nested Lean namespace.
namespace GC

/--
Julia source: base/gcutils.jl:117-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# mirrored from julia.h
const GC_AUTO = 0
```
-/

def gcAuto : JInt .i32 := JInt.lit .i32 0

/--
Julia source: base/gcutils.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const GC_FULL = 1
```
-/
def gcFull : JInt .i32 := JInt.lit .i32 1

/--
Julia source: base/gcutils.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const GC_INCREMENTAL = 2
```
-/
def gcIncremental : JInt .i32 := JInt.lit .i32 2

/--
Julia source: base/gcutils.jl:122-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.gc([full=true])

Perform garbage collection. The argument `full` determines the kind of
collection: a full collection (default) traverses all live objects (i.e. full mark)
and should reclaim memory from all unreachable objects. An incremental collection only
reclaims memory from young objects which are not reachable.

The GC may decide to perform a full collection even if an incremental collection was
requested.

!!! warning
    Excessive use will likely lead to poor performance.
"""
gc(full::Bool=true) =
    ccall(:jl_gc_collect, Cvoid, (Cint,), full ? GC_FULL : GC_INCREMENTAL)
```
-/
def gc {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (full : Bool := true) : m Unit :=
  ops.collect (if full then gcFull else gcIncremental)

/--
Julia source: base/gcutils.jl:139-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.enable(on::Bool)

Control whether garbage collection is enabled using a boolean argument (`true` for enabled,
`false` for disabled). Return previous GC state.

!!! warning
    Disabling garbage collection should be used only with caution, as it can cause memory
    use to grow without bound.
"""
enable(on::Bool) = ccall(:jl_gc_enable, Int32, (Int32,), on) != 0
```
-/
def enable {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (on : Bool) : m Bool := do
  let requested := if on then JInt.lit .i32 1 else JInt.lit .i32 0
  pure ((← ops.setEnabled requested).val != 0)

/--
Julia source: base/gcutils.jl:151-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.enable_finalizers(on::Bool)

Increment or decrement the counter that controls the running of finalizers on
the current Task. Finalizers will only run when the counter is at zero. (Set
`true` for enabling, `false` for disabling). They may still run concurrently on
another Task or thread.
"""
enable_finalizers(on::Bool) = on ? enable_finalizers() : disable_finalizers()
```
-/
def enableFinalizersOn {m : Type → Type} [Monad m]
    (enableFinalizers disableFinalizers : Unit → m Unit) (on : Bool) : m Unit :=
  if on then enableFinalizers () else disableFinalizers ()

/--
Julia source: base/gcutils.jl:161-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function enable_finalizers() @inline
    ccall(:jl_gc_enable_finalizers_internal, Cvoid, ())
    if unsafe_load(cglobal(:jl_gc_have_pending_finalizers, Cint), :monotonic) != 0
        ccall(:jl_gc_run_pending_finalizers, Cvoid, (Ptr{Cvoid},), C_NULL)
    end
end
```
-/
def enableFinalizers {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m Unit := do
  ops.enableFinalizersInternal
  let pending ← ops.pendingFinalizers ops.monotonicOrder
  if pending.val != 0 then ops.runPendingFinalizers ops.nullPointer

/--
Julia source: base/gcutils.jl:168-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function disable_finalizers() @inline
    ccall(:jl_gc_disable_finalizers_internal, Cvoid, ())
end
```
-/
def disableFinalizers {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m Unit :=
  ops.disableFinalizersInternal

/--
Julia source: base/gcutils.jl:172-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.in_finalizer()::Bool

Return `true` if the current task is running a finalizer, return `false`
otherwise. Will also return `false` within a finalizer which was inlined by the
compiler's eager finalization optimization, or if `finalize` is called on the
finalizer directly.

The result of this function may be useful, for example, when a finalizer must
wait on a resource to become available; instead of polling the resource in a
`yield` loop (which is not legal to execute within a task running finalizers),
busy polling or an `@async` continuation could be used instead.
"""
function in_finalizer() @inline
    ccall(:jl_gc_is_in_finalizer, Int8, ()) > 0
end
```
-/
def inFinalizer {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m Bool := do
  pure (decide (0 < (← ops.inFinalizer).val))

-- UNTRANSLATED
-- Source: base/gcutils.jl:189-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     GC.@preserve x1 x2 ... xn expr
-- 
-- Mark the objects `x1, x2, ...` as being *in use* during the evaluation of the
-- expression `expr`. This is only required in unsafe code where `expr`
-- *implicitly uses* memory or other resources owned by one of the `x`s.
-- 
-- *Implicit use* of `x` covers any indirect use of resources logically owned by
-- `x` which the compiler cannot see. Some examples:
-- * Accessing memory of an object directly via a `Ptr`
-- * Passing a pointer to `x` to `ccall`
-- * Using resources of `x` which would be cleaned up in the finalizer.
-- 
-- `@preserve` should generally not have any performance impact in typical use
-- cases where it briefly extends object lifetime. In implementation, `@preserve`
-- has effects such as protecting dynamically allocated objects from garbage
-- collection.
-- 
-- # Examples
-- 
-- When loading from a pointer with `unsafe_load`, the underlying object is
-- implicitly used, for example `x` is implicitly used by `unsafe_load(p)` in the
-- following:
-- 
-- ```jldoctest
-- julia> let
--            x = Ref{Int}(101)
--            p = Base.unsafe_convert(Ptr{Int}, x)
--            GC.@preserve x unsafe_load(p)
--        end
-- 101
-- ```
-- 
-- When passing pointers to `ccall`, the pointed-to object is implicitly used and
-- should be preserved. (Note however that you should normally just pass `x`
-- directly to `ccall` which counts as an explicit use.)
-- 
-- ```jldoctest
-- julia> let
--            x = "Hello"
--            p = pointer(x)
--            Int(GC.@preserve x @ccall strlen(p::Cstring)::Csize_t)
--            # Preferred alternative
--            Int(@ccall strlen(x::Cstring)::Csize_t)
--        end
-- 5
-- ```
-- """
-- macro preserve(args...)
--     syms = args[1:end-1]
--     for x in syms
--         isa(x, Symbol) || error("Preserved variable must be a symbol")
--     end
--     esc(Expr(:gc_preserve, args[end], syms...))
-- end
-- /Source
-- Reason: The macro validates syntax and constructs `Expr(:gc_preserve, ...)`; compiler root-lifetime behavior is not a runtime function body.
/--
Julia source: base/gcutils.jl:245-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.safepoint()

Inserts a point in the program where garbage collection may run.

Safepoints are fast and do not themselves trigger garbage collection.
However, if another thread has requested the GC to run, reaching a safepoint will
cause the current thread to block and wait for the GC.

This can be useful in rare cases in multi-threaded programs where some tasks
are allocating memory (and hence may need to run GC) but other tasks are doing
only simple operations (no allocation, task switches, or I/O), which do not
yield control to Julia's runtime, and therefore blocks the GC from running.
Calling this function periodically in the non-allocating tasks allows garbage
collection to run.

Note that even though safepoints are fast (typically around 2 clock cycles),
they can still degrade performance if called in a tight loop.

!!! compat "Julia 1.4"
    This function is available as of Julia 1.4.
"""
safepoint() = ccall(:jl_gc_safepoint, Cvoid, ())
```
-/
def safepoint {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m Unit :=
  ops.safepoint

/--
Julia source: base/gcutils.jl:269-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.enable_logging(on::Bool)

When turned on, print statistics about each GC to stderr.
"""
function enable_logging(on::Bool=true)
    ccall(:jl_enable_gc_logging, Cvoid, (Cint,), on)
end
```
-/
def enableLogging {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (on : Bool := true) : m Unit :=
  ops.setLogging (if on then JInt.lit .i32 1 else JInt.lit .i32 0)

/--
Julia source: base/gcutils.jl:278-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.logging_enabled()

Return whether GC logging has been enabled via [`GC.enable_logging`](@ref).
"""
function logging_enabled()
    ccall(:jl_is_gc_logging_enabled, Cint, ()) != 0
end
```
-/
def loggingEnabled {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m Bool := do
  pure ((← ops.loggingEnabled).val != 0)

/--
Julia source: base/gcutils.jl:287-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    GC.gc_active_impl()

Return a string stating which GC implementation is being used and possibly
its version according to the list of supported GCs
"""
function gc_active_impl()
    unsafe_string(ccall(:jl_gc_active_impl, Ptr{UInt8}, ()))
end
```
-/
def gcActiveImpl {m : Type → Type} {Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type}
    [Monad m] (ops : GcOps m Object Finalizer ThreadState Pointer Task MemoryOrder Error) : m String := do
  ops.unsafeString (← ops.activeImplementation)

end GC

-- UNTRANSLATED
-- Source: base/gcutils.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module GC
-- /Source
-- Reason: The closing delimiter is represented by the Lean namespace terminator.
end JuliaLean.base.gcutils

namespace JuliaLean.ConcurrencyCov.GcUtils

open JuliaLean.ConcurrencyCov

structure Weak where value : Option Nat
  deriving DecidableEq, Repr

def weakEq (a b : Weak) : Bool := a.value == b.value
def weakEqValue (a : Weak) (b : Option Nat) : Bool := a.value == b
def valueEqWeak (a : Option Nat) (b : Weak) : Bool := a == b.value

def checkMutable (mutable : Bool) : R Unit :=
  if mutable then .ok () else .error (.errorException "object cannot be finalized because it is not mutable")

structure FinalizerState where registered : Nat := 0
  deriving DecidableEq, Repr

def addFinalizer (mutable : Bool) (object : Nat) (s : FinalizerState) : R (Nat × FinalizerState) := do
  checkMutable mutable
  return (object, { registered := s.registered + 1 })

def addPointerFinalizer := addFinalizer
def finalize (object : Nat) : Nat := object

inductive CollectionKind where | full | incremental
  deriving DecidableEq, Repr
def gc (full : Bool := true) : CollectionKind := if full then .full else .incremental

structure Runtime where
  gcEnabled : Bool
  finalizerDepth : Nat
  pendingFinalizers : Bool
  inFinalizer : Bool
  logging : Bool
  activeImpl : String
  safepoints : Nat := 0
  deriving DecidableEq, Repr

def enable (on : Bool) (rt : Runtime) : Bool × Runtime :=
  (rt.gcEnabled, { rt with gcEnabled := on })

def enableFinalizers (rt : Runtime) : Runtime :=
  { rt with finalizerDepth := rt.finalizerDepth - 1, pendingFinalizers := false }
def disableFinalizers (rt : Runtime) : Runtime :=
  { rt with finalizerDepth := rt.finalizerDepth + 1 }
def setFinalizers (on : Bool) (rt : Runtime) : Runtime :=
  if on then enableFinalizers rt else disableFinalizers rt

def inFinalizer (rt : Runtime) : Bool := rt.inFinalizer
def preserve (symbols : List String) (outcome : Outcome) : R Nat :=
  if symbols.all (· != "") then outcome else .error (.errorException "Preserved variable must be a symbol")
def safepoint (rt : Runtime) : Runtime := { rt with safepoints := rt.safepoints + 1 }
def enableLogging (on : Bool) (rt : Runtime) : Runtime := { rt with logging := on }
def loggingEnabled (rt : Runtime) : Bool := rt.logging
def gcActiveImpl (rt : Runtime) : String := rt.activeImpl

end JuliaLean.ConcurrencyCov.GcUtils

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

/-! ## `base/gcutils.jl` -/

structure Weak (α : Type) where value : α

def weakWeakEq (isequal : Nat → Nat → Bool) (a b : Weak Nat) := isequal a.value b.value

def weakValueEq (isequal : Nat → Nat → Bool) (a : Weak Nat) (b : Nat) := isequal a.value b

def valueWeakEq (isequal : Nat → Nat → Bool) (a : Nat) (b : Weak Nat) := isequal a b.value

def checkMutable (isMutable : Bool) (objectType : String) : R Unit :=
  if !isMutable then .error (.errorException s!"objects of type {objectType} cannot be finalized because they are not mutable")
  else .ok ()

def finalizer (check : Nat → R Unit) (register : Nat → Nat → Unit) (f o : Nat) : R Nat := do
  check o
  let _ := register f o
  return o

def pointerFinalizer (check : Nat → R Unit) (register : Nat → Nat → Unit) (f o : Nat) : R Nat := do
  check o
  let _ := register f o
  return o

def finalize (ccall : Nat → Unit) (task object : Nat) : Unit := ccall (task + object)

def gc (collect : Int → Unit) (full : Bool := true) : Unit := collect (if full then 1 else 2)

def gcEnable (enable : Bool → Bool) (on : Bool) : Bool := enable on

def setFinalizers (enable disable : Unit → Unit) (on : Bool) : Unit :=
  if on then enable () else disable ()

def enableFinalizers (enable : Unit → Unit) (pending : Bool) (runPending : Unit → Unit) : Unit :=
  let _ := enable ()
  if pending then runPending () else ()

def disableFinalizers (disable : Unit → Unit) : Unit := disable ()

def inFinalizer (ccall : Unit → Int) : Bool := ccall () > 0

inductive PreserveArg where | symbol (name : String) | other
  deriving DecidableEq, Repr

def preserve (args : List PreserveArg) (body : R Nat) : R Nat :=
  if args.all (fun x => match x with | .symbol _ => true | .other => false)
  then body else .error (.errorException "Preserved variable must be a symbol")

def safepoint (ccall : Unit → Unit) : Unit := ccall ()

def enableLogging (ccall : Bool → Unit) (on : Bool := true) : Unit := ccall on

def loggingEnabled (ccall : Unit → Int) : Bool := ccall () != 0

def gcActiveImpl (ccall : Unit → String) : String := ccall ()

end JuliaLean.ConcurrencyCov.FaithfulSmall

namespace JuliaLean.IdDicts

/-- Objects that `finalizer` accepts (mutable types; base/gcutils.jl:42-45). -/
def finalizable : JVal → Bool
  | .str _ | .vec _ _ | .fvec _ _ => true
  | _ => false

end JuliaLean.IdDicts
