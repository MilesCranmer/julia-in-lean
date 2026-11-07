import JuliaLean.Proofs.base.locks_mt.common
import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int

/-!
# Model of `base/atomics.jl`

`Threads.Atomic{T}` and the `atomic_*` functions of Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. An `Atomic` is a reference `A` into the mutable world
whose single `@atomic value::T` field is accessed through the runtime's field builtins
(`getfield`, `setfield!`, `swapfield!`, `modifyfield!`, `replacefield!`, `setfieldonce!`), each
carrying its memory ordering. The builtins, memory fences and the element type's own methods
(`zero`, `convert`, and the operators applied by `modifyfield!`) are typed parameters with no
assumed laws.
-/

namespace JuliaLean.base.atomics

open JuliaLean
open JuliaLean.base.io (M Error)

/-- A memory-ordering `Symbol`. -/
inductive Order where
  | notatomic
  | unordered
  | monotonic
  | acquire
  | release
  | acquire_release
  | sequentially_consistent
  deriving DecidableEq, Repr

/-- The synchronization scope of a fence. -/
inductive Scope where
  | system
  | singlethread
  deriving DecidableEq, Repr

/-- The runtime builtins on the `value` field of `Atomic` references `A` holding a `T`. -/
structure Fields (World A T : Type) where
  /-- `new(value)`. -/
  new : T → M World A
  getfield : A → Order → M World T
  setfield : A → T → Order → M World T
  swapfield : A → T → Order → M World T
  /-- `modifyfield!(x, :value, op, v, order)`: the old and new values. -/
  modifyfield : A → (T → T → M World T) → T → Order → M World (T × T)
  /-- `replacefield!(x, :value, expected, desired, success, fail)`: the old value and whether
  it was replaced. -/
  replacefield : A → T → T → Order → Order → M World (T × Bool)
  setfieldonce : A → T → Order → Order → M World Bool

/-- The element type's methods. -/
structure ElementOps (World T V : Type) where
  zero : M World T
  /-- `v isa T ? v : convert(T, v)::T`. -/
  toT : V → M World T
  add : T → T → M World T
  sub : T → T → M World T
  band : T → T → M World T
  bor : T → T → M World T
  bxor : T → T → M World T
  bnot : T → M World T
  min : T → T → M World T
  max : T → T → M World T

/-- `Core.Intrinsics.atomic_fence` and `ccall(:jl_membarrier, ...)`. -/
structure Fences (World : Type) where
  fence : Order → Scope → M World Unit
  membarrier : M World Unit

section
variable {World A T V : Type} (f : Fields World A T) (e : ElementOps World T V)

-- Reason: The license line has no method.
-- UNTRANSLATED
-- Source: base/atomics.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /Source

-- Reason: The imports and the export list are load-time structure.
-- UNTRANSLATED
-- Source: base/atomics.jl:3-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- import .Base: getindex
-- import .Base: getindex_atomic, setindex_atomic!, swapindex_atomic!, modifyindex_atomic!,
--     replaceindex_atomic!, setindexonce_atomic!
-- 
-- export
--     Atomic,
--     atomic_cas!,
--     atomic_xchg!,
--     atomic_add!, atomic_sub!,
--     atomic_and!, atomic_nand!, atomic_or!, atomic_xor!,
--     atomic_max!, atomic_min!,
--     atomic_fence, atomic_fence_light, atomic_fence_heavy
-- 
-- /Source

/--
Julia source: base/atomics.jl:16-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Threads.Atomic{T}

Holds a reference to an object of type `T`, ensuring that it is only
accessed atomically, i.e. in a thread-safe manner.

New atomic objects can be created from a non-atomic values; if none is
specified, the atomic object is initialized with zero.

`Atomic` is a standalone, [`Ref`](@ref)-like atomic cell. Like `Ref`, it is a
useful building block and is not going away, but an `@atomic` field of a mutable
struct is usually preferable when you have the choice, since it avoids the extra
indirection.

The value can be loaded with the `[]` notation (`x[]`) and stored with the
reference form of the [`@atomic`](@ref), [`@atomicswap`](@ref),
[`@atomicreplace`](@ref), and [`@atomiconce`](@ref) macros, which also allow the
memory ordering to be specified explicitly:

# Examples
```jldoctest
julia> x = Threads.Atomic{Int}(3)
Base.Threads.Atomic{Int64}(3)

julia> @atomic x[] = 4
4

julia> @atomic :monotonic x[]
4

julia> @atomicswap x[] = 5
4

julia> x[]
5
```

Atomic operations use an `atomic_` prefix, such as [`atomic_add!`](@ref),
[`atomic_xchg!`](@ref), etc.

!!! warning
    Storing with the plain `x[] = value` form is deprecated: read-modify-write
    expressions such as `x[] += 1` look atomic but expand to a separate,
    non-atomic load and store. Use `@atomic x[] = value` (and, for an atomic
    read-modify-write, `@atomic x[] += 1` or [`atomic_add!`](@ref)) instead.

!!! compat "Julia 1.14"
    The `@atomic` reference form (`@atomic x[]`) on `Threads.Atomic` requires
    at least Julia 1.14.
"""
mutable struct Atomic{T}
    @atomic value::T
    Atomic{T}() where {T} = new(zero(T))
    Atomic{T}(value) where {T} = new(value)
end
````
-/
def atomicNew (value : T) : M World A := f.new value

def atomicNewZero : M World A := do f.new (← e.zero)

/--
Julia source: base/atomics.jl:71-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

Atomic() = Atomic{Int}()

```
-/
-- `Atomic()` is `Atomic{Int}()`, given the `Int` field builtins.
def atomicNewInt (fi : Fields World A (JInt .i64)) : M World A := fi.new (JInt.lit .i64 0)

/--
Julia source: base/atomics.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const LOCK_PROFILING = Atomic{Int}(0)
```
-/
-- The global `Atomic{Int}` cell created at load time as `Atomic{Int}(0)`, as the reference
-- the runtime holds.
def LOCK_PROFILING (cell : A) : A := cell

-- Reason: Each block declares a generic function (`function atomic_cas! end` and so on) for its docstring; the methods are modelled below.
-- UNTRANSLATED
-- Source: base/atomics.jl:81-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Threads.atomic_cas!(x::Atomic{T}, cmp::T, newval::T) where T
-- 
-- Atomically compare-and-set `x`
-- 
-- Atomically compares the value in `x` with `cmp`. If equal, write
-- `newval` to `x`. Otherwise, leaves `x` unmodified. Returns the old
-- value in `x`. By comparing the returned value to `cmp` (via `===`) one
-- knows whether `x` was modified and now holds the new value `newval`.
-- 
-- For further details, see LLVM's `cmpxchg` instruction.
-- 
-- This function can be used to implement transactional semantics. Before
-- the transaction, one records the value in `x`. After the transaction,
-- the new value is stored only if `x` has not been modified in the mean
-- time.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_cas!(x, 4, 2);
-- 
-- julia> x
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_cas!(x, 3, 2);
-- 
-- julia> x
-- Base.Threads.Atomic{Int64}(2)
-- ```
-- """
-- function atomic_cas! end
-- 
-- """
--     Threads.atomic_xchg!(x::Atomic{T}, newval::T) where T
-- 
-- Atomically exchange the value in `x`
-- 
-- Atomically exchanges the value in `x` with `newval`. Returns the **old**
-- value.
-- 
-- For further details, see LLVM's `atomicrmw xchg` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_xchg!(x, 2)
-- 3
-- 
-- julia> x[]
-- 2
-- ```
-- """
-- function atomic_xchg! end
-- 
-- """
--     Threads.atomic_add!(x::Atomic{T}, val::T) where T <: ArithmeticTypes
-- 
-- Atomically add `val` to `x`
-- 
-- Performs `x[] += val` atomically. Returns the **old** value. Not defined for
-- `Atomic{Bool}`.
-- 
-- For further details, see LLVM's `atomicrmw add` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_add!(x, 2)
-- 3
-- 
-- julia> x[]
-- 5
-- ```
-- """
-- function atomic_add! end
-- 
-- """
--     Threads.atomic_sub!(x::Atomic{T}, val::T) where T <: ArithmeticTypes
-- 
-- Atomically subtract `val` from `x`
-- 
-- Performs `x[] -= val` atomically. Returns the **old** value. Not defined for
-- `Atomic{Bool}`.
-- 
-- For further details, see LLVM's `atomicrmw sub` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_sub!(x, 2)
-- 3
-- 
-- julia> x[]
-- 1
-- ```
-- """
-- function atomic_sub! end
-- 
-- """
--     Threads.atomic_and!(x::Atomic{T}, val::T) where T
-- 
-- Atomically bitwise-and `x` with `val`
-- 
-- Performs `x[] &= val` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw and` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_and!(x, 2)
-- 3
-- 
-- julia> x[]
-- 2
-- ```
-- """
-- function atomic_and! end
-- 
-- """
--     Threads.atomic_nand!(x::Atomic{T}, val::T) where T
-- 
-- Atomically bitwise-nand (not-and) `x` with `val`
-- 
-- Performs `x[] = ~(x[] & val)` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw nand` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(3)
-- Base.Threads.Atomic{Int64}(3)
-- 
-- julia> Threads.atomic_nand!(x, 2)
-- 3
-- 
-- julia> x[]
-- -3
-- ```
-- """
-- function atomic_nand! end
-- 
-- """
--     Threads.atomic_or!(x::Atomic{T}, val::T) where T
-- 
-- Atomically bitwise-or `x` with `val`
-- 
-- Performs `x[] |= val` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw or` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(5)
-- Base.Threads.Atomic{Int64}(5)
-- 
-- julia> Threads.atomic_or!(x, 7)
-- 5
-- 
-- julia> x[]
-- 7
-- ```
-- """
-- function atomic_or! end
-- 
-- """
--     Threads.atomic_xor!(x::Atomic{T}, val::T) where T
-- 
-- Atomically bitwise-xor (exclusive-or) `x` with `val`
-- 
-- Performs `x[] \$= val` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw xor` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(5)
-- Base.Threads.Atomic{Int64}(5)
-- 
-- julia> Threads.atomic_xor!(x, 7)
-- 5
-- 
-- julia> x[]
-- 2
-- ```
-- """
-- function atomic_xor! end
-- 
-- """
--     Threads.atomic_max!(x::Atomic{T}, val::T) where T
-- 
-- Atomically store the maximum of `x` and `val` in `x`
-- 
-- Performs `x[] = max(x[], val)` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw max` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(5)
-- Base.Threads.Atomic{Int64}(5)
-- 
-- julia> Threads.atomic_max!(x, 7)
-- 5
-- 
-- julia> x[]
-- 7
-- ```
-- """
-- function atomic_max! end
-- 
-- """
--     Threads.atomic_min!(x::Atomic{T}, val::T) where T
-- 
-- Atomically store the minimum of `x` and `val` in `x`
-- 
-- Performs `x[] = min(x[], val)` atomically. Returns the **old** value.
-- 
-- For further details, see LLVM's `atomicrmw min` instruction.
-- 
-- # Examples
-- ```jldoctest
-- julia> x = Threads.Atomic{Int}(7)
-- Base.Threads.Atomic{Int64}(7)
-- 
-- julia> Threads.atomic_min!(x, 5)
-- 7
-- 
-- julia> x[]
-- 5
-- ```
-- """
-- function atomic_min! end
-- 
-- /Source

/--
Julia source: base/atomics.jl:326-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#const nand = (~) ∘ (&) # ComposedFunction generated very poor code quality
nand(x, y) = ~(x & y)

```
-/
def nand (x y : T) : M World T := do e.bnot (← e.band x y)

/--
Julia source: base/atomics.jl:329-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(x::Atomic) = @atomic :acquire x.value
# NOTE: `setindex!(x::Atomic, v)` (the `x[] = v` form) is deprecated in favor of
# `@atomic x[] = v`; see `base/deprecated.jl`. Reads via `x[]` remain a plain
# atomic (acquire) load.

```
-/
def getindex (x : A) : M World T := f.getfield x .acquire

/--
Julia source: base/atomics.jl:334-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Support the reference form of the `@atomic` family of macros (`@atomic x[]`,
# `@atomicswap x[] = v`, `@atomicreplace x[] o => n`, ...) so that an `Atomic`
# can be used as a single atomic memory location with an explicit memory order.
@inline getindex_atomic(x::Atomic, order::Symbol) = getfield(x, :value, order)
```
-/
def getindex_atomic (x : A) (order : Order) : M World T := f.getfield x order

/--
Julia source: base/atomics.jl:338-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex_atomic!(x::Atomic{T}, order::Symbol, v) where {T}
    return setfield!(x, :value, v isa T ? v : convert(T, v)::T, order)
end
```
-/
def setindex_atomic (x : A) (order : Order) (v : V) : M World T := do
  f.setfield x (← e.toT v) order

/--
Julia source: base/atomics.jl:341-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function swapindex_atomic!(x::Atomic{T}, order::Symbol, v) where {T}
    return swapfield!(x, :value, v isa T ? v : convert(T, v)::T, order)
end
```
-/
def swapindex_atomic (x : A) (order : Order) (v : V) : M World T := do
  f.swapfield x (← e.toT v) order

/--
Julia source: base/atomics.jl:344-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline modifyindex_atomic!(x::Atomic, order::Symbol, op, v) =
    modifyfield!(x, :value, op, v, order)
```
-/
def modifyindex_atomic (x : A) (order : Order) (op : T → T → M World T) (v : T) :
    M World (T × T) :=
  f.modifyfield x op v order

/--
Julia source: base/atomics.jl:346-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function replaceindex_atomic!(x::Atomic{T}, success_order::Symbol, fail_order::Symbol, expected, desired) where {T}
    return replacefield!(x, :value, expected, desired isa T ? desired : convert(T, desired)::T, success_order, fail_order)
end
```
-/
def replaceindex_atomic (x : A) (success fail : Order) (expected : T) (desired : V) :
    M World (T × Bool) := do
  f.replacefield x expected (← e.toT desired) success fail

/--
Julia source: base/atomics.jl:349-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindexonce_atomic!(x::Atomic{T}, success_order::Symbol, fail_order::Symbol, v) where {T}
    return setfieldonce!(x, :value, v isa T ? v : convert(T, v)::T, success_order, fail_order)
end
```
-/
def setindexonce_atomic (x : A) (success fail : Order) (v : V) : M World Bool := do
  f.setfieldonce x (← e.toT v) success fail

/--
Julia source: base/atomics.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_cas!(x::Atomic, cmp, new) = (@atomicreplace :acquire_release :acquire x.value cmp => new).old
```
-/
def atomic_cas (x : A) (cmp new : T) : M World T := do
  return (← f.replacefield x cmp new .acquire_release .acquire).1

/--
Julia source: base/atomics.jl:353-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_add!(x::Atomic, v) = (@atomic :acquire_release x.value + v).first
```
-/
def atomic_add (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.add v .acquire_release).1

/--
Julia source: base/atomics.jl:354-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_sub!(x::Atomic, v) = (@atomic :acquire_release x.value - v).first
```
-/
def atomic_sub (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.sub v .acquire_release).1

/--
Julia source: base/atomics.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_and!(x::Atomic, v) = (@atomic :acquire_release x.value & v).first
```
-/
def atomic_and (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.band v .acquire_release).1

/--
Julia source: base/atomics.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_or!(x::Atomic, v) = (@atomic :acquire_release x.value | v).first
```
-/
def atomic_or (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.bor v .acquire_release).1

/--
Julia source: base/atomics.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_xor!(x::Atomic, v) = (@atomic :acquire_release x.value ⊻ v).first
```
-/
def atomic_xor (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.bxor v .acquire_release).1

/--
Julia source: base/atomics.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_nand!(x::Atomic, v) = (@atomic :acquire_release x.value nand v).first
```
-/
def atomic_nand (x : A) (v : T) : M World T := do
  return (← f.modifyfield x (nand e) v .acquire_release).1

/--
Julia source: base/atomics.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_xchg!(x::Atomic, v) = (@atomicswap :acquire_release x.value = v)
```
-/
def atomic_xchg (x : A) (v : T) : M World T := f.swapfield x v .acquire_release

/--
Julia source: base/atomics.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_min!(x::Atomic, v) = (@atomic :acquire_release x.value min v).first
```
-/
def atomic_min (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.min v .acquire_release).1

/--
Julia source: base/atomics.jl:361-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atomic_max!(x::Atomic, v) = (@atomic :acquire_release x.value max v).first

```
-/
def atomic_max (x : A) (v : T) : M World T := do
  return (← f.modifyfield x e.max v .acquire_release).1

/-- The `Int` element methods used by the lock counters. -/
def intAdd (x y : JInt .i64) : M World (JInt .i64) := pure (JuliaLean.base.int.add x y)
def intSub (x y : JInt .i64) : M World (JInt .i64) := pure (JuliaLean.base.int.sub x y)

/--
Julia source: base/atomics.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock_profiling(state::Bool) = state ? atomic_add!(LOCK_PROFILING, 1) : atomic_sub!(LOCK_PROFILING, 1)
```
-/
def lock_profiling_set (fi : Fields World A (JInt .i64)) (profiling : A) (state : Bool) :
    M World (JInt .i64) := do
  if state then
    return (← fi.modifyfield profiling intAdd (JInt.lit .i64 1) .acquire_release).1
  else
    return (← fi.modifyfield profiling intSub (JInt.lit .i64 1) .acquire_release).1

/--
Julia source: base/atomics.jl:76-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock_profiling() = LOCK_PROFILING[] > 0

```
-/
def lock_profiling (fi : Fields World A (JInt .i64)) (profiling : A) : M World Bool := do
  return (← fi.getfield profiling .acquire).val > 0

/--
Julia source: base/atomics.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const LOCK_CONFLICT_COUNT = Atomic{Int}(0);
```
-/
-- The global `Atomic{Int}` cell created at load time as `Atomic{Int}(0)`.
def LOCK_CONFLICT_COUNT (cell : A) : A := cell

/--
Julia source: base/atomics.jl:79-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inc_lock_conflict_count() = atomic_add!(LOCK_CONFLICT_COUNT, 1)

```
-/
def inc_lock_conflict_count (fi : Fields World A (JInt .i64)) (count : A) : M World (JInt .i64) := do
  return (← fi.modifyfield count intAdd (JInt.lit .i64 1) .acquire_release).1

/--
Julia source: base/atomics.jl:363-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Threads.atomic_fence()

Insert a sequential-consistency memory fence

Inserts a memory fence with sequentially-consistent ordering
semantics. There are algorithms where this is needed, i.e. where an
acquire/release ordering is insufficient.

This is likely a very expensive operation. Given that all other atomic
operations in Julia already have acquire/release semantics, explicit
fences should not be necessary in most cases.

For further details, see LLVM's `fence` instruction.
"""
atomic_fence() = Core.Intrinsics.atomic_fence(:sequentially_consistent, :system)

```
-/
def atomic_fence (fe : Fences World) : M World Unit := fe.fence .sequentially_consistent .system

/--
Julia source: base/atomics.jl:380-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Threads.atomic_fence_light()

Insert the light side of an asymmetric sequential-consistency memory fence.
Asymmetric memory fences are useful in scenarios where one side of the
synchronization runs significantly less often than the other side. Use this
function on the side that runs often and [`atomic_fence_heavy`](@ref) on the
side that runs rarely.

On supported operating systems and architectures this fence is cheaper than
`Threads.atomic_fence()`, but synchronizes only with [`atomic_fence_heavy`](@ref)
calls from other threads.
"""
atomic_fence_light() = Core.Intrinsics.atomic_fence(:sequentially_consistent, :singlethread)

```
-/
def atomic_fence_light (fe : Fences World) : M World Unit :=
  fe.fence .sequentially_consistent .singlethread

/--
Julia source: base/atomics.jl:395-402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Threads.atomic_fence_heavy()

Insert the heavy side of an asymmetric sequential-consistency memory fence.
Use this function on the side that runs rarely.
See [`atomic_fence_light`](@ref) for more details.
"""
atomic_fence_heavy() = ccall(:jl_membarrier, Cvoid, ())
```
-/
def atomic_fence_heavy (fe : Fences World) : M World Unit := fe.membarrier

end

end JuliaLean.base.atomics


namespace JuliaLean.Tasks



abbrev AtomicInt := BitVec 64
inductive AtomicAction where
  | cas (expected desired : AtomicInt)
  | exchange (value : AtomicInt)
  | add (value : AtomicInt)
  | sub (value : AtomicInt)
  | band (value : AtomicInt)
  | bnand (value : AtomicInt)
  | bor (value : AtomicInt)
  | bxor (value : AtomicInt)
  | min (value : AtomicInt)
  | max (value : AtomicInt)
  deriving Repr, DecidableEq
/-- The new value of each `Atomic{Int64}` read-modify-write operation,
`base/atomics.jl:326-361`. `BitVec 64` supplies Julia's wrapping Int bits. -/
def atomicUpdate : AtomicAction → AtomicInt → AtomicInt
  | .cas expected desired, old => if old = expected then desired else old
  | .exchange value, _ => value
  | .add value, old => old + value
  | .sub value, old => old - value
  | .band value, old => old &&& value
  | .bnand value, old => ~~~(old &&& value)
  | .bor value, old => old ||| value
  | .bxor value, old => old ^^^ value
  | .min value, old => if old.toInt ≤ value.toInt then old else value
  | .max value, old => if old.toInt ≥ value.toInt then old else value
/-- LLVM atomic RMWs return the old value and perform one update. -/
def atomicStep (action : AtomicAction) (old : AtomicInt) : AtomicInt × AtomicInt :=
  (old, atomicUpdate action old)
def atomicRun (initial : AtomicInt) (actions : List AtomicAction) : AtomicInt :=
  actions.foldl (fun value action => atomicUpdate action value) initial

end JuliaLean.Tasks

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

/-- The field produced by `new`, including conversion to the declared field
type and propagation of conversion failure (`base/atomics.jl:68-69`). -/
structure AtomicCell (α : Type) where
  value : α

def atomicValueCtor {α β : Type} (convert : β → R α) (value : β) : R (AtomicCell α) :=
  match convert value with
  | .ok converted => .ok ⟨converted⟩
  | .error err => .error err

def atomicZeroCtor {α β : Type} (zero : R β) (convert : β → R α) : R (AtomicCell α) :=
  match zero with
  | .ok value => atomicValueCtor convert value
  | .error err => .error err

/-- The unparameterized constructor delegates to `Atomic{Int}()`;
`base/atomics.jl:72`. -/
def atomicDefaultCtor : R (AtomicCell Int) :=
  atomicZeroCtor (.ok 0) (fun value => .ok value)

end JuliaLean.ConcurrencyCov.FaithfulSmall

namespace JuliaLean.Tasks



/-! ## base/atomics.jl:66-361, storage and index/RMW wrappers -/

structure CoverageAtomic where
  value : AtomicInt
  initialized : Bool := true
  deriving Repr, DecidableEq

def atomicDefault : CoverageAtomic := ⟨0, true⟩

def atomicLoad (cell : CoverageAtomic) : AtomicInt := cell.value

def atomicStore (cell : CoverageAtomic) (value : AtomicInt) : AtomicInt × CoverageAtomic :=
  (value, { cell with value := value })

def atomicSwap (cell : CoverageAtomic) (value : AtomicInt) : AtomicInt × CoverageAtomic :=
  (cell.value, { cell with value := value })

def atomicReplace (cell : CoverageAtomic) (expected desired : AtomicInt) :
    AtomicInt × Bool × CoverageAtomic :=
  if cell.value == expected then (cell.value, true, { cell with value := desired })
  else (cell.value, false, cell)

def atomicSetOnce (cell : CoverageAtomic) (value : AtomicInt) : Bool × CoverageAtomic :=
  if cell.initialized then (false, cell) else (true, ⟨value, true⟩)

/-! ## base/atomics.jl:378-402, fences -/

inductive FenceKind where | system | light | heavy
  deriving Repr, DecidableEq

def fenceBody : FenceKind → String
  | .system => "sequentially_consistent:system"
  | .light => "sequentially_consistent:singlethread"
  | .heavy => "jl_membarrier"

end JuliaLean.Tasks
