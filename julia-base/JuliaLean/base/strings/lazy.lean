import JuliaLean.base.strings.search
import JuliaLean.Core
import JuliaLean.base.boot
import JuliaLean.base.atomics
import JuliaLean.base.gmp
import JuliaLean.base.hashing
import JuliaLean.Bindings.base.hashing
import JuliaLean.base.intfuncs
import JuliaLean.base.io
import JuliaLean.base.iobuffer
import JuliaLean.base.operators
import JuliaLean.base.show
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.io
import JuliaLean.base.strings.string

/-!
# Model of `base/strings/lazy.jl`

A `LazyString` is a heap object whose `@atomic str` field is accessed through the installed
`atomics.Fields` record (`lazyFields` instantiates it over `LazyHeap` with the C builtins' ordering
rules); `parts` and `compact` are its `const` fields. `String(l)` runs the installed `sprint` model
(`strings.io.sprintIOBuffer`) with the installed `IOContext` and `print` models; the forwarding
methods call the installed `String` models of `strings/string.lean`, `hash(::String, ::UInt)` of
`hashing.lean` (through the one `String` adapter `Bindings.base.hashing.hashStringBound`), and convert a non-`Int` index with the installed `Int(i)` models. A captured value is a
`strings.io.StrArg`: one of the installed argument kinds of `print_to_string`, or `StrArg.other` for a
value's own `print` method. `@lazy_str` (`lazy_str`, `lazyLoop`) keeps the byte-sequence model and is
blocked on the parser model.
-/

namespace JuliaLean.base.strings.lazy

open JuliaLean

abbrev Index := JInt64
abbrev EagerString := List UInt8

abbrev JString := JuliaLean.base.strings.string.JString

/-- A captured value of the lazy string: `print(io, part)` of the types `print_to_string`
tests, or any other value with its own `print` method (`StrArg.other`). -/
abbrev LazyPart (E V : Type) := JuliaLean.base.strings.io.StrArg E V

/-! ## Exceptions

`String(::LazyString)` and the forwarding methods throw the exceptions of the methods they call. -/
inductive LazyError (E : Type) where
  /-- `sprint`: the IOBuffer, the IOContext and `show` methods, and a captured value's own
  `print` (`E`). -/
  | sprint (error : JuliaLean.base.strings.io.Error E)
  /-- The `getfield`/`replacefield!` builtins on the `str` field. -/
  | field (error : JuliaLean.base.io.Error)
  /-- The exceptions of the `String` methods (`BoundsError`, `StringIndexError`, ...). -/
  | string (error : JuliaLean.Strings.SErr)
  /-- `Int(i)` of a `BitInteger` or `Bool` (boot.jl:1032-1221). -/
  | convert (error : JuliaLean.BootCov.Exc)
  /-- `Int(i)` of a `BigInt` (gmp.jl). -/
  | bigint (error : JlError)
  /-- `old::String` with `old === nothing` (`TypeError`). -/
  | typeAssert

/-- Computations that read and write the world holding the `str` cells; a mutation made before
an exception is kept, as in the installed `io.M`. -/
abbrev M (World E : Type) (α : Type) :=
  World → Option (Except (LazyError E × World) (α × World))

instance {World E : Type} : Monad (M World E) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world =>
    match action world with
    | none => none
    | some (.error result) => some (.error result)
    | some (.ok (value, world)) => next value world

instance {World E : Type} : MonadExceptOf (LazyError E) (M World E) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

def liftField {World E α : Type} (action : JuliaLean.base.io.M World α) : M World E α :=
  fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => some (.error (.field error, world))

def liftPure {World E α : Type} (result : Except (LazyError E) α) : M World E α :=
  fun world =>
    match result with
    | .ok value => some (.ok (value, world))
    | .error error => some (.error (error, world))

/-! ## The `str` field of a `LazyString`

`LazyString` is a mutable struct whose `@atomic str::Union{String,Nothing}` field is read with
`@atomic :acquire l.str` and written with `@atomicreplace`. `Union{String,Nothing}` is not an
isbits union, so the field holds a pointer (`jl_field_isptr`). The macros expand to
`getproperty(l, :str, :acquire)` (expr.jl:1506-1511, Base_compiler.jl:83) and
`replaceproperty!(l, :str, nothing, str, :acquire_release, :acquire)` (expr.jl:1722-1728,
Base_compiler.jl:101-106), which call `Core.getfield` and `Core.replacefield!`. -/

/-- The objects allocated by `new` for `LazyString`: slot `r` holds the `str` field of object
`r`. -/
structure LazyHeap where
  cells : List (Option JString)

abbrev CellRef := Nat

def atomicError (message : _root_.String) : JuliaLean.base.io.Error :=
  .foreignError "ConcurrencyViolationError" message

def invalidOrdering : JuliaLean.base.io.Error := atomicError "invalid atomic ordering"

/-- The order of `enum jl_memory_order` (src/julia_atomics.h:46-57). -/
def orderRank : JuliaLean.base.atomics.Order → Nat
  | .notatomic => 0
  | .unordered => 1
  | .monotonic => 2
  | .acquire => 4
  | .release => 5
  | .acquire_release => 6
  | .sequentially_consistent => 7

/-- `jl_get_atomic_order_checked(order, loading, storing)` (src/builtins.c:1146-1171). -/
def checkedOrder (loading storing : Bool) :
    JuliaLean.base.atomics.Order → Except JuliaLean.base.io.Error Unit
  | .notatomic => .ok ()
  | .unordered => if loading != storing then .ok () else .error invalidOrdering
  | .monotonic => if loading || storing then .ok () else .error invalidOrdering
  | .acquire => if loading then .ok () else .error invalidOrdering
  | .release => if storing then .ok () else .error invalidOrdering
  | .acquire_release => if loading && storing then .ok () else .error invalidOrdering
  | .sequentially_consistent => .ok ()

/-- The `isatomic == (order == jl_memory_order_notatomic)` test of the field builtins
(src/builtins.c:1224-1227, 1248-1250, 1272-1274, 1291-1293, 1317-1322, 1353-1358) for the atomic
field `str`. -/
def requireAtomic (builtin access : _root_.String)
    (order : JuliaLean.base.atomics.Order) : Except JuliaLean.base.io.Error Unit :=
  if order == .notatomic then
    .error (atomicError (builtin ++ ": atomic field cannot be " ++ access ++ " non-atomically"))
  else .ok ()

/-- Reading a slot that `new` never allocated cannot happen for a reference returned by `new`. -/
def cellAt (heap : LazyHeap) (ref : CellRef) :
    Except JuliaLean.base.io.Error (Option JString) :=
  match heap.cells[ref]? with
  | some value => .ok value
  | none => .error (.errorException "reference to an object that was not allocated by new")

def runCell {α : Type} (action : LazyHeap → Except JuliaLean.base.io.Error (α × LazyHeap)) :
    JuliaLean.base.io.M LazyHeap α :=
  fun heap =>
    match action heap with
    | .ok result => some (.ok result)
    | .error error => some (.error (error, heap))

/-- The retry loop of `modify_value` (src/datatype.c:2081-2109): apply `op`, then
compare-and-swap against the value read. -/
partial def modifyLoop (ref : CellRef)
    (op : Option JString → Option JString → JuliaLean.base.io.M LazyHeap (Option JString))
    (value old : Option JString) :
    JuliaLean.base.io.M LazyHeap (Option JString × Option JString) :=
  fun heap =>
    match op old value heap with
    | none => none
    | some (.error result) => some (.error result)
    | some (.ok (updated, heap)) =>
      match cellAt heap ref with
      | .error error => some (.error (error, heap))
      | .ok current =>
        if current == old then
          some (.ok ((old, updated), ⟨heap.cells.set ref updated⟩))
        else modifyLoop ref op value current heap

/-- The builtins `getfield`, `setfield!`, `swapfield!`, `modifyfield!`, `replacefield!` and
`setfieldonce!` on the atomic pointer field `str`, with the ordering rules of
`jl_f_getfield` (src/builtins.c:1202-1234), `jl_f_setfield` (:1236-1258), `jl_f_swapfield`
(:1260-1277), `modifyfield_invoke` (:1279-1296), `jl_f_replacefield` (:1303-1331) and
`jl_f_setfieldonce` (:1333-1361). Reads are `jl_get_nth_field` (src/datatype.c:1886-1893,
a relaxed atomic load of the pointer), writes `set_nth_field` (datatype.c:1944-1953),
`swap_nth_field` (:2057-2073), `modify_nth_field` (:2205-2217), `replace_nth_field`
(:2313-2330, `replace_value` :2219-2237) and `set_nth_fieldonce` (:2354-2380). `new` is the
field initialisation of `jl_new_structv` (datatype.c:1707-1742). Everything here is
sequentially consistent, so the fences of the acquire/release orders have no effect. -/
def lazyFields : JuliaLean.base.atomics.Fields LazyHeap CellRef (Option JString) where
  new value := fun heap => some (.ok (heap.cells.length, ⟨heap.cells ++ [value]⟩))
  getfield ref order := runCell fun heap => do
    checkedOrder true false order
    requireAtomic "getfield" "accessed" order
    pure (← cellAt heap ref, heap)
  setfield ref value order := runCell fun heap => do
    checkedOrder false true order
    requireAtomic "setfield!" "written" order
    let _ ← cellAt heap ref
    pure (value, ⟨heap.cells.set ref value⟩)
  swapfield ref value order := runCell fun heap => do
    checkedOrder true true order
    requireAtomic "swapfield!" "written" order
    let old ← cellAt heap ref
    pure (old, ⟨heap.cells.set ref value⟩)
  modifyfield ref op value order := fun heap =>
    let start : Except JuliaLean.base.io.Error (Option JString) := do
      checkedOrder true true order
      requireAtomic "modifyfield!" "written" order
      cellAt heap ref
    match start with
    | .error error => some (.error (error, heap))
    | .ok old => modifyLoop ref op value old heap
  replacefield ref expected desired success failure := runCell fun heap => do
    checkedOrder true true success
    checkedOrder true false failure
    if orderRank success < orderRank failure then throw invalidOrdering
    requireAtomic "replacefield!" "written" success
    requireAtomic "replacefield!" "accessed" failure
    let current ← cellAt heap ref
    if current == expected then
      pure ((current, true), ⟨heap.cells.set ref desired⟩)
    else pure ((current, false), heap)
  setfieldonce ref _value success failure := runCell fun heap => do
    checkedOrder true true success
    checkedOrder true false failure
    if orderRank success < orderRank failure then throw invalidOrdering
    requireAtomic "setfieldonce!" "written" success
    requireAtomic "setfieldonce!" "accessed" failure
    let _ ← cellAt heap ref
    pure (false, heap)

/-! ## The `LazyString` type and its constructors -/

/--
Julia source: base/strings/lazy.jl:1-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    LazyString <: AbstractString

A lazy representation of string interpolation. This is useful when a string
needs to be constructed in a context where performing the actual interpolation
and string construction is unnecessary or undesirable (e.g. in error paths
of functions).

This type is designed to be cheap to construct at runtime, trying to offload
as much work as possible to either the macro or later printing operations.

# Examples

```jldoctest
julia> n = 5; str = LazyString("n is ", n)
"n is 5"
```

See also [`@lazy_str`](@ref).

!!! compat "Julia 1.8"
    `LazyString` requires Julia 1.8 or later.

# Extended help
## Safety properties for concurrent programs

A lazy string itself does not introduce any concurrency problems even if it is printed in
multiple Julia tasks.  However, if `print` methods on a captured value can have a
concurrency issue when invoked without synchronizations, printing the lazy string may cause
an issue.  Furthermore, the `print` methods on the captured values may be invoked multiple
times, though only exactly one result will be returned.

!!! compat "Julia 1.9"
    `LazyString` is safe in the above sense in Julia 1.9 and later.
"""
````
Julia source: base/strings/lazy.jl:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct LazyString <: AbstractString
    const parts::Tuple
    const compact::Bool # compact & limited output
    # Created on first access
    @atomic str::Union{String,Nothing}
    global _LazyString(parts, str) = new(parts, false, str)
    LazyString(args...; compact::Bool=false) = new(args, compact, nothing)
end

```
A `LazyString` object: `ref` is its heap object (holding the `str` field, accessed through
`atomics.Fields`), `parts` and `compact` are its `const` fields. -/
structure LazyString (Ref E V : Type) where
  ref : Ref
  parts : List (LazyPart E V)
  compact : Bool

/--
Julia source: base/strings/lazy.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global _LazyString(parts, str) = new(parts, false, str)
```
`new(parts, false, str)`: the object is allocated with `str` initialised to the given value
(`Expr(:new)`, src/codegen.cpp:7578-7605; `jl_new_structv`, src/datatype.c:1707-1742). -/
def _LazyString {World Ref E V : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (parts : List (LazyPart E V)) (str : Option JString) : M World E (LazyString Ref E V) := do
  let ref ← liftField (fields.new str)
  pure ⟨ref, parts, false⟩

/--
Julia source: base/strings/lazy.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    LazyString(args...; compact::Bool=false) = new(args, compact, nothing)
```
`new(args, compact, nothing)` initialises the cache to `nothing`: the new object's `str` field is
`fields.new none`. -/
def lazyStringCtor {World Ref E V : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (args : List (LazyPart E V)) (compact : Bool := false) :
    M World E (LazyString Ref E V) := do
  let ref ← liftField (fields.new none)
  pure ⟨ref, args, compact⟩

inductive MacroExpr where
  | text (bytes : EagerString)
  | escaped (expression : MacroExpr)
  | lazyString (parts : List MacroExpr) (compact : Bool)
  deriving Repr

/-- One-based increment of an `Int` index. -/
def nextIndex (i : Index) : Index := i + JInt.lit .i64 1

/-- Julia's byte index `1` on the 64-bit target. -/
def firstIndex : Index := JInt.lit .i64 1

/-- `Macro.parseatom` result with its exact returned expression and source index. -/
abbrev ParsedAtom := MacroExpr × Index

partial def lazyLoop {E : Type}
    (findnext : Char → EagerString → Index → Option Index)
    (prevind : EagerString → Index → Index)
    (lastindex : EagerString → Index)
    (slice : EagerString → Index → Index → EagerString)
    (parseatom : EagerString → Index → String → Except E ParsedAtom)
    (sourceFile : String) (text : EagerString) (idx lastidx : Index)
    (parts : List MacroExpr) : Except E (List MacroExpr) := do
  match findnext '$' text idx with
  | none =>
      if lastidx ≤ lastindex text then
        pure (parts ++ [.text (slice text lastidx (lastindex text))])
      else
        pure parts
  | some dollarIndex =>
      let parts :=
        if lastidx < dollarIndex then
          parts ++ [.text (slice text lastidx (prevind text dollarIndex))]
        else
          parts
      let idx := nextIndex dollarIndex
      let (expression, idx) ← parseatom text idx sourceFile
      let parts := parts ++ [.escaped expression]
      let lastidx := idx
      lazyLoop findnext prevind lastindex slice parseatom sourceFile text idx lastidx parts

/--
Julia source: base/strings/lazy.jl:45-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    lazy"str"
    lazy"str"c

Create a [`LazyString`](@ref) using regular string interpolation syntax.
Note that interpolations are *evaluated* at LazyString construction time,
but *printing* is delayed until the first access to the string.  The `lazy"str"c`
variant uses an [`IOContext`](@ref) with `:compact=>true, :limit=>true` when
printing, in order to keep the output string compact.

See [`LazyString`](@ref) documentation for the safety properties for concurrent programs.

# Examples

```
julia> n = 5; str = lazy"n is \$n"
"n is 5"

julia> typeof(str)
LazyString
```

!!! compat "Julia 1.8"
    `lazy"str"` requires Julia 1.8 or later.

!!! compat "Julia 1.14"
    `lazy"str"c` requires Julia 1.14 or later.
"""
macro lazy_str(text, flags...)
    compact = flags == ("c",)
    isempty(flags) || compact || throw(ArgumentError("unknown lazy-string flag: $flags"))
    parts = Any[]
    lastidx = idx = 1
    while (idx = findnext('$', text, idx)) !== nothing
        lastidx < idx && push!(parts, text[lastidx:prevind(text, idx)])
        idx += 1
        expr, idx = Meta.parseatom(text, idx; filename=string(__source__.file))
        push!(parts, esc(expr))
        lastidx = idx
    end
    lastidx <= lastindex(text) && push!(parts, text[lastidx:end])
    :(LazyString($(parts...); compact=$compact))
end

````
-/
def lazy_str {E : Type}
    (findnext : Char → EagerString → Index → Option Index)
    (prevind : EagerString → Index → Index)
    (lastindex : EagerString → Index)
    (slice : EagerString → Index → Index → EagerString)
    (parseatom : EagerString → Index → String → Except E ParsedAtom)
    (showFlags : List String → String)
    (argumentError : String → E)
    (sourceFile : String) (text : EagerString) (flags : List String) : Except E MacroExpr := do
  let compact := flags == ["c"]
  if flags.isEmpty || compact then
    let parts ← lazyLoop findnext prevind lastindex slice parseatom sourceFile text
      firstIndex firstIndex []
    pure (.lazyString parts compact)
  else
    .error (argumentError ("unknown lazy-string flag: " ++ showFlags flags))

/-! ## `String(::LazyString)` -/

/-- The `String` allocated for the bytes `takestring!` returns: `jl_genericmemory_to_string`
(src/genericmemory.c:189-215) allocates through `jl_alloc_string`, which throws
`OutOfMemoryError` when the size overflows (src/array.c:283-298). A `String` has fewer than
`2^62` code units. -/
def stringFromPrinted {E : Type} (printed : JuliaLean.base.strings.io.JuliaString) :
    Except (LazyError E) JString :=
  if h : printed.bytes.length < 2 ^ 62 then .ok ⟨printed.bytes, h⟩
  else .error (.string .outOfMemory)

/-- The `do io ... end` body passed to `sprint`: `foreach(Fix1(print, io), l.parts)`, or the same
with `IOContext(io, :compact=>true, :limit=>true)` (evaluated once) when `l.compact`. -/
def printParts {Ref E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (displaySize : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty)
    (l : LazyString Ref E V) (io : JuliaLean.base.show.JIO Unit V) (_ : Unit) :
    JuliaLean.base.strings.io.BufferShowM E Unit := do
  if l.compact then
    let context ← JuliaLean.base.show.IOContext_pairs
      (JuliaLean.base.strings.io.bufferPrims (E := E) (V := V) displaySize) a
      (JuliaLean.base.dict.fieldConv JuliaLean.base.show.Sym)
      (JuliaLean.base.show.boolConv a) io ("compact", true) [("limit", true)]
    for part in l.parts do
      JuliaLean.base.strings.io.printArg c displaySize a (.context context) part
  else
    for part in l.parts do
      JuliaLean.base.strings.io.printArg c displaySize a io part

/--
Julia source: base/strings/lazy.jl:89-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(l::LazyString)
    old = @atomic :acquire l.str
    old === nothing || return old
    str = sprint() do io
        if l.compact
            foreach(Fix1(print, IOContext(io, :compact=>true, :limit=>true)), l.parts)
        else
            foreach(Fix1(print, io), l.parts)
        end
    end
    old, ok = @atomicreplace :acquire_release :acquire l.str nothing => str
    return ok ? str : (old::String)
end

```
`sprint()` is `sprint(f; context=nothing, sizehint=0)` (io.jl:104-114): `IOBuffer(sizehint=0)`,
`f(s)`, `takestring!(s)`. -/
def toString {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString Ref E V) : M World E JString := do
  let old ← liftField (fields.getfield l.ref .acquire)
  match old with
  | some cached => pure cached
  | none =>
    let printed ← liftPure ((JuliaLean.base.strings.io.sprintIOBuffer (Args := Unit)
      (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a
      JuliaLean.base.strings.io.SprintContext.none (JuliaLean.base.iobuffer.i 0)
      (printParts c displaySize a l) ()).mapError LazyError.sprint)
    let str ← liftPure (stringFromPrinted printed)
    let (old, ok) ← liftField
      (fields.replacefield l.ref none (some str) .acquire_release .acquire)
    if ok then pure str
    else
      match old with
      | some cached => pure cached
      | none => throw LazyError.typeAssert

/-! ## `Int(i)::Int` of an `Integer` index

`iterate(::String, ::Integer)`, `codeunit(::String, ::Integer)` and `isvalid(::String, ::Integer)`
convert a non-`Int` index with `Int(i)::Int` (basic.jl:107-108, 143-144, 156-157; string.jl:212);
an `Int` index reaches the `Int` method directly, which `Int(i)` leaves unchanged. -/

/-- `Int(x)` of a `BitInteger` (boot.jl:1032-1221, installed `IntConv.ctor`). -/
def bitIntegerIndex {E : Type} (t : IntTy) (x : JInt t) : Except (LazyError E) JInt64 :=
  (JuliaLean.BootCov.IntConv.ctor .i64 (.int t x)).mapError LazyError.convert

/-- `Int(b)` of a `Bool` (boot.jl `toInt64`, installed `IntConv.ctor`). -/
def boolIndex {E : Type} (b : Bool) : Except (LazyError E) JInt64 :=
  (JuliaLean.BootCov.IntConv.ctor .i64 (.bool b)).mapError LazyError.convert

/-- `Int(x::BigInt)` (gmp.jl:396-407, installed `gmp.convertSigned`). -/
def bigIntIndex {E : Type} (x : JuliaLean.base.gmp.BigInt) : Except (LazyError E) JInt64 :=
  (JuliaLean.base.gmp.convertSigned .i64 x).mapError LazyError.bigint

/-! ## The forwarding methods -/

/-- `==(a::String, b::String) = a===b` compares the code units: `jl_egal` of two strings is
`jl_string_len(a) == jl_string_len(b) && memcmp(...) == 0` (`===` is `jl_f_is`,
src/builtins.c:606-610; `jl_egal` src/julia.h:2076, 2094-2103; the `jl_string_tag` case of
`jl_egal__bitstag`, src/builtins.c:346-351). -/
def identicalString (a b : JString) : Bool := a.bytes == b.bytes

/--
Julia source: base/strings/lazy.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(s::LazyString, h::UInt64) = hash(String(s), h)
```
-/
def hash {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (s : LazyString Ref E V)
    (h : JuliaLean.base.hashing.Word) : M World E JuliaLean.base.hashing.Word := do
  let str ← toString fields c displaySize a s
  pure (JuliaLean.Bindings.base.hashing.hashStringBound str h)

/--
Julia source: base/strings/lazy.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(s::LazyString) = lastindex(String(s))
```
`lastindex(s::String) = thisind(s, ncodeunits(s)::Int)` (string.jl:249). -/
def lastindex {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (s : LazyString Ref E V) : M World E Index := do
  let str ← toString fields c displaySize a s
  match JuliaLean.base.strings.string.lastindexString
      JuliaLean.base.strings.string.stringNcodeunits
      JuliaLean.base.strings.string.stringBetweenIndex
      JuliaLean.base.strings.string.stringBetweenByte
      JuliaLean.base.strings.string.stringCodeunitAt str with
  | .ok index => pure index
  | .error error => throw (LazyError.string error)

/--
Julia source: base/strings/lazy.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(s::LazyString) = iterate(String(s))
```
`iterate(s::String, i::Int=firstindex(s))` (string.jl:508-514) at its default `i`. -/
def iterate0 {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (s : LazyString Ref E V) :
    M World E (Option (UInt32 × Index)) := do
  let str ← toString fields c displaySize a s
  pure (JuliaLean.base.strings.string.stringIterate str
    (JuliaLean.base.strings.string.stringFirstindex str))

/--
Julia source: base/strings/lazy.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(s::LazyString, i::Integer) = iterate(String(s), i)
```
`i` is converted by `toInt`, the `Int(i)::Int` of the index type, after `String(s)`. -/
def iterateAt {World Ref E V Ty I : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (toInt : I → Except (LazyError E) JInt64)
    (s : LazyString Ref E V) (i : I) : M World E (Option (UInt32 × Index)) := do
  let str ← toString fields c displaySize a s
  let index ← liftPure (toInt i)
  pure (JuliaLean.base.strings.string.stringIterate str index)

/--
Julia source: base/strings/lazy.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isequal(a::LazyString, b::LazyString) = isequal(String(a), String(b))
```
`isequal(x, y) = (x == y)::Bool` (operators.jl:196) over `==(::String, ::String)`
(string.jl:238). -/
def isequal {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (x y : LazyString Ref E V) : M World E Bool := do
  let first ← toString fields c displaySize a x
  let second ← toString fields c displaySize a y
  pure (JuliaLean.base.operators.isequalDefault
    (JuliaLean.base.strings.string.eqString identicalString) first second)

/--
Julia source: base/strings/lazy.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::LazyString, b::LazyString) = (String(a) == String(b))
```
`==(a::String, b::String) = a===b` (string.jl:238). -/
def eq {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (x y : LazyString Ref E V) : M World E Bool := do
  let first ← toString fields c displaySize a x
  let second ← toString fields c displaySize a y
  pure (JuliaLean.base.strings.string.eqString identicalString first second)

/--
Julia source: base/strings/lazy.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::LazyString) = ncodeunits(String(s))
```
`ncodeunits(s::String) = Core.sizeof(s)` (string.jl:209). -/
def ncodeunits {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (s : LazyString Ref E V) : M World E Index := do
  let str ← toString fields c displaySize a s
  pure (JuliaLean.base.strings.string.stringNcodeunits str)

/--
Julia source: base/strings/lazy.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::LazyString) = codeunit("") # returns UInt8
```
`codeunit("")` calls `codeunit(s::String) = UInt8` (string.jl:210) on the empty literal; the
lazy string is not forced. -/
def codeunitType {Ref E V : Type} (_s : LazyString Ref E V) : Type :=
  JuliaLean.base.strings.string.codeunitType

/--
Julia source: base/strings/lazy.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::LazyString, i::Integer) = codeunit(String(s), i)
```
`codeunit(s::String, i::Integer) = codeunit(s, Int(i)::Int)` (string.jl:212), then
`codeunit(s::String, i::Int)` with its `@boundscheck` (string.jl:213-217). -/
def codeunitAt {World Ref E V Ty I : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (toInt : I → Except (LazyError E) JInt64)
    (s : LazyString Ref E V) (i : I) : M World E UInt8 := do
  let str ← toString fields c displaySize a s
  let index ← liftPure (toInt i)
  match JuliaLean.base.strings.string.stringCodeunitAt true str index with
  | .ok unit => pure unit
  | .error error => throw (LazyError.string error)

/--
Julia source: base/strings/lazy.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::LazyString) = codeunits(String(s))
```
`codeunits(s::AbstractString) = CodeUnits(s)` (basic.jl:827), `CodeUnits{codeunit(s),S}`
(basic.jl:788). -/
def codeunits {World Ref E V Ty : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (s : LazyString Ref E V) :
    M World E (JuliaLean.base.strings.basic.CodeUnits
      JuliaLean.base.strings.string.codeunitType JString) := do
  let str ← toString fields c displaySize a s
  pure (JuliaLean.base.strings.basic.codeunits
    (fun _ => JuliaLean.base.strings.string.codeunitType) str)

/--
Julia source: base/strings/lazy.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(s::LazyString, i::Integer) = isvalid(String(s), i)
```
`isvalid(s::AbstractString, i::Integer) = isvalid(s, Int(i)::Int)` (basic.jl:143-144), then
`isvalid(s::String, i::Int)` (string.jl:662). -/
def isvalid {World Ref E V Ty I : Type}
    (fields : JuliaLean.base.atomics.Fields World Ref (Option JString))
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (toInt : I → Except (LazyError E) JInt64)
    (s : LazyString Ref E V) (i : I) : M World E Bool := do
  let str ← toString fields c displaySize a s
  let index ← liftPure (toInt i)
  pure (JuliaLean.base.strings.string.stringIsvalidIndex str index)

end JuliaLean.base.strings.lazy


/-!
Models for `base/strings/lazy.jl` at Julia `bbfa0ce4150`.  Printed parts are
represented by their resulting byte strings; this keeps the model focused on
the lazy cache and the `AbstractString` forwarding methods.
-/

namespace JuliaLean.StringsCovA.Lazy

structure LazyString where
  parts : List (List UInt8)
  compact : Bool
  cached : Option (List UInt8)

/-- `_LazyString(parts, str)`; `base/strings/lazy.jl:41`. -/
def privateCtor (parts : List (List UInt8)) (str : Option (List UInt8)) : LazyString :=
  ⟨parts, false, str⟩

/-- `LazyString(args...; compact)`; `base/strings/lazy.jl:42`. -/
def ctor (parts : List (List UInt8)) (compact : Bool := false) : LazyString :=
  ⟨parts, compact, none⟩

/-- The parts assembled by `@lazy_str`; `base/strings/lazy.jl:73-87`. -/
def lazyMacro (literalAndInterpolatedParts : List (List UInt8)) (compactFlag : Bool) : LazyString :=
  ctor literalAndInterpolatedParts compactFlag

/-- The bytes printed by the delayed interpolation. -/
def render (parts : List (List UInt8)) : List UInt8 := parts.flatten

/-- `String(l::LazyString)`; `base/strings/lazy.jl:89-101`. -/
def materialize (l : LazyString) : List UInt8 :=
  l.cached.getD (render l.parts)

/-- `hash(s::LazyString, h)`; `base/strings/lazy.jl:103`. -/
def hash (H : List UInt8 → UInt64 → UInt64) (s : LazyString) (h : UInt64) : UInt64 :=
  H (materialize s) h

/-- `lastindex(s::LazyString)`; `base/strings/lazy.jl:104`. -/
def lastindex (stringLastindex : List UInt8 → Int) (s : LazyString) :=
  stringLastindex (materialize s)

/-- `iterate(s::LazyString)`; `base/strings/lazy.jl:105`. -/
def iterate0 {α : Type} (stringIterate : List UInt8 → Option α) (s : LazyString) :=
  stringIterate (materialize s)

/-- `iterate(s::LazyString, i)`; `base/strings/lazy.jl:106`. -/
def iterateAt {α : Type} (stringIterate : List UInt8 → Int → Option α)
    (s : LazyString) (i : Int) := stringIterate (materialize s) i

/-- `isequal(a::LazyString, b::LazyString)`; `base/strings/lazy.jl:107`. -/
def isequal (a b : LazyString) : Bool := materialize a == materialize b

/-- `==(a::LazyString, b::LazyString)`; `base/strings/lazy.jl:108`. -/
def eq (a b : LazyString) : Bool := materialize a == materialize b

/-- `ncodeunits(s::LazyString)`; `base/strings/lazy.jl:109`. -/
def ncodeunits (s : LazyString) : Nat := (materialize s).length

/-- `codeunit(s::LazyString)`; `base/strings/lazy.jl:110`. -/
def codeunitType (_s : LazyString) : Nat := 8

/-- `codeunit(s::LazyString, i)`; `base/strings/lazy.jl:111`. -/
def codeunitAt (s : LazyString) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ (materialize s).length then
    .ok ((materialize s).getD (i.toNat - 1) 0)
  else .error .boundsError

/-- `codeunits(s::LazyString)`; `base/strings/lazy.jl:112`. -/
def codeunits (s : LazyString) : List UInt8 := materialize s

/-- `isvalid(s::LazyString, i)`; `base/strings/lazy.jl:113`. -/
def isvalid (stringIsvalid : List UInt8 → Int → Bool) (s : LazyString) (i : Int) : Bool :=
  stringIsvalid (materialize s) i

end JuliaLean.StringsCovA.Lazy


namespace JuliaLean.StringsCovA.LazyFaithful

open JuliaLean

abbrev JString := Strings.JStr
abbrev Index := JInt64
abbrev Word := IntFuncsCov.Hashing.Word

inductive LazyError where
  | methodError (target : String)
  | argumentErrorFlags (flags : List String)
  | parseError (code : Nat)
  | printError (code : Nat)
  | stringError (error : Strings.SErr)
  deriving Repr, DecidableEq

abbrev LazyResult (α : Type) := Except LazyError α

def liftStringResult : Strings.SJl α → LazyResult α
  | .ok value => .ok value
  | .error error => .error (.stringError error)

def liftIntResult : Jl α → LazyResult α
  | .ok value => .ok value
  | .error error => .error (.stringError (.jl error))

/--
An arbitrary captured Julia value. `identity` represents the value stored in
the source tuple. `print` is its dynamically dispatched `print(io, value)`
behavior on the actual mutable output buffer, including seeks, truncation, and
exceptions. Its Boolean arguments are the `:compact` and `:limit` IOContext
properties. `base/strings/lazy.jl:36-42,94-97`.
-/
structure Part where
  identity : Nat
  print : Bool → Bool → JString → LazyResult JString

structure Lazy where
  parts : List Part
  compact : Bool
  cache : Option JString

structure PartsField where
  converted : LazyResult (List Part)

structure CacheField where
  converted : LazyResult (Option JString)

/-- `_LazyString(parts, str) = new(parts, false, str)`, `base/strings/lazy.jl:41`. -/
def privateCtor (parts : PartsField) (str : CacheField) : LazyResult Lazy :=
  do
    let values ← parts.converted
    let cached ← str.converted
    return ⟨values, false, cached⟩

/-- `LazyString(args...; compact::Bool=false)`, `base/strings/lazy.jl:42`. -/
def ctor (args : List Part) (compact : Bool := false) : Lazy :=
  ⟨args, compact, none⟩

structure MacroExpr where
  identity : Nat
  deriving Repr, DecidableEq

inductive MacroPart where
  | literal (value : JString)
  | escaped (expr : MacroExpr)
  deriving Repr, DecidableEq

structure MacroExpansion where
  parts : List MacroPart
  compact : Bool
  deriving Repr, DecidableEq

structure Parsed (start : Index) where
  expr : MacroExpr
  next : Index
  advances : start.val < next.val

abbrev ParseAtom :=
  (text : JString) → (start : Index) → String → LazyResult (Parsed start)

/-- `text[first:last]` with Julia's range indexing and UTF-8 checks. -/
def textSliceInclusive (text : JString) (first last : Index) : LazyResult JString :=
  liftStringResult (Strings.getindexRange text first last)

/--
The `while` loop of `@lazy_str`, `base/strings/lazy.jl:77-85`. Each successful
parse advances past at least the dollar byte, so `ncodeunits(text)+1` iterations
cannot truncate the loop. The zero branch is consequently unreachable from
`lazyStr` while the loop condition holds.
-/
def lazyLoop (parseatom : ParseAtom) (filename : String) (text : JString) :
    Nat → Index → Index → List MacroPart → LazyResult (List MacroPart)
  | 0, _, _, parts => .ok parts
  | fuel + 1, lastidx, idx, parts => do
      let found ← liftStringResult (Strings.findnextChar 0x24000000 text idx)
      match found with
      | none =>
          if lastidx.val ≤ (Strings.lastindex text).val then
            let literal ← textSliceInclusive text lastidx (Strings.lastindex text)
            return parts ++ [.literal literal]
          else
            return parts
      | some dollar =>
          let parts ←
            if lastidx.val < dollar.val then
              let previous ← liftStringResult (Strings.prevind text dollar)
              let literal ← textSliceInclusive text lastidx previous
              pure (parts ++ [.literal literal])
            else
              pure parts
          let parseidx := dollar + Strings.ix 1
          let parsed ← parseatom text parseidx filename
          lazyLoop parseatom filename text fuel parsed.next parsed.next
            (parts ++ [.escaped parsed.expr])

/-- `macro lazy_str(text, flags...)`, `base/strings/lazy.jl:73-87`. -/
def lazyStr (parseatom : ParseAtom) (sourceFile : String) (text : JString)
    (flags : List String) : LazyResult MacroExpansion :=
  let compact := flags == ["c"]
  if !flags.isEmpty && !compact then
    .error (.argumentErrorFlags flags)
  else do
    let parts ← lazyLoop parseatom sourceFile text (text.bytes.length + 1)
      (Strings.ix 1) (Strings.ix 1) []
    return ⟨parts, compact⟩

/-- Execute `foreach(Fix1(print, io), parts)` from left to right. -/
def printParts (compact limit : Bool) : List Part → JString → LazyResult JString
  | [], output => .ok output
  | part :: parts, output => do
      let output ← part.print compact limit output
      printParts compact limit parts output

/-- The `sprint` block at `base/strings/lazy.jl:92-98`. -/
def sprintParts (parts : List Part) (compact : Bool) : LazyResult JString :=
  printParts compact compact parts Strings.JStr.empty

structure StringCall where
  outcome : LazyResult JString
  cache : Option JString

/--
`String(l::LazyString)`, `base/strings/lazy.jl:89-101`. `concurrent` is the
cache value after printing finishes or throws. A successful compare-exchange
stores this task's string exactly when it is still `nothing`.
-/
def toString (l : Lazy) (concurrent : Option JString) : StringCall :=
  match l.cache with
  | some old => ⟨.ok old, some old⟩
  | none =>
      match sprintParts l.parts l.compact with
      | .error error => ⟨.error error, concurrent⟩
      | .ok rendered =>
          match concurrent with
          | none => ⟨.ok rendered, some rendered⟩
          | some old => ⟨.ok old, some old⟩

structure UnaryCall (α : Type) where
  outcome : LazyResult α
  cache : Option JString

structure BinaryCall (α : Type) where
  outcome : LazyResult α
  leftCache : Option JString
  rightCache : Option JString

inductive IntegerValue where
  | int (value : JInt64)
  | other (value : Int)

def integerToInt : IntegerValue → LazyResult JInt64
  | .int value => .ok value
  | .other value => liftIntResult (JInt.convert (IntTy.i64.name) .i64 value)

/-- `hash(s::LazyString, h)`, `base/strings/lazy.jl:103`. -/
def hash (s : Lazy) (h : Word) (secret : Word × Word × Word × Word)
    (concurrent : Option JString) : UnaryCall Word :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      ⟨.ok (IntFuncsCov.Hashing.hashBytes string.bytes h secret), call.cache⟩

/-- `lastindex(s::LazyString)`, `base/strings/lazy.jl:104`. -/
def lastindex (s : Lazy) (concurrent : Option JString) : UnaryCall JInt64 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.lastindex string), call.cache⟩

/-- `iterate(s::LazyString)`, `base/strings/lazy.jl:105`. -/
def iterate0 (s : Lazy) (concurrent : Option JString) :
    UnaryCall (Option (UInt32 × JInt64)) :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.iterate string (Strings.ix 1)), call.cache⟩

/-- `iterate(s::LazyString, i::Integer)`, `base/strings/lazy.jl:106`. -/
def iterateAt (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall (Option (UInt32 × JInt64)) :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨.ok (Strings.iterate string index), call.cache⟩

/-- `isequal(a::LazyString, b::LazyString)`, `base/strings/lazy.jl:107`. -/
def isequal (a b : Lazy) (leftConcurrent rightConcurrent : Option JString) :
    BinaryCall Bool :=
  let left := toString a leftConcurrent
  match left.outcome with
  | .error error => ⟨.error error, left.cache, b.cache⟩
  | .ok leftString =>
      let right := toString b rightConcurrent
      match right.outcome with
      | .error error => ⟨.error error, left.cache, right.cache⟩
      | .ok rightString =>
          ⟨.ok (leftString.bytes == rightString.bytes), left.cache, right.cache⟩

/-- `==(a::LazyString, b::LazyString)`, `base/strings/lazy.jl:108`. -/
def eq (a b : Lazy) (leftConcurrent rightConcurrent : Option JString) :
    BinaryCall Bool :=
  let left := toString a leftConcurrent
  match left.outcome with
  | .error error => ⟨.error error, left.cache, b.cache⟩
  | .ok leftString =>
      let right := toString b rightConcurrent
      match right.outcome with
      | .error error => ⟨.error error, left.cache, right.cache⟩
      | .ok rightString =>
          ⟨.ok (leftString.bytes == rightString.bytes), left.cache, right.cache⟩

/-- `ncodeunits(s::LazyString)`, `base/strings/lazy.jl:109`. -/
def ncodeunits (s : Lazy) (concurrent : Option JString) : UnaryCall JInt64 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.ncodeunits string), call.cache⟩

inductive JuliaType where
  | uint8
  deriving Repr, DecidableEq

/-- `codeunit(s::LazyString) = codeunit("")`, `base/strings/lazy.jl:110`. -/
def codeunitType (_s : Lazy) : JuliaType := .uint8

/-- `codeunit(s::LazyString, i::Integer)`, `base/strings/lazy.jl:111`. -/
def codeunitAt (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall UInt8 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨liftStringResult (Strings.codeunit string index), call.cache⟩

structure CodeUnits where
  string : JString
  deriving Repr, DecidableEq

/-- `codeunits(s::LazyString)`, `base/strings/lazy.jl:112`. -/
def codeunits (s : Lazy) (concurrent : Option JString) : UnaryCall CodeUnits :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok ⟨string⟩, call.cache⟩

/-- `isvalid(s::LazyString, i::Integer)`, `base/strings/lazy.jl:113`. -/
def isvalid (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall Bool :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨.ok (Strings.isvalidAt string index), call.cache⟩

end JuliaLean.StringsCovA.LazyFaithful
