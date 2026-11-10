import JuliaLean.Compiler.Prelude

/-!
The inlining-size helpers of `Compiler/src/utilities.jl`: `count_const_size` and
`is_inlineable_constant`. They decide whether a constant may be embedded in inlined code and,
through `is_result_constabi_eligible` (`typeinfer.lean`), whether a `CodeInstance` gets the
constant-return ABI and loses its inferred source.

The function reads the memory layout of each object's type (`sizeof`, `isbits`,
`datatype_pointerfree`, which fields are stored as pointers and which fields of a mutable type are
`const`) and the fields of the mutable objects it walks. The C type model records neither, so the
model takes them as tables (`ConstLayout`), filled from the pinned Julia by the difftest.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- The layout facts `count_const_size` reads for one concrete `DataType`: `sizeof(dt)`,
`isbitstype(dt)`, `datatype_pointerfree(dt)`, `DataTypeFieldDesc(dt)[i].isptr` for each field,
and `isconst(dt, i)` for each field (all `true` for an immutable type). -/
structure DTFacts where
  size : Nat
  isbits : Bool
  pointerfree : Bool
  isptr : List Bool
  isconst : List Bool
  deriving Repr, Inhabited

/-- The tables `count_const_size` needs: layout facts by type, and the fields of the mutable
objects (`Val.mutableRef`) it may walk, by object id, with `none` for an undefined field. -/
structure ConstLayout where
  dts : List (Val × DTFacts) := []
  heap : List (Nat × List (Option Val)) := []
  deriving Inhabited

def ConstLayout.facts (C : ConstLayout) (dt : Val) : CM DTFacts :=
  match C.dts.find? (·.1 == dt) with
  | some (_, f) => pure f
  | none => unmodelled s!"layout of {repr dt}"

/-- `MAX_INLINE_CONST_SIZE` (`Compiler/src/utilities.jl:35`). -/
def MAX_INLINE_CONST_SIZE : Nat := 256

/-- The type name of `typeof(x)`, for the `isa` tests on builtin types. -/
def typeNameOf (x : Val) : String :=
  match typeOf x with
  | .datatype name _ => name
  | _ => ""

/-- `isdefined(x, i) ? getfield(x, i) : nothing` for the objects `count_const_size` walks:
immutable structs (their defined fields are a prefix), `TypeVar`s (`name`, `lb`, `ub`), `Vararg`s
(`T`, `N`, either undefined) and the mutable objects of the heap table. -/
def fieldOf (C : ConstLayout) (x : Val) (i : Nat) : CM (Option Val) :=
  match x with
  | .imm _ fs => pure fs[i - 1]?
  | .typevar _ nm lb ub => pure ([Val.symbol nm, lb, ub])[i - 1]?
  | .vararg T N => pure (match i with | 1 => T | 2 => N | _ => none)
  | .mutableRef _ a =>
    match C.heap.lookup a.toNat with
    | some fs => pure (fs[i - 1]?).join
    | none => unmodelled s!"fields of object {a}"
  | _ => unmodelled s!"fields of {repr x}"

/-- `count_const_size(x, count_self)`

Julia source: Compiler/src/utilities.jl:37-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function count_const_size(@nospecialize(x), count_self::Bool = true)
    (x isa Type || x isa Core.TypeName || x isa Symbol) && return 0
    if ismutable(x)
        # No definite size
        (isa(x, GenericMemory) || isa(x, String) || isa(x, SimpleVector)) &&
            return MAX_INLINE_CONST_SIZE + 1
        if isa(x, Module) || isa(x, Method) || isa(x, CodeInstance)
            # We allow modules, methods and CodeInstance, because we already assume they are externally
            # rooted, so we count their contents as 0 size.
            return sizeof(Ptr{Cvoid})
        end
        # We allow mutable types with no mutable fields (i.e. those mutable
        # types used for identity only). The intent of this function is to
        # prevent the rooting of large amounts of data that may have been
        # speculatively computed. If the struct can get mutated later, we
        # cannot assess how much data we might end up rooting. However, if
        # the struct is mutable only for identity, the query still works.
        for i = 1:nfields(x)
            if !isconst(typeof(x), i)
                return MAX_INLINE_CONST_SIZE + 1
            end
        end
    end
    isbits(x) && return Core.sizeof(x)
    dt = typeof(x)
    sz = count_self ? sizeof(dt) : 0
    sz > MAX_INLINE_CONST_SIZE && return MAX_INLINE_CONST_SIZE + 1
    dtfd = DataTypeFieldDesc(dt)
    for i = 1:Int(datatype_nfields(dt))
        isdefined(x, i) || continue
        f = getfield(x, i)
        if !dtfd[i].isptr && datatype_pointerfree(typeof(f))
            continue
        end
        sz += count_const_size(f, dtfd[i].isptr)
        sz > MAX_INLINE_CONST_SIZE && return MAX_INLINE_CONST_SIZE + 1
    end
    return sz
end
```
`sizeof(Ptr{Cvoid})` is 8 (64-bit). -/
def countConstSize (n : Nat) (E : CEnv) (C : ConstLayout) (x : Val) (countSelf : Bool := true) :
    CM Nat :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let tn := typeNameOf x
    if x.isType || tn == "Core.TypeName" || x.isSymbol then return 0
    if ← ismutable E x then
      if tn == "Core.GenericMemory" || tn == "Core.String" || tn == "Core.SimpleVector" then
        return MAX_INLINE_CONST_SIZE + 1
      if x.isModule || tn == "Core.Method" || tn == "Core.CodeInstance" then
        return 8
      let f ← C.facts (typeOf x)
      for i in [1:f.isconst.length + 1] do
        if !(f.isconst[i - 1]?.getD false) then
          return MAX_INLINE_CONST_SIZE + 1
    let dt := typeOf x
    let f ← C.facts dt
    if f.isbits then return f.size
    let mut sz := if countSelf then f.size else 0
    if sz > MAX_INLINE_CONST_SIZE then return MAX_INLINE_CONST_SIZE + 1
    for i in [1:f.isptr.length + 1] do
      let some fv ← fieldOf C x i | continue
      let isptr := f.isptr[i - 1]?.getD false
      if !isptr then
        if (← C.facts (typeOf fv)).pointerfree then
          continue
      sz := sz + (← countConstSize n E C fv isptr)
      if sz > MAX_INLINE_CONST_SIZE then return MAX_INLINE_CONST_SIZE + 1
    return sz

/-- `is_inlineable_constant(x)`

Julia source: Compiler/src/utilities.jl:77-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_inlineable_constant(@nospecialize(x))
    return count_const_size(x) <= MAX_INLINE_CONST_SIZE
end
```
-/
def isInlineableConstant (n : Nat) (E : CEnv) (C : ConstLayout) (x : Val) : CM Bool := do
  return (← countConstSize n E C x) ≤ MAX_INLINE_CONST_SIZE

end JuliaLean.Compiler
