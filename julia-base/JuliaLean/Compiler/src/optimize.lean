import JuliaLean.Core
import JuliaLean.Compiler.src.effects

/-!
Model of the inlining cost model and the statement-flag encoding of `Compiler/src/optimize.jl`:
the `SLOT_*`, `IR_FLAG_*` and `IR_FLAGS_*` constants, `has_flag`, `iscallstmt`,
`flags_for_effects`, `inlining_cost`, `is_inlineable`, `set_inlineable!`, `inline_cost_clamp`,
`is_declared_inline`/`is_declared_noinline`, both `src_inlining_policy` methods,
`is_stmt_inline`/`is_stmt_noinline`, `plus_saturate`, `statement_cost`,
`statement_or_branch_cost`, `inline_cost_model(::IRCode, ...)` and `statement_costs!`.

It also models the code these call or that decides with them outside that file:

* `jl_encode_inlining_cost`, `jl_decode_inlining_cost`, `jl_ir_inlining_cost` and
  `jl_ir_flag_inlining` (`src/ircode.c`), and the part of `jl_compress_ir` that stores the
  `inlining` flag and the cost byte;
* the threshold logic `inline_cost_model(interp, result, inline_flag, ir)` and
  `is_result_constabi_eligible` (`Compiler/src/typeinfer.jl`).

Modelling choices:

* Julia `Int` is `JInt64` (wrapping), `UInt32`/`UInt16`/`UInt8` are Lean's `UInt32`/`UInt16`/
  `UInt8`. C `unsigned` arithmetic on a `uint16_t` input never exceeds 32 bits here, so it is
  `Nat` arithmetic, truncated where C converts to the result type.
* `statement_cost` asks type questions about the statement's arguments (`argextype`,
  `singleton_type`, `isknowntype`, `isdispatchelem`, `isconcretedispatch`, `isconstType`) and
  reads the `add_tfunc` cost tables (`T_IFUNC`, `T_IFUNC_COST`, `T_FFUNC_COST`, filled across
  `Compiler/src/tfuncs.jl`). Those answers are inputs here (`Callee`, `ArgFacts`, `CallFacts`):
  the model mirrors the order in which the code asks them, the branches and the arithmetic.
  Reading an argument the statement does not have is a `BoundsError`, as in Julia. A fact the
  driver did not supply where the model reads it is a model failure (`argumentError "fact"`),
  never a Julia outcome.
* A source (`CodeInfo`, compressed `String`, `UInt8`, `IRCode`, `OptimizationState`) is `Src`,
  holding only the fields these functions read.
* The facts the threshold logic reads about an `InferenceResult` (whether `def` is a `Method`,
  the shape of `specTypes`, the return type tests, the method's module and name) are inputs
  (`ResultFacts`).

All sources are at master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.Compiler.Optimize

open JuliaLean JuliaLean.Compiler

/-- Julia `Int`. -/
abbrev JI := JInt64

/-- An `Int` literal. -/
def ji (x : Int) : JI := JInt.lit .i64 x

/-- `max(x, y)` on `Int`. -/
def jmax (x y : JI) : JI := if y.val < x.val then x else y

/-! ## Constants

Julia source: Compiler/src/optimize.jl:11-71
```julia
const SLOT_STATICUNDEF  = 1 # slot might be used before it is defined (structurally)
const SLOT_ASSIGNEDONCE = 16 # slot is assigned to only once
const SLOT_USEDUNDEF    = 32 # slot has uses that might raise UndefVarError

const IR_FLAG_NULL        = zero(UInt32)
const IR_FLAG_INBOUNDS    = one(UInt32) << 0
const IR_FLAG_INLINE      = one(UInt32) << 1
const IR_FLAG_NOINLINE    = one(UInt32) << 2
const IR_FLAG_CONSISTENT  = one(UInt32) << 3
const IR_FLAG_EFFECT_FREE = one(UInt32) << 4
const IR_FLAG_NOTHROW     = one(UInt32) << 5
const IR_FLAG_TERMINATES  = one(UInt32) << 6
#const IR_FLAG_TERMINATES_LOCALLY = one(UInt32) << 7
#const IR_FLAG_NOTASKSTATE = one(UInt32) << 8
#const IR_FLAG_INACCESSIBLEMEM = one(UInt32) << 9
const IR_FLAG_NOUB        = one(UInt32) << 10
#const IR_FLAG_NOUBINIB   = one(UInt32) << 11
#const IR_FLAG_CONSISTENTOVERLAY = one(UInt32) << 12
const IR_FLAG_NORTCALL = one(UInt32) << 13
const IR_FLAG_RESET_SAFE = one(UInt32) << 14
# Reserved: one(UInt32) << 15 used for RSIIMO below
const IR_FLAG_REFINED     = one(UInt32) << 16
const IR_FLAG_UNUSED      = one(UInt32) << 17
const IR_FLAG_EFIIMO      = one(UInt32) << 18
const IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM = one(UInt32) << 19
const IR_FLAG_RSIIMO      = one(UInt32) << 20

const NUM_IR_FLAGS = 3 # sync with julia.h

const IR_FLAGS_EFFECTS =
    IR_FLAG_CONSISTENT | IR_FLAG_EFFECT_FREE | IR_FLAG_NOTHROW |
    IR_FLAG_TERMINATES | IR_FLAG_NOUB | IR_FLAG_NORTCALL | IR_FLAG_RESET_SAFE

const IR_FLAGS_REMOVABLE = IR_FLAG_EFFECT_FREE | IR_FLAG_NOTHROW | IR_FLAG_TERMINATES

const IR_FLAGS_NEEDS_EA = IR_FLAG_EFIIMO | IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM
```
(Comment lines between the constants are left out.) `NUM_IR_FLAGS` is
`JuliaLean.Compiler.NUM_IR_FLAGS` of the effects model. The C side defines
`IR_FLAG_INBOUNDS 0x01` and `IR_FLAG_RESET_SAFE (1 << 14)` (src/julia_internal.h:2314-2316)
and `NUM_IR_FLAGS 3` (src/julia.h:380). -/

def SLOT_STATICUNDEF : UInt8 := 1
def SLOT_ASSIGNEDONCE : UInt8 := 16
def SLOT_USEDUNDEF : UInt8 := 32

def IR_FLAG_NULL : UInt32 := 0
def IR_FLAG_INBOUNDS : UInt32 := (1 : UInt32) <<< 0
def IR_FLAG_INLINE : UInt32 := (1 : UInt32) <<< 1
def IR_FLAG_NOINLINE : UInt32 := (1 : UInt32) <<< 2
def IR_FLAG_CONSISTENT : UInt32 := (1 : UInt32) <<< 3
def IR_FLAG_EFFECT_FREE : UInt32 := (1 : UInt32) <<< 4
def IR_FLAG_NOTHROW : UInt32 := (1 : UInt32) <<< 5
def IR_FLAG_TERMINATES : UInt32 := (1 : UInt32) <<< 6
def IR_FLAG_NOUB : UInt32 := (1 : UInt32) <<< 10
def IR_FLAG_NORTCALL : UInt32 := (1 : UInt32) <<< 13
def IR_FLAG_RESET_SAFE : UInt32 := (1 : UInt32) <<< 14
def IR_FLAG_REFINED : UInt32 := (1 : UInt32) <<< 16
def IR_FLAG_UNUSED : UInt32 := (1 : UInt32) <<< 17
def IR_FLAG_EFIIMO : UInt32 := (1 : UInt32) <<< 18
def IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM : UInt32 := (1 : UInt32) <<< 19
def IR_FLAG_RSIIMO : UInt32 := (1 : UInt32) <<< 20

def IR_FLAGS_EFFECTS : UInt32 :=
  IR_FLAG_CONSISTENT ||| IR_FLAG_EFFECT_FREE ||| IR_FLAG_NOTHROW |||
  IR_FLAG_TERMINATES ||| IR_FLAG_NOUB ||| IR_FLAG_NORTCALL ||| IR_FLAG_RESET_SAFE

def IR_FLAGS_REMOVABLE : UInt32 := IR_FLAG_EFFECT_FREE ||| IR_FLAG_NOTHROW ||| IR_FLAG_TERMINATES

def IR_FLAGS_NEEDS_EA : UInt32 := IR_FLAG_EFIIMO ||| IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM

/-- The C definitions of the two flags the runtime reads (src/julia_internal.h:2314-2316):
```c
#define IR_FLAG_INBOUNDS 0x01
// This statement is proven :reset_safe (sync with Compiler/src/optimize.jl)
#define IR_FLAG_RESET_SAFE (1 << 14)
```
-/
def C_IR_FLAG_INBOUNDS : UInt32 := 0x01
def C_IR_FLAG_RESET_SAFE : UInt32 := (1 : UInt32) <<< 14

/-- Julia source: Compiler/src/types.jl:11-13
```julia
const InlineCostType = UInt16
const MAX_INLINE_COST = typemax(InlineCostType)
const MIN_INLINE_COST = InlineCostType(10)
```
-/
def MAX_INLINE_COST : UInt16 := 0xffff
def MIN_INLINE_COST : UInt16 := 10

/-- Julia source: Compiler/src/optimize.jl:139-140
```julia
const SRC_FLAG_DECLARED_INLINE = 0x1
const SRC_FLAG_DECLARED_NOINLINE = 0x2
```
-/
def SRC_FLAG_DECLARED_INLINE : UInt8 := 0x1
def SRC_FLAG_DECLARED_NOINLINE : UInt8 := 0x2

/-- `has_flag(curr::UInt32, flag::UInt32) = (curr & flag) == flag`

Julia source: Compiler/src/optimize.jl:73 -/
def hasFlag (curr flag : UInt32) : Bool := (curr &&& flag) == flag

/-- `iscallstmt`; the statement is `none` when it is not an `Expr`, else `some head`.

Julia source: Compiler/src/optimize.jl:75-79
```julia
function iscallstmt(@nospecialize stmt)
    stmt isa Expr || return false
    head = stmt.head
    return head === :call || head === :invoke || head === :foreigncall || head === :foreignglobal
end
```
-/
def iscallstmt : Option String → Bool
  | none => false
  | some head => head == "call" || head == "invoke" || head == "foreigncall" || head == "foreignglobal"

/-- Julia source: Compiler/src/optimize.jl:81-121
```julia
function flags_for_effects(effects::Effects)
    flags = zero(UInt32)
    if is_consistent(effects)
        flags |= IR_FLAG_CONSISTENT
    end
    if is_effect_free(effects)
        flags |= IR_FLAG_EFFECT_FREE
    elseif is_effect_free_if_inaccessiblememonly(effects)
        flags |= IR_FLAG_EFIIMO
    end
    # (comment)
    if is_reset_safe(effects) && is_effect_free(effects)
        flags |= IR_FLAG_RESET_SAFE
    elseif is_reset_safe_if_inaccessiblememonly(effects) && is_effect_free_if_inaccessiblememonly(effects)
        flags |= IR_FLAG_RSIIMO
    end
    if is_nothrow(effects)
        flags |= IR_FLAG_NOTHROW
    end
    if is_terminates(effects)
        flags |= IR_FLAG_TERMINATES
    end
    if is_inaccessiblemem_or_argmemonly(effects)
        flags |= IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM
    end
    if is_noub(effects)
        flags |= IR_FLAG_NOUB
    end
    if is_nortcall(effects)
        flags |= IR_FLAG_NORTCALL
    end
    return flags
end
```
-/
def flagsForEffects (e : Effects) : UInt32 :=
  let f : UInt32 := 0
  let f := if isConsistent e then f ||| IR_FLAG_CONSISTENT else f
  let f := if isEffectFree e then f ||| IR_FLAG_EFFECT_FREE
    else if isEffectFreeIfInaccessiblememonly e then f ||| IR_FLAG_EFIIMO else f
  let f := if isResetSafe e && isEffectFree e then f ||| IR_FLAG_RESET_SAFE
    else if isResetSafeIfInaccessiblememonly e && isEffectFreeIfInaccessiblememonly e then
      f ||| IR_FLAG_RSIIMO
    else f
  let f := if isNothrow e then f ||| IR_FLAG_NOTHROW else f
  let f := if isTerminates e then f ||| IR_FLAG_TERMINATES else f
  let f := if isInaccessiblememOrArgmemonly e then f ||| IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM else f
  let f := if isNoub e then f ||| IR_FLAG_NOUB else f
  let f := if isNortcall e then f ||| IR_FLAG_NORTCALL else f
  f

/-- `is_stmt_inline(stmt_flag::UInt32) = has_flag(stmt_flag, IR_FLAG_INLINE)`

Julia source: Compiler/src/optimize.jl:355 -/
def isStmtInline (flag : UInt32) : Bool := hasFlag flag IR_FLAG_INLINE

/-- `is_stmt_noinline(stmt_flag::UInt32) = has_flag(stmt_flag, IR_FLAG_NOINLINE)`

Julia source: Compiler/src/optimize.jl:356 -/
def isStmtNoinline (flag : UInt32) : Bool := hasFlag flag IR_FLAG_NOINLINE

/-! ## The compressed cost (src/ircode.c) -/

/-- The `while` loop of `jl_encode_inlining_cost`: the least `shift` with
`inlining_cost >> 5 >> shift == 0`. The fuel 16 is never reached: a `uint16_t` shifted right by
5 is below `2^11`, so the loop stops at a shift of at most 11. -/
def encodeShift (c : Nat) : Nat → Nat → Nat
  | 0, shift => shift
  | fuel + 1, shift => if (c >>> 5) >>> shift != 0 then encodeShift c fuel (shift + 1) else shift

/-- Julia source: src/ircode.c:1234-1253
```c
// create a compressed u16 value with range 0..3968, 3 bits exponent, 5 bits mantissa, implicit first digit, rounding up, full accuracy over 0..63
JL_DLLEXPORT uint8_t jl_encode_inlining_cost(uint16_t inlining_cost)
{
    unsigned shift = 0;
    unsigned mantissa;
    if (inlining_cost <= 0x1f) {
        mantissa = inlining_cost;
    }
    else {
        while (inlining_cost >> 5 >> shift != 0)
            shift++;
        assert(1 <= shift && shift <= 11);
        mantissa = (inlining_cost >> (shift - 1)) & 0x1f;
        mantissa += (inlining_cost & ((1 << (shift - 1)) - 1)) != 0; // round up if trailing bits non-zero, overflowing into exp
    }
    unsigned r = (shift << 5) + mantissa;
    if (r > 0xff)
        r = 0xff;
    return r;
}
```
-/
def jlEncodeInliningCost (cost : UInt16) : UInt8 :=
  let c := cost.toNat
  let (shift, mantissa) :=
    if c ≤ 0x1f then (0, c)
    else
      let shift := encodeShift c 16 0
      let mantissa := (c >>> (shift - 1)) &&& 0x1f
      let mantissa := mantissa + (if c &&& ((1 <<< (shift - 1)) - 1) != 0 then 1 else 0)
      (shift, mantissa)
  let r := (shift <<< 5) + mantissa
  let r := if r > 0xff then 0xff else r
  r.toUInt8

/-- Julia source: src/ircode.c:1255-1264
```c
JL_DLLEXPORT uint16_t jl_decode_inlining_cost(uint8_t inlining_cost)
{
    unsigned shift = inlining_cost >> 5;
    if (inlining_cost == 0xff)
        return 0xffff;
    else if (shift == 0)
        return inlining_cost;
    else
        return (0x20 | (inlining_cost & 0x1f)) << (shift - 1);
}
```
-/
def jlDecodeInliningCost (b : UInt8) : UInt16 :=
  let c := b.toNat
  let shift := c >>> 5
  if b == 0xff then 0xffff
  else if shift == 0 then b.toUInt16
  else ((0x20 ||| (c &&& 0x1f)) <<< (shift - 1)).toUInt16

/-- A source as the inlining code sees it. `codeInfo` holds the `CodeInfo` fields
`inlining_cost` and `inlining`; `compressed` is a `String` from `jl_compress_ir`, holding its
cost byte and its `inlining` bitfield; `uint8` is a bare cost byte; `optState` is an
`OptimizationState` whose `src` is the `CodeInfo` given; `other` is anything else (`nothing`,
a `CodeInstance` is excluded by an assertion). -/
inductive Src where
  | codeInfo (inliningCost : UInt16) (inlining : UInt8)
  | compressed (costByte : UInt8) (inlining : UInt8)
  | uint8 (b : UInt8)
  | irCode
  | optState (inliningCost : UInt16) (inlining : UInt8)
  | other
  deriving Repr, DecidableEq, Inhabited

/-- What `jl_compress_ir` stores of a `CodeInfo`'s `inlining` and `inlining_cost`.

Julia source: src/ircode.c:1034-1041 and src/julia_internal.h:804
```c
    jl_code_info_flags_t flags = code_info_flags(code->propagate_inbounds, code->has_fcall, code->has_image_globalref,
                                                 code->nospecializeinfer, code->isva,
                                                 code->inlining, code->constprop,
                                                 nargsmatchesmethod,
                                                 code->ssaflags);
    write_uint16(s.s, checked_size(flags.packed, IR_DATASIZE_FLAGS));
    write_uint16(s.s, checked_size(code->purity.bits, IR_DATASIZE_PURITY));
    write_uint8(s.s, checked_size(jl_encode_inlining_cost(code->inlining_cost), IR_DATASIZE_INLINING_COST));
```
with `uint16_t inlining:2;` in `jl_code_info_flags_bitfield_t`: the bitfield keeps the low two
bits of `code->inlining` (`code_info_flags`, src/ircode.c:562, `flags.bits.inlining = inlining`).
-/
def compressCodeInfo (inliningCost : UInt16) (inlining : UInt8) : Src :=
  .compressed (jlEncodeInliningCost inliningCost) (inlining &&& 3)

/-- `jl_ir_inlining_cost` on a `UInt8`, a `CodeInfo` or a `String`; `none` for other inputs
(the C code asserts a `String`).

Julia source: src/ircode.c:1266-1275
```c
JL_DLLEXPORT uint16_t jl_ir_inlining_cost(jl_value_t *data)
{
    if (jl_is_uint8(data))
        return jl_decode_inlining_cost(*(uint8_t*)data);
    if (jl_is_code_info(data))
        return ((jl_code_info_t*)data)->inlining_cost;
    assert(jl_is_string(data));
    uint16_t res = jl_decode_inlining_cost(*(uint8_t*)(jl_string_data(data) + ir_offset_inlining_cost));
    return res;
}
```
-/
def jlIrInliningCost : Src → Option UInt16
  | .uint8 b => some (jlDecodeInliningCost b)
  | .codeInfo c _ => some c
  | .compressed b _ => some (jlDecodeInliningCost b)
  | _ => none

/-- `jl_ir_flag_inlining` on a `CodeInfo` or a `String`.

Julia source: src/ircode.c:1201-1209
```c
JL_DLLEXPORT uint8_t jl_ir_flag_inlining(jl_string_t *data)
{
    if (jl_is_code_info(data))
        return ((jl_code_info_t*)data)->inlining;
    assert(jl_is_string(data));
    jl_code_info_flags_t flags;
    flags.packed = jl_string_data(data)[ir_offset_flags];
    return flags.bits.inlining;
}
```
-/
def jlIrFlagInlining : Src → Option UInt8
  | .codeInfo _ i => some i
  | .compressed _ i => some i
  | _ => none

/-- Julia source: Compiler/src/optimize.jl:125-126
```julia
inlining_cost(@nospecialize src) =
    src isa Union{MaybeCompressed,UInt8} ? ccall(:jl_ir_inlining_cost, InlineCostType, (Any,), src) : MAX_INLINE_COST
```
-/
def inliningCost (src : Src) : UInt16 :=
  match src with
  | .codeInfo .. | .compressed .. | .uint8 _ => (jlIrInliningCost src).getD MAX_INLINE_COST
  | _ => MAX_INLINE_COST

/-- `is_inlineable(@nospecialize src) = inlining_cost(src) != MAX_INLINE_COST`

Julia source: Compiler/src/optimize.jl:127 -/
def isInlineable (src : Src) : Bool := inliningCost src != MAX_INLINE_COST

/-- The `inlining_cost` that `set_inlineable!` stores.

Julia source: Compiler/src/optimize.jl:128-129
```julia
set_inlineable!(src::CodeInfo, val::Bool) =
    src.inlining_cost = (val ? MIN_INLINE_COST : MAX_INLINE_COST)
```
-/
def setInlineable (val : Bool) : UInt16 := if val then MIN_INLINE_COST else MAX_INLINE_COST

/-- Julia source: Compiler/src/optimize.jl:131-137
```julia
function inline_cost_clamp(x::Int)
    x > MAX_INLINE_COST && return MAX_INLINE_COST
    x < MIN_INLINE_COST && return MIN_INLINE_COST
    x = ccall(:jl_encode_inlining_cost, UInt8, (InlineCostType,), x)
    x = ccall(:jl_decode_inlining_cost, InlineCostType, (UInt8,), x)
    return x
end
```
The `ccall` converts `x`, now in `10:65535`, to `UInt16` exactly. -/
def inlineCostClamp (x : JI) : UInt16 :=
  if x.val > (MAX_INLINE_COST.toNat : Int) then MAX_INLINE_COST
  else if x.val < (MIN_INLINE_COST.toNat : Int) then MIN_INLINE_COST
  else jlDecodeInliningCost (jlEncodeInliningCost x.val.toNat.toUInt16)

/-- `is_declared_inline`; `methodError` on a source that is not `MaybeCompressed`.

Julia source: Compiler/src/optimize.jl:142-143
```julia
is_declared_inline(@nospecialize src::MaybeCompressed) =
    ccall(:jl_ir_flag_inlining, UInt8, (Any,), src) == SRC_FLAG_DECLARED_INLINE
```
-/
def isDeclaredInline (src : Src) : Jl Bool :=
  match src with
  | .codeInfo .. | .compressed .. =>
    match jlIrFlagInlining src with
    | some i => pure (i == SRC_FLAG_DECLARED_INLINE)
    | none => throw (.methodError "is_declared_inline")
  | _ => throw (.methodError "is_declared_inline")

/-- Julia source: Compiler/src/optimize.jl:145-146
```julia
is_declared_noinline(@nospecialize src::MaybeCompressed) =
    ccall(:jl_ir_flag_inlining, UInt8, (Any,), src) == SRC_FLAG_DECLARED_NOINLINE
```
-/
def isDeclaredNoinline (src : Src) : Jl Bool :=
  match src with
  | .codeInfo .. | .compressed .. =>
    match jlIrFlagInlining src with
    | some i => pure (i == SRC_FLAG_DECLARED_NOINLINE)
    | none => throw (.methodError "is_declared_noinline")
  | _ => throw (.methodError "is_declared_noinline")

/-- Julia source: Compiler/src/optimize.jl:164-176
```julia
function src_inlining_policy(::AbstractInterpreter,
    @nospecialize(src), @nospecialize(info::CallInfo), stmt_flag::UInt32)
    isa(src, OptimizationState) && (src = src.src)
    if isa(src, MaybeCompressed)
        src_inlineable = is_stmt_inline(stmt_flag) || is_inlineable(src)
        return src_inlineable
    elseif isa(src, IRCode)
        return true
    end
    @assert !isa(src, CodeInstance) # handled by caller
    return false
end
```
-/
def srcInliningPolicy (src : Src) (stmtFlag : UInt32) : Bool :=
  let src := match src with
    | .optState c i => Src.codeInfo c i
    | s => s
  match src with
  | .codeInfo .. | .compressed .. => isStmtInline stmtFlag || isInlineable src
  | .irCode => true
  | _ => false

/-- The method-instance method of `src_inlining_policy`. `defIsMethod`, `hasGenerator` and
`mayInvokeGenerator` are `isa(mi.def, Method)`, `hasgenerator(mi)` and
`may_invoke_generator(mi)`.

Julia source: Compiler/src/optimize.jl:154-162
```julia
function src_inlining_policy(interp::AbstractInterpreter, mi::MethodInstance,
    @nospecialize(src), @nospecialize(info::CallInfo), stmt_flag::UInt32)
    # If we have a generator, but we can't invoke it (because argument type information is lacking),
    # don't inline so we defer its invocation to runtime where we'll have precise type information.
    if isa(mi.def, Method) && hasgenerator(mi)
        may_invoke_generator(mi) || return false
    end
    return src_inlining_policy(interp, src, info, stmt_flag)
end
```
-/
def srcInliningPolicyMI (defIsMethod hasGenerator mayInvokeGenerator : Bool) (src : Src)
    (stmtFlag : UInt32) : Bool :=
  if defIsMethod && hasGenerator && !mayInvokeGenerator then false
  else srcInliningPolicy src stmtFlag

/-! ## The cost of a statement -/

/-- `plus_saturate(x::Int, y::Int) = max(x, y, x+y)`

Julia source: Compiler/src/optimize.jl:1787-1788
```julia
# saturating sum (inputs are non-negative), prevents overflow with typemax(Int) below
plus_saturate(x::Int, y::Int) = max(x, y, x+y)
```
-/
def plusSaturate (x y : JI) : JI := jmax (jmax x y) (x + y)

/-- The builtins `statement_cost` names, by identity. -/
inductive BuiltinKind where
  | getfield | tuple | getglobal
  | memoryrefget | constMemoryrefget | memoryrefIsassigned
  | memoryrefset | memoryrefunset
  | typeassert | invoke | other
  deriving Repr, DecidableEq, Inhabited

/-- `f = singleton_type(ftyp)` as `statement_cost` classifies it.

* `intrinsic assigned minarg maxarg cost llvmcall`: an `IntrinsicFunction`; `assigned` is
  `isassigned(T_IFUNC, iidx)`, and when it is, `(minarg, maxarg)` are the first two entries of
  `T_IFUNC[iidx]` and `cost` is `T_IFUNC_COST[iidx]`; `llvmcall` is `f === Intrinsics.llvmcall`.
  `maxarg` is an `Int` and may be `INT_INF = typemax(Int)` (Compiler/src/tfuncs.jl:52), so
  `maxarg + 1` wraps.
* `builtin kind tfuncCost`: a `Builtin`; `tfuncCost` is `T_FFUNC_COST[find_tfunc(f)]`, or
  `none` when `find_tfunc(f) === nothing`.
* `other`: anything else (`nothing` included). -/
inductive Callee where
  | intrinsic (assigned : Bool) (minarg maxarg : JI) (cost : JI) (llvmcall : Bool)
  | builtin (kind : BuiltinKind) (tfuncCost : Option JI)
  | other
  deriving Repr, Inhabited

/-- The type answers about one argument `a = ex.args[i]` (`i ≥ 2`):
* `dispatchelem`: `isdispatchelem(widenconst_split(widenconditional(argextype(a, ...))))`;
* `constConcrete`: with `aty = widenconditional(argextype(a, ...))`,
  `aty isa Const && isconcretedispatch(widenconst_split(aty))`;
* `known`: `isknowntype(argextype(a, ...))`;
* `constType`: `isconstType(argextype_widened(a, ...))`. -/
structure ArgFacts where
  dispatchelem : Bool
  constConcrete : Bool
  known : Bool
  constType : Bool
  deriving Repr, Inhabited

/-- The answers `statement_cost` reads about a `:call` statement `ex`.

* `c0`: the callee from `ftyp = argextype(ex.args[1], ...)`;
* `ftypIntrinsic`: `ftyp === IntrinsicFunction`; `fargSSA`: `ex.args[1] isa SSAValue`;
* `defRecoverable`: the statement defining that `SSAValue` is a `GlobalRef`, `QuoteNode`,
  `IntrinsicFunction` or `Expr(:static_parameter)`, and `c1` the callee from its `argextype`;
* `nargs`: `length(ex.args)`;
* `args`: the facts of `ex.args[2]`, `ex.args[3]`, ... (`none` where not supplied);
* `retBottom`: `argextype(SSAValue(line), ...) === Union{}` (read only when `line ≠ -1`). -/
structure CallFacts where
  c0 : Callee
  ftypIntrinsic : Bool
  fargSSA : Bool
  defRecoverable : Bool
  c1 : Callee
  nargs : Nat
  args : List (Option ArgFacts)
  retBottom : Bool
  deriving Repr, Inhabited

/-- An `Expr` statement as `statement_cost` reads it: its head and the answers above.
`metaHead` is a head with `is_meta_expr_head` (`:boundscheck`, `:meta`, `:loopinfo`).
`invoke` covers the heads `:invoke` and `:invoke_modify`; `assign` is `:(=)` with whether the
left side is a `GlobalRef` or `Core.BindingPartition`, and `assignExpr` the same with a right
side that is an `Expr`; `other` is any other head. -/
inductive SExpr where
  | metaHead
  | call (c : CallFacts)
  | foreigncall (stringPtr : Bool)
  | foreignglobal
  | invoke (retBottom : Bool)
  | assign (lhsGlobal : Bool)
  | assignExpr (lhsGlobal : Bool) (rhs : SExpr)
  | copyast
  | other
  deriving Repr, Inhabited

/-- A statement: an `Expr`, a `GotoNode` (its label), a `GotoIfNot` (its `dest`), an
`EnterNode`, or anything else. -/
inductive Stmt where
  | expr (e : SExpr)
  | goto (label : Int)
  | gotoifnot (dest : Int)
  | enter
  | other
  deriving Repr, Inhabited

/-- `UNKNOWN_CALL_COST = 20` (Compiler/src/optimize.jl:1795). -/
def UNKNOWN_CALL_COST : JI := ji 20

/-- `ex.args[i]`'s facts; `BoundsError` past the end, a model failure if not supplied. -/
def argAt (c : CallFacts) (i : Nat) : Jl ArgFacts :=
  if i < 2 ∨ c.nargs < i then throw .boundsError
  else match c.args[i - 2]? with
    | some (some a) => pure a
    | _ => throw (.argumentError "fact")

/-- The callee after the recovery step of `statement_cost` (Compiler/src/optimize.jl:1800-1810). -/
def resolveCallee (c : CallFacts) : Callee :=
  if c.ftypIntrinsic && c.fargSSA && c.defRecoverable then c.c1 else c.c0

/-- The loop over `i = 2:nargs` of the intrinsic case: `none` when some argument is not a
dispatch element (`return cost`), else the count `nconst`. -/
def intrinsicConstCount (c : CallFacts) : Nat → Nat → Int → Jl (Option Int)
  | 0, _, nconst => pure (some nconst)
  | k + 1, i, nconst => do
    let a ← argAt c i
    if !a.dispatchelem then return none
    intrinsicConstCount c k (i + 1) (nconst + (if a.constConcrete then 1 else 0))

/-- Julia source: Compiler/src/optimize.jl:1793-1907
```julia
function statement_cost(ex::Expr, line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState},
                        params::OptimizationParams)
    #=const=# UNKNOWN_CALL_COST = 20
    head = ex.head
    if is_meta_expr_head(head)
        return 0
    elseif head === :call
        farg = ex.args[1]
        ftyp = argextype(farg, src, sptypes)
        if ftyp === IntrinsicFunction && farg isa SSAValue
            # if this comes from code that was already inlined into another function,
            # Consts have been widened. try to recover in simple cases.
            farg = isa(src, CodeInfo) ? src.code[farg.id] : src[farg][:stmt]
            if isa(farg, GlobalRef) || isa(farg, QuoteNode) || isa(farg, IntrinsicFunction) || isexpr(farg, :static_parameter)
                ftyp = argextype(farg, src, sptypes)
            end
        end
        f = singleton_type(ftyp)
        if isa(f, IntrinsicFunction)
            iidx = Int(reinterpret(Int32, f::IntrinsicFunction)) + 1
            if isassigned(T_IFUNC, iidx)
                minarg, maxarg, = T_IFUNC[iidx]
                nargs = length(ex.args)
                if minarg + 1 <= nargs <= maxarg + 1
                    # (comment)
                    cost = T_IFUNC_COST[iidx]
                    if cost == 0 || nargs < 3 || f === Intrinsics.llvmcall
                        # llvmcall holds malformed IR, so argextype will crash on it
                        return cost
                    end
                    nconst = 0
                    for i = 2:nargs
                        aty = widenconditional(argextype(ex.args[i], src, sptypes))
                        aty′ = widenconst_split(aty)
                        if !isdispatchelem(aty′)
                            return cost
                        end
                        nconst += aty isa Const && isconcretedispatch(aty′)
                    end
                    if nconst > 0 && nconst + 2 >= nargs
                        cost = (cost - 1) ÷ 2
                    end
                    return cost
                end
            end
            # unknown/unhandled intrinsic: hopefully the caller gets a slightly better answer after the inlining
            return UNKNOWN_CALL_COST
        end
        if isa(f, Builtin) && f !== invoke
            # (comment)
            if f === Core.getfield || f === Core.tuple || f === Core.getglobal
                # (comment)
                return 0
            elseif (f === Core.memoryrefget || f === Core.const_memoryrefget || f === Core.memoryref_isassigned) && length(ex.args) >= 3
                atyp = argextype(ex.args[2], src, sptypes)
                return isknowntype(atyp) ? 1 : params.inline_nonleaf_penalty
            elseif f === Core.memoryrefset! && length(ex.args) >= 3
                atyp = argextype(ex.args[2], src, sptypes)
                return isknowntype(atyp) ? 5 : params.inline_nonleaf_penalty
            elseif f === Core.memoryrefunset! && length(ex.args) >= 3
                atyp = argextype(ex.args[2], src, sptypes)
                return isknowntype(atyp) ? 5 : params.inline_nonleaf_penalty
            elseif f === typeassert && isconstType(argextype_widened(ex.args[3], src, sptypes))
                return 1
            end
            fidx = find_tfunc(f)
            if fidx === nothing
                # unknown/unhandled builtin
                # Use the generic cost of a direct function call
                return UNKNOWN_CALL_COST
            end
            return T_FFUNC_COST[fidx]
        end
        extyp = line == -1 ? Any : argextype(SSAValue(line), src, sptypes)
        if extyp === Union{}
            return 0
        end
        return params.inline_nonleaf_penalty
    elseif head === :foreigncall
        foreigncall = ex.args[1]
        if isexpr(foreigncall, :tuple, 1)
            foreigncall = foreigncall.args[1]
            if foreigncall isa QuoteNode && foreigncall.value === :jl_string_ptr
                return 1
            end
        end
        return 20
    elseif head === :foreignglobal
        return 1
    elseif head === :invoke || head === :invoke_modify
        # (comment)
        extyp = line == -1 ? Any : argextype(SSAValue(line), src, sptypes)
        return extyp === Union{} ? 0 : UNKNOWN_CALL_COST
    elseif head === :(=)
        # A resolved store to a global should cost the same or less than the `setglobal!` tfunc declared.
        lhs = ex.args[1]
        cost = (isa(lhs, GlobalRef) || isa(lhs, Core.BindingPartition)) ? 3 : 0
        rhs = ex.args[2]
        isa(rhs, Expr) && (cost += statement_cost(rhs, -1, src, sptypes, params))
        return cost
    elseif head === :copyast
        return 100
    end
    return 0
end
```
`penalty` is `params.inline_nonleaf_penalty`. -/
def statementCost (penalty : JI) : SExpr → Int → Jl JI
  | .metaHead, _ => pure (ji 0)
  | .call c, line => do
    match resolveCallee c with
    | .intrinsic assigned minarg maxarg cost llvmcall =>
      if assigned then
        let nargs : Int := c.nargs
        if (minarg + ji 1).val ≤ nargs ∧ nargs ≤ (maxarg + ji 1).val then
          if cost.val == 0 ∨ nargs < 3 ∨ llvmcall then return cost
          match ← intrinsicConstCount c (c.nargs - 1) 2 0 with
          | none => return cost
          | some nconst =>
            if nconst > 0 ∧ nconst + 2 ≥ nargs then JInt.div (cost - ji 1) (ji 2)
            else return cost
        else return UNKNOWN_CALL_COST
      else return UNKNOWN_CALL_COST
    | .builtin kind tfuncCost =>
      if kind != .invoke then
        if kind == .getfield ∨ kind == .tuple ∨ kind == .getglobal then return ji 0
        if (kind == .memoryrefget ∨ kind == .constMemoryrefget ∨ kind == .memoryrefIsassigned) ∧
            c.nargs ≥ 3 then
          return if (← argAt c 2).known then ji 1 else penalty
        if kind == .memoryrefset ∧ c.nargs ≥ 3 then
          return if (← argAt c 2).known then ji 5 else penalty
        if kind == .memoryrefunset ∧ c.nargs ≥ 3 then
          return if (← argAt c 2).known then ji 5 else penalty
        if kind == .typeassert then
          if (← argAt c 3).constType then return ji 1
        match tfuncCost with
        | none => return UNKNOWN_CALL_COST
        | some k => return k
      else
        let bottom := if line == -1 then false else c.retBottom
        return if bottom then ji 0 else penalty
    | .other =>
      let bottom := if line == -1 then false else c.retBottom
      return if bottom then ji 0 else penalty
  | .foreigncall stringPtr, _ => pure (if stringPtr then ji 1 else ji 20)
  | .foreignglobal, _ => pure (ji 1)
  | .invoke retBottom, line =>
    let bottom := if line == -1 then false else retBottom
    pure (if bottom then ji 0 else UNKNOWN_CALL_COST)
  | .assign lhsGlobal, _ => pure (if lhsGlobal then ji 3 else ji 0)
  | .assignExpr lhsGlobal rhs, _ => do
    let cost := if lhsGlobal then ji 3 else ji 0
    return cost + (← statementCost penalty rhs (-1))
  | .copyast, _ => pure (ji 100)
  | .other, _ => pure (ji 0)

/-- Where a branch to `tgt` lands: `tgt` itself in a `CodeInfo`, the first statement of block
`tgt` in an `IRCode` (`blockFirst` lists `first(src.cfg.blocks[b].stmts)` for each block). -/
def branchDst (isIR : Bool) (blockFirst : List Int) (tgt : Int) : Jl Int :=
  if !isIR then pure tgt
  else if tgt < 1 then throw .boundsError
  else match blockFirst[tgt.toNat - 1]? with
    | some d => pure d
    | none => throw .boundsError

/-- Julia source: Compiler/src/optimize.jl:1909-1930
```julia
function statement_or_branch_cost(@nospecialize(stmt), line::Int, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState},
                                  params::OptimizationParams)
    thiscost = 0
    dst(tgt) = isa(src, IRCode) ? first(src.cfg.blocks[tgt].stmts) : tgt
    if stmt isa Expr
        thiscost = statement_cost(stmt, line, src, sptypes, params)::Int
    elseif stmt isa GotoNode
        # loops are generally always expensive
        # but assume that forward jumps are already counted for from
        # summing the cost of the not-taken branch
        thiscost = dst(stmt.label) < line ? 40 : 0
    elseif stmt isa GotoIfNot
        thiscost = dst(stmt.dest) < line ? 40 : 0
    elseif stmt isa EnterNode
        # (comment)
        thiscost = typemax(Int)
    end
    return thiscost
end
```
-/
def statementOrBranchCost (isIR : Bool) (blockFirst : List Int) (penalty : JI) (stmt : Stmt)
    (line : Int) : Jl JI :=
  match stmt with
  | .expr e => statementCost penalty e line
  | .goto label => do return if (← branchDst isIR blockFirst label) < line then ji 40 else ji 0
  | .gotoifnot dest => do return if (← branchDst isIR blockFirst dest) < line then ji 40 else ji 0
  | .enter => pure (JInt.typemax .i64)
  | .other => pure (ji 0)

/-- The loop of `inline_cost_model(::IRCode, ...)` from statement `line` on. -/
def inlineCostLoop (blockFirst : List Int) (penalty threshold : JI) :
    List Stmt → Int → JI → Jl UInt16
  | [], _, bodycost => pure (inlineCostClamp bodycost)
  | s :: rest, line, bodycost => do
    let thiscost ← statementOrBranchCost true blockFirst penalty s line
    let bodycost := plusSaturate bodycost thiscost
    if bodycost > threshold then return MAX_INLINE_COST
    inlineCostLoop blockFirst penalty threshold rest (line + 1) bodycost

/-- `stmts` are the statements `ir[SSAValue(i)][:stmt]` for `i = 1:length(ir.stmts)`.

Julia source: Compiler/src/optimize.jl:1932-1943
```julia
function inline_cost_model(ir::IRCode, params::OptimizationParams, cost_threshold::Int)
    bodycost = 0
    for i = 1:length(ir.stmts)
        stmt = ir[SSAValue(i)][:stmt]
        thiscost = statement_or_branch_cost(stmt, i, ir, ir.sptypes, params)
        bodycost = plus_saturate(bodycost, thiscost)
        if bodycost > cost_threshold
            return MAX_INLINE_COST
        end
    end
    return inline_cost_clamp(bodycost)
end
```
-/
def inlineCostModel (blockFirst : List Int) (penalty threshold : JI) (stmts : List Stmt) :
    Jl UInt16 :=
  inlineCostLoop blockFirst penalty threshold stmts 1 (ji 0)

/-- The loop of `statement_costs!`: the costs written to `cost[line]` and the final `maxcost`. -/
def statementCostsLoop (isIR : Bool) (blockFirst : List Int) (penalty : JI) :
    List Stmt → Int → JI → Jl (List JI × JI)
  | [], _, maxcost => pure ([], maxcost)
  | s :: rest, line, maxcost => do
    let thiscost ← statementOrBranchCost isIR blockFirst penalty s line
    let maxcost := if thiscost > maxcost then thiscost else maxcost
    let (cs, m) ← statementCostsLoop isIR blockFirst penalty rest (line + 1) maxcost
    return (thiscost :: cs, m)

/-- The values written to `cost` and the returned `maxcost`.

Julia source: Compiler/src/optimize.jl:1945-1957
```julia
function statement_costs!(cost::Vector{Int}, body::Vector{Any}, src::Union{CodeInfo, IRCode}, sptypes::Vector{VarState}, params::OptimizationParams)
    maxcost = 0
    for line = 1:length(body)
        stmt = body[line]
        thiscost = statement_or_branch_cost(stmt, line, src, sptypes,
                                            params)
        cost[line] = thiscost
        if thiscost > maxcost
            maxcost = thiscost
        end
    end
    return maxcost
end
```
-/
def statementCosts (isIR : Bool) (blockFirst : List Int) (penalty : JI) (body : List Stmt) :
    Jl (List JI × JI) :=
  statementCostsLoop isIR blockFirst penalty body 1 (ji 0)

/-! ## The threshold logic (Compiler/src/typeinfer.jl) -/

/-- The fields of `OptimizationParams(interp)` the cost model reads. -/
structure CostParams where
  inline_cost_threshold : JI
  inline_nonleaf_penalty : JI
  inline_tupleret_bonus : JI
  deriving Repr

/-- What `inline_cost_model(interp, result, inline_flag, ir)` asks about `result`:

* `defIsMethod`: `isa(result.linfo.def, Method)`;
* `sigIsTuple`: `isa(sig, DataType) && sig.name === Tuple.name` for
  `sig = unwrap_unionall(result.linfo.specTypes)`;
* `rtIsBottom`: `widenslotwrapper(result.result) === Bottom`;
* `isDispatchTuple`: `isdispatchtuple(specTypes)`;
* `tupleRet`: `⊑(optimizer_lattice(interp), rt, Tuple) && !isconcretetype(widenconst(rt))`;
* `moduleIsTop`: `def.module === _topmod(def.module)`, and `name` is `def.name`. -/
structure ResultFacts where
  defIsMethod : Bool
  sigIsTuple : Bool
  rtIsBottom : Bool
  isDispatchTuple : Bool
  tupleRet : Bool
  moduleIsTop : Bool
  name : String
  deriving Repr, Inhabited

/-- The threshold `inline_cost_model(interp, ...)` passes on, or its early result. -/
def costThreshold (p : CostParams) (r : ResultFacts) (declaredInline : Bool) : JI :=
  let default := p.inline_cost_threshold
  let t := default
  let t := if r.tupleRet then t + p.inline_tupleret_bonus else t
  let t := if declaredInline then t + ji 19 * default else t
  let t := if r.moduleIsTop ∧ (r.name == "iterate" ∨ r.name == "unsafe_convert" ∨ r.name == "cconvert")
    then t + ji 4 * default else t
  t

/-- `stmts` and `blockFirst` describe `ir` as for `inlineCostModel`. The assertion
`@assert !(rt isa LimitedAccuracy)` is not modelled.

Julia source: Compiler/src/typeinfer.jl:498-546
```julia
function inline_cost_model(interp::AbstractInterpreter, result::InferenceResult,
        inline_flag::UInt8, ir::IRCode)

    inline_flag === SRC_FLAG_DECLARED_NOINLINE && return MAX_INLINE_COST

    mi = result.linfo
    (; def, specTypes) = mi
    if !isa(def, Method)
        return MAX_INLINE_COST
    end

    declared_inline = inline_flag === SRC_FLAG_DECLARED_INLINE

    rt = result.result
    @assert !(rt isa LimitedAccuracy)
    rt = widenslotwrapper(rt)

    sig = unwrap_unionall(specTypes)
    if !(isa(sig, DataType) && sig.name === Tuple.name)
        return MAX_INLINE_COST
    end
    if !declared_inline && rt === Bottom
        return MAX_INLINE_COST
    end

    if declared_inline && isdispatchtuple(specTypes)
        # obey @inline declaration if a dispatch barrier would not help
        return MIN_INLINE_COST
    else
        # compute the cost (size) of inlining this code
        params = OptimizationParams(interp)
        cost_threshold = default = params.inline_cost_threshold
        if ⊑(optimizer_lattice(interp), rt, Tuple) && !isconcretetype(widenconst(rt))
            cost_threshold += params.inline_tupleret_bonus
        end
        # if the method is declared as `@inline`, increase the cost threshold 20x
        if declared_inline
            cost_threshold += 19*default
        end
        # a few functions get special treatment
        if def.module === _topmod(def.module)
            name = def.name
            if name === :iterate || name === :unsafe_convert || name === :cconvert
                cost_threshold += 4*default
            end
        end
        return inline_cost_model(ir, params, cost_threshold)
    end
end
```
-/
def inlineCostModelResult (p : CostParams) (r : ResultFacts) (inlineFlag : UInt8)
    (blockFirst : List Int) (stmts : List Stmt) : Jl UInt16 :=
  if inlineFlag == SRC_FLAG_DECLARED_NOINLINE then pure MAX_INLINE_COST
  else if !r.defIsMethod then pure MAX_INLINE_COST
  else
    let declaredInline := inlineFlag == SRC_FLAG_DECLARED_INLINE
    if !r.sigIsTuple then pure MAX_INLINE_COST
    else if !declaredInline && r.rtIsBottom then pure MAX_INLINE_COST
    else if declaredInline && r.isDispatchTuple then pure MIN_INLINE_COST
    else inlineCostModel blockFirst p.inline_nonleaf_penalty (costThreshold p r declaredInline) stmts

/-- `isConst` is `isa(result.result, Const)`, `valInlineable` is
`is_inlineable_constant(result.result.val)` (read only when `isConst`).

Julia source: Compiler/src/typeinfer.jl:483-486
```julia
function is_result_constabi_eligible(result::InferenceResult)
    result_type = result.result
    return isa(result_type, Const) && is_foldable_nothrow(result.ipo_effects) && is_inlineable_constant(result_type.val)
end
```
-/
def isResultConstabiEligible (isConst : Bool) (ipoEffects : Effects) (valInlineable : Bool) : Bool :=
  isConst && isFoldableNothrow ipoEffects && valInlineable

end JuliaLean.Compiler.Optimize
