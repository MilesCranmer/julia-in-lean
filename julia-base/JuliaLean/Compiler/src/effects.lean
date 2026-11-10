import JuliaLean.base.expr

/-!
Model of `Compiler/src/effects.jl`: the `Effects` record, its constants, `merge_effects`,
`is_better_effects`, the `is_*` queries, and the `UInt32` encoding that `CodeInstance`
stores in `ipo_purity_bits`. It also models where the effects and their overrides are read and
written outside that file:

* `override_effects` (`Compiler/src/abstractinterpretation.jl`), the call-site and `ccall`
  override application, and the method-level part of `adjust_effects`
  (`Compiler/src/typeinfer.jl`);
* `decode_statement_effects_override`, which reads the override bits of a statement flag;
* the C side: how `jl_method_set_source` (`src/method.c`) turns `Expr(:purity, ...)` into
  `Method.purity` and statement flags, and the two C readers of `ipo_purity_bits`,
  `effects_foldable` (`src/staticdata.c`) and `effects_ipo_reset_safe` (`src/codegen.cpp`).

`EffectsOverride` and `encode_effects_override`/`decode_effects_override` (`base/expr.jl`) are
the existing Base model in `JuliaLean.base.expr`; this file only adapts their `UInt16` type.

Julia's `UInt8`, `UInt16` and `UInt32` are Lean's `UInt8`, `UInt16` and `UInt32`: both wrap
modulo `2^n`, and `x % UInt32` of a `UInt8` is `x.toUInt32` (zero extension). Every shift
here is by a constant below the width, where Lean's `<<<`/`>>>` (shift modulo the width) and
Julia's `<<`/`>>` agree. `Bool % UInt32` is `0` or `1`.

All sources are at master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.Compiler

/-- `struct Effects`

Julia source: Compiler/src/effects.jl:132-166
```julia
struct Effects
    consistent::UInt8
    effect_free::UInt8
    reset_safe::UInt8
    nothrow::Bool
    terminates::Bool
    notaskstate::Bool
    inaccessiblememonly::UInt8
    noub::UInt8
    nonoverlayed::UInt8
    nortcall::Bool
    function Effects(
        consistent::UInt8,
        ...
        nortcall::Bool)
        return new(
            consistent,
            ...
            nortcall)
    end
end
```
The inner constructor only stores its arguments, so it is the structure's constructor. -/
structure Effects where
  consistent : UInt8
  effect_free : UInt8
  reset_safe : UInt8
  nothrow : Bool
  terminates : Bool
  notaskstate : Bool
  inaccessiblememonly : UInt8
  noub : UInt8
  nonoverlayed : UInt8
  nortcall : Bool
  deriving DecidableEq, Repr, Inhabited

/-! Julia source: Compiler/src/effects.jl:168-195
```julia
const ALWAYS_TRUE  = 0x00
const ALWAYS_FALSE = 0x01

# :consistent-cy bits
const CONSISTENT_IF_NOTRETURNED         = 0x01 << 1
const CONSISTENT_IF_INACCESSIBLEMEMONLY = 0x01 << 2

# :effect_free-ness bits
const EFFECT_FREE_IF_INACCESSIBLEMEMONLY = 0x02

const EFFECT_FREE_GLOBALLY = 0x03

# :inaccessiblememonly bits
const INACCESSIBLEMEM_OR_ARGMEMONLY = 0x01 << 1

# :noub bits
const NOUB_IF_NOINBOUNDS = 0x01 << 1

# :nonoverlayed bits
const CONSISTENT_OVERLAY = 0x01 << 1

# :reset_safe bits
const RESET_SAFE_IF_INACCESSIBLEMEMONLY = 0x01 << 1
```
`0x01 << 1` is a `UInt8` shifted by an `Int`, which stays `UInt8`. -/
def ALWAYS_TRUE : UInt8 := 0x00
def ALWAYS_FALSE : UInt8 := 0x01
def CONSISTENT_IF_NOTRETURNED : UInt8 := (0x01 : UInt8) <<< 1
def CONSISTENT_IF_INACCESSIBLEMEMONLY : UInt8 := (0x01 : UInt8) <<< 2
def EFFECT_FREE_IF_INACCESSIBLEMEMONLY : UInt8 := 0x02
def EFFECT_FREE_GLOBALLY : UInt8 := 0x03
def INACCESSIBLEMEM_OR_ARGMEMONLY : UInt8 := (0x01 : UInt8) <<< 1
def NOUB_IF_NOINBOUNDS : UInt8 := (0x01 : UInt8) <<< 1
def CONSISTENT_OVERLAY : UInt8 := (0x01 : UInt8) <<< 1
def RESET_SAFE_IF_INACCESSIBLEMEMONLY : UInt8 := (0x01 : UInt8) <<< 1

/-! Julia source: Compiler/src/effects.jl:197-200
```julia
const EFFECTS_TOTAL   = Effects(ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE, true,  true,  true,  ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE, true)
const EFFECTS_THROWS  = Effects(ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE, false, true,  true,  ALWAYS_TRUE,  ALWAYS_TRUE,  ALWAYS_TRUE, true)
const EFFECTS_UNKNOWN = Effects(ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false, false, false, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_TRUE, false) # unknown mostly, but it's not overlayed at least (e.g. it's not a call)
const EFFECTS_MINIMAL = Effects(ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false, false, false, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false)
```
-/
def EFFECTS_TOTAL : Effects :=
  ⟨ALWAYS_TRUE, ALWAYS_TRUE, ALWAYS_TRUE, true, true, true, ALWAYS_TRUE, ALWAYS_TRUE, ALWAYS_TRUE, true⟩
def EFFECTS_THROWS : Effects :=
  ⟨ALWAYS_TRUE, ALWAYS_TRUE, ALWAYS_TRUE, false, true, true, ALWAYS_TRUE, ALWAYS_TRUE, ALWAYS_TRUE, true⟩
def EFFECTS_UNKNOWN : Effects :=
  ⟨ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false, false, false, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_TRUE,
    false⟩
def EFFECTS_MINIMAL : Effects :=
  ⟨ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE, false, false, false, ALWAYS_FALSE, ALWAYS_FALSE, ALWAYS_FALSE,
    false⟩

/-- `Effects(effects=EFFECTS_MINIMAL; kwargs...)`: copy `effects` with the named fields replaced.

Julia source: Compiler/src/effects.jl:202-224
```julia
function Effects(effects::Effects=EFFECTS_MINIMAL;
    consistent::UInt8 = effects.consistent,
    effect_free::UInt8 = effects.effect_free,
    reset_safe::UInt8 = effects.reset_safe,
    nothrow::Bool = effects.nothrow,
    terminates::Bool = effects.terminates,
    notaskstate::Bool = effects.notaskstate,
    inaccessiblememonly::UInt8 = effects.inaccessiblememonly,
    noub::UInt8 = effects.noub,
    nonoverlayed::UInt8 = effects.nonoverlayed,
    nortcall::Bool = effects.nortcall)
    return Effects(
        consistent,
        effect_free,
        reset_safe,
        nothrow,
        terminates,
        notaskstate,
        inaccessiblememonly,
        noub,
        nonoverlayed,
        nortcall)
end
```
-/
def Effects.kw (effects : Effects := EFFECTS_MINIMAL)
    (consistent : UInt8 := effects.consistent) (effect_free : UInt8 := effects.effect_free)
    (reset_safe : UInt8 := effects.reset_safe) (nothrow : Bool := effects.nothrow)
    (terminates : Bool := effects.terminates) (notaskstate : Bool := effects.notaskstate)
    (inaccessiblememonly : UInt8 := effects.inaccessiblememonly) (noub : UInt8 := effects.noub)
    (nonoverlayed : UInt8 := effects.nonoverlayed) (nortcall : Bool := effects.nortcall) : Effects :=
  ⟨consistent, effect_free, reset_safe, nothrow, terminates, notaskstate, inaccessiblememonly, noub,
    nonoverlayed, nortcall⟩

/-- `is_better_effects(new, old)`

Julia source: Compiler/src/effects.jl:226-302
```julia
function is_better_effects(new::Effects, old::Effects)
    any_improved = false
    if new.consistent == ALWAYS_TRUE
        any_improved |= old.consistent != ALWAYS_TRUE
    else
        if !iszero(new.consistent & CONSISTENT_IF_NOTRETURNED)
            old.consistent == ALWAYS_TRUE && return false
            any_improved |= iszero(old.consistent & CONSISTENT_IF_NOTRETURNED)
        elseif !iszero(new.consistent & CONSISTENT_IF_INACCESSIBLEMEMONLY)
            old.consistent == ALWAYS_TRUE && return false
            any_improved |= iszero(old.consistent & CONSISTENT_IF_INACCESSIBLEMEMONLY)
        else
            return false
        end
    end
    if new.effect_free == ALWAYS_TRUE
        any_improved |= old.effect_free != ALWAYS_TRUE
    elseif new.effect_free == EFFECT_FREE_IF_INACCESSIBLEMEMONLY
        old.effect_free == ALWAYS_TRUE && return false
        any_improved |= old.effect_free != EFFECT_FREE_IF_INACCESSIBLEMEMONLY
    elseif new.effect_free != old.effect_free
        return false
    end
    if new.reset_safe == ALWAYS_TRUE
        any_improved |= old.reset_safe != ALWAYS_TRUE
    elseif new.reset_safe == RESET_SAFE_IF_INACCESSIBLEMEMONLY
        old.reset_safe == ALWAYS_TRUE && return false
        any_improved |= old.reset_safe != RESET_SAFE_IF_INACCESSIBLEMEMONLY
    elseif new.reset_safe != old.reset_safe
        return false
    end
    if new.nothrow
        any_improved |= !old.nothrow
    elseif new.nothrow != old.nothrow
        return false
    end
    if new.terminates
        any_improved |= !old.terminates
    elseif new.terminates != old.terminates
        return false
    end
    if new.notaskstate
        any_improved |= !old.notaskstate
    elseif new.notaskstate != old.notaskstate
        return false
    end
    if new.inaccessiblememonly == ALWAYS_TRUE
        any_improved |= old.inaccessiblememonly != ALWAYS_TRUE
    elseif new.inaccessiblememonly == INACCESSIBLEMEM_OR_ARGMEMONLY
        old.inaccessiblememonly == ALWAYS_TRUE && return false
        any_improved |= old.inaccessiblememonly != INACCESSIBLEMEM_OR_ARGMEMONLY
    elseif new.inaccessiblememonly != old.inaccessiblememonly
        return false
    end
    if new.noub == ALWAYS_TRUE
        any_improved |= old.noub != ALWAYS_TRUE
    elseif new.noub == NOUB_IF_NOINBOUNDS
        old.noub == ALWAYS_TRUE && return false
        any_improved |= old.noub != NOUB_IF_NOINBOUNDS
    elseif new.noub != old.noub
        return false
    end
    if new.nonoverlayed == ALWAYS_TRUE
        any_improved |= old.nonoverlayed != ALWAYS_TRUE
    elseif new.nonoverlayed == CONSISTENT_OVERLAY
        old.nonoverlayed == ALWAYS_TRUE && return false
        any_improved |= old.nonoverlayed != CONSISTENT_OVERLAY
    elseif new.nonoverlayed != old.nonoverlayed
        return false
    end
    if new.nortcall
        any_improved |= !old.nortcall
    elseif new.nortcall != old.nortcall
        return false
    end
    return any_improved
end
```
-/
def isBetterEffects (new old : Effects) : Bool := Id.run do
  let mut anyImproved := false
  if new.consistent == ALWAYS_TRUE then
    anyImproved := anyImproved || old.consistent != ALWAYS_TRUE
  else
    if new.consistent &&& CONSISTENT_IF_NOTRETURNED != 0 then
      if old.consistent == ALWAYS_TRUE then return false
      anyImproved := anyImproved || old.consistent &&& CONSISTENT_IF_NOTRETURNED == 0
    else if new.consistent &&& CONSISTENT_IF_INACCESSIBLEMEMONLY != 0 then
      if old.consistent == ALWAYS_TRUE then return false
      anyImproved := anyImproved || old.consistent &&& CONSISTENT_IF_INACCESSIBLEMEMONLY == 0
    else
      return false
  if new.effect_free == ALWAYS_TRUE then
    anyImproved := anyImproved || old.effect_free != ALWAYS_TRUE
  else if new.effect_free == EFFECT_FREE_IF_INACCESSIBLEMEMONLY then
    if old.effect_free == ALWAYS_TRUE then return false
    anyImproved := anyImproved || old.effect_free != EFFECT_FREE_IF_INACCESSIBLEMEMONLY
  else if new.effect_free != old.effect_free then
    return false
  if new.reset_safe == ALWAYS_TRUE then
    anyImproved := anyImproved || old.reset_safe != ALWAYS_TRUE
  else if new.reset_safe == RESET_SAFE_IF_INACCESSIBLEMEMONLY then
    if old.reset_safe == ALWAYS_TRUE then return false
    anyImproved := anyImproved || old.reset_safe != RESET_SAFE_IF_INACCESSIBLEMEMONLY
  else if new.reset_safe != old.reset_safe then
    return false
  if new.nothrow then
    anyImproved := anyImproved || !old.nothrow
  else if new.nothrow != old.nothrow then
    return false
  if new.terminates then
    anyImproved := anyImproved || !old.terminates
  else if new.terminates != old.terminates then
    return false
  if new.notaskstate then
    anyImproved := anyImproved || !old.notaskstate
  else if new.notaskstate != old.notaskstate then
    return false
  if new.inaccessiblememonly == ALWAYS_TRUE then
    anyImproved := anyImproved || old.inaccessiblememonly != ALWAYS_TRUE
  else if new.inaccessiblememonly == INACCESSIBLEMEM_OR_ARGMEMONLY then
    if old.inaccessiblememonly == ALWAYS_TRUE then return false
    anyImproved := anyImproved || old.inaccessiblememonly != INACCESSIBLEMEM_OR_ARGMEMONLY
  else if new.inaccessiblememonly != old.inaccessiblememonly then
    return false
  if new.noub == ALWAYS_TRUE then
    anyImproved := anyImproved || old.noub != ALWAYS_TRUE
  else if new.noub == NOUB_IF_NOINBOUNDS then
    if old.noub == ALWAYS_TRUE then return false
    anyImproved := anyImproved || old.noub != NOUB_IF_NOINBOUNDS
  else if new.noub != old.noub then
    return false
  if new.nonoverlayed == ALWAYS_TRUE then
    anyImproved := anyImproved || old.nonoverlayed != ALWAYS_TRUE
  else if new.nonoverlayed == CONSISTENT_OVERLAY then
    if old.nonoverlayed == ALWAYS_TRUE then return false
    anyImproved := anyImproved || old.nonoverlayed != CONSISTENT_OVERLAY
  else if new.nonoverlayed != old.nonoverlayed then
    return false
  if new.nortcall then
    anyImproved := anyImproved || !old.nortcall
  else if new.nortcall != old.nortcall then
    return false
  return anyImproved

/-- `merge_effectbits(old::UInt8, new::UInt8)`

Julia source: Compiler/src/effects.jl:318-323
```julia
function merge_effectbits(old::UInt8, new::UInt8)
    if old === ALWAYS_FALSE || new === ALWAYS_FALSE
        return ALWAYS_FALSE
    end
    return old | new
end
```
-/
def mergeEffectbits (old new : UInt8) : UInt8 :=
  if old == ALWAYS_FALSE || new == ALWAYS_FALSE then ALWAYS_FALSE else old ||| new

/-- `merge_effectbits(old::Bool, new::Bool)`

Julia source: Compiler/src/effects.jl:324
```julia
merge_effectbits(old::Bool, new::Bool) = old & new
```
-/
def mergeEffectbitsBool (old new : Bool) : Bool := old && new

/-- `merge_effects(old, new)`

Julia source: Compiler/src/effects.jl:304-316
```julia
function merge_effects(old::Effects, new::Effects)
    return Effects(
        merge_effectbits(old.consistent, new.consistent),
        merge_effectbits(old.effect_free, new.effect_free),
        merge_effectbits(old.reset_safe, new.reset_safe),
        merge_effectbits(old.nothrow, new.nothrow),
        merge_effectbits(old.terminates, new.terminates),
        merge_effectbits(old.notaskstate, new.notaskstate),
        merge_effectbits(old.inaccessiblememonly, new.inaccessiblememonly),
        merge_effectbits(old.noub, new.noub),
        merge_effectbits(old.nonoverlayed, new.nonoverlayed),
        merge_effectbits(old.nortcall, new.nortcall))
end
```
-/
def mergeEffects (old new : Effects) : Effects :=
  ⟨mergeEffectbits old.consistent new.consistent,
   mergeEffectbits old.effect_free new.effect_free,
   mergeEffectbits old.reset_safe new.reset_safe,
   mergeEffectbitsBool old.nothrow new.nothrow,
   mergeEffectbitsBool old.terminates new.terminates,
   mergeEffectbitsBool old.notaskstate new.notaskstate,
   mergeEffectbits old.inaccessiblememonly new.inaccessiblememonly,
   mergeEffectbits old.noub new.noub,
   mergeEffectbits old.nonoverlayed new.nonoverlayed,
   mergeEffectbitsBool old.nortcall new.nortcall⟩

/-! The single-field queries.

Julia source: Compiler/src/effects.jl:326-336
```julia
is_consistent(effects::Effects)          = effects.consistent === ALWAYS_TRUE
is_effect_free(effects::Effects)         = effects.effect_free === ALWAYS_TRUE
is_reset_safe(effects::Effects)          = effects.reset_safe === ALWAYS_TRUE
is_nothrow(effects::Effects)             = effects.nothrow
is_terminates(effects::Effects)          = effects.terminates
is_notaskstate(effects::Effects)         = effects.notaskstate
is_inaccessiblememonly(effects::Effects) = effects.inaccessiblememonly === ALWAYS_TRUE
is_noub(effects::Effects)                = effects.noub === ALWAYS_TRUE
is_noub_if_noinbounds(effects::Effects)  = effects.noub === NOUB_IF_NOINBOUNDS
is_nonoverlayed(effects::Effects)        = effects.nonoverlayed === ALWAYS_TRUE
is_nortcall(effects::Effects)            = effects.nortcall
```
-/
def isConsistent (e : Effects) : Bool := e.consistent == ALWAYS_TRUE
def isEffectFree (e : Effects) : Bool := e.effect_free == ALWAYS_TRUE
def isResetSafe (e : Effects) : Bool := e.reset_safe == ALWAYS_TRUE
def isNothrow (e : Effects) : Bool := e.nothrow
def isTerminates (e : Effects) : Bool := e.terminates
def isNotaskstate (e : Effects) : Bool := e.notaskstate
def isInaccessiblememonly (e : Effects) : Bool := e.inaccessiblememonly == ALWAYS_TRUE
def isNoub (e : Effects) : Bool := e.noub == ALWAYS_TRUE
def isNoubIfNoinbounds (e : Effects) : Bool := e.noub == NOUB_IF_NOINBOUNDS
def isNonoverlayed (e : Effects) : Bool := e.nonoverlayed == ALWAYS_TRUE
def isNortcall (e : Effects) : Bool := e.nortcall

/-- `is_foldable(effects, check_rtcall=false)`

Julia source: Compiler/src/effects.jl:338-344
```julia
# implies `is_notaskstate` & `is_inaccessiblememonly`, but not explicitly checked here
is_foldable(effects::Effects, check_rtcall::Bool=false) =
    is_consistent(effects) &&
    (is_noub(effects) || is_noub_if_noinbounds(effects)) &&
    is_effect_free(effects) &&
    is_terminates(effects) &&
    (!check_rtcall || is_nortcall(effects))
```
-/
def isFoldable (e : Effects) (checkRtcall : Bool := false) : Bool :=
  isConsistent e && (isNoub e || isNoubIfNoinbounds e) && isEffectFree e && isTerminates e &&
    (!checkRtcall || isNortcall e)

/-- `is_foldable_nothrow(effects, check_rtcall=false)`

Julia source: Compiler/src/effects.jl:346-348
```julia
is_foldable_nothrow(effects::Effects, check_rtcall::Bool=false) =
    is_foldable(effects, check_rtcall) &&
    is_nothrow(effects)
```
-/
def isFoldableNothrow (e : Effects) (checkRtcall : Bool := false) : Bool :=
  isFoldable e checkRtcall && isNothrow e

/-- `is_removable_if_unused(effects)`

Julia source: Compiler/src/effects.jl:350-354
```julia
# TODO add `is_noub` here?
is_removable_if_unused(effects::Effects) =
    is_effect_free(effects) &&
    is_terminates(effects) &&
    is_nothrow(effects)
```
-/
def isRemovableIfUnused (e : Effects) : Bool := isEffectFree e && isTerminates e && isNothrow e

/-- `is_finalizer_inlineable(effects)`

Julia source: Compiler/src/effects.jl:356-358
```julia
is_finalizer_inlineable(effects::Effects) =
    is_nothrow(effects) &&
    is_notaskstate(effects)
```
-/
def isFinalizerInlineable (e : Effects) : Bool := isNothrow e && isNotaskstate e

/-! The conditional-state queries.

Julia source: Compiler/src/effects.jl:360-369
```julia
is_consistent_if_notreturned(effects::Effects)         = !iszero(effects.consistent & CONSISTENT_IF_NOTRETURNED)
is_consistent_if_inaccessiblememonly(effects::Effects) = !iszero(effects.consistent & CONSISTENT_IF_INACCESSIBLEMEMONLY)

is_effect_free_if_inaccessiblememonly(effects::Effects) = !iszero(effects.effect_free & EFFECT_FREE_IF_INACCESSIBLEMEMONLY)

is_reset_safe_if_inaccessiblememonly(effects::Effects) = !iszero(effects.reset_safe & RESET_SAFE_IF_INACCESSIBLEMEMONLY)

is_inaccessiblemem_or_argmemonly(effects::Effects) = effects.inaccessiblememonly === INACCESSIBLEMEM_OR_ARGMEMONLY

is_consistent_overlay(effects::Effects) = effects.nonoverlayed === CONSISTENT_OVERLAY
```
-/
def isConsistentIfNotreturned (e : Effects) : Bool := e.consistent &&& CONSISTENT_IF_NOTRETURNED != 0
def isConsistentIfInaccessiblememonly (e : Effects) : Bool :=
  e.consistent &&& CONSISTENT_IF_INACCESSIBLEMEMONLY != 0
def isEffectFreeIfInaccessiblememonly (e : Effects) : Bool :=
  e.effect_free &&& EFFECT_FREE_IF_INACCESSIBLEMEMONLY != 0
def isResetSafeIfInaccessiblememonly (e : Effects) : Bool :=
  e.reset_safe &&& RESET_SAFE_IF_INACCESSIBLEMEMONLY != 0
def isInaccessiblememOrArgmemonly (e : Effects) : Bool := e.inaccessiblememonly == INACCESSIBLEMEM_OR_ARGMEMONLY
def isConsistentOverlay (e : Effects) : Bool := e.nonoverlayed == CONSISTENT_OVERLAY

/-- `b % UInt32` for a `Bool`. -/
def boolU32 (b : Bool) : UInt32 := if b then 1 else 0

/-- `encode_effects(e)`, the word stored in `CodeInstance.ipo_purity_bits`.

Julia source: Compiler/src/effects.jl:371-383
```julia
# (sync this with codegen.cpp and staticdata.c effects_foldable functions)
function encode_effects(e::Effects)
    return ((e.consistent          % UInt32) << 0)  |
           ((e.effect_free         % UInt32) << 3)  |
           ((e.nothrow             % UInt32) << 5)  |
           ((e.terminates          % UInt32) << 6)  |
           ((e.notaskstate         % UInt32) << 7)  |
           ((e.inaccessiblememonly % UInt32) << 8)  |
           ((e.noub                % UInt32) << 10) |
           ((e.nonoverlayed        % UInt32) << 12) |
           ((e.nortcall            % UInt32) << 14) |
           ((e.reset_safe          % UInt32) << 15)
end
```
-/
def encodeEffects (e : Effects) : UInt32 :=
  (e.consistent.toUInt32 <<< 0) |||
  (e.effect_free.toUInt32 <<< 3) |||
  (boolU32 e.nothrow <<< 5) |||
  (boolU32 e.terminates <<< 6) |||
  (boolU32 e.notaskstate <<< 7) |||
  (e.inaccessiblememonly.toUInt32 <<< 8) |||
  (e.noub.toUInt32 <<< 10) |||
  (e.nonoverlayed.toUInt32 <<< 12) |||
  (boolU32 e.nortcall <<< 14) |||
  (e.reset_safe.toUInt32 <<< 15)

/-- `decode_effects(e)`

Julia source: Compiler/src/effects.jl:385-397
```julia
function decode_effects(e::UInt32)
    return Effects(
        UInt8((e >> 0) & 0x07),
        UInt8((e >> 3) & 0x03),
        UInt8((e >> 15) & 0x03),
        Bool((e >> 5) & 0x01),
        Bool((e >> 6) & 0x01),
        Bool((e >> 7) & 0x01),
        UInt8((e >> 8) & 0x03),
        UInt8((e >> 10) & 0x03),
        UInt8((e >> 12) & 0x03),
        Bool((e >> 14) & 0x01))
end
```
Each `UInt8(...)` and `Bool(...)` gets a value already masked into range, so none throws
`InexactError`. -/
def decodeEffects (e : UInt32) : Effects :=
  ⟨((e >>> 0) &&& 0x07).toUInt8,
   ((e >>> 3) &&& 0x03).toUInt8,
   ((e >>> 15) &&& 0x03).toUInt8,
   (e >>> 5) &&& 0x01 != 0,
   (e >>> 6) &&& 0x01 != 0,
   (e >>> 7) &&& 0x01 != 0,
   ((e >>> 8) &&& 0x03).toUInt8,
   ((e >>> 10) &&& 0x03).toUInt8,
   ((e >>> 12) &&& 0x03).toUInt8,
   (e >>> 14) &&& 0x01 != 0⟩

/-! ## Overrides -/

abbrev EffectsOverride := JuliaLean.base.expr.EffectsOverride

/-- `encode_effects_override(eo)` (`base/expr.jl:1035-1049`), the Base model with its result as
a `UInt16`. -/
def encodeEffectsOverride (eo : EffectsOverride) : UInt16 :=
  (JuliaLean.base.expr.encode_effects_override eo).val.toNat.toUInt16

/-- `decode_effects_override(e)` (`base/expr.jl:1051-1064`), the Base model on a `UInt16`. -/
def decodeEffectsOverride (e : UInt16) : EffectsOverride :=
  JuliaLean.base.expr.decode_effects_override (JuliaLean.JInt.wrap .u16 e.toNat)

/-- `NUM_IR_FLAGS` (Compiler/src/optimize.jl:59, `const NUM_IR_FLAGS = 3 # sync with julia.h`)
and `NUM_EFFECTS_OVERRIDES` (base/expr.jl:990, `const NUM_EFFECTS_OVERRIDES = 11`). -/
def NUM_IR_FLAGS : Nat := 3
def NUM_EFFECTS_OVERRIDES : Nat := 11

/-- `decode_statement_effects_override(ssaflag)`: the override bits of a statement flag.

Julia source: Compiler/src/effects.jl:399-400
```julia
decode_statement_effects_override(ssaflag::UInt32) =
    decode_effects_override(UInt16((ssaflag >> NUM_IR_FLAGS) & (1 << NUM_EFFECTS_OVERRIDES - 1)))
```
`<<` binds tighter than `-`, so the mask is `(1 << 11) - 1 = 0x7ff`. The `&` promotes to
`Int`; the result is at most `0x7ff`, so `UInt16(...)` never throws. -/
def decodeStatementEffectsOverride (ssaflag : UInt32) : EffectsOverride :=
  decodeEffectsOverride
    (((ssaflag >>> NUM_IR_FLAGS.toUInt32).toNat &&& ((1 <<< NUM_EFFECTS_OVERRIDES) - 1)).toUInt16)

/-- `override_effects(effects, override)`: the call-site (`@assume_effects` on an expression)
and `ccall` override application.

Julia source: Compiler/src/abstractinterpretation.jl:4023-4035
```julia
function override_effects(effects::Effects, override::EffectsOverride)
    return Effects(effects;
        consistent = override.consistent ? ALWAYS_TRUE : effects.consistent,
        effect_free = override.effect_free ? ALWAYS_TRUE : effects.effect_free,
        nothrow = override.nothrow ? true : effects.nothrow,
        terminates = override.terminates_globally ? true : effects.terminates,
        notaskstate = override.notaskstate ? true : effects.notaskstate,
        inaccessiblememonly = override.inaccessiblememonly ? ALWAYS_TRUE : effects.inaccessiblememonly,
        noub = override.noub ? ALWAYS_TRUE :
            (override.noub_if_noinbounds && effects.noub !== ALWAYS_TRUE) ? NOUB_IF_NOINBOUNDS :
            effects.noub,
        nortcall = override.nortcall ? true : effects.nortcall)
end
```
-/
def overrideEffects (effects : Effects) (override : EffectsOverride) : Effects :=
  Effects.kw effects
    (consistent := if override.consistent then ALWAYS_TRUE else effects.consistent)
    (effect_free := if override.effect_free then ALWAYS_TRUE else effects.effect_free)
    (nothrow := if override.nothrow then true else effects.nothrow)
    (terminates := if override.terminates_globally then true else effects.terminates)
    (notaskstate := if override.notaskstate then true else effects.notaskstate)
    (inaccessiblememonly := if override.inaccessiblememonly then ALWAYS_TRUE else effects.inaccessiblememonly)
    (noub := if override.noub then ALWAYS_TRUE
      else if override.noub_if_noinbounds && effects.noub != ALWAYS_TRUE then NOUB_IF_NOINBOUNDS
      else effects.noub)
    (nortcall := if override.nortcall then true else effects.nortcall)

/-- `adjust_effects(ipo_effects, def::Method)`: the method-level override application, with
`def.purity` passed as the word it reads. `is_effect_overridden(override, effect)` is
`getfield(override, effect)` (Compiler/src/inferencestate.jl:1325).

Julia source: Compiler/src/typeinfer.jl:633-666
```julia
function adjust_effects(ipo_effects::Effects, def::Method)
    # override the analyzed effects using manually annotated effect settings
    override = decode_effects_override(def.purity)
    if is_effect_overridden(override, :consistent)
        ipo_effects = Effects(ipo_effects; consistent=ALWAYS_TRUE)
    end
    if is_effect_overridden(override, :effect_free)
        ipo_effects = Effects(ipo_effects; effect_free=ALWAYS_TRUE)
    end
    if is_effect_overridden(override, :nothrow)
        ipo_effects = Effects(ipo_effects; nothrow=true)
    end
    if is_effect_overridden(override, :terminates_globally)
        ipo_effects = Effects(ipo_effects; terminates=true)
    end
    if is_effect_overridden(override, :notaskstate)
        ipo_effects = Effects(ipo_effects; notaskstate=true)
    end
    if is_effect_overridden(override, :inaccessiblememonly)
        ipo_effects = Effects(ipo_effects; inaccessiblememonly=ALWAYS_TRUE)
    end
    if is_effect_overridden(override, :noub)
        ipo_effects = Effects(ipo_effects; noub=ALWAYS_TRUE)
    elseif is_effect_overridden(override, :noub_if_noinbounds) && ipo_effects.noub !== ALWAYS_TRUE
        ipo_effects = Effects(ipo_effects; noub=NOUB_IF_NOINBOUNDS)
    end
    if is_effect_overridden(override, :consistent_overlay)
        ipo_effects = Effects(ipo_effects; nonoverlayed=CONSISTENT_OVERLAY)
    end
    if is_effect_overridden(override, :nortcall)
        ipo_effects = Effects(ipo_effects; nortcall=true)
    end
    return ipo_effects
end
```
-/
def adjustEffectsMethod (ipoEffects : Effects) (purity : UInt16) : Effects := Id.run do
  let override := decodeEffectsOverride purity
  let mut e := ipoEffects
  if override.consistent then e := Effects.kw e (consistent := ALWAYS_TRUE)
  if override.effect_free then e := Effects.kw e (effect_free := ALWAYS_TRUE)
  if override.nothrow then e := Effects.kw e (nothrow := true)
  if override.terminates_globally then e := Effects.kw e (terminates := true)
  if override.notaskstate then e := Effects.kw e (notaskstate := true)
  if override.inaccessiblememonly then e := Effects.kw e (inaccessiblememonly := ALWAYS_TRUE)
  if override.noub then
    e := Effects.kw e (noub := ALWAYS_TRUE)
  else if override.noub_if_noinbounds && e.noub != ALWAYS_TRUE then
    e := Effects.kw e (noub := NOUB_IF_NOINBOUNDS)
  if override.consistent_overlay then e := Effects.kw e (nonoverlayed := CONSISTENT_OVERLAY)
  if override.nortcall then e := Effects.kw e (nortcall := true)
  return e

/-! ## The C side -/

/-- The bit of `_jl_purity_overrides_t` (src/julia.h:358-377) that `Expr(:purity, ...)`
argument `j` sets. The C bitfield members are declared in `EffectsOverride` field order, and
the GCC/Clang ABIs Julia supports allocate bitfields from the least significant bit, so
member `j` is bit `j` of `bits`. -/
def purityBit (j : Nat) : UInt16 := (1 : UInt16) <<< j.toUInt16

/-- What the `Expr(:purity, ...)` arguments of a function's `:meta` nodes make of
`Method.purity` (a `CodeInfo`'s `purity.bits`, copied to the method at src/method.c:953).
Each argument list of length `NUM_EFFECTS_OVERRIDES` sets the bits of its `true` arguments and
never clears one; `bits` starts at `0` (src/method.c:711).

Julia source: src/method.c:507-534
```c
else if (jl_is_expr(ma) && ((jl_expr_t*)ma)->head == jl_purity_sym) {
    if (jl_expr_nargs(ma) == NUM_EFFECTS_OVERRIDES) {
        // N.B. this code allows multiple :purity expressions to be present in a single `:meta` node
        int8_t consistent = jl_unbox_bool(jl_exprarg(ma, 0));
        if (consistent) li->purity.overrides.ipo_consistent = consistent;
        ...
        int8_t nortcall = jl_unbox_bool(jl_exprarg(ma, 10));
        if (nortcall) li->purity.overrides.ipo_nortcall = nortcall;
    } else {
        assert(jl_expr_nargs(ma) == 0);
    }
}
```
-/
def methodPurityBits (exprs : List (List Bool)) : UInt16 :=
  exprs.foldl (init := 0) fun bits args =>
    if args.length == NUM_EFFECTS_OVERRIDES then
      (List.range NUM_EFFECTS_OVERRIDES).foldl (init := bits) fun b j =>
        if args.getD j false then b ||| purityBit j else b
    else bits

/-- The override part of a statement's flag inside the `Expr(:purity, ...)` regions in
`exprs` (the open regions, outermost first): argument `j` of each sets bit
`NUM_IR_FLAGS + j`.

Julia source: src/method.c:617-626
```c
int n_purity_exprs = purity_exprs->len;
if (n_purity_exprs > 0) {
    // apply all purity overrides
    for (int i = 0; i < n_purity_exprs; i++) {
        void* purity_expr = purity_exprs->items[i];
        for (int j = 0; j < NUM_EFFECTS_OVERRIDES; j++) {
            flag |= jl_unbox_bool(jl_exprarg((jl_value_t*)purity_expr, j)) ? (1 << (NUM_IR_FLAGS+j)) : 0;
        }
    }
}
```
Only argument lists of length `NUM_EFFECTS_OVERRIDES` are pushed (src/method.c:578-588). -/
def statementPurityFlag (exprs : List (List Bool)) : UInt32 :=
  exprs.foldl (init := 0) fun flag args =>
    (List.range NUM_EFFECTS_OVERRIDES).foldl (init := flag) fun f j =>
      if args.getD j false then f ||| ((1 : UInt32) <<< (NUM_IR_FLAGS + j).toUInt32) else f

/-- `effects_foldable(effects)`, which decides whether serialization keeps a `CodeInstance`'s
inferred code for constant folding.

Julia source: src/staticdata.c:645-652
```c
static int effects_foldable(uint32_t effects)
{
    // N.B.: This needs to be kept in sync with Core.Compiler.is_foldable(effects, true)
    return ((effects & 0x7) == 0) && // is_consistent(effects)
           (((effects >> 10) & 0x03) == 0) && // is_noub(effects)
           (((effects >> 3) & 0x03) == 0) && // is_effect_free(effects)
           ((effects >> 6) & 0x01); // is_terminates(effects)
}
```
-/
def effectsFoldableC (effects : UInt32) : Bool :=
  effects &&& 0x7 == 0 && (effects >>> 10) &&& 0x03 == 0 && (effects >>> 3) &&& 0x03 == 0 &&
    (effects >>> 6) &&& 0x01 != 0

/-- `effects_ipo_reset_safe(effects)`, which codegen uses to mark a call `julia.reset_safe`.

Julia source: src/codegen.cpp:2516-2525
```c
// Check whether a set of encoded ipo_purity_bits proves the callee's own IPO
// effects reset-safe. N.B.: kept in sync with Compiler/src/effects.jl
// (encode_effects); 0 means "no recorded effects" and is treated
// conservatively.
static bool effects_ipo_reset_safe(uint32_t effects) JL_NOTSAFEPOINT
{
    return effects != 0 &&
           ((effects >> 3) & 0x03u) == 0u && // is_effect_free
           ((effects >> 15) & 0x03u) == 0u;  // is_reset_safe
}
```
-/
def effectsIpoResetSafeC (effects : UInt32) : Bool :=
  effects != 0 && (effects >>> 3) &&& 0x03 == 0 && (effects >>> 15) &&& 0x03 == 0

end JuliaLean.Compiler
