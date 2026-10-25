import JuliaLean.Core

/-!
Bit-level helpers for unsigned `BitInteger` values, as Julia evaluates them.

All helpers take unsigned `JInt` operands, whose values are nonnegative, and
return the bit pattern Julia's intrinsics produce:

* `shr x k` is `x >> k` for a nonnegative count (`lshr_int`; a count of at
  least the width gives zero), `shl x k` is `x << k` (`shl_int`, wrapping).
* `shrI x k` is `x >> k` for an `Int` count: a negative count shifts left,
  `base/int.jl:542-560`.
* `band`, `bor`, `bxor` are `&`, `|`, `xor` (`and_int`, `or_int`, `xor_int`).
* `ofBool b` is `T(b)`, the value Julia uses for `x + b` with `b::Bool`.
-/

namespace JuliaLean.ParsePrint

open JuliaLean

variable {t : IntTy}

/-- `x >> k` with a nonnegative count on an unsigned value (`lshr_int`). -/
def shr (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val.toNat / 2^k)

/-- `x << k` with a nonnegative count (`shl_int`), wrapping. -/
def shl (x : JInt t) (k : Nat) : JInt t := JInt.wrap t (x.val.toNat * 2^k)

/-- `x >> k` for an `Int` count on an unsigned value, `base/int.jl:542-560`. -/
def shrI (x : JInt t) (k : Int) : JInt t :=
  if k ≥ 0 then shr x k.toNat else shl x (-k).toNat

/-- `x << k` for an `Int` count on an unsigned value, `base/int.jl:542-560`. -/
def shlI (x : JInt t) (k : Int) : JInt t :=
  if k ≥ 0 then shl x k.toNat else shr x (-k).toNat

/-- `x & y` (`and_int`) on unsigned values. -/
def band (x y : JInt t) : JInt t := JInt.wrap t (Nat.land x.val.toNat y.val.toNat)

/-- `x | y` (`or_int`) on unsigned values. -/
def bor (x y : JInt t) : JInt t := JInt.wrap t (Nat.lor x.val.toNat y.val.toNat)

/-- `x ⊻ y` (`xor_int`) on unsigned values. -/
def bxor (x y : JInt t) : JInt t := JInt.wrap t (Nat.xor x.val.toNat y.val.toNat)

/-- `T(b)` for `b::Bool`: Julia promotes a `Bool` operand to `0` or `1`. -/
def ofBool (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)

/-- Unsigned truncated division by a nonzero literal (`udiv_int`); no error is possible. -/
def udivLit (x : JInt t) (d : Nat) : JInt t := JInt.wrap t (x.val.toNat / d)

end JuliaLean.ParsePrint
