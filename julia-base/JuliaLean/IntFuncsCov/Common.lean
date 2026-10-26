import JuliaLean.Core

/-!
Shared helpers of the `IntFuncsCov` area: decidable equality of `Jl` results and the
finite input grids its exhaustive properties quantify over.
-/

namespace JuliaLean.IntFuncsCov

open JuliaLean

instance instDecEqJl {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- The two byte-wide integer types, `Int8` (`true`) and `UInt8` (`false`). -/
def byteTy (s : Bool) : IntTy := if s then .i8 else .u8

/-- Sixteen edge values of a byte type (as `x % T` of these integers): zero, ±1, ±2, the
extremes and their neighbours, a few odd and even interior values. -/
def edge (k : Fin 16) : Int :=
  [0, 1, -1, 2, -2, 3, 6, 12, -12, 64, -64, 127, -127, 128, 255, 100].getD k.val 0

/-- `ok v` with the value of a `Jl (JInt t)` result. -/
def okVal {t : IntTy} (r : Jl (JInt t)) : Jl Int := r.map Subtype.val

/-- Whether a `Jl` result satisfies `p` when it returns and `q` when it throws. -/
def okSat {α : Type} (r : Jl α) (p : α → Bool) (q : JlError → Bool) : Bool :=
  match r with
  | .ok a => p a
  | .error e => q e

/-- Exception kinds, ignoring messages. -/
def isDomainErr : JlError → Bool
  | .domainError _ => true | _ => false
def isOverflowErr : JlError → Bool
  | .overflowError _ => true | _ => false
def isArgumentErr : JlError → Bool
  | .argumentError _ => true | _ => false
def isInexactErr : JlError → Bool
  | .inexactError _ => true | _ => false

end JuliaLean.IntFuncsCov
