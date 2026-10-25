import JuliaLean.Core
import JuliaLean.ParsePrint.Bits

/-!
Shared definitions for the Base64, UUIDs and CRC32c model.

* `Byte` is Julia's `UInt8` (`JInt .u8`); byte strings and vectors are `List Byte`.
* `JErr` adds `EOFError` to the shared `JlError`: the decoding pipe throws it, and
  `JlError` has no constructor for it. `Jle α` is a Julia call that may throw.
* The bit operations are `JuliaLean.ParsePrint.{band, bor, shl, shr}`.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

abbrev Byte := JInt .u8

/-- A `UInt8` literal. -/
def b8 (n : Nat) : Byte := JInt.lit .u8 n

/-- The value of a byte as a natural number. -/
def bn (x : Byte) : Nat := x.val.toNat

/-- The bytes of an ASCII string literal (used for examples and counterexamples). -/
def ascii (s : String) : List Byte := s.toList.map (fun c => b8 c.toNat)

/-- Julia exceptions thrown in this area. -/
inductive JErr where
  | jl (e : JlError)
  /-- `EOFError()`. -/
  | eof
  deriving Repr, DecidableEq

abbrev Jle (α : Type) := Except JErr α

instance instDecidableEqExceptJErr {α} [DecidableEq α] : DecidableEq (Except JErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- `ArgumentError("malformed base64 sequence")` and other `ArgumentError`s. -/
def argErr (msg : String) : JErr := .jl (.argumentError msg)

end JuliaLean.Base64Uuid
