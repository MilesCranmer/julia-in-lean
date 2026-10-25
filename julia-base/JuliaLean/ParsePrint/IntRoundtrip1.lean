import JuliaLean.ParsePrint.IntParse
import JuliaLean.ParsePrint.IntPrint

/-!
Exhaustive checks that `parse(T, string(n; base=b); base=b) == n` for the 8-bit
types, `decide +kernel` over all 256 values per type and base. The roundtrip
property itself is `JuliaLean.ParsePrint.IntParse.RoundtripInt8`.
-/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

/-- The bytes of a written string. -/
def bytesOf (s : List Nat) : Bytes := s.map fun (c : Nat) => JInt.lit .u8 (c : Int)

/-- `parse(T, string(n; base=b); base=b) == n` for `n = T(k)`, as a Boolean check. -/
def rtOK (t : IntTy) (k : Nat) (b : Int) : Bool :=
  match IntPrint.string (JInt.lit t k) (JInt.lit .i64 b) 1 with
  | .ok s => match parse t (bytesOf s) (some b) with
    | .ok v => v.val == (JInt.lit t k).val
    | .error _ => false
  | .error _ => false

theorem rt_u8_2 : ∀ k : Fin 256, rtOK .u8 k 2 = true := by decide +kernel
theorem rt_i8_2 : ∀ k : Fin 256, rtOK .i8 k 2 = true := by decide +kernel
theorem rt_u8_3 : ∀ k : Fin 256, rtOK .u8 k 3 = true := by decide +kernel
theorem rt_i8_3 : ∀ k : Fin 256, rtOK .i8 k 3 = true := by decide +kernel
theorem rt_u8_7 : ∀ k : Fin 256, rtOK .u8 k 7 = true := by decide +kernel
theorem rt_i8_7 : ∀ k : Fin 256, rtOK .i8 k 7 = true := by decide +kernel
theorem rt_u8_8 : ∀ k : Fin 256, rtOK .u8 k 8 = true := by decide +kernel
theorem rt_i8_8 : ∀ k : Fin 256, rtOK .i8 k 8 = true := by decide +kernel
theorem rt_u8_10 : ∀ k : Fin 256, rtOK .u8 k 10 = true := by decide +kernel
theorem rt_i8_10 : ∀ k : Fin 256, rtOK .i8 k 10 = true := by decide +kernel

end JuliaLean.ParsePrint.IntParse
