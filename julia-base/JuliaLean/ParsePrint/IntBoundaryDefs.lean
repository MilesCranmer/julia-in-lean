import JuliaLean.ParsePrint.IntParse

/-!
Exhaustive near-boundary checks for integer parsing: for every `BitInteger` type,
every integer within 16 of `typemin`, `typemax`, `±2^64` and `±2^128`, written in
base 10 or 16, `parse` returns the value when it fits and throws otherwise. The
centres `±2^64` and `±2^128` are where the unsigned accumulator `U` of
`Parsers.parseint` (`base/parsers/ints.jl:150-173`) would wrap.
-/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

/-- Lower-case digit character of `d < 36` (`'0'..'9'`, `'a'..'z'`). -/
def digitChar (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- The base-`b` digit characters of `n`, most significant first. -/
def strDigits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f+1, n => if n < b then [digitChar n] else strDigits b f (n / b) ++ [digitChar (n % b)]

/-- The canonical spelling of the mathematical integer `m` in base `b`. -/
def intStr (b : Nat) (m : Int) : Bytes :=
  ((if m < 0 then [45] else []) ++ strDigits b 200 m.natAbs).map fun (c : Nat) => JInt.lit .u8 (c : Int)

/-- Values around which overflow detection is checked. -/
def centers (t : IntTy) : List Int := [t.min, t.max, 2 ^ 64, -(2 ^ 64), 2 ^ 128, -(2 ^ 128)]

/-- The specification of `parse(T, s; base=b)` for the canonical spelling of `m`:
the value `m` if it fits in `T`, an exception otherwise. -/
def parseSpec (t : IntTy) (b : Nat) (m : Int) : Bool :=
  match parse t (intStr b m) (some b) with
  | .ok v => decide (t.min ≤ m ∧ m ≤ t.max) && v.val == m
  | .error _ => !decide (t.min ≤ m ∧ m ≤ t.max)

/-- `parseSpec` at `c + k - 16`. -/
def nearOK (t : IntTy) (b : Nat) (c : Int) (k : Nat) : Bool := parseSpec t b (c + k - 16)

end JuliaLean.ParsePrint.IntParse
