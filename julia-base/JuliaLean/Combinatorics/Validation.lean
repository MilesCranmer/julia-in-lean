import JuliaLean.Combinatorics.Integer
import JuliaLean.Combinatorics.Permutation
import JuliaLean.Combinatorics.Matrix
import JuliaLean.Combinatorics.Nextprod

namespace JuliaLean.Combinatorics.Validation

open JuliaLean JuliaLean.Combinatorics

private def ints (xs : List Int) : String := String.intercalate "," (xs.map toString)
private def nats (xs : List Nat) : String := String.intercalate "-" (xs.map toString)

private def intTypes : List IntTy :=
  [.i8, .u8, .i16, .u16, .i32, .u32, .i64, .u64, .i128, .u128]

private def signedTypes : List IntTy := [.i8, .i16, .i32, .i64, .i128]

private def outInts : Jl (List Int) → String
  | .ok xs => "ok:" ++ ints xs
  | .error (.argumentError _) => "argument"
  | .error .boundsError => "bounds"
  | .error _ => "other-error"

private def outPermute : PermuteResult (List Int) → String
  | .ok xs => "ok:" ++ ints xs
  | .error .bounds => "bounds"
  | .error .dimensionMismatch => "dimension"

private def outFixed : Jl FixedInteger → String
  | .ok r => s!"ok:{r.ty.name}:{r.val}"
  | .error (.overflowError _) => "overflow"
  | .error (.domainError _) => "domain"
  | .error (.inexactError _) => "inexact"
  | .error _ => "other-error"

private def outJInt {t : IntTy} : Jl (JInt t) → String
  | .ok x => s!"ok:{x.val}"
  | .error (.overflowError _) => "overflow"
  | .error _ => "other-error"

private def outBig : Jl Int → String
  | .ok x => s!"ok:{x}"
  | .error (.overflowError _) => "overflow"
  | .error (.domainError _) => "domain"
  | .error (.inexactError _) => "inexact"
  | .error _ => "other-error"

private def outNat : Jl Nat → String
  | .ok x => s!"ok:{x}"
  | .error .boundsError => "bounds"
  | .error (.domainError _) => "domain"
  | .error _ => "other-error"

private def outCols {t : IntTy} : Jl (List Int × List (JInt t)) → String
  | .ok (cols, p) => "ok:" ++ ints cols ++ "|" ++ ints (p.map (·.val))
  | .error _ => "error"

def differential : IO Unit := do
  IO.println s!"isperm-empty {isperm ([] : List Int)}"
  IO.println s!"isperm-valid {isperm [3, 1, 2]}"
  IO.println s!"isperm-invalid {isperm [1, 1, 2]}"
  IO.println s!"invperm-valid {outInts (invperm [3, 1, 2])}"
  IO.println s!"invperm-invalid {outInts (invperm [1, 1, 2])}"
  IO.println s!"permute-valid {outPermute (permuteBang [10, 20, 30] [3, 1, 2])}"
  IO.println s!"permute-duplicate {outPermute (permuteBang [10, 20, 30] [1, 1, 2])}"
  IO.println s!"permute-oob {outPermute (permuteBang [10, 20, 30] [1, 4, 2])}"
  IO.println s!"invpermute-valid {outPermute (invpermuteBang [10, 20, 30] [3, 1, 2])}"
  IO.println s!"factorial-i64-20 {outFixed (factorialFixed .i64 (JInt.lit .i64 20))}"
  IO.println s!"factorial-i64-21 {outFixed (factorialFixed .i64 (JInt.lit .i64 21))}"
  IO.println s!"factorial-u64-max {outFixed (factorialFixed .u64 (JInt.typemax .u64))}"
  IO.println s!"factorial-i128-min {outFixed (factorialFixed .i128 (JInt.typemin .i128))}"
  IO.println s!"binomial-i8-safe {outJInt (binomialFixed .i8 (JInt.lit .i8 5) (JInt.lit .i8 3))}"
  IO.println s!"binomial-i8-overflow {outJInt (binomialFixed .i8 (JInt.lit .i8 20) (JInt.lit .i8 3))}"
  IO.println s!"binomial-i8-min {outJInt (binomialFixed .i8 (JInt.typemin .i8) (JInt.lit .i8 1))}"
  IO.println s!"permutecols-u8 {outCols (permuteCols [1, 2, 3] [JInt.lit .u8 3, JInt.lit .u8 1, JInt.lit .u8 2])}"
  IO.println s!"invpermutecols-i8 {outCols (invPermuteCols [1, 2, 3] [JInt.lit .i8 3, JInt.lit .i8 1, JInt.lit .i8 2])}"
  IO.println s!"permutecolsbang-u8 {outCols (permuteColsBangBang [1, 2, 3] [JInt.lit .u8 3, JInt.lit .u8 1, JInt.lit .u8 2])}"
  IO.println s!"nextprod-2-3-33 {outNat (nextprod [2, 3] 33)}"
  IO.println s!"nextprod-empty {outNat (nextprod [] 1)}"
  IO.println s!"factorial-BigInt-culongplus {outBig (factorialBig (cULongMax + 1))}"
  IO.println s!"binomial-BigInt-huge {outBig (binomialBig (2^65) (2^64))}"
  for t in intTypes do
    for n in [0, 7, factorialLimit t, factorialLimit t + 1] do
      IO.println s!"factorial-{t.name}-{n} {outFixed (factorialFixed t (JInt.wrap t n))}"
    IO.println s!"factorial-{t.name}-max {outFixed (factorialFixed t (JInt.typemax t))}"
    let p := [JInt.lit t 3, JInt.lit t 1, JInt.lit t 2]
    IO.println s!"permutecols-{t.name} {outCols (permuteCols [1, 2, 3] p)}"
    IO.println s!"invpermutecols-{t.name} {outCols (invPermuteCols [1, 2, 3] p)}"
    IO.println s!"permutecolsbang-{t.name} {outCols (permuteColsBangBang [1, 2, 3] p)}"
    IO.println s!"binomial-{t.name}-5-3 {outJInt (binomialFixed t (JInt.lit t 5) (JInt.lit t 3))}"
    IO.println s!"binomial-{t.name}-20-3 {outJInt (binomialFixed t (JInt.lit t 20) (JInt.lit t 3))}"
    IO.println s!"binomial-{t.name}-max-1 {outJInt (binomialFixed t (JInt.typemax t) (JInt.lit t 1))}"
    IO.println s!"binomial-{t.name}-max-2 {outJInt (binomialFixed t (JInt.typemax t) (JInt.lit t 2))}"
  for t in signedTypes do
    IO.println s!"factorial-{t.name}-min {outFixed (factorialFixed t (JInt.typemin t))}"
    IO.println s!"binomial-{t.name}--5-3 {outJInt (binomialFixed t (JInt.lit t (-5)) (JInt.lit t 3))}"
    IO.println s!"binomial-{t.name}-min-1 {outJInt (binomialFixed t (JInt.typemin t) (JInt.lit t 1))}"
  for factors in [[2], [2, 3], [3, 2], [2, 2, 3], [3, 5], [5, 3, 2]] do
    for x in [1, 2, 17, 33, 105, 200] do
      IO.println s!"nextprod-{nats factors}-{x} {outNat (nextprod factors x)}"

end JuliaLean.Combinatorics.Validation

def main : IO Unit := JuliaLean.Combinatorics.Validation.differential
