import JuliaLean.Proofs.base.gmp.integer_contracts

/-!
Parsing and printing of `BigInt` and `BigFloat` at master `bbfa0ce4150`
(`base/gmp.jl:307-331,765-782`, `base/mpfr.jl:407-415`, `base/parse.jl:96-121`,
`base/intfuncs.jl:1047-1119`).

Strings are lists of characters. Whitespace is the ASCII set that `isspace_ascii` and C's
`isspace` share (space and `\t`..`\r`); non-ASCII whitespace is outside the model.
-/

namespace JuliaLean.BigNums

open JuliaLean

/-- `parse(BigInt, s)` accepts at most one sign, as Julia's integer grammar
(`parseint_preamble`) and every other integer type do; checked on strings without whitespace. -/
def ParseBigIntMatchesInt : Prop :=
  ∀ (s : List Char) (base : Nat) (v : Int), s.all (fun c => !isSpace c) = true →
    parseBig s base = .ok v → (s.filter (fun c => c = '-' || c = '+')).length ≤ 1

theorem parseBigIntMatchesInt_refuted : ¬ ParseBigIntMatchesInt := by
  intro h
  have := h ['-', '-', '5'] 0 5 (by decide) (by decide +kernel)
  revert this
  decide

/-- `parse(BigInt, s)` rejects whitespace between digits, as `parse(Int, s)` does
(`base/parse.jl:126-160`: only leading and trailing whitespace is skipped); checked on strings
without signs. -/
def ParseBigIntNoInteriorSpace : Prop :=
  ∀ (s : List Char) (base : Nat) (v : Int), s.all (fun c => c != '-' && c != '+') = true →
    parseBig s base = .ok v →
      ((s.dropWhile isSpace).reverse.dropWhile isSpace).all (fun c => !isSpace c) = true

theorem parseBigIntNoInteriorSpace_refuted : ¬ ParseBigIntNoInteriorSpace := by
  intro h
  have := h ['1', ' ', '2'] 0 12 (by decide) (by decide +kernel)
  revert this
  decide

/-- `string(n; base, pad)` on BigInt agrees with `string(n; base, pad)` on `Int64`: the same text,
or the same exception type. -/
def StringBigIntMatchesInt : Prop :=
  ∀ (n : JInt .i64) (base pad : Int),
    sameJl id (stringBig n.val base pad) (stringMachine n.val base pad) = true

theorem stringBigIntMatchesInt_refuted : ¬ StringBigIntMatchesInt := by
  intro h
  have := h (JInt.lit .i64 7) 63 1
  revert this
  decide +kernel

/-- `parse(BigInt, string(n; base, pad); base) == n` for every `BigInt` `n`, base `2..62` and
`pad ≥ 1`. -/
def StringParseRoundtrip : Prop :=
  ∀ (n : Int) (b : Nat) (pad : Int), 2 ≤ b → b ≤ 62 → 1 ≤ pad →
    (do let s ← stringBig n b pad; parseBig s b) = .ok n

end JuliaLean.BigNums
