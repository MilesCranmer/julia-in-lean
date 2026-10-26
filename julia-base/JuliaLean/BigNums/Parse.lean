import JuliaLean.BigNums.Float

/-!
Parsing and printing of `BigInt` and `BigFloat` at master `bbfa0ce4150`
(`base/gmp.jl:307-331,765-782`, `base/mpfr.jl:407-415`, `base/parse.jl:96-121`,
`base/intfuncs.jl:1047-1119`).

Strings are lists of characters. Whitespace is the ASCII set that `isspace_ascii` and C's
`isspace` share (space and `\t`..`\r`); non-ASCII whitespace is outside the model.
-/

namespace JuliaLean.BigNums

open JuliaLean

/-- ASCII whitespace: `isspace_ascii` (`base/strings/unicode.jl`) and C `isspace`. -/
def isSpace (c : Char) : Bool := c = ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)

/-- The value of a digit character in `base`, or `99` for a non-digit: GMP's `digit_value`
table (`mpz/set_str.c`), which agrees with Julia's `Parsers.digitvalue`: case-insensitive
letters for bases up to 36; above, upper-case letters are 10..35 and lower-case 36..61. -/
def digitVal (c : Char) (base : Nat) : Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then n - 48
  else if 65 ≤ n ∧ n ≤ 90 then n - 55
  else if 97 ≤ n ∧ n ≤ 122 then (if base ≤ 36 then n - 87 else n - 61)
  else 99

/-- The digit character for value `d < base` (`mpz_get_str`, GMP manual §5.12: lower-case
letters for bases up to 36; upper-case then lower-case for bases 37 to 62). -/
def digitChar (d base : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d)
  else if base ≤ 36 then Char.ofNat (87 + d)
  else if d < 36 then Char.ofNat (55 + d) else Char.ofNat (61 + d)

/-- `mpz_set_str(rop, str, base)` for `2 ≤ base ≤ 62`, as implemented in GMP 6.3
`mpz/set_str.c`: leading whitespace, an optional `-`, a first character that must be a digit,
and then digits with whitespace anywhere ignored (GMP manual §5.2: "White space is allowed in
the string, and is simply ignored"). -/
def mpzSetStr (s : List Char) (base : Nat) : Option Int :=
  let s := s.dropWhile isSpace
  let (neg, s) := match s with
    | '-' :: t => (true, t)
    | _ => (false, s)
  match s with
  | [] => none
  | c :: _ =>
    if digitVal c base ≥ base then none
    else
      let ds := s.filter (fun c => !isSpace c)
      if ds.any (fun c => digitVal c base ≥ base) then none
      else
        let v : Int := ds.foldl (fun acc c => acc * base + digitVal c base) 0
        some (if neg then -v else v)

/-- `parseint_preamble(true, base, s, i, j)`, `base/parse.jl:96-121`: the sign, the base (from an
`0b`/`0o`/`0x` prefix when `base == 0`), and the digits after the preamble (`none` for the
zero index returned when a prefix has nothing after it). -/
def preamble (base : Nat) (s : List Char) : Int × Nat × Option (List Char) :=
  let s := s.dropWhile isSpace
  if s = [] then (0, 0, none)
  else
    let (sgn, s) := match s with
      | '-' :: t => (-1, t.dropWhile isSpace)
      | '+' :: t => (1, t.dropWhile isSpace)
      | _ => (1, s)
    if s = [] then (0, 0, none)
    else if base = 0 then
      match s with
      | '0' :: c :: t =>
        let b := if c = 'b' then 2 else if c = 'o' then 8 else if c = 'x' then 16 else 10
        if b = 10 then (sgn, 10, some s)
        else (sgn, b, if t = [] then none else some t)
      | _ => (sgn, 10, some s)
    else (sgn, base, some s)

/-- `tryparse_internal(::Type{BigInt}, s, ..., base, raise = true)` (`parse(BigInt, s; base)`),
`base/gmp.jl:307-331`. -/
def parseBig (s : List Char) (base : Nat) : Jl Int :=
  let (sgn, b, rest) := preamble base s
  if ¬ (2 ≤ b ∧ b ≤ 62) then .error (.argumentError "invalid base")
  else match rest with
    | none => .error (.argumentError "premature end of integer")
    | some r =>
      if s.contains (Char.ofNat 0) then .error (.argumentError "invalid BigInt")
      else match mpzSetStr r b with
        | none => .error (.argumentError "invalid BigInt")
        | some v => .ok (if sgn < 0 then -v else v)

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

/-! ## Printing -/

/-- The base-`b` digit characters of `abs(n)`, most significant first. -/
def digitChars (n : Int) (b : Nat) : List Char :=
  ((absDigits n.natAbs b).map (fun d => digitChar d b)).reverse

/-- Canonical positive-base rendering with zero padding to `pad` digits: `mpz_get_str` plus the
padding of `string(n::BigInt; base, pad)` (`base/gmp.jl:768-781`), and equally
`dec`/`hex`/`oct`/`bin`/`_base` for machine integers (`base/intfuncs.jl:1047-1119`). -/
def renderPos (n : Int) (b : Nat) (pad : Int) : List Char :=
  if n = 0 ∧ pad < 1 then []
  else
    let ds := digitChars n b
    let z := pad.toNat - ds.length
    (if n < 0 then ['-'] else []) ++ List.replicate z '0' ++ ds

/-- Negative-base digits of `_base` (`base/intfuncs.jl:1056-1066`): `mod(x, -b)` and `cld(x, b)`,
least significant first, at least `pad` of them. -/
def negDigits (x : Int) (b : Nat) (pad : Nat) : List Nat := go x (x.natAbs + pad + 1) 0
where
  go (x : Int) : Nat → Nat → List Nat
    | 0, _ => []
    | k + 1, i =>
      if x = 0 ∧ pad ≤ i then []
      else (x.fmod b).toNat :: go (-((-x).fdiv (-(b : Int)))) k (i + 1)

/-- `_base(base, x, pad, false)` for `base < 0`, `base/intfuncs.jl:1047-1070`. -/
def baseNeg (base : Int) (x : Int) (pad : Int) : Jl (List Char) :=
  if ¬ (2 ≤ -base ∧ -base ≤ 62) then .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  else
    let b := (-base).toNat
    let ds := negDigits x b pad.toNat
    .ok ((ds.map fun d => digitChar d b).reverse)

/-- `string(n::BigInt; base, pad)`, `base/gmp.jl:765-782`. -/
def stringBig (n : Int) (base pad : Int) : Jl (List Char) :=
  if base < 0 then baseNeg base n pad
  else if ¬ (2 ≤ base ∧ base ≤ 62) then .error (.argumentError "base must be 2 ≤ base ≤ 62")
  else .ok (renderPos n base.toNat pad)

/-- `string(n::Integer; base, pad)` for a machine integer, `base/intfuncs.jl:1101-1119`. -/
def stringMachine (n : Int) (base pad : Int) : Jl (List Char) :=
  if base = 2 ∨ base = 8 ∨ base = 10 ∨ base = 16 then .ok (renderPos n base.toNat pad)
  else if base < 0 then baseNeg base n pad
  else if ¬ (2 ≤ base ∧ base ≤ 62) then
    .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  else .ok (renderPos n base.toNat pad)

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

/-! ## `tryparse(BigFloat, s; base)` (`base/mpfr.jl:407-412`) -/

/-- A call's outcome: a value, a thrown exception, or a process abort. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | throw (e : JlError)
  | abort
  deriving DecidableEq, Repr

/-- `tryparse(BigFloat, s; base)`, `base/mpfr.jl:407-412`. Trailing whitespace is stripped first;
the `Cstring` conversion of the argument throws `ArgumentError` for embedded NULs
(`base/strings/cstring.jl:85`); `mpfr_set_str` asserts `base == 0 || 2 <= base <= 62`
(MPFR `strtofr.c`, `MPFR_ASSERTN`, active in release builds), aborting the process otherwise.
For a valid base, `setStr` is MPFR's documented parser (MPFR manual §5.2 `mpfr_strtofr`); its
numeric grammar does not matter for the properties below, so it is a parameter. -/
def tryparseBF (setStr : List Char → Nat → Option BF) (s : List Char) (base : Int) :
    Outcome (Option BF) :=
  let s := (s.reverse.dropWhile isSpace).reverse
  if s.contains (Char.ofNat 0) then .throw (.argumentError "embedded NULs are not allowed in C strings")
  else if ¬ (base = 0 ∨ (2 ≤ base ∧ base ≤ 62)) then .abort
  else .ok (setStr s base.toNat)

/-- `tryparse(BigFloat, s; base)` never aborts the process, whatever `s` and `base`. -/
def TryparseBigFloatTotal : Prop :=
  ∀ (setStr : List Char → Nat → Option BF) (s : List Char) (base : Int),
    tryparseBF setStr s base ≠ .abort

theorem tryparseBigFloatTotal_refuted : ¬ TryparseBigFloatTotal := by
  intro h
  exact h (fun _ _ => none) ['1'] 1 (by decide)

/-- `tryparse(BigFloat, s)` returns a value or `nothing` and never throws (the `tryparse`
docstring, `base/parse.jl:241-246`). -/
def TryparseBigFloatNoThrow : Prop :=
  ∀ (setStr : List Char → Nat → Option BF) (s : List Char),
    ∃ v, tryparseBF setStr s 0 = .ok v

theorem tryparseBigFloatNoThrow_refuted : ¬ TryparseBigFloatNoThrow := by
  intro h
  obtain ⟨v, hv⟩ := h (fun _ _ => none) ['1', Char.ofNat 0]
  have h2 : tryparseBF (fun _ _ => none) ['1', Char.ofNat 0] 0 =
      .throw (.argumentError "embedded NULs are not allowed in C strings") := by decide
  rw [h2] at hv
  cases hv

end JuliaLean.BigNums
