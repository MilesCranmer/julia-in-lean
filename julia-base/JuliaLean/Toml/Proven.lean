import JuliaLean.Toml.Props

/-!
# Proven TOML properties

Each property is checked exhaustively over its finite family of documents by
kernel evaluation of the parser model.
-/

namespace JuliaLean.Toml

/-- `c = 1` defines the one-character key `c` exactly when `c` is a bare-key
byte `A-Za-z0-9_-` (TOML v1.1.0, "Keys"); every other first byte gives a
`ParserError`, a comment, or a different key. -/
def BareKeyCharset : Prop :=
  ∀ c : Nat, c < 256 →
    (rootValue ([c] ++ bytes% " = 1") [c] = some (.int .i64 1) ↔ bareByte c = true)

theorem bareKeyCharset : BareKeyCharset := by
  unfold BareKeyCharset; decide +kernel

/-- The value of the TOML v1.1.0 single-character escape `\c`. -/
def escapeValue (c : Nat) : Option Nat :=
  if c = 98 then some 8 else if c = 116 then some 9 else if c = 110 then some 10
  else if c = 102 then some 12 else if c = 114 then some 13 else if c = 101 then some 27
  else if c = 34 then some 34 else if c = 92 then some 92 else none

/-- For every printable ASCII `c`, `"\c"` is the escaped character when `\c` is
one of TOML's escapes `\b \t \n \f \r \e \" \\`, and a `ParserError`
otherwise (`\x`, `\u`, `\U` need hex digits; "All other escape sequences ...
TOML should produce an error", TOML v1.1.0, "String"). -/
def EscapeTable : Prop :=
  ∀ c : Nat, c < 127 → 32 ≤ c →
    rootValue (bytes% "a = \"\\" ++ [c] ++ bytes% "\"") (bytes% "a") =
      (escapeValue c).map fun v => .str [v]

theorem escapeTable : EscapeTable := by
  unfold EscapeTable; decide +kernel

/-- Spellings of keys and the key paths they denote. -/
def keySpellings : List (Str × List Str) :=
  [(bytes% "a", [bytes% "a"]), (bytes% "\"a\"", [bytes% "a"]), (bytes% "'a'", [bytes% "a"]),
   (bytes% "b", [bytes% "b"]), (bytes% "a.b", [bytes% "a", bytes% "b"]),
   (bytes% "a . b", [bytes% "a", bytes% "b"]), (bytes% "\"a\".'b'", [bytes% "a", bytes% "b"]),
   (bytes% "a.c", [bytes% "a", bytes% "c"]), (bytes% "\"a.b\"", [bytes% "a.b"]),
   (bytes% "a.b.c", [bytes% "a", bytes% "b", bytes% "c"])]

/-- Two assignments `k1 = 1` and `k2 = 2` are rejected exactly when one key path
is a prefix of the other: the same key defined twice, or a value used as a
table (TOML v1.1.0, "Keys": "Defining a key multiple times is invalid", "bare
keys and quoted keys are equivalent", "You can't turn an integer into a table"). -/
def DuplicateKeys : Prop :=
  ∀ i j : Fin 10,
    let k1 := keySpellings.getD i.val ([], [])
    let k2 := keySpellings.getD j.val ([], [])
    rejected (k1.1 ++ bytes% " = 1\n" ++ k2.1 ++ bytes% " = 2") =
      (k1.2.isPrefixOf k2.2 || k2.2.isPrefixOf k1.2)

theorem duplicateKeys : DuplicateKeys := by
  unfold DuplicateKeys; decide +kernel

/-- Spellings of table header keys and their key paths. -/
def headerSpellings : List (Str × List Str) :=
  [(bytes% "a", [bytes% "a"]), (bytes% "\"a\"", [bytes% "a"]), (bytes% "a.b", [bytes% "a", bytes% "b"]),
   (bytes% "a . 'b'", [bytes% "a", bytes% "b"]), (bytes% "b", [bytes% "b"]),
   (bytes% "a.b.c", [bytes% "a", bytes% "b", bytes% "c"]), (bytes% "a.c", [bytes% "a", bytes% "c"])]

/-- Two `[table]` headers are rejected exactly when they name the same table
("you cannot define a table more than once"; super-tables may come later), and
two `[[array]]` headers exactly when the second names a proper prefix of the
first, which the first made a table ("Attempting to redefine a normal table as
an array must likewise produce a parse-time error"), TOML v1.1.0, "Table" and
"Array of Tables". -/
def TableHeaders : Prop :=
  ∀ i j : Fin 7,
    let p := headerSpellings.getD i.val ([], [])
    let q := headerSpellings.getD j.val ([], [])
    rejected (bytes% "[" ++ p.1 ++ bytes% "]\n[" ++ q.1 ++ bytes% "]") = (p.2 == q.2) ∧
      rejected (bytes% "[[" ++ p.1 ++ bytes% "]]\n[[" ++ q.1 ++ bytes% "]]") =
        (q.2.isPrefixOf p.2 && q.2 != p.2)

theorem tableHeaders : TableHeaders := by
  unfold TableHeaders; decide +kernel

/-- Two decimal digits. -/
def twoDigits (n : Nat) : Str := [48 + n / 10, 48 + n % 10]

/-- The number of days of month `m` of year `y` in the proleptic Gregorian
calendar (RFC 3339, section 5.7). -/
def rfcMaxDay (y m : Nat) : Nat :=
  if m = 2 then (if y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31

/-- `TOML.tryparse` accepts the local date `Y-MM-DD` (`MM` in `01-12`, `DD` in
`01-31`) of year `y` exactly when it is a day of that year. -/
def LocalDateValidIn (y : Nat) : Prop :=
  ∀ m : Nat, m < 13 → 1 ≤ m → ∀ d : Nat, d < 32 → 1 ≤ d →
    accepted (bytes% "a = " ++ (Nat.toDigits 10 y).map Char.toNat ++ [45] ++ twoDigits m ++ [45] ++
      twoDigits d) = decide (d ≤ rfcMaxDay y m)

/-- RFC 3339 `date-mday` validity (which TOML v1.1.0 "Local Date" uses) for a
common year, a leap year, and the century years 1900 and 2000. -/
def LocalDateValid : Prop := ∀ y ∈ [2023, 2024, 1900, 2000], LocalDateValidIn y

theorem localDateValid_2023 : LocalDateValidIn 2023 := by unfold LocalDateValidIn; decide +kernel
theorem localDateValid_2024 : LocalDateValidIn 2024 := by unfold LocalDateValidIn; decide +kernel
theorem localDateValid_1900 : LocalDateValidIn 1900 := by unfold LocalDateValidIn; decide +kernel
theorem localDateValid_2000 : LocalDateValidIn 2000 := by unfold LocalDateValidIn; decide +kernel

theorem localDateValid : LocalDateValid := by
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact localDateValid_2023
  · exact localDateValid_2024
  · exact localDateValid_1900
  · exact localDateValid_2000

/-- The literal of `n` with prefix `pre` in base `b`, and the value it denotes. -/
def intLiteral : Fin 5 → Nat → Str × Val
  | 0, n => (digitsStr 10 n, .int .i64 n)
  | 1, n => (45 :: digitsStr 10 n, .int .i64 (-(n : Int)))
  | 2, n => (bytes% "0x" ++ digitsStr 16 n, .int .u64 n)
  | 3, n => (bytes% "0o" ++ digitsStr 8 n, .int .u64 n)
  | 4, n => (bytes% "0b" ++ digitsStr 2 n, .int .u64 n)

/-- Small integer literals in each form (decimal, negative decimal, hexadecimal,
octal, binary) parse to their value, as `Int64` (decimal) or `UInt64` (the
others): TOML v1.1.0, "Integer", and the type convention of PR #47903. -/
def SmallIntegerLiterals : Prop :=
  ∀ f : Fin 5, ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral f n).1) (bytes% "a") = some (intLiteral f n).2

theorem smallIntegerLiterals_0 : ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral 0 n).1) (bytes% "a") = some (intLiteral 0 n).2 := by
  decide +kernel
theorem smallIntegerLiterals_1 : ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral 1 n).1) (bytes% "a") = some (intLiteral 1 n).2 := by
  decide +kernel
theorem smallIntegerLiterals_2 : ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral 2 n).1) (bytes% "a") = some (intLiteral 2 n).2 := by
  decide +kernel
theorem smallIntegerLiterals_3 : ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral 3 n).1) (bytes% "a") = some (intLiteral 3 n).2 := by
  decide +kernel
theorem smallIntegerLiterals_4 : ∀ n : Nat, n < 256 →
    rootValue (bytes% "a = " ++ (intLiteral 4 n).1) (bytes% "a") = some (intLiteral 4 n).2 := by
  decide +kernel

theorem smallIntegerLiterals : SmallIntegerLiterals := by
  intro f
  match f with
  | 0 => exact smallIntegerLiterals_0
  | 1 => exact smallIntegerLiterals_1
  | 2 => exact smallIntegerLiterals_2
  | 3 => exact smallIntegerLiterals_3
  | 4 => exact smallIntegerLiterals_4

end JuliaLean.Toml
