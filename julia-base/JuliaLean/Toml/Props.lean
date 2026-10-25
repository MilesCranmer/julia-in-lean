import JuliaLean.Toml.Render

/-!
# Properties of the TOML parser

Each property states a rule of the TOML v1.1.0 specification (which the TOML
stdlib says it implements, `stdlib/TOML/src/TOML.jl:4`), a promise of the
`TOML.parse`/`TOML.tryparse` docstrings (`stdlib/TOML/src/TOML.jl:115-152`), or
an invariant the parser's own code states, for a family of documents.
`dates = true` is `TOML.tryparse(str)` (`Parser{Dates}`); `dates = false` is
Base's own parser (`Parser{nothing}`), used by code loading.
-/

namespace JuliaLean.Toml

/-- The exception `tryparse` ends with, if any (a `ParserError` is returned by
`tryparse`; every other `Exc` is thrown). -/
def thrown (s : Str) (dates : Bool := true) : Option Exc :=
  match tryparseState s dates with
  | .ok _ => none
  | .error e => some e

/-- `tryparse` returns a table. -/
def accepted (s : Str) (dates : Bool := true) : Bool := (thrown s dates).isNone

/-- `tryparse` returns a `ParserError`. -/
def rejected (s : Str) (dates : Bool := true) : Bool :=
  match thrown s dates with
  | some (.parserError _) => true
  | _ => false

/-- The value of a top-level key after a successful parse. -/
def rootValue (s : Str) (key : Str) (dates : Bool := true) : Option Val :=
  match tryparseState s dates with
  | .ok l => match l.heap.getD 0 (.table []) with
    | .table kvs => (kvs.find? (·.1 == key)).map (·.2)
    | .array .. => none
  | .error _ => none

/-- `A-Za-z0-9_-`, the bare-key bytes (TOML v1.1.0, "Keys"). -/
def bareByte (b : Nat) : Bool :=
  (97 ≤ b && b ≤ 122) || (65 ≤ b && b ≤ 90) || (48 ≤ b && b ≤ 57) || b == 45 || b == 95

/-- A non-empty bare key. -/
def BareKey (k : Str) : Prop := k ≠ [] ∧ ∀ b ∈ k, bareByte b = true

instance (k : Str) : Decidable (BareKey k) := by unfold BareKey; infer_instance

def decDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 57
def octDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 55
def lowerLetter (b : Nat) : Bool := 97 ≤ b && b ≤ 122

/-- The digits of `n` in base `b` (lowercase), as bytes. -/
def digitsStr (b n : Nat) : Str := (Nat.toDigits b n).map Char.toNat

/-- The value of a string of octal digit bytes. -/
def octVal (ds : Str) : Nat := ds.foldl (fun acc b => 8 * acc + (b - 48)) 0

/-! ### `tryparse` reports failures as `ParserError` -/

/-- `TOML.tryparse` never throws a `TypeError`. -/
def TryparseNoTypeError : Prop := ∀ s : Str, thrown s ≠ some .typeError

/-- `TOML.tryparse` never throws an `ArgumentError`. -/
def TryparseNoArgumentError : Prop :=
  ∀ (s : Str) (msg : String), thrown s ≠ some (.jl (.argumentError msg))

/-- Base's own parser (`Parser{nothing}`) returns a table or a `ParserError`. -/
def BaseParserNoThrow : Prop :=
  ∀ (s : Str) (e : Exc), thrown s false = some e → ∃ t, e = .parserError t

/-! ### Invalid documents are rejected -/

/-- An array-of-tables header cannot add a key to an inline table
(TOML v1.1.0, "Inline Table": "Keys and sub-tables cannot be added outside the braces"). -/
def InlineTableClosed : Prop :=
  ∀ k j : Str, BareKey k → BareKey j →
    rejected (k ++ bytes% " = {}\n[[" ++ k ++ bytes% "." ++ j ++ bytes% "]]") = true

/-- `0x` with a fractional part is not a TOML number (TOML v1.1.0, "Float"). -/
def NoHexFloat : Prop :=
  ∀ ds : Str, ds ≠ [] → (∀ b ∈ ds, decDigit b = true) →
    rejected (bytes% "a = 0x." ++ ds) = true

/-- Dates and times have no sign; the year has four digits and the hour two
(TOML v1.1.0, "Local Date", "Local Time", RFC 3339 `date-fullyear = 4DIGIT`,
`time-hour = 2DIGIT`). -/
def DateTimeUnsigned : Prop :=
  (∀ sg d1 d2 d3 : Nat, (sg = 43 ∨ sg = 45) → decDigit d1 = true → decDigit d2 = true →
      decDigit d3 = true → rejected (bytes% "a = " ++ [sg, d1, d2, d3] ++ bytes% "-01-01") = true) ∧
    (∀ sg h : Nat, (sg = 43 ∨ sg = 45) → decDigit h = true →
      rejected (bytes% "a = " ++ [sg, h] ++ bytes% ":30:00") = true)

/-- A key that names a table (created by `[a.b.c]`) cannot then be given a value
(TOML v1.1.0, "Keys": "Defining a key multiple times is invalid"). -/
def NoTableOverwrite : Prop :=
  ∀ a b c : Str, BareKey a → BareKey b → BareKey c → ∀ n : Nat, decDigit n = true →
    rejected (bytes% "[" ++ a ++ bytes% "." ++ b ++ bytes% "." ++ c ++ bytes% "]\n[" ++ a ++
      bytes% "]\n" ++ b ++ bytes% " = " ++ [n]) = true

/-- A single-line basic string cannot contain a newline, escaped or not
(TOML v1.1.0, "String"). -/
def SingleLineNoContinuation : Prop :=
  ∀ x y : Str, (∀ b ∈ x ++ y, lowerLetter b = true) →
    rejected (bytes% "a = \"" ++ x ++ bytes% "\\\n" ++ y ++ bytes% "\"") = true

/-- Control characters other than tab are not allowed in basic strings
(TOML v1.1.0, "String"). -/
def ControlCharsRejected : Prop :=
  ∀ c : Nat, (c ≤ 8 ∨ (10 ≤ c ∧ c ≤ 31) ∨ c = 127) →
    rejected (bytes% "a = \"x" ++ [c] ++ bytes% "y\"") = true

/-- A document must be valid UTF-8 (TOML v1.1.0, "Preliminaries"): the bytes
`0xF8`-`0xFF` never occur in UTF-8. -/
def InvalidUtf8Rejected : Prop :=
  ∀ b : Nat, 0xF8 ≤ b → b ≤ 0xFF → rejected (bytes% "a = \"" ++ [b] ++ bytes% "\"") = true

/-! ### Valid documents parse to the right value -/

/-- `\xHH` is the character U+00HH (TOML v1.1.0, "String"). -/
def HexEscapeCodepoint : Prop :=
  ∀ h1 h2 : Nat, (hexByte h1).isSome = true → (hexByte h2).isSome = true →
    rootValue (bytes% "a = \"\\x" ++ [h1, h2] ++ bytes% "\"") (bytes% "a") =
      some (.str (utf8 (16 * (hexByte h1).getD 0 + (hexByte h2).getD 0)))

/-- One or two quotes may stand just inside the delimiters of a multi-line
basic string (TOML v1.1.0, "String"). -/
def MultilineQuotesBeforeDelimiter : Prop :=
  ∀ x : Str, (∀ b ∈ x, lowerLetter b = true) →
    rootValue (bytes% "a = \"\"\"\"" ++ x ++ bytes% "\"\"\"\"") (bytes% "a") = some (.str (34 :: x ++ [34]))

/-- A line-ending backslash trims the whitespace after it, including spaces
before the newline (TOML v1.1.0, "String"). -/
def ContinuationTrailingWhitespace : Prop :=
  ∀ n : Nat, 1 ≤ n →
    rootValue (bytes% "a = \"\"\"x \\" ++ List.replicate n 32 ++ bytes% "\n  y\"\"\"") (bytes% "a") =
      some (.str (bytes% "x y"))

/-- A float may have underscores between digits before its exponent
(TOML v1.1.0, "Float"). -/
def FloatUnderscoreExponent : Prop :=
  ∀ d1 d2 d3 : Nat, (49 ≤ d1 ∧ d1 ≤ 57) → decDigit d2 = true → decDigit d3 = true →
    accepted (bytes% "a = " ++ [d1, 95, d2, 101, d3]) = true

/-- An offset date-time with a numeric offset `±HH:MM` is a TOML value
(TOML v1.1.0, "Offset Date-Time"; the TOML stdlib claims TOML v1.1 support,
`stdlib/TOML/src/TOML.jl:4`). -/
def OffsetDateTimeAccepted : Prop :=
  ∀ sg h1 h2 m1 m2 : Nat, (sg = 43 ∨ sg = 45) → (48 ≤ h1 ∧ h1 ≤ 49) → decDigit h2 = true →
    (48 ≤ m1 ∧ m1 ≤ 53) → decDigit m2 = true →
      accepted (bytes% "a = 1979-05-27T00:32:00" ++ [sg, h1, h2, 58, m1, m2]) = true

/-- A non-negative decimal integer in the `Int64` range is parsed as an `Int64`
(the convention of PR #47903, which introduced the wider types: "all numbers
below UInt64 and Int64 are parsed as UInt64 or Int64 for compatibility"). -/
def DecimalInt64Typed : Prop :=
  ∀ n : Nat, n < 2 ^ 63 →
    rootValue (bytes% "a = " ++ digitsStr 10 n) (bytes% "a") = some (.int .i64 n)

/-- Whether an octal literal is accepted does not decrease with its value
(invariant of the `UInt64`/`UInt128`/`BigInt` widening, `base/toml/parser.jl:1140-1162`). -/
def OctalAcceptanceMonotone : Prop :=
  ∀ d1 d2 : Str, d1 ≠ [] → d2 ≠ [] → (∀ b ∈ d1 ++ d2, octDigit b = true) →
    octVal d1 ≤ octVal d2 → accepted (bytes% "a = 0o" ++ d2) = true →
      accepted (bytes% "a = 0o" ++ d1) = true

/-- A leading byte order mark is skipped (`startup`, `base/toml/parser.jl:167-175`). -/
def BomSkipped : Prop := ∀ s : Str, outcome ([0xEF, 0xBB, 0xBF] ++ s) = outcome s

end JuliaLean.Toml
