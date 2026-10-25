import JuliaLean.Toml.Basic
import JuliaLean.ParsePrint.IntParse

/-!
# TOML numbers, dates and times

`base/toml/parser.jl:964-1353` at master `bbfa0ce4150`, with the callees it
relies on:

* `Base.parse(T, s; base)` for `T` in `Int64`, `Int128`, `UInt64`, `UInt128` is
  `JuliaLean.ParsePrint.IntParse.parse` (`base/parse.jl`); for `BigInt` it is
  `parseBigInt` below (`base/gmp.jl:307-331`).
* `Base.tryparse(Float64, s)` is `parsefloat` below (`base/parse.jl:267-279`,
  `base/parsers/floats.jl:288-420`). It keeps the exact value of the literal and
  assumes the library rounds to nearest, ties to even, so a literal is
  `UNDERFLOW` exactly when its value is at most `2^-1075` and `OVERFLOW` exactly
  when it is at least `2^1024 - 2^970`.
* `Dates.Date`, `Dates.Time` and `Dates.DateTime` validate their fields as
  `stdlib/Dates/src/types.jl:337-341,383-397,412-416,437-449`.
-/

namespace JuliaLean.Toml

open JuliaLean

/-! ### `Base.tryparse(Float64, s)` -/

/-- The outcome of `Base.Parsers.parsefloat`. -/
inductive FRes where
  | invalid | overflow | underflow
  | val (f : FloatV)
  deriving Repr, DecidableEq

def isDecByte (b : Nat) : Bool := 48 ≤ b && b ≤ 57

/-- The value of a hexadecimal digit byte. -/
def hexByte (b : Nat) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b - 48)
  else if 97 ≤ b && b ≤ 102 then some (b - 87)
  else if 65 ≤ b && b ≤ 70 then some (b - 55)
  else none

/-- `scandigits`: the decimal digits at the start of `bs` appended to `w`, their
count, and the rest. The value is exact (Julia wraps it modulo `2^64` only when
there are more than 19 digits, and then re-derives the rounding from the digits,
`base/parsers/floats.jl:394-418`). -/
def scanDec : List Nat → Nat → Nat × Nat × List Nat
  | b :: bs, w =>
    if isDecByte b then
      let (w', k, r) := scanDec bs (10 * w + (b - 48))
      (w', k + 1, r)
    else (w, 0, b :: bs)
  | [], w => (w, 0, [])

/-- `scanhex` without the 16-digit window: the exact value, count and rest. -/
def scanHex : List Nat → Nat → Nat × Nat × List Nat
  | b :: bs, w =>
    match hexByte b with
    | some d =>
      let (w', k, r) := scanHex bs (16 * w + d)
      (w', k + 1, r)
    | none => (w, 0, b :: bs)
  | [], w => (w, 0, [])

/-- `scanexponent`, `base/parsers/floats.jl:228-243`: the value (which stops
growing at `10^8`), the rest, and whether there was a digit. -/
def scanExponent (bs : List Nat) : Int × List Nat × Bool :=
  let (neg, bs) := match bs with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let rec go : List Nat → Nat → Nat × Nat × List Nat
    | b :: r, e =>
      if isDecByte b then
        let (e', k, rest) := go r (if e < 100000000 then 10 * e + (b - 48) else e)
        (e', k + 1, rest)
      else (e, 0, b :: r)
    | [], e => (e, 0, [])
  let (e, k, rest) := go bs 0
  ((if neg then -(e : Int) else e), rest, k > 0)

/-- `2^1024 - 2^970`, the smallest value that rounds to `Inf`. -/
def ovfBound : Nat := 2 ^ 1024 - 2 ^ 970

/-- The number of decimal digits of a positive `n`. -/
def ndigits10 (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- Rounding outcome of the positive value `w * 10^q`. -/
def classifyDec (neg : Bool) (w : Nat) (q : Int) : FRes :=
  if w = 0 then .val (.finite neg 0 1) else
  let sd := ndigits10 w
  if q ≥ 0 then
    if q + sd > 310 then .overflow
    else if w * 10 ^ q.toNat ≥ ovfBound then .overflow
    else .val (.finite neg (w * 10 ^ q.toNat) 1)
  else
    let k := (-q).toNat
    if (sd : Int) + q < -330 then .underflow
    else if w * 2 ^ 1075 ≤ 10 ^ k then .underflow
    else if w ≥ ovfBound * 10 ^ k then .overflow
    else .val (.finite neg w (10 ^ k))

/-- Rounding outcome of the positive value `m * 2^e`. -/
def classifyBin (neg : Bool) (m : Nat) (e : Int) : FRes :=
  if m = 0 then .val (.finite neg 0 1) else
  if e > 5000 then .overflow
  else if e < -5000 - (Nat.log2 m : Int) then .underflow
  else if e ≥ 0 then
    if m * 2 ^ e.toNat ≥ ovfBound then .overflow else .val (.finite neg (m * 2 ^ e.toNat) 1)
  else
    let k := (-e).toNat
    if m * 2 ^ 1075 ≤ 2 ^ k then .underflow
    else if m ≥ ovfBound * 2 ^ k then .overflow
    else .val (.finite neg m (2 ^ k))

/-- `parsehex`, `base/parsers/floats.jl:288-309`, on the bytes after `0x`. -/
def parsehex (bs : List Nat) (neg : Bool) : FRes :=
  let (m, ni, r) := scanHex bs 0
  let (m, nf, r) := match r with
    | 46 :: r' => scanHex r' m
    | _ => (m, 0, r)
  if ni + nf = 0 then .invalid else
  let (pe, ok, r) : Int × Bool × List Nat := match r with
    | b :: r' =>
      if b = 112 ∨ b = 80 then
        let (x, rest, ok) := scanExponent r'
        (x, ok, rest)
      else (0, true, b :: r')
    | [] => (0, true, [])
  if !ok then .invalid else
  if r ≠ [] then .invalid else
  classifyBin neg m (pe - 4 * (nf : Int))

/-- `Base.tryparse(Float64, s)` on the bytes TOML passes to it (`parse_float`,
`base/toml/parser.jl:1122-1127`): `base/parse.jl:268-279` and `parsefloat`,
`base/parsers/floats.jl:364-420`. After an optional sign these strings start with
a digit, so `parsespecial` (`inf`, `nan`, ...) is not reached and is modelled as
`INVALID`. ASCII whitespace never occurs in them. -/
def parsefloat (s : List Nat) : FRes :=
  let (neg, bs) := match s with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  match bs with
  | [] => .invalid
  | b :: rest =>
    if !(isDecByte b || b = 46) then .invalid
    else if b == 48 && (match rest with | c :: _ => c ||| 32 == 120 | [] => false) then
      parsehex (rest.drop 1) neg
    else
      let (w, ni, r) := scanDec bs 0
      let (w, nf, r) := match r with
        | 46 :: r' => scanDec r' w
        | _ => (w, 0, r)
      if ni + nf = 0 then .invalid else
      let (e, ok, r) : Int × Bool × List Nat := match r with
        | c :: r' =>
          if c ||| 32 = 101 then
            let (x, rest, ok) := scanExponent r'
            (x, ok, rest)
          else (0, true, c :: r')
        | [] => (0, true, [])
      if !ok then .invalid else
      if r ≠ [] then .invalid else
      classifyDec neg w (e - nf)

/-! ### `Base.parse(BigInt, s)` -/

/-- `Base.parse(BigInt, s)` for an ASCII `s` without whitespace or NUL:
`parseint_preamble` (`base/parse.jl:102-123`) then `mpz_set_str`
(`base/gmp.jl:307-331`), which accepts an optional `-` and at least one digit of
the base. -/
def parseBigInt (s : List Nat) : Except Exc Int :=
  let (sgn, s) : Int × List Nat := match s with
    | 45 :: r => (-1, r)
    | 43 :: r => (1, r)
    | r => (1, r)
  if s = [] then .error (.jl (.argumentError "invalid base")) else
  let (base, s, ok) : Nat × List Nat × Bool := match s with
    | 48 :: c :: r =>
      if c = 98 then (2, r, true) else if c = 111 then (8, r, true)
      else if c = 120 then (16, r, true) else (10, 48 :: c :: r, true)
    | r => (10, r, true)
  -- `i + 2 <= j ? i + 2 : 0` and `i == 0` give "premature end of integer"
  if !ok ∨ (base ≠ 10 ∧ s = []) then .error (.jl (.argumentError "premature end of integer")) else
  let (gsgn, ds) : Int × List Nat := match s with
    | 45 :: r => (-1, r)
    | r => (1, r)
  let digit (b : Nat) : Option Nat :=
    match hexByte b with
    | some d => if d < base then some d else none
    | none => none
  if ds = [] ∨ ds.any (fun b => (digit b).isNone) then
    .error (.jl (.argumentError "invalid BigInt"))
  else
    let v := ds.foldl (fun acc b => acc * base + (digit b).getD 0) 0
    .ok (sgn * gsgn * v)

/-! ### Number lexing, `base/toml/parser.jl:968-1162` -/

/-- `ok_end_value`, `base/toml/parser.jl:1169-1170`. -/
def ok_end_value (c : Nat) : Bool :=
  iswhitespace c || c == ch '#' || c == EOF || c == ch ']' ||
    c == ch '}' || c == ch ',' || c == ch '\n' || c == ch '\r'

/-- `parse_inf`, `base/toml/parser.jl:968`. -/
def parse_inf (sgn : Int) : M (Option Val) := do
  if (← acceptC 'n') then
    if (← acceptC 'f') then return some (.float (.inf (sgn < 0)))
  return none

/-- `parse_nan`, `base/toml/parser.jl:969`. -/
def parse_nan : M (Option Val) := do
  if (← acceptC 'a') then
    if (← acceptC 'n') then return some (.float .nan)
  return none

/-- `parse_bool`, `base/toml/parser.jl:971-976`, after the first letter. -/
def parse_bool (v : Bool) : M (Option Val) := do
  if v then
    if (← acceptC 'r') then if (← acceptC 'u') then if (← acceptC 'e') then
      return some (.bool true)
  else
    if (← acceptC 'a') then if (← acceptC 'l') then if (← acceptC 's') then
      if (← acceptC 'e') then return some (.bool false)
  return none

/-- `isvalid_hex`, `isvalid_oct`, `isvalid_binary`, `base/toml/parser.jl:978-980`. -/
def isvalid_hex (c : Nat) : Bool :=
  isdigit c || (ch 'a' ≤ c && c ≤ ch 'f') || (ch 'A' ≤ c && c ≤ ch 'F')
def isvalid_oct (c : Nat) : Bool := ch '0' ≤ c && c ≤ ch '7'
def isvalid_binary (c : Nat) : Bool := ch '0' ≤ c && c ≤ ch '1'

/-- The loop of `accept_batch_underscore`, `base/toml/parser.jl:985-1014`, with its
state `(fail_if_underscore, contains_underscore, at_least_one, last_underscore)`. -/
def abuLoop (f : Nat → Bool) : Nat → Bool → Bool → Bool → Bool → M (Bool × Bool)
  | 0, _, _, _, _ => throw .outOfFuel
  | fuel + 1, failU, contains, atLeastOne, lastU => do
    let c ← peek
    if c == ch '_' then
      if failU then perr .ErrUnderscoreNotSurroundedByDigits
      discard eat_char
      abuLoop f fuel true true atLeastOne true
    else
      if f c then
        discard eat_char
        abuLoop f fuel false contains true false
      else
        if lastU then perr .ErrTrailingUnderscoreNumber
        return (atLeastOne, contains)

/-- `accept_batch_underscore(l, f, fail_if_underscore)`: whether it ate a digit and
whether it ate an underscore. -/
def accept_batch_underscore (fuel : Nat) (f : Nat → Bool) (failU : Bool := true) :
    M (Bool × Bool) :=
  abuLoop f fuel failU false false false

/-- `take_string_or_substring`, `base/toml/parser.jl:1115-1120`. -/
def take_string_or_substring (containsUnderscore : Bool) : M Str := do
  let subs ← take_substring
  return if containsUnderscore then subs.filter (· != 95) else subs

/-- `parse_float`, `base/toml/parser.jl:1122-1127`. -/
def parse_float (containsUnderscore : Bool) : M Val := do
  let s ← take_string_or_substring containsUnderscore
  match parsefloat s with
  | .val f => return .float f
  | _ => perr .ErrGenericValueError

/-- `Base.parse(T, s; base)` for a `BitInteger` `T`, with `OverflowError` turned
into `ErrOverflowError` and other exceptions rethrown (the `try`/`catch` of
`base/toml/parser.jl:1131-1136,1148-1159`). -/
def parseBits (t : IntTy) (s : Str) (base : Option Int) : M Int :=
  match ParsePrint.IntParse.parse t (s.map ParsePrint.IntParse.byte) base with
  | .ok v => return v.val
  | .error (.overflowError _) => perr .ErrOverflowError
  | .error e => throw (.jl e)

/-- `parse_int(l, contains_underscore, base)`, `base/toml/parser.jl:1129-1138`. -/
def parse_int (containsUnderscore : Bool) (base : Option Int := none) : M Int := do
  let s ← take_string_or_substring containsUnderscore
  parseBits .i64 s base

/-- Which of the generated `parse_integer`, `parse_hex`, `parse_oct`, `parse_bin`. -/
inductive IntSyntax where
  | integer | hex | oct | bin
  deriving Repr, DecidableEq

/-- `(T1, T2, n1, n2)` of `base/toml/parser.jl:1140-1144`. -/
def IntSyntax.table : IntSyntax → IntTy × IntTy × Nat × Nat
  | .integer => (.i64, .i128, 17, 33)
  | .hex => (.u64, .u128, 18, 34)
  | .oct => (.u64, .u128, 24, 45)
  | .bin => (.u64, .u128, 66, 130)

def kindOf : IntTy → IntKind
  | .i64 => .i64 | .i128 => .i128 | .u64 => .u64 | .u128 => .u128 | _ => .big

/-- `parse_integer`, `parse_hex`, `parse_oct`, `parse_bin`,
`base/toml/parser.jl:1145-1161`. -/
def parse_intlike (sx : IntSyntax) (containsUnderscore : Bool) : M Val := do
  let s ← take_string_or_substring containsUnderscore
  let (t1, t2, n1, n2) := sx.table
  let len := s.length
  if len ≤ n1 then return .int (kindOf t1) (← parseBits t1 s none)
  else if len ≤ n2 then return .int (kindOf t2) (← parseBits t2 s none)
  else
    match parseBigInt s with
    | .ok v => return .int .big v
    | .error e => throw e

/-! ### Dates and times, `base/toml/parser.jl:1197-1353` -/

/-- `isleapyear`, `stdlib/Dates/src/types.jl:337` (`%` is `rem`; only divisibility matters). -/
def isleapyear (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- `daysinmonth(y, m)` for `1 ≤ m ≤ 12`, `stdlib/Dates/src/types.jl:340-341`. -/
def daysinmonth (y m : Int) : Int :=
  ([31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31] : List Int).getD (m - 1).toNat 0 +
    (if m == 2 && isleapyear y then 1 else 0)

/-- `validargs(Date, y, m, d) === nothing`, `stdlib/Dates/src/types.jl:412-416`. -/
def validDate (y m d : Int) : Bool := 0 < m && m < 13 && 0 < d && d < daysinmonth y m + 1

/-- `validargs(Time, h, mi, s, ms, 0, 0) === nothing`, `stdlib/Dates/src/types.jl:437-449`. -/
def validTime (h mi s ms : Int) : Bool :=
  -1 < h && h < 24 && -1 < mi && mi < 60 && -1 < s && s < 60 && -1 < ms && ms < 1000

/-- `validargs(DateTime, ...) === nothing`, `stdlib/Dates/src/types.jl:383-397`. -/
def validDateTime (y m d h mi s ms : Int) : Bool :=
  0 < m && m < 13 && 0 < d && d < daysinmonth y m + 1 &&
    (-1 < h && h < 24 || (h == 24 && mi == 0 && s == 0 && ms == 0)) &&
    -1 < mi && mi < 60 && -1 < s && s < 60 && -1 < ms && ms < 1000

/-- `accept_two`, `base/toml/parser.jl:1197`. -/
def accept_two (f : Nat → Bool) : M Unit := do
  if !(← accept_n f 2) then perr .ErrParsingDateTime

/-- `try_return_datetime`, `base/toml/parser.jl:1252-1263`: with `Dates`, an
`ArgumentError` from the constructor becomes `ErrParsingDateTime`; Base's own
struct checks nothing. -/
def try_return_datetime (y m d h mi s ms : Int) : M Val := do
  if (← get).dates && !validDateTime y m d h mi s ms then perr .ErrParsingDateTime
  return .datetime y m d h mi s ms

/-- `try_return_date`, `base/toml/parser.jl:1265-1276`. -/
def try_return_date (y m d : Int) : M Val := do
  if (← get).dates && !validDate y m d then perr .ErrParsingDateTime
  return .date y m d

/-- `try_return_time`, `base/toml/parser.jl:1289-1300`. -/
def try_return_time (h mi s ms : Int) : M Val := do
  if (← get).dates && !validTime h mi s ms then perr .ErrParsingDateTime
  return .time h mi s ms

def inRange (x lo hi : Int) : Bool := lo ≤ x && x ≤ hi

/-- `_parse_local_time(l, skip_hour)`, `base/toml/parser.jl:1302-1353`. -/
def _parse_local_time (fuel : Nat) (skipHour : Bool) : M (Int × Int × Int × Int) := do
  let mut hour : Int := 0
  if !skipHour then
    set_marker
    accept_two isdigit
    hour ← parse_int false
    if !inRange hour 0 23 then perr .ErrParsingDateTime
  if !(← acceptC ':') then perr .ErrParsingDateTime
  set_marker
  accept_two isdigit
  let minute ← parse_int false
  if !inRange minute 0 59 then perr .ErrParsingDateTime
  let mut second : Int := 0
  let mut millisecond : Int := 0
  if (← acceptC ':') then
    set_marker
    accept_two isdigit
    second ← parse_int false
    if !inRange second 0 59 then perr .ErrParsingDateTime
    if (← acceptC '.') then
      set_marker
      let a1 ← accept isdigit
      let a2 ← accept isdigit
      let a3 ← accept isdigit
      if !(a1 || a2 || a3) then perr .ErrParsingDateTime
      let l ← get
      let nd := l.prevpos - l.marker
      let frac ← parse_int false
      millisecond := frac * 10 ^ (3 - nd).toNat
      discard (accept_batch isdigit fuel)
  return (hour, minute, second, millisecond)

/-- `parse_local_time`, `base/toml/parser.jl:1278-1287`, after the hour digits. -/
def parse_local_time (fuel : Nat) : M Val := do
  let l ← get
  if l.prevpos - l.marker != 2 then perr .ErrParsingDateTime
  let h ← parse_int false
  if !inRange h 0 23 then perr .ErrParsingDateTime
  let (_, m, s, ms) ← _parse_local_time fuel true
  try_return_time h m s ms

/-- `parse_datetime`, `base/toml/parser.jl:1198-1250`, after the year digits. -/
def parse_datetime (fuel : Nat) : M Val := do
  let yearStart := (← get).marker
  let year ← parse_int false
  if (← get).prevpos - yearStart != 4 then perr .ErrParsingDateTime
  if !(← acceptC '-') then perr .ErrParsingDateTime
  set_marker
  accept_two isdigit
  let month ← parse_int false
  if !inRange month 1 12 then perr .ErrParsingDateTime
  if !(← acceptC '-') then perr .ErrParsingDateTime
  set_marker
  accept_two isdigit
  let day ← parse_int false
  if !inRange day 1 31 then perr .ErrParsingDateTime
  let mut readSpace := false
  if ok_end_value (← peek) then
    readSpace ← acceptC ' '
    if readSpace then
      if !isdigit (← peek) then return ← try_return_date year month day
    else return ← try_return_date year month day
  if !readSpace then
    if !(← acceptC 'T') then
      if !(← acceptC 't') then perr .ErrParsingDateTime
  let (h, m, s, ms) ← _parse_local_time fuel false
  if !(← acceptC 'Z') then
    if (← acceptC '+') then perr .ErrOffsetDateNotSupported
    if (← acceptC '-') then perr .ErrOffsetDateNotSupported
  if !ok_end_value (← peek) then perr .ErrParsingDateTime
  try_return_datetime year month day h m s ms

/-- `parse_number_or_date_start`, `base/toml/parser.jl:1016-1112`. `none` is
Julia's `nothing` (from `parse_inf`/`parse_nan`). -/
def parse_number_or_date_start (fuel : Nat) : M (Option Val) := do
  set_marker
  let mut sgn : Int := 1
  let mut parsedSign := false
  if (← acceptC '+') then
    parsedSign := true
  else
    let minus ← acceptC '-'
    if minus then
      parsedSign := true
      sgn := -1
  if (← acceptC 'i') then return ← parse_inf sgn
  if (← acceptC 'n') then return ← parse_nan
  if (← acceptC '.') then perr .ErrLeadingDot
  let mut readedZero := false
  if (← acceptC '0') then
    readedZero := true
    if ok_end_value (← peek) then return some (.int .i64 0)
    let x ← acceptC 'x'
    if x then
      if parsedSign then perr .ErrSignInNonBase10Number
      let (ate, cu) ← accept_batch_underscore fuel isvalid_hex
      if ate then return some (← parse_intlike .hex cu)
    else
      let o ← acceptC 'o'
      if o then
        if parsedSign then perr .ErrSignInNonBase10Number
        let (ate, cu) ← accept_batch_underscore fuel isvalid_oct
        if ate then return some (← parse_intlike .oct cu)
      else
        let b ← acceptC 'b'
        if b then
          if parsedSign then perr .ErrSignInNonBase10Number
          let (ate, cu) ← accept_batch_underscore fuel isvalid_binary
          if ate then return some (← parse_intlike .bin cu)
        else
          let d ← accept isdigit
          if d then
            discard (accept_batch isdigit fuel)
            if (← peek) == ch ':' then return some (← parse_local_time fuel)
            if (← peek) == ch '-' then return some (← parse_datetime fuel)
            perr .ErrLeadingZeroNotAllowedInteger
  let mut readUnderscore := false
  let readDigit ← accept isdigit
  if !readedZero && !readDigit then
    if (← peek) == EOF then perr .ErrUnexpectedEofExpectedValue
    else perr .ErrUnexpectedStartOfValue
  let (ate, containsUnderscore) ← accept_batch_underscore fuel isdigit readedZero
  readUnderscore := readUnderscore || containsUnderscore
  if (readDigit || ate) && ok_end_value (← peek) then
    return some (← parse_intlike .integer containsUnderscore)
  if !readUnderscore then
    if (← peek) == ch '-' then return some (← parse_datetime fuel)
    else if (← peek) == ch ':' then return some (← parse_local_time fuel)
  let ateDot ← acceptC '.'
  let (ate, containsUnderscore) ← accept_batch_underscore fuel isdigit true
  if ateDot && !ate then perr .ErrNoTrailingDigitAfterDot
  readUnderscore := readUnderscore || containsUnderscore
  if (← accept fun x => x == ch 'e' || x == ch 'E') then
    discard (accept fun x => x == ch '+' || x == ch '-')
    let readDigit ← accept_batch isdigit fuel
    -- `_, read_underscore = @try accept_batch_underscore(...)` replaces the flag
    let (_, ru) ← accept_batch_underscore fuel isdigit (!readDigit)
    readUnderscore := ru
  if !ok_end_value (← peek) then
    discard eat_char
    perr .ErrGenericValueError
  return some (← parse_float readUnderscore)

end JuliaLean.Toml
