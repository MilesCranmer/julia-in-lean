import Lean
import JuliaLean.Core

/-!
# TOML parser model: characters, values and parser state

Model of `base/toml/parser.jl` at master `bbfa0ce4150` (the same code is
`base/toml/parser.jl` in Julia 1.13.2, which lacks only the comment capture).

* A Julia `String` is its list of bytes (`Str`). `iterate(s, i)` decodes UTF-8
  exactly as `base/strings/string.jl:504-538`: a `Char` is its raw `UInt32`
  (the UTF-8 bytes left-aligned), so malformed sequences are represented too, and
  `Char` comparisons compare raw values.
* Positions (`pos`, `prevpos`, `marker`) are byte indices, as in Julia.
* Tables and arrays are mutable objects compared by identity (`IdSet`), so they
  live in a heap (`List Obj`) and values refer to them by index; the root table
  is object `0`.
* The model covers parsing without comment capture (`comments === nothing`, the
  case of `TOML.parse(str)`, `TOML.tryparse(str)` and Base's code loading).
  Line and column bookkeeping only feeds error messages and is omitted.
* Every `while true` loop and every recursive call consumes one unit of fuel;
  each loop iteration eats at least one byte, so fuel equal to the input length
  plus a constant is never exhausted (`Exc.outOfFuel` is a model artefact).
-/

namespace JuliaLean.Toml

/-- Bytes of a Julia `String`. -/
abbrev Str := List Nat

/-- The UTF-8 encoding of a code point below `0x110000`. -/
def utf8 (cp : Nat) : List Nat :=
  if cp < 0x80 then [cp]
  else if cp < 0x800 then [0xC0 + cp / 64, 0x80 + cp % 64]
  else if cp < 0x10000 then [0xE0 + cp / 4096, 0x80 + (cp / 64) % 64, 0x80 + cp % 64]
  else [0xF0 + cp / 262144, 0x80 + (cp / 4096) % 64, 0x80 + (cp / 64) % 64, 0x80 + cp % 64]

/-- The raw `UInt32` of the Julia `Char` with code point `cp` (`base/char.jl:47-57`). -/
def rawOf (cp : Nat) : Nat :=
  let bs := utf8 cp
  bs.foldl (fun acc b => acc * 256 + b) 0 * 2 ^ (8 * (4 - bs.length))

/-- The raw value of a Julia character literal. -/
def ch (c : Char) : Nat := rawOf c.toNat

/-- `EOF_CHAR = typemax(Char)`, `base/toml/parser.jl:26`. -/
def EOF : Nat := 0xFFFFFFFF

/-- `bytes% "..."`: the UTF-8 bytes of a string literal, as a `List Nat` literal
(computed at elaboration time, so the kernel never decodes a `String`). -/
elab "bytes% " s:str : term => do
  return Lean.toExpr (s.getString.toUTF8.toList.map (·.toNat))

/-- `codeunit(s, i)` for `1 ≤ i ≤ ncodeunits(s)`. -/
def cu (s : Str) (i : Int) : Nat := s.getD (i - 1).toNat 0

/-- `iterate(s::String, i)`, `base/strings/string.jl:504-538`. -/
def iterate (s : Str) (i : Int) : Option (Nat × Int) :=
  let n : Int := s.length
  if i > n then none else
  let b := cu s i
  let u := b * 2 ^ 24
  if ¬ (0x80 ≤ b ∧ b ≤ 0xf7) then some (u, i + 1)
  else if u < 0xc0000000 then some (u, i + 1)
  else
    let i := i + 1
    if i > n then some (u, i) else
    let b := cu s i
    if b / 64 != 2 then some (u, i) else
    let u := u + b * 2 ^ 16
    let i := i + 1
    if i > n ∨ u < 0xe0000000 then some (u, i) else
    let b := cu s i
    if b / 64 != 2 then some (u, i) else
    let u := u + b * 2 ^ 8
    let i := i + 1
    if i > n ∨ u < 0xf0000000 then some (u, i) else
    let b := cu s i
    if b / 64 != 2 then some (u, i) else
    some (u + b, i + 1)

/-- The bytes `s[a:b]` (a byte range, as `SubString` and `unsafe_copyto!` take them). -/
def slice (s : Str) (a b : Int) : Str :=
  if b < a then [] else (s.drop (a - 1).toNat).take (b - a + 1).toNat

/-- `ErrorType`, `base/toml/parser.jl:228-282`. -/
inductive ErrType where
  | ErrRedefineTableArray | ErrExpectedNewLineKeyValue | ErrAddKeyToInlineTable
  | ErrAddArrayToStaticArray | ErrArrayTreatedAsDictionary | ErrExpectedEndOfTable
  | ErrExpectedEndArrayOfTable
  | ErrExpectedEqualAfterKey | ErrDuplicatedKey | ErrKeyAlreadyHasValue
  | ErrInvalidBareKeyCharacter | ErrEmptyBareKey
  | ErrUnexpectedEofExpectedValue | ErrUnexpectedStartOfValue | ErrGenericValueError
  | ErrExpectedCommaBetweenItemsArray
  | ErrExpectedCommaBetweenItemsInlineTable | ErrTrailingCommaInlineTable | ErrInlineTableRedefine
  | ErrUnderscoreNotSurroundedByDigits | ErrLeadingZeroNotAllowedInteger | ErrOverflowError
  | ErrLeadingDot | ErrNoTrailingDigitAfterDot | ErrTrailingUnderscoreNumber
  | ErrSignInNonBase10Number
  | ErrParsingDateTime | ErrOffsetDateNotSupported
  | ErrNewLineInString | ErrUnexpectedEndString | ErrInvalidEscapeCharacter
  | ErrInvalidUnicodeScalar | ErrMultilineStringAsKey
  deriving Repr, DecidableEq, Inhabited

/-- How a parse ends abnormally. `parserError` is a `ParserError` (returned by
`tryparse`, thrown by `parse`); the others are exceptions thrown out of both. -/
inductive Exc where
  | parserError (e : ErrType)
  /-- `TypeError` from a failed type assertion `x::T`. -/
  | typeError
  /-- An exception from a function modelled in `JuliaLean.Core` terms, e.g. the
  `ArgumentError` that `Base.parse` throws. -/
  | jl (e : JlError)
  /-- `ErrorException` from `error(msg)`. -/
  | errorException (msg : String)
  /-- Model artefact: fuel exhausted. -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- The integer types the parser produces (`base/toml/parser.jl:1140-1144`). -/
inductive IntKind where
  | i64 | i128 | big | u64 | u128
  deriving Repr, DecidableEq, Inhabited

/-- A `Float64` result: the exact value of the literal (rounding to nearest
`Float64` is left implicit; a literal that rounds to zero or to infinity is
rejected by `Base.tryparse` and never reaches a `Val`), or infinity / NaN. -/
inductive FloatV where
  | finite (neg : Bool) (num den : Nat)
  | inf (neg : Bool)
  | nan
  deriving Repr, DecidableEq, Inhabited

/-- A parsed TOML value; `ref k` is the table or array stored at heap index `k`. -/
inductive Val where
  | str (s : Str)
  | int (k : IntKind) (v : Int)
  | float (f : FloatV)
  | bool (b : Bool)
  | date (y m d : Int)
  | time (h mi s ms : Int)
  | datetime (y m d h mi s ms : Int)
  | ref (id : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Element types of the typed arrays `parse_array` builds
(`base/toml/parser.jl:910-933`); `any` is `Vector{Any}`. -/
inductive ElTy where
  | any | string | bool | i64 | u64 | f64
  deriving Repr, DecidableEq, Inhabited

/-- A heap object: a `Dict{String,Any}` (key order is irrelevant) or a `Vector`. -/
inductive Obj where
  | table (kvs : List (Str × Val))
  | array (el : ElTy) (xs : List Val)
  deriving Repr, DecidableEq, Inhabited

/-- `typeof` of a value, as compared in `parse_array`. With `Dates === nothing`
dates and times are Base's own structs; otherwise `Dates.Date` etc.; the two are
distinguished by `Parser.dates`. -/
inductive JTy where
  | string | i64 | i128 | big | u64 | u128 | f64 | bool | date | time | datetime | dict
  | vec (e : ElTy)
  deriving Repr, DecidableEq, Inhabited

/-- The mutable `Parser` (`base/toml/parser.jl:76-134`), without the fields that
only serve comments, line/column bookkeeping and the file path. -/
structure Parser where
  str : Str
  /-- `Dates !== nothing` (the TOML stdlib) or `Dates === nothing` (Base's code loading). -/
  dates : Bool
  current_char : Nat
  pos : Int
  prevpos : Int
  marker : Int
  active_table : Nat
  dotted_keys : List Str
  chunks : List (Int × Int)
  inline_tables : List Nat
  static_arrays : List Nat
  defined_tables : List Nat
  implicit_tables : List Nat
  heap : List Obj
  deriving Repr, Inhabited

/-- Computations on the parser. -/
abbrev M := StateT Parser (Except Exc)

def perr {α} (e : ErrType) : M α := throw (.parserError e)

/-! ### Heap -/

def getObj (k : Nat) : M Obj := do return (← get).heap.getD k (.table [])

def setObj (k : Nat) (o : Obj) : M Unit :=
  modify fun l => { l with heap := l.heap.set k o }

/-- Allocate a new object and return its index. -/
def alloc (o : Obj) : M Nat := do
  let l ← get
  set { l with heap := l.heap ++ [o] }
  return l.heap.length

/-- `typeof(v)`. -/
def typeOf (v : Val) : M JTy := do
  match v with
  | .str _ => return .string
  | .int .i64 _ => return .i64
  | .int .i128 _ => return .i128
  | .int .big _ => return .big
  | .int .u64 _ => return .u64
  | .int .u128 _ => return .u128
  | .float _ => return .f64
  | .bool _ => return .bool
  | .date .. => return .date
  | .time .. => return .time
  | .datetime .. => return .datetime
  | .ref k =>
    match ← getObj k with
    | .table _ => return .dict
    | .array e _ => return .vec e

/-- `get(d, k, nothing)` on the table at index `t`. -/
def dictGet (t : Nat) (k : Str) : M (Option Val) := do
  match ← getObj t with
  | .table kvs => return (kvs.find? (·.1 == k)).map (·.2)
  | .array .. => return none

/-- `d[k] = v` on the table at index `t`. -/
def dictSet (t : Nat) (k : Str) (v : Val) : M Unit := do
  match ← getObj t with
  | .table kvs =>
    if kvs.any (·.1 == k) then
      setObj t (.table (kvs.map fun kv => if kv.1 == k then (k, v) else kv))
    else setObj t (.table (kvs ++ [(k, v)]))
  | .array .. => return ()

/-! ### Parser utilities, `base/toml/parser.jl:413-585` -/

/-- `next_char(l)`, `base/toml/parser.jl:413-425`. -/
def next_char : M Nat := do
  let l ← get
  match iterate l.str l.pos with
  | none =>
    set { l with prevpos := l.pos }
    return EOF
  | some (c, p) =>
    set { l with prevpos := l.pos, pos := p }
    return c

/-- `eat_char(l)`, `base/toml/parser.jl:427-431`. -/
def eat_char : M Nat := do
  let c := (← get).current_char
  let n ← next_char
  modify fun l => { l with current_char := n }
  return c

/-- `peek(l)`, `base/toml/parser.jl:433`. -/
def peek : M Nat := do return (← get).current_char

/-- `accept(l, f)`, `base/toml/parser.jl:437-448`. -/
def accept (f : Nat → Bool) : M Bool := do
  let c ← peek
  if c == EOF then return false
  let ok := f c
  if ok then discard eat_char
  return ok

/-- `accept(l, c::Char)`. -/
def acceptC (c : Char) : M Bool := accept (· == ch c)

/-- `accept_batch(l, f)`, `base/toml/parser.jl:451-457`. -/
def accept_batch (f : Nat → Bool) : Nat → M Bool
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    if ← accept f then
      discard (accept_batch f fuel)
      return true
    return false

/-- `accept_n(l, n, f)`, `base/toml/parser.jl:460-467`. -/
def accept_n (f : Nat → Bool) : Nat → M Bool
  | 0 => return true
  | n + 1 => do
    if !(← accept f) then return false
    accept_n f n

/-- `iswhitespace`, `base/toml/parser.jl:469`. -/
def iswhitespace (c : Nat) : Bool := c == ch ' ' || c == ch '\t'

/-- `isnewline`, `base/toml/parser.jl:470`. -/
def isnewline (c : Nat) : Bool := c == ch '\n' || c == ch '\r'

/-- `isdigit(c::AbstractChar)`: `'0' <= c <= '9'` on raw values. -/
def isdigit (c : Nat) : Bool := ch '0' ≤ c && c ≤ ch '9'

/-- `skip_ws`, `base/toml/parser.jl:472`. -/
def skip_ws (fuel : Nat) : M Bool := accept_batch iswhitespace fuel

/-- `skip_ws_nl_no_comment`, `base/toml/parser.jl:474`. -/
def skip_ws_nl_no_comment (fuel : Nat) : M Bool :=
  accept_batch (fun x => iswhitespace x || isnewline x) fuel

/-- `skip_comment` without comment capture, `base/toml/parser.jl:527-539`. -/
def skip_comment (fuel : Nat) : M Bool := do
  let found ← acceptC '#'
  if found then discard (accept_batch (fun c => !isnewline c) fuel)
  return found

/-- `skip_ws_nl` without comment capture, `base/toml/parser.jl:476-490`;
`skip_ws_nl_toplevel` is the same when `l.comments === nothing`
(`base/toml/parser.jl:493-494`). -/
def skip_ws_nl (fuel : Nat) : Nat → M Bool
  | 0 => throw .outOfFuel
  | k + 1 => do
    let skippedWs ← accept_batch (fun x => iswhitespace x || isnewline x) fuel
    let skippedComment ← skip_comment fuel
    if !skippedWs && !skippedComment then return false
    discard (skip_ws_nl fuel k)
    return true

/-- `skip_ws_comment`, `base/toml/parser.jl:541-544`. -/
def skip_ws_comment (fuel : Nat) : M Bool := do
  discard (skip_ws fuel)
  skip_comment fuel

/-- `set_marker!`, `base/toml/parser.jl:584`. -/
def set_marker : M Unit := modify fun l => { l with marker := l.prevpos }

/-- `take_substring`, `base/toml/parser.jl:585`. -/
def take_substring : M Str := do
  let l ← get
  return slice l.str l.marker (l.prevpos - 1)

/-- A new parser after `startup`, `base/toml/parser.jl:136-175`. The BOM test
compares the value returned by the first `eat_char`, which is the initial
`EOF_CHAR`. -/
def Parser.new (s : Str) (dates : Bool) : Except Exc Parser :=
  let l0 : Parser :=
    { str := s, dates := dates, current_char := EOF, pos := 1, prevpos := 0, marker := 0,
      active_table := 0, dotted_keys := [], chunks := [], inline_tables := [],
      static_arrays := [], defined_tables := [], implicit_tables := [],
      heap := [.table []] }
  let startup : M Unit := do
    let c ← eat_char
    if c == rawOf 0xFEFF then
      discard eat_char
  (startup.run l0).map (·.2)

end JuliaLean.Toml
