import JuliaLean.base.parse
import Lean
import JuliaLean.base.expr
import JuliaLean.base.io
import JuliaLean.base.strings.basic
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.char
import JuliaLean.base.strings.string
import JuliaLean.base.strings.unicode
import JuliaLean.base.show

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



section

/-!
# The TOML lexer with comment capture (`base/toml/parser.jl`)

Model, at master `bbfa0ce4150`, of the parser state and the character-level utilities of
`base/toml/parser.jl` including line/column bookkeeping and comment capture
(`comments !== nothing`), which `JuliaLean.Toml` leaves out; the comment containers
`CommentBlock` and `Comments`; the `Parser` constructors, `startup` and `reinit!`; the
`@try` macro; and `ParserError` with its formatting (`format_error_message_for_err_type`,
`point_to_line`, `showerror`).

Strings are their bytes and characters their raw `UInt32` values, as in `JuliaLean.Toml`
(`Toml.iterate` decodes UTF-8 as `base/strings/string.jl`). The parsed document, needed by
`path_traverses_array`, is a tree of tables, arrays and leaves. Every `while` loop consumes
one unit of fuel per iteration (each iteration eats at least one byte).
-/

namespace JuliaLean.DocsSyntaxCov.TomlLex

open JuliaLean JuliaLean.DocsSyntaxCov
open JuliaLean.Toml (Str ch EOF iterate slice rawOf iswhitespace isnewline ErrType)

/-! ## Comments, lines 30-69 -/

/-- `CommentBlock`: the comment lines above an item and its inline comment. -/
structure CommentBlock where
  above : List Str
  inline : Option Str
  deriving DecidableEq, Repr

/-- `CommentBlock() = CommentBlock(String[], nothing)`, line 45. -/
def CommentBlock.new : CommentBlock := ⟨[], none⟩

/-- A `Dict` as its entries in insertion order (keys are distinct). -/
abbrev Dict (κ α : Type) := List (κ × α)

def dget {κ α : Type} [BEq κ] (d : Dict κ α) (k : κ) : Option α := (d.find? (·.1 == k)).map (·.2)

/-- `d[k] = v`. -/
def dset {κ α : Type} [BEq κ] (d : Dict κ α) (k : κ) (v : α) : Dict κ α :=
  if d.any (·.1 == k) then d.map (fun p => if p.1 == k then (k, v) else p) else d ++ [(k, v)]

/-- `get!(f, d, k)`: the value at `k`, inserting `dflt` first when absent. -/
def dgetBang {κ α : Type} [BEq κ] (d : Dict κ α) (k : κ) (dflt : α) : Dict κ α × α :=
  match dget d k with
  | some v => (d, v)
  | none => (d ++ [(k, dflt)], dflt)

/-- `a == b` on dictionaries: the same keys, with `==` values. -/
def dictEq {κ α : Type} [BEq κ] (eqv : α → α → Bool) (a b : Dict κ α) : Bool :=
  a.length == b.length && a.all fun (k, v) => match dget b k with
    | some w => eqv v w
    | none => false

/-- `Comments`: comment blocks keyed by item path, and floating comments keyed by table path. -/
structure Comments where
  items : Dict (List Str) CommentBlock
  floating : Dict (List Str) (List Str)
  deriving DecidableEq, Repr

/-- `Comments()`, line 60. -/
def Comments.new : Comments := ⟨[], []⟩

/-- `isempty(c::Comments)`, line 62. -/
def Comments.isempty (c : Comments) : Bool := c.items.isEmpty && c.floating.isEmpty

/-- `empty!(c::Comments)`, lines 63-67. -/
def Comments.empty (_ : Comments) : Comments := ⟨[], []⟩

/-- `==(a::CommentBlock, b::CommentBlock)`, line 68. -/
def CommentBlock.eq (a b : CommentBlock) : Bool := a.above == b.above && a.inline == b.inline

/-- `==(a::Comments, b::Comments)`, line 69. -/
def Comments.eq (a b : Comments) : Bool :=
  dictEq CommentBlock.eq a.items b.items && dictEq (· == ·) a.floating b.floating

/-! ## Parser state, lines 75-209 -/

/-- The parsed document, as far as `path_traverses_array` looks at it. -/
inductive TV where
  | dict (kvs : List (Str × TV))
  | vec (xs : List TV)
  | leaf
  deriving Inhabited

/-- The mutable `Parser{Dates}` (lines 75-134). Tables are identified by numbers (the
`IdSet`s hold identities); the root table is `0` and `active_table` is a table identity. -/
structure LP where
  str : Str
  currentChar : Nat
  pos : Int
  prevpos : Int
  column : Int
  line : Int
  marker : Int
  activeTable : Nat
  dottedKeys : List Str
  chunks : List (Int × Int)
  inlineTables : List Nat
  staticArrays : List Nat
  definedTables : List Nat
  implicitTables : List Nat
  root : List (Str × TV)
  filepath : Option Str
  comments : Option Comments
  pendingComments : List Str
  capturedComment : Str
  activeTablePath : List Str
  lastItemPath : Option (List Str)
  inArrayTable : Bool
  deriving Inhabited

/-- `next_char(l)`, lines 413-425: the character read and the new state. -/
def nextChar (l : LP) : Nat × LP :=
  let state := iterate l.str l.pos
  let l := { l with prevpos := l.pos, column := l.column + 1 }
  match state with
  | none => (EOF, l)
  | some (c, pos) =>
    let l := { l with pos := pos }
    if c == ch '\n' then (c, { l with line := l.line + 1, column := 0 }) else (c, l)

/-- `eat_char(l)`, lines 427-431. -/
def eatChar (l : LP) : Nat × LP :=
  let c := l.currentChar
  let (n, l) := nextChar l
  (c, { l with currentChar := n })

/-- `peek(l)`, line 433. -/
def peek (l : LP) : Nat := l.currentChar

/-- The `f::Union{Function, Char}` argument of `accept`. -/
inductive Acc where
  | fn (f : Nat → Bool)
  | char (c : Nat)

/-- Whether `accept` takes the character `c` (`f(c)`, or `c === f`, which compares raw values). -/
def Acc.test : Acc → Nat → Bool
  | .fn g, c => g c
  | .char d, c => c == d

/-- `accept(l, f)`, lines 437-448. -/
def accept (f : Acc) (l : LP) : Bool × LP :=
  let c := peek l
  if c == EOF then (false, l)
  else
    let ok := f.test c
    if ok then (true, (eatChar l).2) else (false, l)

/-- `accept_batch(l, f)`, lines 451-457, with fuel for the `while` loop. -/
def acceptBatch (f : Acc) : Nat → LP → DJ (Bool × LP)
  | 0, _ => .error (.errorException "out of fuel")
  | n + 1, l =>
    let (ok, l) := accept f l
    if ok then do
      let (_, l) ← acceptBatch f n l
      pure (true, l)
    else pure (false, l)

/-- `accept_n(l, n, f)`, lines 460-467. -/
def acceptN (f : Acc) : Nat → LP → Bool × LP
  | 0, l => (true, l)
  | n + 1, l =>
    let (ok, l) := accept f l
    if !ok then (false, l) else acceptN f n l

/-- `skip_ws(l)`, line 472. -/
def skipWs (fuel : Nat) (l : LP) : DJ (Bool × LP) := acceptBatch (.fn iswhitespace) fuel l

/-- `skip_ws_nl_no_comment(l)`, line 474. -/
def skipWsNlNoComment (fuel : Nat) (l : LP) : DJ (Bool × LP) :=
  acceptBatch (.fn fun x => iswhitespace x || isnewline x) fuel l

/-- `skip_comment(l)`, lines 527-539. The captured text is
`SubString(l.str, start:prevind(l.str, l.prevpos))`: the bytes from `start` up to the one
before the look-ahead character. -/
def skipComment (fuel : Nat) (l : LP) : DJ (Bool × LP) := do
  let (found, l) := accept (.char (ch '#')) l
  if found then
    match l.comments with
    | none =>
      let (_, l) ← acceptBatch (.fn fun c => !isnewline c) fuel l
      pure (found, l)
    | some _ =>
      let start := l.prevpos
      let (_, l) ← acceptBatch (.fn fun c => !isnewline c) fuel l
      pure (found, { l with capturedComment := slice l.str start (l.prevpos - 1) })
  else pure (found, l)

/-- `skip_ws_nl(l)`, lines 476-490, with fuel for the `while true` loop. -/
def skipWsNl (fuel : Nat) : Nat → LP → DJ (Bool × LP)
  | 0, _ => .error (.errorException "out of fuel")
  | k + 1, l => do
    let (skippedWs, l) ← acceptBatch (.fn fun x => iswhitespace x || isnewline x) fuel l
    let (skippedComment, l) ← skipComment fuel l
    let l := if skippedComment && l.comments.isSome then
        { l with pendingComments := l.pendingComments ++ [l.capturedComment] } else l
    if !skippedWs && !skippedComment then return (false, l)
    let (_, l) ← skipWsNl fuel k l
    return (true, l)

/-- `skip_ws_comment(l)`, lines 541-544. -/
def skipWsComment (fuel : Nat) (l : LP) : DJ (Bool × LP) := do
  let (_, l) ← skipWs fuel l
  skipComment fuel l

/-- `flush_pending_comments!(l)`, lines 546-555. -/
def flushPendingComments (l : LP) : LP :=
  if l.pendingComments.isEmpty then l
  else
    let l := match l.comments with
      | some c =>
        if !l.inArrayTable then
          let (fl, old) := dgetBang c.floating l.activeTablePath []
          { l with comments := some { c with floating := dset fl l.activeTablePath (old ++ l.pendingComments) } }
        else l
      | none => l
    { l with pendingComments := [] }

/-- `attach_pending_comments!(l, path)`, lines 557-563 (`l.comments::Comments` throws a
`TypeError` without comments). -/
def attachPendingComments (path : List Str) (l : LP) : DJ LP :=
  if l.pendingComments.isEmpty then pure l
  else match l.comments with
    | none => .error .typeError
    | some c =>
      let (items, block) := dgetBang c.items path CommentBlock.new
      let block := { block with above := block.above ++ l.pendingComments }
      pure { l with comments := some { c with items := dset items path block }, pendingComments := [] }

/-- `attach_inline_comment!(l)`, lines 565-571. -/
def attachInlineComment (l : LP) : DJ LP :=
  match l.lastItemPath with
  | none => pure l
  | some path =>
    match l.comments with
    | none => .error .typeError
    | some c =>
      let (items, block) := dgetBang c.items path CommentBlock.new
      pure { l with comments := some { c with items := dset items path { block with inline := some l.capturedComment } } }

/-- The inner `while true` loop of `skip_ws_nl_toplevel` (lines 499-514): whitespace and
newlines, counting `'\n'`s and flushing at the second. Returns progress, the newline count and
the state. -/
def toplevelWs : Nat → Bool → Int → LP → DJ (Bool × Int × LP)
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | k + 1, progress, nlines, l =>
    let c := peek l
    if iswhitespace c then toplevelWs k true nlines (eatChar l).2
    else if isnewline c then
      let (nlines, l) := if c == ch '\n' then
          let n := nlines + 1
          (n, if n == 2 then flushPendingComments l else l)
        else (nlines, l)
      toplevelWs k true nlines (eatChar l).2
    else pure (progress, nlines, l)

/-- The outer `while true` loop of `skip_ws_nl_toplevel`, lines 497-522. -/
def toplevelLoop (fuel : Nat) : Nat → Int → LP → DJ (Bool × LP)
  | 0, _, _ => .error (.errorException "out of fuel")
  | k + 1, nlines, l => do
    let (progress, nlines, l) ← toplevelWs fuel false nlines l
    let (sc, l) ← skipComment fuel l
    let (progress, nlines, l) := if sc then
        (true, (0 : Int), { l with pendingComments := l.pendingComments ++ [l.capturedComment] })
      else (progress, nlines, l)
    if !progress then return (false, l)
    let (_, l) ← toplevelLoop fuel k nlines l
    return (true, l)

/-- `skip_ws_nl_toplevel(l)`, lines 493-524. -/
def skipWsNlToplevel (fuel : Nat) (l : LP) : DJ (Bool × LP) :=
  if l.comments.isNone then skipWsNl fuel fuel l else toplevelLoop fuel fuel 0 l

/-- `path_traverses_array(l, keys)`, lines 573-582, from the table `d` (initially `l.root`). -/
def pathTraversesArray : List (Str × TV) → List Str → Bool
  | _, [] => false
  | d, k :: ks =>
    match (d.find? (·.1 == k)).map (·.2) with
    | some (TV.vec _) => true
    | some (TV.dict kvs) => pathTraversesArray kvs ks
    | _ => false

/-- `set_marker!(l)`, line 584. -/
def setMarker (l : LP) : LP := { l with marker := l.prevpos }

/-- `take_substring(l)`, line 585. -/
def takeSubstring (l : LP) : Str := slice l.str l.marker (l.prevpos - 1)

/-- `startup(l)`, lines 167-175. -/
def startup (l : LP) : LP :=
  let (c, l) := eatChar l
  if c == rawOf 0xFEFF then (eatChar { l with column := l.column - 1 }).2 else l

/-- The fields `Parser{Dates}(str; filepath, comments)` sets before `startup` (lines 136-165),
with the passed `comments` emptied. -/
def freshState (str : Str) (filepath : Option Str) (comments : Option Comments) : LP :=
  { str := str, currentChar := EOF, pos := 1, prevpos := 0, column := 0, line := 1, marker := 0,
    activeTable := 0, dottedKeys := [], chunks := [], inlineTables := [], staticArrays := [],
    definedTables := [], implicitTables := [], root := [], filepath := filepath,
    comments := comments.map Comments.empty, pendingComments := [], capturedComment := [],
    activeTablePath := [], lastItemPath := none, inArrayTable := false }

/-- `Parser{Dates}(str; filepath, comments)`, lines 136-165. -/
def parserNew (str : Str) (filepath : Option Str := none) (comments : Option Comments := none) : LP :=
  startup (freshState str filepath comments)

/-- `Parser{Dates}()`, line 177. -/
def parserEmpty : LP := parserNew []

/-- `Parser{Dates}(io::IO)`, line 178: `read(io, String)` is the remaining bytes. -/
def parserIO (bytes : Str) : LP := parserNew bytes

/-- `reinit!(p, str; filepath, comments)`, lines 182-209. -/
def reinit (p : LP) (str : Str) (filepath : Option Str := none) (comments : Option Comments := none) : LP :=
  let p : LP := { p with
    str := str
    currentChar := EOF
    pos := 1
    prevpos := 0
    column := 0
    line := 1
    marker := 0
    root := []
    activeTable := 0
    dottedKeys := []
    chunks := []
    inlineTables := []
    staticArrays := []
    definedTables := []
    implicitTables := []
    filepath := filepath }
  let p : LP := { p with
    comments := comments.map Comments.empty
    pendingComments := []
    capturedComment := []
    activeTablePath := []
    lastItemPath := none
    inArrayTable := false }
  startup p

/-- `copyto_typed!(a, b)`, lines 879-884: `a[i] = b[i]::T` for each index of `b`. -/
def copytoTyped {α : Type} (isT : α → Bool) (a b : List α) : DJ (List α) :=
  go 0 a b
where
  go (i : Nat) (a : List α) : List α → DJ (List α)
    | [] => pure a
    | x :: xs =>
      if !isT x then .error .typeError
      else if i < a.length then go (i + 1) (a.set i x) xs
      else .error .boundsError

/-! ## `@try`, lines 219-225 -/

/-- The expansion of `@try expr`: `quote v = $(esc(expr)); v isa ParserError && return v; v end`
(line numbers dropped). -/
def tryMacro (e : JV) : JV :=
  .expr "block" [.expr "=" [.sym "v", esc e],
    .expr "&&" [call (.sym "isa") [.sym "v", .sym "ParserError"], .expr "return" [.sym "v"]],
    .sym "v"]

/-- What the expansion does with the value of `expr` inside a function returning
`Err{T}`: a `ParserError` returns from the function, any other value is the result. -/
def tryValue {α β : Type} (v : Except ErrType α) (k : α → Except ErrType β) : Except ErrType β :=
  match v with
  | .error e => .error e
  | .ok x => k x

/-! ## Errors, lines 228-406 -/

/-- `err_message`, lines 285-319. -/
def errMessage : ErrType → String
  | .ErrTrailingCommaInlineTable => "trailing comma not allowed in inline table"
  | .ErrExpectedCommaBetweenItemsArray => "expected comma between items in array"
  | .ErrExpectedCommaBetweenItemsInlineTable => "expected comma between items in inline table"
  | .ErrExpectedEndArrayOfTable => "expected array of table to end with ']]'"
  | .ErrInvalidBareKeyCharacter => "invalid bare key character"
  | .ErrRedefineTableArray => "tried to redefine an existing table as an array"
  | .ErrDuplicatedKey => "key already defined"
  | .ErrKeyAlreadyHasValue => "key already has a value"
  | .ErrEmptyBareKey => "bare key cannot be empty"
  | .ErrExpectedNewLineKeyValue => "expected newline after key value pair"
  | .ErrNewLineInString => "newline character in single quoted string"
  | .ErrUnexpectedEndString => "string literal ended unexpectedly"
  | .ErrExpectedEndOfTable => "expected end of table ']'"
  | .ErrAddKeyToInlineTable => "tried to add a new key to an inline table"
  | .ErrInlineTableRedefine => "inline table overwrote key from other table"
  | .ErrArrayTreatedAsDictionary => "tried to add a key to an array"
  | .ErrAddArrayToStaticArray => "tried to append to a statically defined array"
  | .ErrGenericValueError => "failed to parse value"
  | .ErrLeadingZeroNotAllowedInteger => "leading zero in integer not allowed"
  | .ErrUnderscoreNotSurroundedByDigits => "underscore is not surrounded by digits"
  | .ErrUnexpectedStartOfValue => "unexpected start of value"
  | .ErrOffsetDateNotSupported => "offset date-time is not supported"
  | .ErrParsingDateTime => "parsing date/time value failed"
  | .ErrTrailingUnderscoreNumber => "trailing underscore in number"
  | .ErrLeadingDot => "floats require a leading zero"
  | .ErrExpectedEqualAfterKey => "expected equal sign after key"
  | .ErrNoTrailingDigitAfterDot => "expected digit after dot"
  | .ErrOverflowError => "overflowed when parsing integer"
  | .ErrInvalidUnicodeScalar => "invalid unicode scalar"
  | .ErrInvalidEscapeCharacter => "invalid escape character"
  | .ErrMultilineStringAsKey => "multiline strings are not allowed as keys"
  | .ErrUnexpectedEofExpectedValue => "unexpected end of file, expected a value"
  | .ErrSignInNonBase10Number => "number not in base 10 is not allowed to have a sign"

/-- `ParserError`, lines 323-337. -/
structure ParserError where
  type : ErrType
  data : Option Nat
  str : Option Str
  filepath : Option Str
  line : Option Int
  column : Option Int
  pos : Option Int
  hasTable : Bool
  deriving DecidableEq

/-- `ParserError(type, data)`, line 340. -/
def ParserError.mk2 (type : ErrType) (data : Option Nat) : ParserError :=
  ⟨type, data, none, none, none, none, none, false⟩

/-- `ParserError(type)`, line 341. -/
def ParserError.mk1 (type : ErrType) : ParserError := ParserError.mk2 type none

/-- `format_error_message_for_err_type(error)`, lines 350-357; `escape` is
`escape_string(string(c))`. -/
def formatErrorMessage (escape : Nat → Str) (e : ParserError) : DJ Str :=
  let msg := (errMessage e.type).toUTF8.toList.map (·.toNat)
  if e.type == .ErrInvalidBareKeyCharacter then
    match e.data with
    | none => .error .typeError
    | some c => pure (msg ++ (bytes% ": '") ++ escape c ++ (bytes% "'"))
  else pure msg

/-- `findprev('\n', s, k)`: the last index `≤ k` holding a newline byte. -/
def findprevNewline (s : Str) (k : Int) : Option Int :=
  ((List.range k.toNat).reverse.find? fun j => s.getD j 0 == 10).map (fun j => (j : Int) + 1)

/-- `point_to_line(str, a, b, context)`, lines 365-385, with `caret` the styled `"^"`. Returns
the line containing `a` and the marker line. -/
def pointToLine (caret : Str) (s : Str) (a b : Int) : DJ (Str × Str) := do
  if !(b ≥ a) then throw .assertionError
  let a ← thisind s a
  let b ← thisind s b
  let p ← prevind s a
  let pos := (findprevNewline s p).getD 0 + 1
  go (s.length + 2) pos [] []
where
  go : Nat → Int → Str → Str → DJ (Str × Str)
    | 0, _, o1, o2 => pure (o1, o2)
    | k + 1, pos, o1, o2 =>
      let o2 := o2 ++ (if a ≤ pos && pos ≤ b then caret else [32])
      match iterate s pos with
      | none => pure (o1, o2)
      | some (c, pos) =>
        if c == ch '\n' then pure (o1, o2)
        else go k pos (o1 ++ charBytes c) o2

/-- The styling `printstyled` adds: identity for an `IO` without colour. -/
structure Style where
  error : Str → Str
  bold : Str → Str
  caret : Str

/-- `print(io, x)` for an `Int` or `nothing`. -/
def showOptInt (showInt : Int → Str) : Option Int → Str
  | some i => showInt i
  | none => bytes% "nothing"

/-- `showerror(io, err::ParserError)`, lines 387-406 (the `else` branch of the version
check). -/
def showerror (st : Style) (showInt : Int → Str) (escape : Nat → Str) (err : ParserError) : DJ Str := do
  let head := st.error (bytes% "TOML Parser error:\n")
  let f := err.filepath.getD (bytes% "none")
  let loc := st.bold (f ++ [58] ++ showOptInt showInt err.line ++ [58] ++ showOptInt showInt err.column)
  let msg ← formatErrorMessage escape err
  let pos ← match err.pos with
    | some p => pure p
    | none => throw .typeError
  let pos := if err.type == .ErrUnexpectedEofExpectedValue then pos + 1 else pos
  let s ← match err.str with
    | some s => pure s
    | none => throw .typeError
  let (str1, err1) ← pointToLine st.caret s pos pos
  pure (head ++ loc ++ st.error (bytes% " error: ") ++ msg ++ [10] ++ [32, 32] ++ str1 ++ [10] ++ [32, 32] ++ err1)

/-- `DateTime(y, m, d, h, mi, s, ms) = DateTime(Date(y,m,d), Time(h, mi, s, ms))`, lines 23-24. -/
structure Date where
  year : Int
  month : Int
  day : Int
  deriving DecidableEq

structure Time where
  hour : Int
  minute : Int
  second : Int
  ms : Int
  deriving DecidableEq

structure DateTime where
  date : Date
  time : Time
  deriving DecidableEq

def dateTime7 (y m d h mi s ms : Int) : DateTime := ⟨⟨y, m, d⟩, ⟨h, mi, s, ms⟩⟩

end JuliaLean.DocsSyntaxCov.TomlLex

end


/-!
# Model of `base/toml/parser.jl`

Typed model of `Base.TOML`'s parser at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit
platform. Each method is a Lean definition preceded by its verbatim source; its body follows the
Julia body call by call.

* The parser is a mutable object; methods run in `PM o`, a state monad over `Parser`. Julia
  exceptions are `Thrown` errors, and an outer `none` is non-termination (loops over the input are
  `partial_fixpoint` definitions).
* A `ParserError` returned by a method is an `ExceptT ParserError` error: `@try f(l)` is `← f o`,
  `return ParserError(…)` is `throw`. Where Julia uses a returned `ParserError` as a value without
  `@try`, the model observes it with `observe`.
* `TOMLDict`s and `Vector`s are mutable objects compared by identity (`IdSet`s, aliasing between
  `root` and `active_table`). They live in the parser's heaps `tables` and `vectors` and are
  referred to by index; `Val` is a value of type `Any`.
* `Dict{String,Any}` and the comment dictionaries are `DictOps` parameters (their hashing is not
  modelled here). Calls into other Base files and the user's `Dates` module (`Base.parse`,
  `Base.tryparse(Float64, …)`, `unescape_string`, `SubString`, …) are parameters of `Ops`.
  String iteration uses the `base/strings/string.jl` model and `isdigit` the
  `base/strings/unicode.jl` model.
-/

namespace JuliaLean.base.toml.parser

open JuliaLean

abbrev Bytes := List UInt8
abbrev JInt64 := JInt .i64
abbrev I32 := JInt .i32
abbrev JChar := JuliaLean.base.char.JChar

def i64 (z : Int) : JInt64 := JInt.wrap .i64 z

/-- Storage pattern of the Julia `Char` literal `c`: its UTF-8 bytes, left-aligned. -/
def jc (c : Char) : JChar :=
  let bs := (String.singleton c).toUTF8.toList
  (bs.zipIdx.foldl (fun (u : UInt32) (b, k) => u ||| (b.toUInt32 <<< (24 - 8 * k).toUInt32)) 0)

/-- Bytes of a `String` literal. -/
def lit (s : String) : Bytes := s.toUTF8.toList

/-- `isdigit(c)` (`base/strings/unicode.jl`). -/
def isdigit (c : JChar) : Bool := JuliaLean.base.strings.unicode.isdigit JuliaLean.base.strings.unicode.charOps c

/-- `iterate(s::String, i)` (`base/strings/string.jl`) on the bytes of `s`. -/
def iterateStr (s : Bytes) (i : JInt64) : Option (JChar × JInt64) :=
  JuliaLean.base.strings.string.iterateString (fun _ => JuliaLean.Strings.ix 1)
    (fun s => JuliaLean.Strings.ix s.length) (fun s i => s.getD (i.val.toNat - 1) 0)
    (JuliaLean.base.strings.string.between (· ≤ ·)) s i

-- UNTRANSLATED
-- `using Base: IdSet` import statement; no method
-- Source: base/toml/parser.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- using Base: IdSet
-- 
-- /Source

/--
Julia source: base/toml/parser.jl:5-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# we parse DateTime into these internal structs,
# unless a different DateTime library is passed to the Parser constructor
# note that these do not do any argument checking
struct Date
    year::Int
    month::Int
    day::Int
end
struct Time
    hour::Int
    minute::Int
    second::Int
    ms::Int
end
struct DateTime
    date::Date
    time::Time
end
```
-/
structure Date where
  year : JInt64
  month : JInt64
  day : JInt64

structure Time where
  hour : JInt64
  minute : JInt64
  second : JInt64
  ms : JInt64

structure DateTime where
  date : Date
  time : Time

/--
Julia source: base/toml/parser.jl:23-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DateTime(y, m, d, h, mi, s, ms) =
    DateTime(Date(y,m,d), Time(h, mi, s, ms))

```
-/
def DateTime_7 (y m d h mi s ms : JInt64) : DateTime := ⟨⟨y, m, d⟩, ⟨h, mi, s, ms⟩⟩

/--
Julia source: base/toml/parser.jl:26-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const EOF_CHAR = typemax(Char)

```
-/
def EOF_CHAR : JChar := JuliaLean.base.char.typemax_Char 0xffffffff

/--
Julia source: base/toml/parser.jl:28-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const TOMLDict  = Dict{String, Any}

```
-/
-- A `TOMLDict` is referred to by its index in the parser's `tables` heap.
abbrev TOMLDictRef := Nat

/--
Julia source: base/toml/parser.jl:30-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
############
# Comments #
############

# The empty path identifies the root table.
# TODO: Formatting choices (e.g. which tables print inline, indentation) could
# be retained for full round-tripping the same way as comments: captured into a
# sibling side-channel keyed by these item paths and passed back to `print`.
const CommentPath = Vector{String}

```
-/
abbrev CommentPath := List Bytes

/--
Julia source: base/toml/parser.jl:40-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Text excludes `#`; `nothing` means no inline comment and `""` a bare `#`.
mutable struct CommentBlock
    above::Vector{String}
    inline::Union{String, Nothing}
end
```
-/
structure CommentBlock where
  above : List Bytes
  inline : Option Bytes

/--
Julia source: base/toml/parser.jl:45-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
CommentBlock() = CommentBlock(String[], nothing)

```
-/
def CommentBlock_new : CommentBlock := ⟨[], none⟩

/-- Operations of a `Dict{K,V}` (`base/dict.jl`) used by the parser, on a dictionary value `D`;
the parser holds the only reference to each dictionary, so mutation is replacement. -/
structure DictOps (K V D : Type) where
  /-- `Dict{K,V}()`. -/
  empty : D
  /-- The value stored under `k`, if any (`get`, `haskey`). -/
  get : D → K → Option V
  /-- `d[k] = v`. -/
  set : D → K → V → D
  isempty : D → Bool
  /-- `empty!(d)`. -/
  emptyBang : D → D
  /-- `a == b`, given `==` on values. -/
  eq : (V → V → Bool) → D → D → Bool
  /-- The pairs of `d` in iteration order (`for (k, v) in d`). -/
  pairs : D → List (K × V)
  /-- `delete!(d, k)`. -/
  delete : D → K → D

/--
Julia source: base/toml/parser.jl:47-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Comments()

A container for comments captured while parsing a TOML document. Pass it via
the `comments` keyword argument to the parsing functions to populate it, and
via the `comments` keyword argument to the printing functions to write the
comments back out. See the TOML stdlib documentation for the rules of how
comments are associated with items of the document.
"""
struct Comments
    items::Dict{CommentPath, CommentBlock}
    floating::Dict{CommentPath, Vector{String}}
end
```
-/
structure Comments (CI CF : Type) where
  items : CI
  floating : CF

/--
Julia source: base/toml/parser.jl:60-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Comments() = Comments(Dict{CommentPath, CommentBlock}(), Dict{CommentPath, Vector{String}}())

```
-/
def Comments_new {CI CF : Type} (ci : DictOps CommentPath CommentBlock CI) (cf : DictOps CommentPath (List Bytes) CF) :
    Comments CI CF :=
  ⟨ci.empty, cf.empty⟩

/--
Julia source: base/toml/parser.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isempty(c::Comments) = isempty(c.items) && isempty(c.floating)
```
-/
def isempty_Comments {CI CF : Type} (ci : DictOps CommentPath CommentBlock CI)
    (cf : DictOps CommentPath (List Bytes) CF) (c : Comments CI CF) : Bool :=
  ci.isempty c.items && cf.isempty c.floating

/--
Julia source: base/toml/parser.jl:63-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.empty!(c::Comments)
    empty!(c.items)
    empty!(c.floating)
    return c
end
```
-/
def emptyBang_Comments {CI CF : Type} (ci : DictOps CommentPath CommentBlock CI)
    (cf : DictOps CommentPath (List Bytes) CF) (c : Comments CI CF) : Comments CI CF :=
  let c := { c with items := ci.emptyBang c.items }
  let c := { c with floating := cf.emptyBang c.floating }
  c

/--
Julia source: base/toml/parser.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:(==)(a::CommentBlock, b::CommentBlock) = a.above == b.above && a.inline == b.inline
```
-/
def eq_CommentBlock (a b : CommentBlock) : Bool := a.above == b.above && a.inline == b.inline

/--
Julia source: base/toml/parser.jl:69-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:(==)(a::Comments, b::Comments) = a.items == b.items && a.floating == b.floating

```
-/
def eq_Comments {CI CF : Type} (ci : DictOps CommentPath CommentBlock CI)
    (cf : DictOps CommentPath (List Bytes) CF) (a b : Comments CI CF) : Bool :=
  ci.eq eq_CommentBlock a.items b.items && cf.eq (· == ·) a.floating b.floating

/-- Element types of the `Vector`s the parser creates. -/
inductive ElType where
  | any | string | bool | int64 | uint64 | float64
  deriving DecidableEq, Repr

/-- A value of type `Any` stored in a `TOMLDict` or `Vector{Any}`; `dates` is a value of the
user's `Dates` module, `table` and `vector` are references into the parser's heaps. -/
inductive Val (X : Type) where
  | str (s : Bytes)
  | bool (b : Bool)
  | int64 (x : JInt .i64)
  | uint64 (x : JInt .u64)
  | int128 (x : JInt .i128)
  | uint128 (x : JInt .u128)
  | bigint (x : Int)
  | float64 (x : JuliaLean.base.float.FV .f64)
  | date (d : Date)
  | time (t : Time)
  | datetime (d : DateTime)
  | dates (x : X)
  | table (r : TOMLDictRef)
  | vector (r : Nat)

/-- A `Vector` object: its element type and elements. -/
structure Vec (X : Type) where
  eltype : ElType
  elems : List (Val X)

/-- Julia types of `Val`s (`typeof`), with `Union{}` and `Any` for the `T` of `parse_array`. -/
inductive VType (Y : Type) where
  | string | bool | int64 | uint64 | int128 | uint128 | bigint | float64 | date | time | datetime
  | dates (y : Y)
  | table
  | vector (e : ElType)
  | bottom
  | any

/-- `===` on types. -/
def VType.eq {Y : Type} (yeq : Y → Y → Bool) : VType Y → VType Y → Bool
  | .string, .string | .bool, .bool | .int64, .int64 | .uint64, .uint64 | .int128, .int128
  | .uint128, .uint128 | .bigint, .bigint | .float64, .float64 | .date, .date | .time, .time
  | .datetime, .datetime | .table, .table | .bottom, .bottom | .any, .any => true
  | .dates a, .dates b => yeq a b
  | .vector a, .vector b => a == b
  | _, _ => false

-- UNTRANSLATED
-- the `@try` macro; `@try f(l)` is a bind in the `ExceptT ParserError` layer of `PM`
-- Source: base/toml/parser.jl:211-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ##########
-- # Errors #
-- ##########
-- 
-- # Many functions return a ParserError. We want this to bubble up
-- # all the way and have this error be returned to the user
-- # if the parse is called with `raise=false`. This macro
-- # makes that easier
-- @eval macro $(:var"try")(expr)
--     return quote
--         v = $(esc(expr))
--         v isa ParserError && return v
--         v
--     end
-- end
-- 
-- /Source

/--
Julia source: base/toml/parser.jl:227-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: Check all of these are used
@enum ErrorType begin

    # Toplevel #
    ############
    ErrRedefineTableArray
    ErrExpectedNewLineKeyValue
    ErrAddKeyToInlineTable
    ErrAddArrayToStaticArray
    ErrArrayTreatedAsDictionary
    ErrExpectedEndOfTable
    ErrExpectedEndArrayOfTable

    # Keys #
    ########
    ErrExpectedEqualAfterKey
    # Check, are these the same?
    ErrDuplicatedKey
    ErrKeyAlreadyHasValue
    ErrInvalidBareKeyCharacter
    ErrEmptyBareKey

    # Values #
    ##########
    ErrUnexpectedEofExpectedValue
    ErrUnexpectedStartOfValue
    ErrGenericValueError

    # Arrays
    ErrExpectedCommaBetweenItemsArray

    # Inline tables
    ErrExpectedCommaBetweenItemsInlineTable
    ErrTrailingCommaInlineTable
    ErrInlineTableRedefine

    # Numbers
    ErrUnderscoreNotSurroundedByDigits
    ErrLeadingZeroNotAllowedInteger
    ErrOverflowError
    ErrLeadingDot
    ErrNoTrailingDigitAfterDot
    ErrTrailingUnderscoreNumber
    ErrSignInNonBase10Number

    # DateTime
    ErrParsingDateTime
    ErrOffsetDateNotSupported

    # Strings
    ErrNewLineInString
    ErrUnexpectedEndString
    ErrInvalidEscapeCharacter
    ErrInvalidUnicodeScalar
    ErrMultilineStringAsKey
end

```
-/
inductive ErrorType where
  -- Toplevel
  | ErrRedefineTableArray
  | ErrExpectedNewLineKeyValue
  | ErrAddKeyToInlineTable
  | ErrAddArrayToStaticArray
  | ErrArrayTreatedAsDictionary
  | ErrExpectedEndOfTable
  | ErrExpectedEndArrayOfTable
  -- Keys
  | ErrExpectedEqualAfterKey
  | ErrDuplicatedKey
  | ErrKeyAlreadyHasValue
  | ErrInvalidBareKeyCharacter
  | ErrEmptyBareKey
  -- Values
  | ErrUnexpectedEofExpectedValue
  | ErrUnexpectedStartOfValue
  | ErrGenericValueError
  -- Arrays
  | ErrExpectedCommaBetweenItemsArray
  -- Inline tables
  | ErrExpectedCommaBetweenItemsInlineTable
  | ErrTrailingCommaInlineTable
  | ErrInlineTableRedefine
  -- Numbers
  | ErrUnderscoreNotSurroundedByDigits
  | ErrLeadingZeroNotAllowedInteger
  | ErrOverflowError
  | ErrLeadingDot
  | ErrNoTrailingDigitAfterDot
  | ErrTrailingUnderscoreNumber
  | ErrSignInNonBase10Number
  -- DateTime
  | ErrParsingDateTime
  | ErrOffsetDateNotSupported
  -- Strings
  | ErrNewLineInString
  | ErrUnexpectedEndString
  | ErrInvalidEscapeCharacter
  | ErrInvalidUnicodeScalar
  | ErrMultilineStringAsKey
  deriving DecidableEq, Repr

/--
Julia source: base/toml/parser.jl:284-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const err_message = Dict(
    ErrTrailingCommaInlineTable             => "trailing comma not allowed in inline table",
    ErrExpectedCommaBetweenItemsArray       => "expected comma between items in array",
    ErrExpectedCommaBetweenItemsInlineTable => "expected comma between items in inline table",
    ErrExpectedEndArrayOfTable              => "expected array of table to end with ']]'",
    ErrInvalidBareKeyCharacter              => "invalid bare key character",
    ErrRedefineTableArray                   => "tried to redefine an existing table as an array",
    ErrDuplicatedKey                        => "key already defined",
    ErrKeyAlreadyHasValue                   => "key already has a value",
    ErrEmptyBareKey                         => "bare key cannot be empty",
    ErrExpectedNewLineKeyValue              => "expected newline after key value pair",
    ErrNewLineInString                      => "newline character in single quoted string",
    ErrUnexpectedEndString                  => "string literal ended unexpectedly",
    ErrExpectedEndOfTable                   => "expected end of table ']'",
    ErrAddKeyToInlineTable                  => "tried to add a new key to an inline table",
    ErrInlineTableRedefine                  => "inline table overwrote key from other table",
    ErrArrayTreatedAsDictionary             => "tried to add a key to an array",
    ErrAddArrayToStaticArray                => "tried to append to a statically defined array",
    ErrGenericValueError                    => "failed to parse value",
    ErrLeadingZeroNotAllowedInteger         => "leading zero in integer not allowed",
    ErrUnderscoreNotSurroundedByDigits      => "underscore is not surrounded by digits",
    ErrUnexpectedStartOfValue               => "unexpected start of value",
    ErrOffsetDateNotSupported               => "offset date-time is not supported",
    ErrParsingDateTime                      => "parsing date/time value failed",
    ErrTrailingUnderscoreNumber             => "trailing underscore in number",
    ErrLeadingDot                           => "floats require a leading zero",
    ErrExpectedEqualAfterKey                => "expected equal sign after key",
    ErrNoTrailingDigitAfterDot              => "expected digit after dot",
    ErrOverflowError                        => "overflowed when parsing integer",
    ErrInvalidUnicodeScalar                 => "invalid unicode scalar",
    ErrInvalidEscapeCharacter               => "invalid escape character",
    ErrMultilineStringAsKey                 => "multiline strings are not allowed as keys",
    ErrUnexpectedEofExpectedValue           => "unexpected end of file, expected a value",
    ErrSignInNonBase10Number                => "number not in base 10 is not allowed to have a sign",
)

```
-/
-- The constant `Dict` has a key for every `ErrorType`, so `err_message[t]` is total.
def err_message : ErrorType → String
  | .ErrTrailingCommaInlineTable => "trailing comma not allowed in inline table"
  | .ErrExpectedCommaBetweenItemsArray => "expected comma between items in array"
  | .ErrExpectedCommaBetweenItemsInlineTable => "expected comma between items in inline table"
  | .ErrExpectedEndArrayOfTable => "expected array of table to end with ']]'"
  | .ErrInvalidBareKeyCharacter => "invalid bare key character"
  | .ErrRedefineTableArray => "tried to redefine an existing table as an array"
  | .ErrDuplicatedKey => "key already defined"
  | .ErrKeyAlreadyHasValue => "key already has a value"
  | .ErrEmptyBareKey => "bare key cannot be empty"
  | .ErrExpectedNewLineKeyValue => "expected newline after key value pair"
  | .ErrNewLineInString => "newline character in single quoted string"
  | .ErrUnexpectedEndString => "string literal ended unexpectedly"
  | .ErrExpectedEndOfTable => "expected end of table ']'"
  | .ErrAddKeyToInlineTable => "tried to add a new key to an inline table"
  | .ErrInlineTableRedefine => "inline table overwrote key from other table"
  | .ErrArrayTreatedAsDictionary => "tried to add a key to an array"
  | .ErrAddArrayToStaticArray => "tried to append to a statically defined array"
  | .ErrGenericValueError => "failed to parse value"
  | .ErrLeadingZeroNotAllowedInteger => "leading zero in integer not allowed"
  | .ErrUnderscoreNotSurroundedByDigits => "underscore is not surrounded by digits"
  | .ErrUnexpectedStartOfValue => "unexpected start of value"
  | .ErrOffsetDateNotSupported => "offset date-time is not supported"
  | .ErrParsingDateTime => "parsing date/time value failed"
  | .ErrTrailingUnderscoreNumber => "trailing underscore in number"
  | .ErrLeadingDot => "floats require a leading zero"
  | .ErrExpectedEqualAfterKey => "expected equal sign after key"
  | .ErrNoTrailingDigitAfterDot => "expected digit after dot"
  | .ErrOverflowError => "overflowed when parsing integer"
  | .ErrInvalidUnicodeScalar => "invalid unicode scalar"
  | .ErrInvalidEscapeCharacter => "invalid escape character"
  | .ErrMultilineStringAsKey => "multiline strings are not allowed as keys"
  | .ErrUnexpectedEofExpectedValue => "unexpected end of file, expected a value"
  | .ErrSignInNonBase10Number => "number not in base 10 is not allowed to have a sign"

-- UNTRANSLATED
-- load-time `@assert` that every `ErrorType` has a message; `err_message` above is total
-- Source: base/toml/parser.jl:320-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for err in instances(ErrorType)
--     @assert haskey(err_message, err) "$err does not have an error message"
-- end
-- 
-- /Source

/--
Julia source: base/toml/parser.jl:324-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct ParserError <: Exception
    type::ErrorType

    # Data to store at the
    # call site to be used when formatting
    # the error
    data::Union{Char, Nothing}

    # These are filled in before returning from parse function
    str       ::Union{String,   Nothing}
    filepath  ::Union{String,   Nothing}
    line      ::Union{Int,      Nothing}
    column    ::Union{Int,      Nothing}
    pos       ::Union{Int,      Nothing} # position of parser when
    table     ::Union{TOMLDict, Nothing} # result parsed until error
end
```
-/
structure ParserError where
  type : ErrorType
  data : Option JChar
  str : Option Bytes
  filepath : Option Bytes
  line : Option JInt64
  column : Option JInt64
  pos : Option JInt64
  table : Option TOMLDictRef

/--
Julia source: base/toml/parser.jl:340-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ParserError(type, data) = ParserError(type, data, nothing, nothing, nothing, nothing, nothing, nothing)
ParserError(type) = ParserError(type, nothing)
```
-/
def ParserError_2 (type : ErrorType) (data : Option JChar) : ParserError :=
  ⟨type, data, none, none, none, none, none, none⟩
def ParserError_1 (type : ErrorType) : ParserError := ParserError_2 type none

/--
Julia source: base/toml/parser.jl:342-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Defining these below can be useful when debugging code that erroneously returns a
# ParserError because you get a stacktrace to where the ParserError was created
#ParserError(type) = error(type)
#ParserError(type, data) = error(type, data)

# Many functions return either a T or a ParserError
const Err{T} = Union{T, ParserError}

```
-/
-- A method returning `Err{T}` is a `PM o T` whose `ParserError`s are `ExceptT` errors.
abbrev Err (α : Type) := Except ParserError α

/-- Exceptions thrown (not returned) by the parser: Julia errors, failed type assertions,
`error(msg)`, a thrown `ParserError` (`parse`), and exceptions of the `Ops` callees. -/
inductive Thrown (E : Type) where
  | jl (e : JlError)
  | typeError
  | errorException (msg : String)
  | parserError (e : ParserError)
  | ext (e : E)
/--
Base `Enums.jl:17`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeBaseType : IntTy := .i32

/--
Base `Enums.jl:221-224`; `membershiptest` is `Enums.jl:79-87`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeFromInteger {I E : Type}
    (atLeastZero : I32 → I → Bool) (atMostThirtyTwo : I → I32 → Bool)
    (convert : I → Except (Thrown E) I32) (showInteger : I → String) (x : I) :
    Except (Thrown E) ErrorType :=
  if !atLeastZero (JInt.lit .i32 0) x then
    .error (.jl (.argumentError ("invalid value for Enum ErrorType: " ++ showInteger x)))
  else if !atMostThirtyTwo x (JInt.lit .i32 32) then
    .error (.jl (.argumentError ("invalid value for Enum ErrorType: " ++ showInteger x)))
  else do
    let code ← convert x
    match code.val with
    | 0 => pure .ErrRedefineTableArray
    | 1 => pure .ErrExpectedNewLineKeyValue
    | 2 => pure .ErrAddKeyToInlineTable
    | 3 => pure .ErrAddArrayToStaticArray
    | 4 => pure .ErrArrayTreatedAsDictionary
    | 5 => pure .ErrExpectedEndOfTable
    | 6 => pure .ErrExpectedEndArrayOfTable
    | 7 => pure .ErrExpectedEqualAfterKey
    | 8 => pure .ErrDuplicatedKey
    | 9 => pure .ErrKeyAlreadyHasValue
    | 10 => pure .ErrInvalidBareKeyCharacter
    | 11 => pure .ErrEmptyBareKey
    | 12 => pure .ErrUnexpectedEofExpectedValue
    | 13 => pure .ErrUnexpectedStartOfValue
    | 14 => pure .ErrGenericValueError
    | 15 => pure .ErrExpectedCommaBetweenItemsArray
    | 16 => pure .ErrExpectedCommaBetweenItemsInlineTable
    | 17 => pure .ErrTrailingCommaInlineTable
    | 18 => pure .ErrInlineTableRedefine
    | 19 => pure .ErrUnderscoreNotSurroundedByDigits
    | 20 => pure .ErrLeadingZeroNotAllowedInteger
    | 21 => pure .ErrOverflowError
    | 22 => pure .ErrLeadingDot
    | 23 => pure .ErrNoTrailingDigitAfterDot
    | 24 => pure .ErrTrailingUnderscoreNumber
    | 25 => pure .ErrSignInNonBase10Number
    | 26 => pure .ErrParsingDateTime
    | 27 => pure .ErrOffsetDateNotSupported
    | 28 => pure .ErrNewLineInString
    | 29 => pure .ErrUnexpectedEndString
    | 30 => pure .ErrInvalidEscapeCharacter
    | 31 => pure .ErrInvalidUnicodeScalar
    | 32 => pure .ErrMultilineStringAsKey
    | _ => .error (.jl (.argumentError ("invalid value for Enum ErrorType: " ++ showInteger x)))

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeInteger : ErrorType → I32
  | .ErrRedefineTableArray => JInt.lit .i32 0
  | .ErrExpectedNewLineKeyValue => JInt.lit .i32 1
  | .ErrAddKeyToInlineTable => JInt.lit .i32 2
  | .ErrAddArrayToStaticArray => JInt.lit .i32 3
  | .ErrArrayTreatedAsDictionary => JInt.lit .i32 4
  | .ErrExpectedEndOfTable => JInt.lit .i32 5
  | .ErrExpectedEndArrayOfTable => JInt.lit .i32 6
  | .ErrExpectedEqualAfterKey => JInt.lit .i32 7
  | .ErrDuplicatedKey => JInt.lit .i32 8
  | .ErrKeyAlreadyHasValue => JInt.lit .i32 9
  | .ErrInvalidBareKeyCharacter => JInt.lit .i32 10
  | .ErrEmptyBareKey => JInt.lit .i32 11
  | .ErrUnexpectedEofExpectedValue => JInt.lit .i32 12
  | .ErrUnexpectedStartOfValue => JInt.lit .i32 13
  | .ErrGenericValueError => JInt.lit .i32 14
  | .ErrExpectedCommaBetweenItemsArray => JInt.lit .i32 15
  | .ErrExpectedCommaBetweenItemsInlineTable => JInt.lit .i32 16
  | .ErrTrailingCommaInlineTable => JInt.lit .i32 17
  | .ErrInlineTableRedefine => JInt.lit .i32 18
  | .ErrUnderscoreNotSurroundedByDigits => JInt.lit .i32 19
  | .ErrLeadingZeroNotAllowedInteger => JInt.lit .i32 20
  | .ErrOverflowError => JInt.lit .i32 21
  | .ErrLeadingDot => JInt.lit .i32 22
  | .ErrNoTrailingDigitAfterDot => JInt.lit .i32 23
  | .ErrTrailingUnderscoreNumber => JInt.lit .i32 24
  | .ErrSignInNonBase10Number => JInt.lit .i32 25
  | .ErrParsingDateTime => JInt.lit .i32 26
  | .ErrOffsetDateNotSupported => JInt.lit .i32 27
  | .ErrNewLineInString => JInt.lit .i32 28
  | .ErrUnexpectedEndString => JInt.lit .i32 29
  | .ErrInvalidEscapeCharacter => JInt.lit .i32 30
  | .ErrInvalidUnicodeScalar => JInt.lit .i32 31
  | .ErrMultilineStringAsKey => JInt.lit .i32 32

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeConvert {E Target : Type} (convert : I32 → Except (Thrown E) Target)
    (x : ErrorType) : Except (Thrown E) Target :=
  convert (errorTypeInteger x)

/--
Base `Enums.jl:20`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeCconvert {M : Type → Type} {A : Type}
    (convert : I32 → M A) (x : ErrorType) : M A :=
  convert (errorTypeInteger x)

/--
Base `Enums.jl:21`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeWrite {Io Result : Type} {M : Type → Type}
    (writeInteger : Io → I32 → M Result) (io : Io) (x : ErrorType) : M Result :=
  writeInteger io (errorTypeInteger x)

/--
Base `Enums.jl:22`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeRead {Io : Type} {M : Type → Type} [Monad M]
    (readInteger : Io → M I32) (construct : I32 → M ErrorType) (io : Io) : M ErrorType := do
  let code ← readInteger io
  construct code

/--
Base `Enums.jl:32`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeIsless (x y : ErrorType) : Bool :=
  JuliaLean.base.int.ltSame (errorTypeInteger x) (errorTypeInteger y)

/--
Base `Enums.jl:30, 233-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeEnumHash (typeHash : JInt .u64)
    (hashInteger : I32 → JInt .u64 → JInt .u64)
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64)
    (x : ErrorType) (h : JInt .u64) : JInt .u64 :=
  hashUInt typeHash (hashInteger (errorTypeInteger x) h)

/--
Base `Enums.jl:226`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeTypemin : ErrorType := .ErrRedefineTableArray

/--
Base `Enums.jl:227`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeTypemax : ErrorType := .ErrMultilineStringAsKey

/--
Base `Enums.jl:235-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeInstances : List ErrorType :=
  [.ErrRedefineTableArray, .ErrExpectedNewLineKeyValue, .ErrAddKeyToInlineTable,
   .ErrAddArrayToStaticArray, .ErrArrayTreatedAsDictionary, .ErrExpectedEndOfTable,
   .ErrExpectedEndArrayOfTable, .ErrExpectedEqualAfterKey, .ErrDuplicatedKey,
   .ErrKeyAlreadyHasValue, .ErrInvalidBareKeyCharacter, .ErrEmptyBareKey,
   .ErrUnexpectedEofExpectedValue, .ErrUnexpectedStartOfValue, .ErrGenericValueError,
   .ErrExpectedCommaBetweenItemsArray, .ErrExpectedCommaBetweenItemsInlineTable,
   .ErrTrailingCommaInlineTable, .ErrInlineTableRedefine, .ErrUnderscoreNotSurroundedByDigits,
   .ErrLeadingZeroNotAllowedInteger, .ErrOverflowError, .ErrLeadingDot,
   .ErrNoTrailingDigitAfterDot, .ErrTrailingUnderscoreNumber, .ErrSignInNonBase10Number,
   .ErrParsingDateTime, .ErrOffsetDateNotSupported, .ErrNewLineInString,
   .ErrUnexpectedEndString, .ErrInvalidEscapeCharacter, .ErrInvalidUnicodeScalar,
   .ErrMultilineStringAsKey]

/--
Base `Enums.jl:34`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeSymbol (x : ErrorType) : String :=
  match x with
  | .ErrRedefineTableArray => "ErrRedefineTableArray"
  | .ErrExpectedNewLineKeyValue => "ErrExpectedNewLineKeyValue"
  | .ErrAddKeyToInlineTable => "ErrAddKeyToInlineTable"
  | .ErrAddArrayToStaticArray => "ErrAddArrayToStaticArray"
  | .ErrArrayTreatedAsDictionary => "ErrArrayTreatedAsDictionary"
  | .ErrExpectedEndOfTable => "ErrExpectedEndOfTable"
  | .ErrExpectedEndArrayOfTable => "ErrExpectedEndArrayOfTable"
  | .ErrExpectedEqualAfterKey => "ErrExpectedEqualAfterKey"
  | .ErrDuplicatedKey => "ErrDuplicatedKey"
  | .ErrKeyAlreadyHasValue => "ErrKeyAlreadyHasValue"
  | .ErrInvalidBareKeyCharacter => "ErrInvalidBareKeyCharacter"
  | .ErrEmptyBareKey => "ErrEmptyBareKey"
  | .ErrUnexpectedEofExpectedValue => "ErrUnexpectedEofExpectedValue"
  | .ErrUnexpectedStartOfValue => "ErrUnexpectedStartOfValue"
  | .ErrGenericValueError => "ErrGenericValueError"
  | .ErrExpectedCommaBetweenItemsArray => "ErrExpectedCommaBetweenItemsArray"
  | .ErrExpectedCommaBetweenItemsInlineTable => "ErrExpectedCommaBetweenItemsInlineTable"
  | .ErrTrailingCommaInlineTable => "ErrTrailingCommaInlineTable"
  | .ErrInlineTableRedefine => "ErrInlineTableRedefine"
  | .ErrUnderscoreNotSurroundedByDigits => "ErrUnderscoreNotSurroundedByDigits"
  | .ErrLeadingZeroNotAllowedInteger => "ErrLeadingZeroNotAllowedInteger"
  | .ErrOverflowError => "ErrOverflowError"
  | .ErrLeadingDot => "ErrLeadingDot"
  | .ErrNoTrailingDigitAfterDot => "ErrNoTrailingDigitAfterDot"
  | .ErrTrailingUnderscoreNumber => "ErrTrailingUnderscoreNumber"
  | .ErrSignInNonBase10Number => "ErrSignInNonBase10Number"
  | .ErrParsingDateTime => "ErrParsingDateTime"
  | .ErrOffsetDateNotSupported => "ErrOffsetDateNotSupported"
  | .ErrNewLineInString => "ErrNewLineInString"
  | .ErrUnexpectedEndString => "ErrUnexpectedEndString"
  | .ErrInvalidEscapeCharacter => "ErrInvalidEscapeCharacter"
  | .ErrInvalidUnicodeScalar => "ErrInvalidUnicodeScalar"
  | .ErrMultilineStringAsKey => "ErrMultilineStringAsKey"
/--
Base `Enums.jl:225`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeNameMap : List (I32 × String) :=
  errorTypeInstances.map (fun value => (errorTypeInteger value, errorTypeSymbol value))


/--
Base `Enums.jl:36-40`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeInternalSymbol (code : I32) : String :=
  match errorTypeNameMap.find? (fun (value, _) => value.val == code.val) with
  | some (_, name) => name
  | none => "<invalid #" ++ toString code.val ++ ">"

/--
Base `Enums.jl:42`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypePrint {m : Type → Type} [Monad m] {Io V : Type}
    (p : JuliaLean.base.show.IOPrims m Io V)
    (io : JuliaLean.base.show.JIO Io V) (x : ErrorType) : m Unit :=
  JuliaLean.base.show.print_Symbol p io (errorTypeSymbol x)

/--
Base `Enums.jl:44-55`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeShow {m : Type → Type} {Io V Ty Mod : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (moduleOfValue : V → Except JuliaLean.base.show.ShowError (Option Mod))
    (main parent : Mod) (isvisible : String → Mod → Mod → m Bool)
    (showModule : JuliaLean.base.show.JIO Io V → Mod → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : ErrorType) : m Unit := do
  if !(← JuliaLean.base.show.assertBool a (JuliaLean.base.show.getIO p io "compact" false)) then
    let origin ← match JuliaLean.base.show.getIO p io "module" main with
      | .inl value =>
          match moduleOfValue value with
          | .ok module => pure module
          | .error error => JuliaLean.base.show.throwShow error
      | .inr fallback => pure (some fallback)
    let qualify ← match origin with
      | none => pure true
      | some originModule => do
          let visible ← isvisible (errorTypeSymbol x) parent originModule
          pure !visible
    if qualify then
      showModule io parent
      JuliaLean.base.show.printStr p io "."
  JuliaLean.base.show.print_Symbol p io (errorTypeSymbol x)

/--
Base `Enums.jl:57-62`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeShowTextPlain {m : Type → Type} {Io V Ty : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (showType : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → I32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : ErrorType) : m Unit := do
  errorTypePrint p io x
  JuliaLean.base.show.printStr p io "::"
  let compactIO ← JuliaLean.base.show.withBool p a io "compact" true
  showType compactIO
  JuliaLean.base.show.printStr p io " = "
  showInteger io (errorTypeInteger x)

/--
Base `Enums.jl:64-75`; macro expansion is `Enums.jl:218-237`.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeShowTypeTextPlain {m : Type → Type} {Io V : Type} [Monad m]
    (p : JuliaLean.base.show.IOPrims m Io V)
    (showDatatype : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → I32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) : m Unit := do
  JuliaLean.base.show.printStr p io "Enum "
  showDatatype io
  JuliaLean.base.show.printStr p io ":"
  for x in errorTypeInstances do
    JuliaLean.base.show.printStr p io "\n"
    JuliaLean.base.show.print_Symbol p io (errorTypeSymbol x)
    JuliaLean.base.show.printStr p io " = "
    showInteger io (errorTypeInteger x)

/--
Base `Enums.jl:91`; `Ref` uses the installed `base/refvalue.jl` constructor.
Julia source: base/toml/parser.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum ErrorType begin
```
-/
def errorTypeBroadcastable {R : Type} (makeRef : ErrorType → R) (x : ErrorType) : R :=
  makeRef x

/-- The user's `Dates` module (`Parser{Dates}` with `Dates !== nothing`). -/
structure DatesOps (X Y E : Type) where
  Date : JInt64 → JInt64 → JInt64 → Except (Thrown E) X
  Time : JInt64 → JInt64 → JInt64 → JInt64 → Except (Thrown E) X
  DateTime : JInt64 → JInt64 → JInt64 → JInt64 → JInt64 → JInt64 → JInt64 → Except (Thrown E) X
  /-- `typeof(x)` and `===` on these types. -/
  typeOf : X → Y
  typeEq : Y → Y → Bool
  dateType : Y
  timeType : Y
  dateTimeType : Y

/-- Callees in other files and in `Dates`. -/
structure Ops (X Y E D CI CF : Type) where
  dict : DictOps Bytes (Val X) D
  items : DictOps CommentPath CommentBlock CI
  floating : DictOps CommentPath (List Bytes) CF
  /-- `Dates`: `none` is `Parser{nothing}`. -/
  dates : Option (DatesOps X Y E)
  /-- `Base.parse(T, s; base)` for `T` in `Int64`, `UInt64`, `Int128`, `UInt128`, `BigInt`
  (`base/parse.jl`, `base/gmp.jl`). -/
  parse_Int64 : Bytes → Option JInt64 → Except (Thrown E) (JInt .i64)
  parse_UInt64 : Bytes → Option JInt64 → Except (Thrown E) (JInt .u64)
  parse_Int128 : Bytes → Option JInt64 → Except (Thrown E) (JInt .i128)
  parse_UInt128 : Bytes → Option JInt64 → Except (Thrown E) (JInt .u128)
  parse_BigInt : Bytes → Option JInt64 → Except (Thrown E) Int
  /-- `Base.tryparse(Float64, s)`. -/
  tryparse_Float64 : Bytes → Except (Thrown E) (Option (JuliaLean.base.float.FV .f64))
  /-- `unescape_string(s)` and `escape_string(s)` (`base/strings/io.jl`). -/
  unescape_string : Bytes → Except (Thrown E) Bytes
  escape_string : Bytes → Except (Thrown E) Bytes
  /-- `string(c::Char)`. -/
  string_Char : JChar → Bytes
  /-- `SubString(s, i:j)` as a `String`, `prevind(s, i)`, `length(s)` and `filter(!=('_'), s)`
  (`base/strings/`). -/
  substring : Bytes → JInt64 → JInt64 → Except (Thrown E) Bytes
  prevind : Bytes → JInt64 → Except (Thrown E) JInt64
  length : Bytes → JInt64
  filter_underscore : Bytes → Bytes
  /-- `x ^ p` on `Int` (`base/intfuncs.jl`). -/
  pow_Int : JInt64 → JInt64 → Except (Thrown E) JInt64
  /-- `read(io, String)` of the `Parser(io::IO)` constructor. -/
  readString : {IO : Type} → IO → Except (Thrown E) Bytes

/--
Julia source: base/toml/parser.jl:71-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
##########
# Parser #
##########

mutable struct Parser{Dates}
    str::String
    # 1 character look ahead
    current_char::Char
    pos::Int
    # prevpos equals the startbyte of the look ahead character
    # prevpos-1 is therefore the end byte of the character we last ate
    prevpos::Int

    # File info
    column::Int
    line::Int

    # The function `take_substring` takes the substring from `marker` up
    # to `prevpos-1`.
    marker::Int

    # The current table that `key = value` entries are inserted into
    active_table::TOMLDict

    # As we parse dotted keys we store each part of the key in this cache
    # A future improvement would be to also store the spans of the keys
    # so that in error messages we could also show the previous key
    # definition in case of duplicated keys
    dotted_keys::Vector{String}

    # Strings in TOML can have line continuations ('\' as the last character
    # on a line. We store the byte ranges for each of these "chunks" in here
    chunks::Vector{UnitRange{Int}}

    # We need to keep track of those tables / arrays that are defined
    # inline since we are not allowed to add keys to those
    inline_tables::IdSet{TOMLDict}
    static_arrays::IdSet{Any}

    # [a.b.c.d] doesn't "define" the table [a]
    # so keys can later be added to [a], therefore
    # we need to keep track of what tables are
    # actually defined
    defined_tables::IdSet{TOMLDict}

    # Tables implicitly created as intermediates by dotted keys
    # in key-value entries (e.g. `a` in `a.b = 1`).
    # These cannot be reopened by [table] headers.
    implicit_tables::IdSet{TOMLDict}

    # The table we will finally return to the user
    root::TOMLDict

    # Filled in in case we are parsing a file to improve error messages
    filepath::Union{String, Nothing}

    comments::Union{Comments, Nothing}
    pending_comments::Vector{String}
    captured_comment::String
    active_table_path::Vector{String}
    last_item_path::Union{CommentPath, Nothing}
    # Paths cannot distinguish array-of-tables elements, so their comments are ignored.
    in_array_table::Bool
end

```
-/
structure Parser (X D CI CF : Type) where
  str : Bytes
  -- 1 character look ahead
  current_char : JChar
  pos : JInt64
  -- prevpos equals the startbyte of the look ahead character
  prevpos : JInt64
  -- File info
  column : JInt64
  line : JInt64
  marker : JInt64
  active_table : TOMLDictRef
  dotted_keys : List Bytes
  chunks : List (JInt64 × JInt64)
  inline_tables : List TOMLDictRef
  static_arrays : List Nat
  defined_tables : List TOMLDictRef
  implicit_tables : List TOMLDictRef
  root : TOMLDictRef
  filepath : Option Bytes
  comments : Option (Comments CI CF)
  pending_comments : List Bytes
  captured_comment : Bytes
  active_table_path : List Bytes
  last_item_path : Option CommentPath
  in_array_table : Bool
  /-- Heaps of the `TOMLDict` and `Vector` objects created while parsing (not Julia fields). -/
  tables : List D
  vectors : List (Vec X)

section
variable {X Y E D CI CF : Type}

/-- The parser monad of `Ops o`. -/
abbrev PM (_o : Ops X Y E D CI CF) (α : Type) :=
  ExceptT ParserError (StateT (Parser X D CI CF) (ExceptT (Thrown E) Option)) α

def throwP (o : Ops X Y E D CI CF) {α : Type} (e : ParserError) : PM o α := throwThe ParserError e
def throwT (o : Ops X Y E D CI CF) {α : Type} (e : Thrown E) : PM o α :=
  ExceptT.lift (StateT.lift (throw e))
def liftT (o : Ops X Y E D CI CF) {α : Type} : Except (Thrown E) α → PM o α
  | .ok a => pure a
  | .error e => throwT o e

/-- A `ParserError` returned as a value (a call without `@try`). -/
def observe (o : Ops X Y E D CI CF) {α : Type} (x : PM o α) : PM o (Except ParserError α) :=
  tryCatchThe ParserError (Except.ok <$> x) (fun e => pure (.error e))

def getP (o : Ops X Y E D CI CF) : PM o (Parser X D CI CF) := get
def modifyP (o : Ops X Y E D CI CF) (f : Parser X D CI CF → Parser X D CI CF) : PM o Unit := modify f

/-- Heap access; references come only from `allocTable`/`allocVector`. -/
def getTable (o : Ops X Y E D CI CF) (r : TOMLDictRef) : PM o D := do
  match (← getP o).tables[r]? with
  | some d => pure d
  | none => throwT o (.jl .boundsError)
def setTable (o : Ops X Y E D CI CF) (r : TOMLDictRef) (d : D) : PM o Unit :=
  modifyP o fun l => { l with tables := l.tables.set r d }
/-- `TOMLDict()`. -/
def allocTable (o : Ops X Y E D CI CF) : PM o TOMLDictRef := do
  let l ← getP o
  modifyP o fun l => { l with tables := l.tables ++ [o.dict.empty] }
  return l.tables.length
def getVector (o : Ops X Y E D CI CF) (r : Nat) : PM o (Vec X) := do
  match (← getP o).vectors[r]? with
  | some v => pure v
  | none => throwT o (.jl .boundsError)
def setVector (o : Ops X Y E D CI CF) (r : Nat) (v : Vec X) : PM o Unit :=
  modifyP o fun l => { l with vectors := l.vectors.set r v }
/-- `Vector{T}()`. -/
def allocVector (o : Ops X Y E D CI CF) (eltype : ElType) (elems : List (Val X) := []) : PM o Nat := do
  let l ← getP o
  modifyP o fun l => { l with vectors := l.vectors ++ [⟨eltype, elems⟩] }
  return l.vectors.length

/-- `typeof(v)`. -/
def typeofVal (o : Ops X Y E D CI CF) : Val X → PM o (VType Y)
  | .str _ => pure .string
  | .bool _ => pure .bool
  | .int64 _ => pure .int64
  | .uint64 _ => pure .uint64
  | .int128 _ => pure .int128
  | .uint128 _ => pure .uint128
  | .bigint _ => pure .bigint
  | .float64 _ => pure .float64
  | .date _ => pure .date
  | .time _ => pure .time
  | .datetime _ => pure .datetime
  | .dates x => match o.dates with
    | some d => pure (.dates (d.typeOf x))
    | none => throwT o .typeError
  | .table _ => pure .table
  | .vector r => do return .vector (← getVector o r).eltype

def yEq (o : Ops X Y E D CI CF) (a b : Y) : Bool :=
  match o.dates with
  | some d => d.typeEq a b
  | none => false


/-- `accept`'s argument: a predicate (`f::Function`) or a character (`f::Char`). -/
inductive Acc where
  | fn (f : JChar → Bool)
  | ch (c : JChar)

def chr (c : Char) : Acc := .ch (jc c)

/--
Julia source: base/toml/parser.jl:408-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

################
# Parser utils #
################

@inline function next_char(l::Parser)::Char
    state = iterate(l.str, l.pos)
    l.prevpos = l.pos
    l.column += 1
    state === nothing && return EOF_CHAR
    c, pos = state
    l.pos = pos
    if c == '\n'
        l.line += 1
        l.column = 0
    end
    return c
end

```
-/
def next_char (o : Ops X Y E D CI CF) : PM o JChar := do
  let l ← getP o
  let state := iterateStr l.str l.pos
  modifyP o fun l => { l with prevpos := l.pos }
  modifyP o fun l => { l with column := i64 (l.column.val + 1) }
  match state with
  | none => return EOF_CHAR
  | some (c, pos) =>
    modifyP o fun l => { l with pos := pos }
    if c == jc '\n' then
      modifyP o fun l => { l with line := i64 (l.line.val + 1) }
      modifyP o fun l => { l with column := i64 0 }
    return c

/--
Julia source: base/toml/parser.jl:427-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function eat_char(l::Parser)::Char
    c = l.current_char
    l.current_char = next_char(l)
    return c
end

```
-/
def eat_char (o : Ops X Y E D CI CF) : PM o JChar := do
  let c := (← getP o).current_char
  let n ← next_char o
  modifyP o fun l => { l with current_char := n }
  return c

/--
Julia source: base/toml/parser.jl:433-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline peek(l::Parser) = l.current_char

```
-/
def peek (o : Ops X Y E D CI CF) : PM o JChar := do return (← getP o).current_char

/--
Julia source: base/toml/parser.jl:435-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return true if the character was accepted. When a character
# is accepted it gets eaten and we move to the next character
@inline function accept(l::Parser, f::Union{Function, Char})::Bool
    c = peek(l)
    c == EOF_CHAR && return false
    ok = false
    if isa(f, Function)
        ok = f(c)
    elseif isa(f, Char)
        ok = c === f
    end
    ok && eat_char(l)
    return ok
end

```
-/
def accept (o : Ops X Y E D CI CF) (f : Acc) : PM o Bool := do
  let c ← peek o
  if c == EOF_CHAR then return false
  let ok := match f with
    | .fn g => g c
    | .ch d => c == d
  if ok then discard (eat_char o)
  return ok

/-- The `while accept(l, f)` loop of `accept_batch`. -/
def accept_batch_loop (o : Ops X Y E D CI CF) (f : Acc) (ok : Bool) : PM o Bool := do
  if (← accept o f) then accept_batch_loop o f true
  else return ok
partial_fixpoint

/--
Julia source: base/toml/parser.jl:450-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return true if any character was accepted
function accept_batch(l::Parser, f::F)::Bool where {F}
    ok = false
    while accept(l, f)
        ok = true
    end
    return ok
end

```
-/
def accept_batch (o : Ops X Y E D CI CF) (f : Acc) : PM o Bool := accept_batch_loop o f false

/-- The `for _ in 1:n` loop of `accept_n`. -/
def accept_n_loop (o : Ops X Y E D CI CF) (f : Acc) : Nat → PM o Bool
  | 0 => pure true
  | k + 1 => do
    if !(← accept o f) then return false
    accept_n_loop o f k

/--
Julia source: base/toml/parser.jl:459-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return true if `f` was accepted `n` times
@inline function accept_n(l::Parser, n, f::F)::Bool where {F}
    for _ in 1:n
        if !accept(l, f)
            return false
        end
    end
    return true
end

```
-/
def accept_n (o : Ops X Y E D CI CF) (n : JInt64) (f : Acc) : PM o Bool := accept_n_loop o f n.val.toNat

/--
Julia source: base/toml/parser.jl:469-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline iswhitespace(c::Char) = c == ' ' || c == '\t'
@inline isnewline(c::Char) = c == '\n' || c == '\r'

```
-/
def iswhitespace (c : JChar) : Bool := c == jc ' ' || c == jc '\t'
def isnewline (c : JChar) : Bool := c == jc '\n' || c == jc '\r'

/--
Julia source: base/toml/parser.jl:472-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
skip_ws(l::Parser) = accept_batch(l, iswhitespace)

skip_ws_nl_no_comment(l::Parser)::Bool = accept_batch(l, x -> iswhitespace(x) || isnewline(x))

```
-/
def skip_ws (o : Ops X Y E D CI CF) : PM o Bool := accept_batch o (.fn iswhitespace)
def skip_ws_nl_no_comment (o : Ops X Y E D CI CF) : PM o Bool :=
  accept_batch o (.fn fun x => iswhitespace x || isnewline x)

/--
Julia source: base/toml/parser.jl:167-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function startup(l::Parser)
    # Populate our one character look-ahead
    c = eat_char(l)
    # Skip BOM
    if c === '\ufeff'
        l.column -= 1
        eat_char(l)
    end
end

```
-/
def startup (o : Ops X Y E D CI CF) : PM o Unit := do
  -- Populate our one character look-ahead
  let c ← eat_char o
  -- Skip BOM
  if c == jc '\ufeff' then
    modifyP o fun l => { l with column := i64 (l.column.val - 1) }
    discard (eat_char o)

/-- Runs a parser action on a parser state. -/
def runP (o : Ops X Y E D CI CF) {α : Type} (x : PM o α) (l : Parser X D CI CF) :
    Option (Except (Thrown E) (Err α × Parser X D CI CF)) :=
  (x.run.run l).run

/--
Julia source: base/toml/parser.jl:136-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Parser{Dates}(str::String; filepath=nothing, comments::Union{Comments, Nothing}=nothing) where {Dates}
    root = TOMLDict()
    comments === nothing || empty!(comments)
    l = Parser{Dates}(
            str,                  # str
            EOF_CHAR,             # current_char
            firstindex(str),      # pos
            0,                    # prevpos
            0,                    # column
            1,                    # line
            0,                    # marker
            root,                 # active_table
            String[],             # dotted_keys
            UnitRange{Int}[],     # chunks
            IdSet{TOMLDict}(),    # inline_tables
            IdSet{Any}(),         # static_arrays
            IdSet{TOMLDict}(),    # defined_tables
            IdSet{TOMLDict}(),    # implicit_tables
            root,
            filepath,
            comments,             # comments
            String[],             # pending_comments
            "",                   # captured_comment
            String[],             # active_table_path
            nothing,              # last_item_path
            false,                # in_array_table
        )
    startup(l)
    return l
end

```
-/
def Parser_new (o : Ops X Y E D CI CF) (str : Bytes) (filepath : Option Bytes := none)
    (comments : Option (Comments CI CF) := none) : Option (Except (Thrown E) (Err Unit × Parser X D CI CF)) :=
  -- `root = TOMLDict()` is the first table of the heap
  let root : TOMLDictRef := 0
  let comments := comments.map (emptyBang_Comments o.items o.floating)
  let l : Parser X D CI CF := {
    str := str
    current_char := EOF_CHAR
    pos := i64 1
    prevpos := i64 0
    column := i64 0
    line := i64 1
    marker := i64 0
    active_table := root
    dotted_keys := []
    chunks := []
    inline_tables := []
    static_arrays := []
    defined_tables := []
    implicit_tables := []
    root := root
    filepath := filepath
    comments := comments
    pending_comments := []
    captured_comment := []
    active_table_path := []
    last_item_path := none
    in_array_table := false
    tables := [o.dict.empty]
    vectors := [] }
  runP o (startup o) l

/--
Julia source: base/toml/parser.jl:177-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Parser{Dates}() where {Dates} = Parser{Dates}("")
Parser{Dates}(io::IO) where {Dates} = Parser{Dates}(read(io, String))

```
-/
def Parser_0 (o : Ops X Y E D CI CF) : Option (Except (Thrown E) (Err Unit × Parser X D CI CF)) :=
  Parser_new o (lit "")
def Parser_IO (o : Ops X Y E D CI CF) {IO : Type} (io : IO) :
    Option (Except (Thrown E) (Err Unit × Parser X D CI CF)) :=
  match o.readString io with
  | .ok s => Parser_new o s
  | .error e => some (.error e)

/--
Julia source: base/toml/parser.jl:180-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parser(...) will be defined by TOML stdlib

function reinit!(p::Parser, str::String; filepath::Union{Nothing, String}=nothing,
                 comments::Union{Comments, Nothing}=nothing)
    p.str = str
    p.current_char = EOF_CHAR
    p.pos = firstindex(str)
    p.prevpos = 0
    p.column = 0
    p.line = 1
    p.marker = 0
    p.root = TOMLDict()
    p.active_table = p.root
    empty!(p.dotted_keys)
    empty!(p.chunks)
    empty!(p.inline_tables)
    empty!(p.static_arrays)
    empty!(p.defined_tables)
    empty!(p.implicit_tables)
    p.filepath = filepath
    comments === nothing || empty!(comments)
    p.comments = comments
    empty!(p.pending_comments)
    p.captured_comment = ""
    empty!(p.active_table_path)
    p.last_item_path = nothing
    p.in_array_table = false
    startup(p)
    return p
end

```
-/
def reinit (o : Ops X Y E D CI CF) (str : Bytes) (filepath : Option Bytes := none)
    (comments : Option (Comments CI CF) := none) : PM o Unit := do
  modifyP o fun p => { p with str := str }
  modifyP o fun p => { p with current_char := EOF_CHAR }
  modifyP o fun p => { p with pos := i64 1 }
  modifyP o fun p => { p with prevpos := i64 0 }
  modifyP o fun p => { p with column := i64 0 }
  modifyP o fun p => { p with line := i64 1 }
  modifyP o fun p => { p with marker := i64 0 }
  let root ← allocTable o
  modifyP o fun p => { p with root := root }
  modifyP o fun p => { p with active_table := p.root }
  modifyP o fun p => { p with dotted_keys := [] }
  modifyP o fun p => { p with chunks := [] }
  modifyP o fun p => { p with inline_tables := [] }
  modifyP o fun p => { p with static_arrays := [] }
  modifyP o fun p => { p with defined_tables := [] }
  modifyP o fun p => { p with implicit_tables := [] }
  modifyP o fun p => { p with filepath := filepath }
  let comments := comments.map (emptyBang_Comments o.items o.floating)
  modifyP o fun p => { p with comments := comments }
  modifyP o fun p => { p with pending_comments := [] }
  modifyP o fun p => { p with captured_comment := [] }
  modifyP o fun p => { p with active_table_path := [] }
  modifyP o fun p => { p with last_item_path := none }
  modifyP o fun p => { p with in_array_table := false }
  startup o

/--
Julia source: base/toml/parser.jl:350-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function format_error_message_for_err_type(error::ParserError)
    msg = err_message[error.type]
    if error.type == ErrInvalidBareKeyCharacter
        c_escaped = escape_string(string(error.data::Char))
        msg *= ": '$c_escaped'"
    end
    return msg
end

```
-/
def format_error_message_for_err_type (o : Ops X Y E D CI CF) (error : ParserError) : Except (Thrown E) Bytes := do
  let msg := lit (err_message error.type)
  if error.type == .ErrInvalidBareKeyCharacter then
    let c ← match error.data with
      | some c => pure c
      | none => throw .typeError
    let c_escaped ← o.escape_string (o.string_Char c)
    return msg ++ lit ": '" ++ c_escaped ++ lit "'"
  return msg

structure PointToLineOps (E S Context : Type) where
  assertRange : Bool → String → Except E Unit
  thisind : S → JInt64 → Except E JInt64
  prevind : S → JInt64 → Except E JInt64
  findPrevNewline : S → JInt64 → Except E (Option JInt64)
  iterate : S → JInt64 → Except E (Option (JChar × JInt64))
  ncodeunits : S → Nat
  charString : JChar → Bytes
  styledCaret : Context → Except E Bytes

def pointToLineScan {E S Context : Type} (ops : PointToLineOps E S Context)
    (str : S) (a b : JInt64) (context : Context) :
    Nat → JInt64 → Except E (Bytes × Bytes)
  | 0, _ => .ok ([], [])
  | fuel + 1, pos => do
    let caret ← if decide (a.val ≤ pos.val) && decide (pos.val ≤ b.val) then
      ops.styledCaret context
    else pure [32]
    match ← ops.iterate str pos with
    | none => pure ([], caret)
    | some (c, next) =>
      if c == jc '\n' then pure ([], caret)
      else do
        let (line, marks) ← pointToLineScan ops str a b context fuel next
        pure (ops.charString c ++ line, caret ++ marks)

def pointToLineBody {E S Context : Type} (ops : PointToLineOps E S Context)
    (str : S) (a b : JInt64) (context : Context) : Except E (Bytes × Bytes) := do
  ops.assertRange (decide (b.val ≥ a.val)) "invalid range"
  let a ← ops.thisind str a
  let b ← ops.thisind str b
  let previous ← ops.prevind str a
  let newline ← ops.findPrevNewline str previous
  let pos := (newline.getD (i64 0)) + i64 1
  pointToLineScan ops str a b context (ops.ncodeunits str + 1) pos

inductive ErrorDisplayPart where
  | bytes (value : Bytes)
  | integer (value : JInt64)
  | optionalInteger (value : Option JInt64)

structure ErrorDisplayOps (M : Type → Type) (IO Color : Type) where
  errorColor : M Color
  formatErrorMessage : ParserError → M Bytes
  pointToLine : Bytes → JInt64 → JInt64 → IO → M (Bytes × Bytes)
  printStyled : IO → List ErrorDisplayPart → Option Color → Bool → M Unit
  println : IO → List ErrorDisplayPart → M Unit
  print : IO → List ErrorDisplayPart → M Unit
  typeError : {A : Type} → M A

/-!
Julia source: base/toml/parser.jl:359-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This is used in error formatting, for example,
# point_to_line("aa\nfoobar\n\bb", 4, 6) would return the strings:
# str1 = "foobar"
# str2 = "^^^"
# used to show the interval where an error happened
# Right now, it is only called with a == b
function point_to_line(str::AbstractString, a::Int, b::Int, context)
    @assert b >= a "invalid range"
    a = thisind(str, a)
    b = thisind(str, b)
    pos = something(findprev('\n', str, prevind(str, a)), 0) + 1
    io1 = IOContext(IOBuffer(), context)
    io2 = IOContext(IOBuffer(), context)
    while true
        if a <= pos <= b
            printstyled(io2, "^"; color=:light_green)
        else
            print(io2, " ")
        end
        it = iterate(str, pos)
        it === nothing && break
        c, pos = it
        c == '\n' && break
        print(io1, c)
    end
    return takestring!(io1.io), takestring!(io2.io)
end
```
-/
def pointToLine {E S Context : Type} (ops : PointToLineOps E S Context)
    (str : S) (a b : JInt64) (context : Context) : Except E (Bytes × Bytes) :=
  pointToLineBody ops str a b context

/-!
Julia source: base/toml/parser.jl:387-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showerror(io::IO, err::ParserError)
    printstyled(io, "TOML Parser error:\n"; color=Base.error_color())
    f = something(err.filepath, "none")
    printstyled(io, f, ':', err.line, ':', err.column; bold=true)
    printstyled(io, " error: "; color=Base.error_color())
    println(io, format_error_message_for_err_type(err))
    # In this case we want the arrow to point one character
    pos = err.pos::Int
    err.type == ErrUnexpectedEofExpectedValue && (pos += 1)
    str1, err1 = point_to_line(err.str::String, pos, pos, io)
    @static if VERSION <= v"1.6.0-DEV.121"
        # See https://github.com/JuliaLang/julia/issues/36015
        format_fixer = get(io, :color, false)::Bool == true ? "\e[0m" : ""
        println(io, "$format_fixer  ", str1)
        print(io, "$format_fixer  ", err1)
    else
        println(io, "  ", str1)
        print(io, "  ", err1)
    end
end

```
-/
-- Julia 1.15 compiles the `@static` condition to the modern branch.
def showParserError {M : Type → Type} [Monad M] {IO Color : Type}
    (ops : ErrorDisplayOps M IO Color) (io : IO) (error : ParserError) : M Unit := do
  let headerColor ← ops.errorColor
  ops.printStyled io [.bytes (lit "TOML Parser error:\n")] (some headerColor) false
  let filepath := error.filepath.getD (lit "none")
  ops.printStyled io
    [.bytes filepath, .bytes (lit ":"), .optionalInteger error.line,
      .bytes (lit ":"), .optionalInteger error.column] none true
  let messageColor ← ops.errorColor
  ops.printStyled io [.bytes (lit " error: ")] (some messageColor) false
  let message ← ops.formatErrorMessage error
  ops.println io [.bytes message]
  let pos ← match error.pos with
    | some pos => pure pos
    | none => ops.typeError
  let pos := if error.type == .ErrUnexpectedEofExpectedValue then pos + i64 1 else pos
  let source ← match error.str with
    | some source => pure source
    | none => ops.typeError
  let (line, caret) ← ops.pointToLine source pos pos io
  ops.println io [.bytes (lit "  "), .bytes line]
  ops.print io [.bytes (lit "  "), .bytes caret]

/--
Julia source: base/toml/parser.jl:526-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Returns true if a comment was skipped
function skip_comment(l::Parser)::Bool
    found_comment = accept(l, '#')
    if found_comment
        if l.comments === nothing
            accept_batch(l, !isnewline)
        else
            start = l.prevpos
            accept_batch(l, !isnewline)
            l.captured_comment = String(SubString(l.str, start:prevind(l.str, l.prevpos)))
        end
    end
    return found_comment
end

```
-/
def skip_comment (o : Ops X Y E D CI CF) : PM o Bool := do
  let found_comment ← accept o (chr '#')
  if found_comment then
    if (← getP o).comments.isNone then
      discard (accept_batch o (.fn fun c => !isnewline c))
    else
      let start := (← getP o).prevpos
      discard (accept_batch o (.fn fun c => !isnewline c))
      let l ← getP o
      let j ← liftT o (o.prevind l.str l.prevpos)
      let s ← liftT o (o.substring l.str start j)
      modifyP o fun l => { l with captured_comment := s }
  return found_comment

/-- The `while true` loop of `skip_ws_nl`. -/
def skip_ws_nl_loop (o : Ops X Y E D CI CF) (skipped : Bool) : PM o Bool := do
  let skipped_ws ← accept_batch o (.fn fun x => iswhitespace x || isnewline x)
  let skipped_comment ← skip_comment o
  if skipped_comment && (← getP o).comments.isSome then
    modifyP o fun l => { l with pending_comments := l.pending_comments ++ [l.captured_comment] }
  if !skipped_ws && !skipped_comment then
    return skipped
  skip_ws_nl_loop o true
partial_fixpoint

/--
Julia source: base/toml/parser.jl:476-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip_ws_nl(l::Parser)::Bool
    skipped = false
    while true
        skipped_ws = accept_batch(l, x -> iswhitespace(x) || isnewline(x))
        skipped_comment = skip_comment(l)
        if skipped_comment && l.comments !== nothing
            push!(l.pending_comments, l.captured_comment)
        end
        if !skipped_ws && !skipped_comment
            break
        end
        skipped = true
    end
    return skipped
end

```
-/
def skip_ws_nl (o : Ops X Y E D CI CF) : PM o Bool := skip_ws_nl_loop o false

/--
Julia source: base/toml/parser.jl:546-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flush_pending_comments!(l::Parser)
    isempty(l.pending_comments) && return
    comments = l.comments
    if comments !== nothing && !l.in_array_table
        floating = get!(() -> String[], comments.floating, copy(l.active_table_path))
        append!(floating, l.pending_comments)
    end
    empty!(l.pending_comments)
    return
end

```
-/
def flush_pending_comments (o : Ops X Y E D CI CF) : PM o Unit := do
  let l ← getP o
  if l.pending_comments.isEmpty then return
  match l.comments with
  | some comments =>
    if !l.in_array_table then
      -- `get!(() -> String[], comments.floating, copy(l.active_table_path))`, then `append!`
      let key := l.active_table_path
      let floating := (o.floating.get comments.floating key).getD []
      let comments := { comments with floating := o.floating.set comments.floating key (floating ++ l.pending_comments) }
      modifyP o fun l => { l with comments := some comments }
  | none => pure ()
  modifyP o fun l => { l with pending_comments := [] }

/-- The inner `while true` loop of `skip_ws_nl_toplevel`; returns `(progress, nlines)`. -/
def skip_toplevel_inner (o : Ops X Y E D CI CF) (progress : Bool) (nlines : JInt64) : PM o (Bool × JInt64) := do
  let c ← peek o
  if iswhitespace c then
    discard (eat_char o)
    skip_toplevel_inner o true nlines
  else if isnewline c then
    let mut nlines := nlines
    if c == jc '\n' then
      nlines := i64 (nlines.val + 1)
      if nlines.val == 2 then flush_pending_comments o
    discard (eat_char o)
    skip_toplevel_inner o true nlines
  else
    return (progress, nlines)
partial_fixpoint

/-- The outer `while true` loop of `skip_ws_nl_toplevel`. -/
def skip_toplevel_outer (o : Ops X Y E D CI CF) (skipped : Bool) (nlines : JInt64) : PM o Bool := do
  let (progress, nlines) ← skip_toplevel_inner o false nlines
  let mut progress := progress
  let mut nlines := nlines
  if (← skip_comment o) then
    modifyP o fun l => { l with pending_comments := l.pending_comments ++ [l.captured_comment] }
    nlines := i64 0
    progress := true
  if !progress then return skipped
  skip_toplevel_outer o true nlines
partial_fixpoint

/--
Julia source: base/toml/parser.jl:492-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A blank line makes pending comments float rather than attach to the next item.
function skip_ws_nl_toplevel(l::Parser)::Bool
    l.comments === nothing && return skip_ws_nl(l)
    skipped = false
    nlines = 0 # newlines seen since the last comment (or the previous item)
    while true
        progress = false
        while true
            c = peek(l)
            if iswhitespace(c)
                eat_char(l)
                progress = true
            elseif isnewline(c)
                if c == '\n'
                    nlines += 1
                    nlines == 2 && flush_pending_comments!(l)
                end
                eat_char(l)
                progress = true
            else
                break
            end
        end
        if skip_comment(l)
            push!(l.pending_comments, l.captured_comment)
            nlines = 0
            progress = true
        end
        progress || break
        skipped = true
    end
    return skipped
end

```
-/
def skip_ws_nl_toplevel (o : Ops X Y E D CI CF) : PM o Bool := do
  if (← getP o).comments.isNone then return (← skip_ws_nl o)
  skip_toplevel_outer o false (i64 0) -- newlines seen since the last comment (or the previous item)

/--
Julia source: base/toml/parser.jl:541-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip_ws_comment(l::Parser)::Bool
    skip_ws(l)
    return skip_comment(l)
end

```
-/
def skip_ws_comment (o : Ops X Y E D CI CF) : PM o Bool := do
  discard (skip_ws o)
  skip_comment o

/-- `(l.comments::Comments)`. -/
def commentsOf (o : Ops X Y E D CI CF) : PM o (Comments CI CF) := do
  match (← getP o).comments with
  | some c => pure c
  | none => throwT o .typeError

/--
Julia source: base/toml/parser.jl:557-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function attach_pending_comments!(l::Parser, path::CommentPath)
    isempty(l.pending_comments) && return
    block = get!(CommentBlock, (l.comments::Comments).items, path)
    append!(block.above, l.pending_comments)
    empty!(l.pending_comments)
    return
end

```
-/
def attach_pending_comments (o : Ops X Y E D CI CF) (path : CommentPath) : PM o Unit := do
  if (← getP o).pending_comments.isEmpty then return
  let comments ← commentsOf o
  -- `get!(CommentBlock, items, path)`, then `append!(block.above, …)`
  let block := (o.items.get comments.items path).getD CommentBlock_new
  let block := { block with above := block.above ++ (← getP o).pending_comments }
  modifyP o fun l => { l with comments := some { comments with items := o.items.set comments.items path block } }
  modifyP o fun l => { l with pending_comments := [] }

/--
Julia source: base/toml/parser.jl:565-572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function attach_inline_comment!(l::Parser)
    path = l.last_item_path
    path === nothing && return
    block = get!(CommentBlock, (l.comments::Comments).items, path)
    block.inline = l.captured_comment
    return
end

```
-/
def attach_inline_comment (o : Ops X Y E D CI CF) : PM o Unit := do
  let path := (← getP o).last_item_path
  match path with
  | none => return
  | some path =>
    let comments ← commentsOf o
    let block := (o.items.get comments.items path).getD CommentBlock_new
    let block := { block with inline := some (← getP o).captured_comment }
    modifyP o fun l => { l with comments := some { comments with items := o.items.set comments.items path block } }

/-- The `for k in keys` loop of `path_traverses_array`. -/
def path_traverses_array_loop (o : Ops X Y E D CI CF) (d : TOMLDictRef) : List Bytes → PM o Bool
  | [] => pure false
  | k :: ks => do
    let v := o.dict.get (← getTable o d) k
    match v with
    | some (.vector _) => return true
    | some (.table r) => path_traverses_array_loop o r ks
    | _ => return false

/--
Julia source: base/toml/parser.jl:573-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function path_traverses_array(l::Parser, keys::AbstractVector{String})
    d = l.root
    for k in keys
        v = get(d, k, nothing)
        v isa Vector && return true
        v isa TOMLDict || return false
        d = v
    end
    return false
end

```
-/
def path_traverses_array (o : Ops X Y E D CI CF) (keys : List Bytes) : PM o Bool := do
  path_traverses_array_loop o (← getP o).root keys

/--
Julia source: base/toml/parser.jl:584-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline set_marker!(l::Parser) = l.marker = l.prevpos
take_substring(l::Parser) = SubString(l.str, l.marker:(l.prevpos-1))

```
-/
def set_marker (o : Ops X Y E D CI CF) : PM o Unit := modifyP o fun l => { l with marker := l.prevpos }
def take_substring (o : Ops X Y E D CI CF) : PM o Bytes := do
  let l ← getP o
  liftT o (o.substring l.str l.marker (i64 (l.prevpos.val - 1)))

/-- `push!` on an `IdSet`. -/
def idPush (xs : List Nat) (x : Nat) : List Nat := if xs.contains x then xs else xs ++ [x]

/-- `get!(TOMLDict, d, key)`. -/
def getBang_table (o : Ops X Y E D CI CF) (r : TOMLDictRef) (key : Bytes) : PM o (Val X) := do
  match o.dict.get (← getTable o r) key with
  | some v => return v
  | none =>
    let nr ← allocTable o
    setTable o r (o.dict.set (← getTable o r) key (.table nr))
    return .table nr

/-- `get!(() -> Any[], d, key)`. -/
def getBang_vector (o : Ops X Y E D CI CF) (r : TOMLDictRef) (key : Bytes) : PM o (Val X) := do
  match o.dict.get (← getTable o r) key with
  | some v => return v
  | none =>
    let nr ← allocVector o .any
    setTable o r (o.dict.set (← getTable o r) key (.vector nr))
    return .vector nr

/--
Julia source: base/toml/parser.jl:669-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_allowed_add_key(l::Parser, d, check_defined=true)::Err{Nothing}
    if !(d isa Dict)
        return ParserError(ErrKeyAlreadyHasValue)
    elseif d isa Dict && d in l.inline_tables
        return ParserError(ErrAddKeyToInlineTable)
    elseif check_defined && d in l.defined_tables
        return ParserError(ErrDuplicatedKey)
    end
    return nothing
end

```
-/
def check_allowed_add_key (o : Ops X Y E D CI CF) (d : Val X) (check_defined : Bool := true) : PM o Unit := do
  let l ← getP o
  match d with
  | .table r =>
    if l.inline_tables.contains r then
      throwP o (ParserError_1 .ErrAddKeyToInlineTable)
    else if check_defined && l.defined_tables.contains r then
      throwP o (ParserError_1 .ErrDuplicatedKey)
  | _ => throwP o (ParserError_1 .ErrKeyAlreadyHasValue)

/-- The `for i in 1:length(dotted_keys)` loop of `recurse_dict!`. -/
def recurse_dict_loop (o : Ops X Y E D CI CF) (n : Nat) (check define_implicit : Bool) :
    Val X → Nat → List Bytes → PM o TOMLDictRef
  | d, _, [] => match d with
    | .table r => pure r
    | _ => throwT o .typeError
  | d, i, key :: rest => do
    let r ← match d with
      | .table r => pure r
      | _ => throwT o .typeError
    let mut d ← getBang_table o r key
    match d with
    | .vector vr =>
      let v ← getVector o vr
      if v.eltype == .any then
        match v.elems.getLast? with
        | none => throwP o (ParserError_1 .ErrArrayTreatedAsDictionary)
        | some x => d := x
      else
        throwP o (ParserError_1 .ErrKeyAlreadyHasValue)
    | _ => pure ()
    if check then
      -- When called from parse_entry (define_implicit=true), check
      -- defined_tables for ALL intermediates to prevent appending to
      -- tables that were closed by a different [table] section.
      let check_def := if define_implicit then true else i == n
      check_allowed_add_key o d check_def
    if define_implicit then
      match d with
      | .table t => modifyP o fun l => { l with implicit_tables := idPush l.implicit_tables t }
      | _ => pure ()
    recurse_dict_loop o n check define_implicit d (i + 1) rest

/--
Julia source: base/toml/parser.jl:644-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function recurse_dict!(l::Parser, d::Dict, dotted_keys::AbstractVector{String}, check=true, define_implicit=false)::Err{TOMLDict}
    for i in 1:length(dotted_keys)
        d = d::TOMLDict
        key = dotted_keys[i]
        d = get!(TOMLDict, d, key)
        if d isa Vector{Any}
            isempty(d) && return ParserError(ErrArrayTreatedAsDictionary)
            d = d[end]
        elseif d isa Vector
            return ParserError(ErrKeyAlreadyHasValue)
        end
        if check
            # When called from parse_entry (define_implicit=true), check
            # defined_tables for ALL intermediates to prevent appending to
            # tables that were closed by a different [table] section.
            check_def = define_implicit ? true : (i == length(dotted_keys))
            @try check_allowed_add_key(l, d, check_def)
        end
        if define_implicit && d isa TOMLDict
            push!(l.implicit_tables, d)
        end
    end
    return d::TOMLDict
end

```
-/
def recurse_dict (o : Ops X Y E D CI CF) (d : Val X) (dotted_keys : List Bytes) (check : Bool := true)
    (define_implicit : Bool := false) : PM o TOMLDictRef :=
  recurse_dict_loop o dotted_keys.length check define_implicit d 1 dotted_keys

/--
Julia source: base/toml/parser.jl:791-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

########
# Keys #
########

# SPEC: "Bare keys may only contain ASCII letters, ASCII digits, underscores,
# and dashes (A-Za-z0-9_-).
# Note that bare keys are allowed to be composed of only ASCII digits, e.g. 1234,
# but are always interpreted as strings."
@inline isvalid_barekey_char(c::Char) =
    'a' <= c <= 'z' ||
    'A' <= c <= 'Z' ||
    isdigit(c) ||
    c == '-' || c == '_'

```
-/
def isvalid_barekey_char (c : JChar) : Bool :=
  (jc 'a' ≤ c && c ≤ jc 'z') ||
  (jc 'A' ≤ c && c ≤ jc 'Z') ||
  isdigit c ||
  c == jc '-' || c == jc '_'

/--
Julia source: base/toml/parser.jl:1164-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

##########################
# Date / Time / DateTime #
##########################

ok_end_value(c::Char) = iswhitespace(c) || c == '#' || c == EOF_CHAR || c == ']' ||
                               c == '}' || c == ',' || c == '\n'     || c == '\r'
```
-/
def ok_end_value (c : JChar) : Bool :=
  iswhitespace c || c == jc '#' || c == EOF_CHAR || c == jc ']' ||
    c == jc '}' || c == jc ',' || c == jc '\n' || c == jc '\r'

/--
Julia source: base/toml/parser.jl:1378-1382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline stop_candidates_multiline(x)         = x != '"'  &&  x != '\\'
@inline stop_candidates_singleline(x)        = x != '"'  &&  x != '\\' && x != '\n'
@inline stop_candidates_multiline_quoted(x)  = x != '\'' &&  x != '\\'
@inline stop_candidates_singleline_quoted(x) = x != '\'' &&  x != '\\' && x != '\n'

```
-/
def stop_candidates_multiline (x : JChar) : Bool := x != jc '"' && x != jc '\\'
def stop_candidates_singleline (x : JChar) : Bool := x != jc '"' && x != jc '\\' && x != jc '\n'
def stop_candidates_multiline_quoted (x : JChar) : Bool := x != jc '\'' && x != jc '\\'
def stop_candidates_singleline_quoted (x : JChar) : Bool := x != jc '\'' && x != jc '\\' && x != jc '\n'

/--
Julia source: base/toml/parser.jl:1447-1462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take_chunks(l::Parser, unescape::Bool)::String
    nbytes = sum(length, l.chunks; init=0)
    str = Base._string_n(nbytes)
    offset = 1
    for chunk in l.chunks
        # The SubString constructor takes as an index the first byte of the
        # last character but we have the last byte.
        n = length(chunk)
        GC.@preserve str begin
            unsafe_copyto!(pointer(str, offset), pointer(l.str, first(chunk)), n)
        end
        offset += n
    end
    empty!(l.chunks)
    return unescape ? unescape_string(str) : str
end
```
-/
def take_chunks (o : Ops X Y E D CI CF) (unescape : Bool) : PM o Bytes := do
  let l ← getP o
  -- `length(chunk)` of a `UnitRange{Int}`
  let len (c : JInt64 × JInt64) : Int := max 0 (c.2.val - c.1.val + 1)
  let _nbytes := l.chunks.foldl (fun acc c => acc + len c) 0
  -- `Base._string_n(nbytes)`, filled by `unsafe_copyto!` from each chunk
  let str := l.chunks.foldl (fun acc c => acc ++ (l.str.drop (c.1.val.toNat - 1)).take (len c).toNat) []
  modifyP o fun l => { l with chunks := [] }
  if unescape then liftT o (o.unescape_string str) else return str

/--
Julia source: base/toml/parser.jl:1115-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take_string_or_substring(l, contains_underscore)::SubString
    subs = take_substring(l)
    # Need to pass an AbstractString to `parse` so materialize it in case it
    # contains underscore.
    return contains_underscore ? SubString(filter(!=('_'), subs)) : subs
end

```
-/
def take_string_or_substring (o : Ops X Y E D CI CF) (contains_underscore : Bool) : PM o Bytes := do
  let subs ← take_substring o
  -- Need to pass an AbstractString to `parse` so materialize it in case it
  -- contains underscore.
  return if contains_underscore then o.filter_underscore subs else subs

/--
Julia source: base/toml/parser.jl:1122-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_float(l::Parser, contains_underscore)::Err{Float64}
    s = take_string_or_substring(l, contains_underscore)
    v = Base.tryparse(Float64, s)
    v === nothing && return ParserError(ErrGenericValueError)
    return v
end

```
-/
def parse_float (o : Ops X Y E D CI CF) (contains_underscore : Bool) : PM o (JuliaLean.base.float.FV .f64) := do
  let s ← take_string_or_substring o contains_underscore
  let v ← liftT o (o.tryparse_Float64 s)
  match v with
  | none => throwP o (ParserError_1 .ErrGenericValueError)
  | some v => return v

/-- `try … catch e; e isa Base.OverflowError && return ParserError(ErrOverflowError); rethrow() end`. -/
def catchOverflow (o : Ops X Y E D CI CF) {α : Type} : Except (Thrown E) α → PM o α
  | .ok v => pure v
  | .error (.jl (.overflowError _)) => throwP o (ParserError_1 .ErrOverflowError)
  | .error e => throwT o e

/--
Julia source: base/toml/parser.jl:1129-1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_int(l::Parser, contains_underscore, base=nothing)::Err{Int64}
    s = take_string_or_substring(l, contains_underscore)
    v = try
        Base.parse(Int64, s; base=base)
    catch e
        e isa Base.OverflowError && return ParserError(ErrOverflowError)
        rethrow()
    end
    return v
end

```
-/
def parse_int (o : Ops X Y E D CI CF) (contains_underscore : Bool) (base : Option JInt64 := none) : PM o JInt64 := do
  let s ← take_string_or_substring o contains_underscore
  catchOverflow o (o.parse_Int64 s base)

/--
Julia source: base/toml/parser.jl:1140-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (name, T1, T2, n1, n2) in (("integer", Int64,  Int128,  17,  33),
                               ("hex", UInt64, UInt128, 18,  34),
                               ("oct", UInt64, UInt128, 24,  45),
                               ("bin", UInt64, UInt128, 66, 130),
                               )
    @eval function $(Symbol("parse_", name))(l::Parser, contains_underscore, base=nothing)::Err{Union{$(T1), $(T2), BigInt}}
        s = take_string_or_substring(l, contains_underscore)
        len = length(s)
        v = try
            if len ≤ $(n1)
                Base.parse($(T1), s; base)
            elseif $(n1) < len ≤ $(n2)
                Base.parse($(T2), s; base)
            else
                Base.parse(BigInt, s; base)
            end
        catch e
            e isa Base.OverflowError && return ParserError(ErrOverflowError)
            rethrow()
        end
        return v
    end
end

```
-/
-- The `@eval` loop defines `parse_integer`, `parse_hex`, `parse_oct` and `parse_bin`, each an
-- instance of `parse_sized`.
def parse_sized (o : Ops X Y E D CI CF) (n1 n2 : JInt64)
    (parse1 parse2 : Bytes → Option JInt64 → Except (Thrown E) (Val X))
    (contains_underscore : Bool) (base : Option JInt64 := none) : PM o (Val X) := do
  let s ← take_string_or_substring o contains_underscore
  let len := o.length s
  catchOverflow o <|
    if len.val ≤ n1.val then
      parse1 s base
    else if n1.val < len.val && len.val ≤ n2.val then
      parse2 s base
    else
      Val.bigint <$> o.parse_BigInt s base
def parse_integer (o : Ops X Y E D CI CF) (contains_underscore : Bool) (base : Option JInt64 := none) : PM o (Val X) :=
  parse_sized o (i64 17) (i64 33) (fun s b => Val.int64 <$> o.parse_Int64 s b)
    (fun s b => Val.int128 <$> o.parse_Int128 s b) contains_underscore base
def parse_hex (o : Ops X Y E D CI CF) (contains_underscore : Bool) (base : Option JInt64 := none) : PM o (Val X) :=
  parse_sized o (i64 18) (i64 34) (fun s b => Val.uint64 <$> o.parse_UInt64 s b)
    (fun s b => Val.uint128 <$> o.parse_UInt128 s b) contains_underscore base
def parse_oct (o : Ops X Y E D CI CF) (contains_underscore : Bool) (base : Option JInt64 := none) : PM o (Val X) :=
  parse_sized o (i64 24) (i64 45) (fun s b => Val.uint64 <$> o.parse_UInt64 s b)
    (fun s b => Val.uint128 <$> o.parse_UInt128 s b) contains_underscore base
def parse_bin (o : Ops X Y E D CI CF) (contains_underscore : Bool) (base : Option JInt64 := none) : PM o (Val X) :=
  parse_sized o (i64 66) (i64 130) (fun s b => Val.uint64 <$> o.parse_UInt64 s b)
    (fun s b => Val.uint128 <$> o.parse_UInt128 s b) contains_underscore base

/--
Julia source: base/toml/parser.jl:963-970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

###########
# Numbers #
###########

parse_inf(l::Parser, sgn::Int) = accept(l, 'n') && accept(l, 'f') ? sgn * Inf : nothing
parse_nan(l::Parser) = accept(l, 'a') && accept(l, 'n') ? NaN : nothing

```
-/
def parse_inf (o : Ops X Y E D CI CF) (sgn : JInt64) : PM o (Option (Val X)) := do
  if (← accept o (chr 'n')) then
    if (← accept o (chr 'f')) then
      -- `sgn * Inf` promotes `sgn` to `Float64`
      return some (.float64 (JuliaLean.base.float.mul_float (JuliaLean.base.float.float_BitSigned64 .f64 sgn)
        JuliaLean.base.float.Inf))
  return none
def parse_nan (o : Ops X Y E D CI CF) : PM o (Option (Val X)) := do
  if (← accept o (chr 'a')) then
    if (← accept o (chr 'n')) then
      return some (.float64 JuliaLean.base.float.NaN)
  return none

/--
Julia source: base/toml/parser.jl:971-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_bool(l::Parser, v::Bool)::Union{Bool, Nothing}
    # Have eaten a 't' if `v` is true, otherwise have eaten a `f`.
    v ? (accept(l, 'r') && accept(l, 'u') && accept(l, 'e') && return true) :
        (accept(l, 'a') && accept(l, 'l') && accept(l, 's') && accept(l, 'e') && return false)
    return nothing
end

```
-/
def parse_bool (o : Ops X Y E D CI CF) (v : Bool) : PM o (Option Bool) := do
  -- Have eaten a 't' if `v` is true, otherwise have eaten a `f`.
  if v then
    if (← accept o (chr 'r')) then
      if (← accept o (chr 'u')) then
        if (← accept o (chr 'e')) then
          return some true
  else
    if (← accept o (chr 'a')) then
      if (← accept o (chr 'l')) then
        if (← accept o (chr 's')) then
          if (← accept o (chr 'e')) then
            return some false
  return none

/--
Julia source: base/toml/parser.jl:978-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid_hex(c::Char) = isdigit(c) || ('a' <= c <= 'f') || ('A' <= c <= 'F')
isvalid_oct(c::Char) = '0' <= c <= '7'
isvalid_binary(c::Char) = '0' <= c <= '1'

```
-/
def isvalid_hex (c : JChar) : Bool := isdigit c || (jc 'a' ≤ c && c ≤ jc 'f') || (jc 'A' ≤ c && c ≤ jc 'F')
def isvalid_oct (c : JChar) : Bool := jc '0' ≤ c && c ≤ jc '7'
def isvalid_binary (c : JChar) : Bool := jc '0' ≤ c && c ≤ jc '1'

/-- The `while true` loop of `accept_batch_underscore`. -/
def accept_batch_underscore_loop (o : Ops X Y E D CI CF) (f : JChar → Bool)
    (fail_if_underscore contains_underscore at_least_one last_underscore : Bool) : PM o (Bool × Bool) := do
  let c ← peek o
  if c == jc '_' then
    if fail_if_underscore then
      throwP o (ParserError_1 .ErrUnderscoreNotSurroundedByDigits)
    discard (eat_char o)
    accept_batch_underscore_loop o f true true at_least_one true
  else
    -- SPEC:  "Each underscore must be surrounded by at least one digit on each side."
    if f c then
      discard (eat_char o)
      accept_batch_underscore_loop o f false contains_underscore true false
    else
      if last_underscore then
        throwP o (ParserError_1 .ErrTrailingUnderscoreNumber)
      return (at_least_one, contains_underscore)
partial_fixpoint

/--
Julia source: base/toml/parser.jl:982-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ValidSigs = Union{typeof(isvalid_hex), typeof(isvalid_oct), typeof(isvalid_binary), typeof(isdigit)}
# This function eats things accepted by `f` but also allows eating `_` in between
# digits. Returns if it ate at least one character and if it ate an underscore
function accept_batch_underscore(l::Parser, f::ValidSigs, fail_if_underscore=true)::Err{Tuple{Bool, Bool}}
    contains_underscore = false
    at_least_one = false
    last_underscore = false
    while true
        c = peek(l)
        if c == '_'
            contains_underscore = true
            if fail_if_underscore
                return ParserError(ErrUnderscoreNotSurroundedByDigits)
            end
            eat_char(l)
            fail_if_underscore = true
            last_underscore = true
        else
            # SPEC:  "Each underscore must be surrounded by at least one digit on each side."
            fail_if_underscore = false
            if f(c)
                at_least_one = true
                eat_char(l)
            else
                if last_underscore
                    return ParserError(ErrTrailingUnderscoreNumber)
                end
                return at_least_one, contains_underscore
            end
            last_underscore = false
        end
    end
end

```
-/
-- `f` is one of `isvalid_hex`, `isvalid_oct`, `isvalid_binary`, `isdigit` (`ValidSigs`).
def accept_batch_underscore (o : Ops X Y E D CI CF) (f : JChar → Bool) (fail_if_underscore : Bool := true) :
    PM o (Bool × Bool) :=
  accept_batch_underscore_loop o f fail_if_underscore false false false

/--
Julia source: base/toml/parser.jl:1171-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

#=
# https://tools.ietf.org/html/rfc3339

# Internet Protocols MUST generate four digit years in dates.

   date-fullyear   = 4DIGIT
   date-month      = 2DIGIT  ; 01-12
   date-mday       = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on
                             ; month/year
   time-hour       = 2DIGIT  ; 00-23
   time-minute     = 2DIGIT  ; 00-59
   time-second     = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second
                             ; rules
   time-secfrac    = "." 1*DIGIT
   time-numoffset  = ("+" / "-") time-hour ":" time-minute
   time-offset     = "Z" / time-numoffset

   partial-time    = time-hour ":" time-minute ":" time-second
                     [time-secfrac]
   full-date       = date-fullyear "-" date-month "-" date-mday
   full-time       = partial-time time-offset

   date-time       = full-date "T" full-time
=#

accept_two(l, f::F) where {F} = accept_n(l, 2, f) || return(ParserError(ErrParsingDateTime))
```
-/
def accept_two (o : Ops X Y E D CI CF) (f : Acc) : PM o Bool := do
  if (← accept_n o (i64 2) f) then return true
  throwP o (ParserError_1 .ErrParsingDateTime)

/-- `x in lo:hi` of an `Err{Int}` value: a `ParserError` is in no range. -/
def inRange (x : Err JInt64) (lo hi : Int) : Bool :=
  match x with
  | .ok v => lo ≤ v.val && v.val ≤ hi
  | .error _ => false

/-- An `Err{Int}` used as an `Int`. -/
def assertInt (o : Ops X Y E D CI CF) : Err JInt64 → PM o JInt64
  | .ok v => pure v
  | .error _ => throwT o .typeError

/--
Julia source: base/toml/parser.jl:1302-1354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _parse_local_time(l::Parser, skip_hour=false)::Err{NTuple{4, Int64}}
    # Hour has potentially been already parsed in
    # `parse_number_or_date_start` already
    if skip_hour
        hour = Int64(0)
    else
        set_marker!(l)
        @try accept_two(l, isdigit)
        hour = parse_int(l, false)
        hour in 0:23 || return ParserError(ErrParsingDateTime)
    end

    accept(l, ':') || return ParserError(ErrParsingDateTime)

    # minute
    set_marker!(l)
    @try accept_two(l, isdigit)
    minute = parse_int(l, false)
    minute in 0:59 || return ParserError(ErrParsingDateTime)

    # seconds are optional in TOML v1.1
    second = Int64(0)
    millisecond = Int64(0)
    if accept(l, ':')
        # second
        set_marker!(l)
        @try accept_two(l, isdigit)
        second = parse_int(l, false)
        second in 0:59 || return ParserError(ErrParsingDateTime)

        # optional fractional second
        if accept(l, '.')
            set_marker!(l)
            found_fractional_digit = false
            for _ in 1:3
                found_fractional_digit |= accept(l, isdigit)
            end
            if !found_fractional_digit
                return ParserError(ErrParsingDateTime)
            end
            # DateTime in base only manages 3 significant digits in fractional
            # second. Interpret parsed digits as fractional seconds and scale to
            # milliseconds precision (e.g., ".2" => 200ms, ".20" => 200ms).
            ndigits = l.prevpos - l.marker
            fractional_second = parse_int(l, false)::Int64
            millisecond = fractional_second * 10^(3 - ndigits)
            # Truncate off the rest eventual digits
            accept_batch(l, isdigit)
        end
    end
    return hour, minute, second, millisecond
end

```
-/
def _parse_local_time (o : Ops X Y E D CI CF) (skip_hour : Bool := false) :
    PM o (JInt64 × JInt64 × JInt64 × JInt64) := do
  -- Hour has potentially been already parsed in
  -- `parse_number_or_date_start` already
  let hour ← if skip_hour then pure (Except.ok (i64 0)) else do
      set_marker o
      discard (accept_two o (.fn isdigit))
      let hour ← observe o (parse_int o false)
      if !inRange hour 0 23 then throwP o (ParserError_1 .ErrParsingDateTime)
      pure hour
  if !(← accept o (chr ':')) then throwP o (ParserError_1 .ErrParsingDateTime)
  -- minute
  set_marker o
  discard (accept_two o (.fn isdigit))
  let minute ← observe o (parse_int o false)
  if !inRange minute 0 59 then throwP o (ParserError_1 .ErrParsingDateTime)
  -- seconds are optional in TOML v1.1
  let mut second : Err JInt64 := .ok (i64 0)
  let mut millisecond := i64 0
  if (← accept o (chr ':')) then
    -- second
    set_marker o
    discard (accept_two o (.fn isdigit))
    second ← observe o (parse_int o false)
    if !inRange second 0 59 then throwP o (ParserError_1 .ErrParsingDateTime)
    -- optional fractional second
    if (← accept o (chr '.')) then
      set_marker o
      let mut found_fractional_digit := false
      found_fractional_digit := found_fractional_digit || (← accept o (.fn isdigit))
      found_fractional_digit := found_fractional_digit || (← accept o (.fn isdigit))
      found_fractional_digit := found_fractional_digit || (← accept o (.fn isdigit))
      if !found_fractional_digit then throwP o (ParserError_1 .ErrParsingDateTime)
      let l ← getP o
      let ndigits := i64 (l.prevpos.val - l.marker.val)
      let fractional_second ← assertInt o (← observe o (parse_int o false))
      let p ← liftT o (o.pow_Int (i64 10) (i64 (3 - ndigits.val)))
      millisecond := i64 (fractional_second.val * p.val)
      -- Truncate off the rest eventual digits
      discard (accept_batch o (.fn isdigit))
  -- `Err{NTuple{4, Int64}}`: converting a `ParserError` element fails
  return (← assertInt o hour, ← assertInt o minute, ← assertInt o second, millisecond)

/--
Julia source: base/toml/parser.jl:1252-1264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_return_datetime(::Parser{Dates}, year, month, day, h, m, s, ms) where Dates
    if Dates !== nothing
        try
            return Dates.DateTime(year, month, day, h, m, s, ms)
        catch ex
            ex isa ArgumentError && return ParserError(ErrParsingDateTime)
            rethrow()
        end
    else
        return DateTime(year, month, day, h, m, s, ms)
    end
end

```
-/
def try_return_datetime (o : Ops X Y E D CI CF) (year month day h m s ms : JInt64) : PM o (Val X) := do
  match o.dates with
  | some dates =>
    match dates.DateTime year month day h m s ms with
    | .ok x => return .dates x
    | .error (.jl (.argumentError _)) => throwP o (ParserError_1 .ErrParsingDateTime)
    | .error e => throwT o e
  | none => return .datetime (DateTime_7 year month day h m s ms)

/--
Julia source: base/toml/parser.jl:1265-1277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_return_date(::Parser{Dates}, year, month, day) where Dates
    if Dates !== nothing
        try
            return Dates.Date(year, month, day)
        catch ex
            ex isa ArgumentError && return ParserError(ErrParsingDateTime)
            rethrow()
        end
    else
        return Date(year, month, day)
    end
end

```
-/
def try_return_date (o : Ops X Y E D CI CF) (year month day : JInt64) : PM o (Val X) := do
  match o.dates with
  | some dates =>
    match dates.Date year month day with
    | .ok x => return .dates x
    | .error (.jl (.argumentError _)) => throwP o (ParserError_1 .ErrParsingDateTime)
    | .error e => throwT o e
  | none => return .date ⟨year, month, day⟩

/--
Julia source: base/toml/parser.jl:1289-1301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_return_time(::Parser{Dates}, h, m, s, ms) where Dates
    if Dates !== nothing
        try
            return Dates.Time(h, m, s, ms)
        catch ex
            ex isa ArgumentError && return ParserError(ErrParsingDateTime)
            rethrow()
        end
    else
        return Time(h, m, s, ms)
    end
end

```
-/
def try_return_time (o : Ops X Y E D CI CF) (h m s ms : JInt64) : PM o (Val X) := do
  match o.dates with
  | some dates =>
    match dates.Time h m s ms with
    | .ok x => return .dates x
    | .error (.jl (.argumentError _)) => throwP o (ParserError_1 .ErrParsingDateTime)
    | .error e => throwT o e
  | none => return .time ⟨h, m, s, ms⟩

/--
Julia source: base/toml/parser.jl:1278-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_local_time(l::Parser)
    # SPEC: partial-time = time-hour ":" ... where time-hour = 2DIGIT
    (l.prevpos - l.marker) == 2 || return ParserError(ErrParsingDateTime)
    h = @try parse_int(l, false)
    h in 0:23 || return ParserError(ErrParsingDateTime)
    _, m, s, ms = @try _parse_local_time(l, true)
    # TODO: Could potentially parse greater accuracy for the
    # fractional seconds here.
    return try_return_time(l, h, m, s, ms)
end

```
-/
def parse_local_time (o : Ops X Y E D CI CF) : PM o (Val X) := do
  -- SPEC: partial-time = time-hour ":" ... where time-hour = 2DIGIT
  let l ← getP o
  if !((i64 (l.prevpos.val - l.marker.val)).val == 2) then throwP o (ParserError_1 .ErrParsingDateTime)
  let h ← parse_int o false
  if !(0 ≤ h.val && h.val ≤ 23) then throwP o (ParserError_1 .ErrParsingDateTime)
  let (_, m, s, ms) ← _parse_local_time o true
  try_return_time o h m s ms

/--
Julia source: base/toml/parser.jl:1198-1251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_datetime(l)
    # Year has already been eaten when we reach here
    year_start = l.marker
    year = @try parse_int(l, false)
    # SPEC: date-fullyear = 4DIGIT (exactly 4 digits required)
    (l.prevpos - year_start) == 4 || return ParserError(ErrParsingDateTime)

    # Month
    accept(l, '-') || return ParserError(ErrParsingDateTime)
    set_marker!(l)
    @try accept_two(l, isdigit)
    month = @try parse_int(l, false)
    month in 1:12 || return ParserError(ErrParsingDateTime)
    accept(l, '-') || return ParserError(ErrParsingDateTime)

    # Day
    set_marker!(l)
    @try accept_two(l, isdigit)
    day = @try parse_int(l, false)
    # Verify the real range in the constructor below
    day in 1:31 || return ParserError(ErrParsingDateTime)

    # We might have a local date now
    read_space = false
    if ok_end_value(peek(l))
        if (read_space = accept(l, ' '))
            if !isdigit(peek(l))
                return try_return_date(l, year, month, day)
            end
        else
            return try_return_date(l, year, month, day)
        end
    end
    if !read_space
        accept(l, 'T') || accept(l, 't') || return ParserError(ErrParsingDateTime)
    end

    h, m, s, ms = @try _parse_local_time(l)

    # Julia doesn't support offset times
    if !accept(l, 'Z')
        if accept(l, '+') || accept(l, '-')
            return ParserError(ErrOffsetDateNotSupported)
        end
    end

    if !ok_end_value(peek(l))
        return ParserError(ErrParsingDateTime)
    end

    # The DateTime parser verifies things like leap year for us
    return try_return_datetime(l, year, month, day, h, m, s, ms)
end

```
-/
def parse_datetime (o : Ops X Y E D CI CF) : PM o (Val X) := do
  -- Year has already been eaten when we reach here
  let year_start := (← getP o).marker
  let year ← parse_int o false
  -- SPEC: date-fullyear = 4DIGIT (exactly 4 digits required)
  if !((i64 ((← getP o).prevpos.val - year_start.val)).val == 4) then throwP o (ParserError_1 .ErrParsingDateTime)
  -- Month
  if !(← accept o (chr '-')) then throwP o (ParserError_1 .ErrParsingDateTime)
  set_marker o
  discard (accept_two o (.fn isdigit))
  let month ← parse_int o false
  if !(1 ≤ month.val && month.val ≤ 12) then throwP o (ParserError_1 .ErrParsingDateTime)
  if !(← accept o (chr '-')) then throwP o (ParserError_1 .ErrParsingDateTime)
  -- Day
  set_marker o
  discard (accept_two o (.fn isdigit))
  let day ← parse_int o false
  -- Verify the real range in the constructor below
  if !(1 ≤ day.val && day.val ≤ 31) then throwP o (ParserError_1 .ErrParsingDateTime)
  -- We might have a local date now
  let mut read_space := false
  if ok_end_value (← peek o) then
    read_space ← accept o (chr ' ')
    if read_space then
      if !isdigit (← peek o) then
        return (← try_return_date o year month day)
    else
      return (← try_return_date o year month day)
  if !read_space then
    if !(← accept o (chr 'T')) then
      if !(← accept o (chr 't')) then
        throwP o (ParserError_1 .ErrParsingDateTime)
  let (h, m, s, ms) ← _parse_local_time o
  -- Julia doesn't support offset times
  if !(← accept o (chr 'Z')) then
    if (← accept o (chr '+')) then
      throwP o (ParserError_1 .ErrOffsetDateNotSupported)
    else
      if (← accept o (chr '-')) then
        throwP o (ParserError_1 .ErrOffsetDateNotSupported)
  if !ok_end_value (← peek o) then
    throwP o (ParserError_1 .ErrParsingDateTime)
  -- The DateTime parser verifies things like leap year for us
  try_return_datetime o year month day h m s ms

/--
Julia source: base/toml/parser.jl:1016-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_number_or_date_start(l::Parser)
    set_marker!(l)
    sgn = 1
    parsed_sign = false
    if accept(l, '+')
        parsed_sign = true
    elseif accept(l, '-')
        parsed_sign = true
        sgn = -1
    end
    if accept(l, 'i')
        return parse_inf(l, sgn)
    elseif accept(l, 'n')
        return parse_nan(l)
    end

    if accept(l, '.')
        return ParserError(ErrLeadingDot)
    end

    # Zero is allowed to follow by a end value char, a base x, o, b or a dot
    readed_zero = false
    if accept(l, '0')
        readed_zero = true # Intentional bad grammar to remove the ambiguity in "read"...
        if ok_end_value(peek(l))
            return Int64(0)
        elseif accept(l, 'x')
            parsed_sign && return ParserError(ErrSignInNonBase10Number)
            ate, contains_underscore = @try accept_batch_underscore(l, isvalid_hex)
            ate && return parse_hex(l, contains_underscore)
        elseif accept(l, 'o')
            parsed_sign && return ParserError(ErrSignInNonBase10Number)
            ate, contains_underscore = @try accept_batch_underscore(l, isvalid_oct)
            ate && return parse_oct(l, contains_underscore)
        elseif accept(l, 'b')
            parsed_sign && return ParserError(ErrSignInNonBase10Number)
            ate, contains_underscore = @try accept_batch_underscore(l, isvalid_binary)
            ate && return parse_bin(l, contains_underscore)
        elseif accept(l, isdigit)
            # Could be a local time (00:30) or a zero-padded date (0001-01-01).
            # Consume remaining digits, then check for ':' or '-'.
            accept_batch(l, isdigit)
            if peek(l) == ':'
                return parse_local_time(l)
            elseif peek(l) == '-'
                return parse_datetime(l)
            else
                return ParserError(ErrLeadingZeroNotAllowedInteger)
            end
        end
    end

    read_underscore = false
    read_digit = accept(l, isdigit)
    if !readed_zero && !read_digit
        if peek(l) == EOF_CHAR
            return ParserError(ErrUnexpectedEofExpectedValue)
        else
            return ParserError(ErrUnexpectedStartOfValue)
        end
    end
    ate, contains_underscore = @try accept_batch_underscore(l, isdigit, readed_zero)
    read_underscore |= contains_underscore
    if (read_digit || ate) && ok_end_value(peek(l))
        return parse_integer(l, contains_underscore)
    end
    # Done with integers here

    if !read_underscore
        # No underscores in date / times
        if peek(l) == '-'
            return parse_datetime(l)
        elseif peek(l) == ':'
            return parse_local_time(l)
        end
    end
    # Done with datetime / localtime here

    # can optionally read a . + digits and then exponent
    ate_dot = accept(l, '.')
    ate, contains_underscore = @try accept_batch_underscore(l, isdigit, true)
    if ate_dot && !ate
        return ParserError(ErrNoTrailingDigitAfterDot)
    end
    read_underscore |= contains_underscore
    if accept(l, x -> x == 'e' || x == 'E')
        accept(l, x-> x == '+' || x == '-')
        # SPEC: (which follows the same rules as decimal integer values but may include leading zeros)
        read_digit = accept_batch(l, isdigit)
        _, read_underscore = @try accept_batch_underscore(l, isdigit, !read_digit)
    end
    if !ok_end_value(peek(l))
        eat_char(l)
        return ParserError(ErrGenericValueError)
    end
    return parse_float(l, read_underscore)
end


```
-/
def parse_number_or_date_start (o : Ops X Y E D CI CF) : PM o (Option (Val X)) := do
  set_marker o
  let mut sgn := i64 1
  let mut parsed_sign := false
  if (← accept o (chr '+')) then
    parsed_sign := true
  else
    if (← accept o (chr '-')) then
      parsed_sign := true
      sgn := i64 (-1)
  if (← accept o (chr 'i')) then
    return (← parse_inf o sgn)
  else
    if (← accept o (chr 'n')) then
      return (← parse_nan o)
  if (← accept o (chr '.')) then
    throwP o (ParserError_1 .ErrLeadingDot)
  -- Zero is allowed to follow by a end value char, a base x, o, b or a dot
  let mut readed_zero := false
  if (← accept o (chr '0')) then
    readed_zero := true -- Intentional bad grammar to remove the ambiguity in "read"...
    if ok_end_value (← peek o) then
      return some (.int64 (i64 0))
    else
      if (← accept o (chr 'x')) then
        if parsed_sign then throwP o (ParserError_1 .ErrSignInNonBase10Number)
        let (ate, contains_underscore) ← accept_batch_underscore o isvalid_hex
        if ate then return some (← parse_hex o contains_underscore)
      else
        if (← accept o (chr 'o')) then
          if parsed_sign then throwP o (ParserError_1 .ErrSignInNonBase10Number)
          let (ate, contains_underscore) ← accept_batch_underscore o isvalid_oct
          if ate then return some (← parse_oct o contains_underscore)
        else
          if (← accept o (chr 'b')) then
            if parsed_sign then throwP o (ParserError_1 .ErrSignInNonBase10Number)
            let (ate, contains_underscore) ← accept_batch_underscore o isvalid_binary
            if ate then return some (← parse_bin o contains_underscore)
          else
            if (← accept o (.fn isdigit)) then
              -- Could be a local time (00:30) or a zero-padded date (0001-01-01).
              -- Consume remaining digits, then check for ':' or '-'.
              discard (accept_batch o (.fn isdigit))
              if (← peek o) == jc ':' then
                return some (← parse_local_time o)
              else if (← peek o) == jc '-' then
                return some (← parse_datetime o)
              else
                throwP o (ParserError_1 .ErrLeadingZeroNotAllowedInteger)
  let mut read_underscore := false
  let read_digit ← accept o (.fn isdigit)
  if !readed_zero && !read_digit then
    if (← peek o) == EOF_CHAR then
      throwP o (ParserError_1 .ErrUnexpectedEofExpectedValue)
    else
      throwP o (ParserError_1 .ErrUnexpectedStartOfValue)
  let (ate, contains_underscore) ← accept_batch_underscore o isdigit readed_zero
  read_underscore := read_underscore || contains_underscore
  if (read_digit || ate) && ok_end_value (← peek o) then
    return some (← parse_integer o contains_underscore)
  -- Done with integers here
  if !read_underscore then
    -- No underscores in date / times
    if (← peek o) == jc '-' then
      return some (← parse_datetime o)
    else if (← peek o) == jc ':' then
      return some (← parse_local_time o)
  -- Done with datetime / localtime here
  -- can optionally read a . + digits and then exponent
  let ate_dot ← accept o (chr '.')
  let (ate, contains_underscore) ← accept_batch_underscore o isdigit true
  if ate_dot && !ate then
    throwP o (ParserError_1 .ErrNoTrailingDigitAfterDot)
  read_underscore := read_underscore || contains_underscore
  if (← accept o (.fn fun x => x == jc 'e' || x == jc 'E')) then
    discard (accept o (.fn fun x => x == jc '+' || x == jc '-'))
    -- SPEC: (which follows the same rules as decimal integer values but may include leading zeros)
    let read_digit ← accept_batch o (.fn isdigit)
    let (_, ru) ← accept_batch_underscore o isdigit !read_digit
    read_underscore := ru
  if !ok_end_value (← peek o) then
    discard (eat_char o)
    throwP o (ParserError_1 .ErrGenericValueError)
  return some (.float64 (← parse_float o read_underscore))

/-- The `while true` loop of `parse_string_continue`. -/
def parse_string_continue_loop (o : Ops X Y E D CI CF) (multiline quoted : Bool) (q : JChar) (offset : Int)
    (start_chunk : JInt64) (contains_backslash : Bool) : PM o Bytes := do
  if (← peek o) == EOF_CHAR then
    throwP o (ParserError_1 .ErrUnexpectedEndString)
  if quoted then
    discard (accept_batch o (.fn (if multiline then stop_candidates_multiline_quoted else stop_candidates_singleline_quoted)))
  else
    discard (accept_batch o (.fn (if multiline then stop_candidates_multiline else stop_candidates_singleline)))
  if !multiline && (← peek o) == jc '\n' then
    throwP o (ParserError_1 .ErrNewLineInString)
  let next_slash := (← peek o) == jc '\\'
  if !next_slash then
    -- `accept(l, q) && (!multiline || (accept(l, q) && accept(l, q)))`
    let closed ← do
      if (← accept o (.ch q)) then
        if !multiline then pure true
        else
          if (← accept o (.ch q)) then accept o (.ch q) else pure false
      else pure false
    if closed then
      modifyP o fun l => { l with chunks := l.chunks ++ [(start_chunk, i64 (l.prevpos.val - offset - 1))] }
      return (← take_chunks o contains_backslash)
  let c ← eat_char o -- eat the character we stopped at
  let next_slash := c == jc '\\'
  let mut start_chunk := start_chunk
  let mut contains_backslash := contains_backslash
  if next_slash && !quoted then
    let p ← peek o
    if p == jc '\n' || p == jc '\r' then
      modifyP o fun l => { l with chunks := l.chunks ++ [(start_chunk, i64 (l.prevpos.val - 1 - 1))] } -- -1 due to eating the slash
      discard (skip_ws_nl_no_comment o)
      start_chunk := (← getP o).prevpos
    else
      let c ← eat_char o -- eat the escaped character
      if c == jc 'x' || c == jc 'u' || c == jc 'U' then
        let n : Int := if c == jc 'x' then 2 else if c == jc 'u' then 4 else 8
        set_marker o
        if !(← accept_n o (i64 n) (.fn isvalid_hex)) then
          throwP o (ParserError_1 .ErrInvalidUnicodeScalar)
        let codepoint ← assertInt o (← observe o (parse_int o false (some (i64 16))))
        if c == jc 'x' then
          -- \xHH is always valid (0x00-0xFF)
          pure ()
        else if !(codepoint.val ≤ 0xD7FF || (0xE000 ≤ codepoint.val && codepoint.val ≤ 0x10FFFF)) then
          throwP o (ParserError_1 .ErrInvalidUnicodeScalar)
      else if c != jc 'b' && c != jc 't' && c != jc 'n' && c != jc 'f' && c != jc 'r' && c != jc 'e' &&
          c != jc '"' && c != jc '\\' then
        throwP o (ParserError_1 .ErrInvalidEscapeCharacter)
      contains_backslash := true
  parse_string_continue_loop o multiline quoted q offset start_chunk contains_backslash
partial_fixpoint

/--
Julia source: base/toml/parser.jl:1383-1446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_string_continue(l::Parser, multiline::Bool, quoted::Bool)::Err{String}
    start_chunk = l.prevpos
    q = quoted ? '\'' : '"'
    contains_backslash = false
    offset = multiline ? 3 : 1
    while true
        if peek(l) == EOF_CHAR
            return ParserError(ErrUnexpectedEndString)
        end
        if quoted
            accept_batch(l, multiline ? stop_candidates_multiline_quoted : stop_candidates_singleline_quoted)
        else
            accept_batch(l, multiline ? stop_candidates_multiline : stop_candidates_singleline)
        end
        if !multiline && peek(l) == '\n'
            return ParserError(ErrNewLineInString)
        end
        next_slash = peek(l) == '\\'
        if !next_slash
            # TODO: Doesn't handle values with e.g. format `""""str""""`
            if accept(l, q) && (!multiline || (accept(l, q) && accept(l, q)))
                push!(l.chunks, start_chunk:(l.prevpos-offset-1))
                return take_chunks(l, contains_backslash)
            end
        end
        c = eat_char(l) # eat the character we stopped at
        next_slash = c == '\\'
        if next_slash && !quoted
            if peek(l) == '\n' || peek(l) == '\r'
                push!(l.chunks, start_chunk:(l.prevpos-1-1)) # -1 due to eating the slash
                skip_ws_nl_no_comment(l)
                start_chunk = l.prevpos
            else
                c = eat_char(l) # eat the escaped character
                if c == 'x' || c == 'u' || c == 'U'
                    n = c == 'x' ? 2 :
                        c == 'u' ? 4 : 8
                    set_marker!(l)
                    if !accept_n(l, n, isvalid_hex)
                        return ParserError(ErrInvalidUnicodeScalar)
                    end
                    codepoint = parse_int(l, false, 16)::Int64
                    #=
                    Unicode Scalar Value
                    ---------------------
                    Any Unicode code point except high-surrogate and
                    low-surrogate code points.  In other words, the ranges of
                    integers 0 to D7FF16 and E00016 to 10FFFF16 inclusive.
                    For \x, the range is 0x00-0xFF (U+0000-U+00FF).
                    =#
                    if c == 'x'
                        # \xHH is always valid (0x00-0xFF)
                    elseif !(codepoint <= 0xD7FF || 0xE000 <= codepoint <= 0x10FFFF)
                        return ParserError(ErrInvalidUnicodeScalar)
                    end
                elseif c != 'b' && c != 't' && c != 'n' && c != 'f' && c != 'r' && c != 'e' && c != '"' && c!= '\\'
                    return ParserError(ErrInvalidEscapeCharacter)
                end
                contains_backslash = true
            end
        end
    end
end

```
-/
def parse_string_continue (o : Ops X Y E D CI CF) (multiline quoted : Bool) : PM o Bytes := do
  let start_chunk := (← getP o).prevpos
  let q := if quoted then jc '\'' else jc '"'
  let contains_backslash := false
  let offset : Int := if multiline then 3 else 1
  parse_string_continue_loop o multiline quoted q offset start_chunk contains_backslash

/--
Julia source: base/toml/parser.jl:1355-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

##########
# String #
##########

function parse_string_start(l::Parser, quoted::Bool; allow_multiline::Bool=true)::Err{String}
    # Have eaten a `'` if `quoted` is true, otherwise have eaten a `"`
    multiline = false
    c = quoted ? '\'' : '"'
    if accept(l, c) # Eat second quote
        if !accept(l, c)
            return ""
        end
        if !allow_multiline
            return ParserError(ErrMultilineStringAsKey)
        end
        accept(l, '\r') # Eat optional carriage return after opening triple quote
        accept(l, '\n') # Eat optional newline after opening triple quote
        multiline = true
    end
    return parse_string_continue(l, multiline, quoted)
end

```
-/
def parse_string_start (o : Ops X Y E D CI CF) (quoted : Bool) (allow_multiline : Bool := true) : PM o Bytes := do
  -- Have eaten a `'` if `quoted` is true, otherwise have eaten a `"`
  let mut multiline := false
  let c := if quoted then jc '\'' else jc '"'
  if (← accept o (.ch c)) then -- Eat second quote
    if !(← accept o (.ch c)) then
      return []
    if !allow_multiline then
      throwP o (ParserError_1 .ErrMultilineStringAsKey)
    discard (accept o (chr '\r')) -- Eat optional carriage return after opening triple quote
    discard (accept o (chr '\n')) -- Eat optional newline after opening triple quote
    multiline := true
  parse_string_continue o multiline quoted

/--
Julia source: base/toml/parser.jl:812-846 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Recursively add dotted keys to `l.dotted_key`
function _parse_key(l::Parser)
    skip_ws(l)
    # SPEC: "A bare key must be non-empty,"
    if isempty(l.dotted_keys) && accept(l, '=')
        return ParserError(ErrEmptyBareKey)
    end
    keyval = if accept(l, '"')
        @try parse_string_start(l, false; allow_multiline=false)
    elseif accept(l, '\'')
        @try parse_string_start(l, true; allow_multiline=false)
    else
        set_marker!(l)
        if accept_batch(l, isvalid_barekey_char)
            if !(peek(l) == '.' || iswhitespace(peek(l)) || peek(l) == ']' || peek(l) == '=')
                c = eat_char(l)
                return ParserError(ErrInvalidBareKeyCharacter, c)
            end
            String(take_substring(l))
        else
            c = eat_char(l)
            return ParserError(ErrInvalidBareKeyCharacter, c)
        end
    end
    new_key = keyval
    push!(l.dotted_keys, new_key)
    # SPEC: "Whitespace around dot-separated parts is ignored."
    skip_ws(l)
    if accept(l, '.')
        skip_ws(l)
        @try _parse_key(l)
    end
    return l.dotted_keys
end

```
-/
def _parse_key (o : Ops X Y E D CI CF) : PM o (List Bytes) := do
  discard (skip_ws o)
  -- SPEC: "A bare key must be non-empty,"
  if (← getP o).dotted_keys.isEmpty then
    if (← accept o (chr '=')) then
      throwP o (ParserError_1 .ErrEmptyBareKey)
  let keyval ← do
    if (← accept o (chr '"')) then
      parse_string_start o false (allow_multiline := false)
    else
      if (← accept o (chr '\'')) then
        parse_string_start o true (allow_multiline := false)
      else
        set_marker o
        if (← accept_batch o (.fn isvalid_barekey_char)) then
          let p ← peek o
          if !(p == jc '.' || iswhitespace p || p == jc ']' || p == jc '=') then
            let c ← eat_char o
            throwP o (ParserError_2 .ErrInvalidBareKeyCharacter (some c))
          take_substring o
        else
          let c ← eat_char o
          throwP o (ParserError_2 .ErrInvalidBareKeyCharacter (some c))
  let new_key := keyval
  modifyP o fun l => { l with dotted_keys := l.dotted_keys ++ [new_key] }
  -- SPEC: "Whitespace around dot-separated parts is ignored."
  discard (skip_ws o)
  if (← accept o (chr '.')) then
    discard (skip_ws o)
    let _ ← _parse_key o
    pure ()
  return (← getP o).dotted_keys
partial_fixpoint

/--
Julia source: base/toml/parser.jl:806-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Current key...
function parse_key(l::Parser)
    empty!(l.dotted_keys)
    _parse_key(l)
end

```
-/
def parse_key (o : Ops X Y E D CI CF) : PM o (List Bytes) := do
  modifyP o fun l => { l with dotted_keys := [] }
  _parse_key o

/-- The `T` loop of `parse_array`: `T` becomes `Any` at the first element of another type. -/
def array_type_loop (o : Ops X Y E D CI CF) (T : VType Y) : List (Val X) → PM o (VType Y)
  | [] => pure T
  | el :: rest => do
    if !VType.eq (yEq o) (← typeofVal o el) T then return .any
    array_type_loop o T rest

/-- The `b[i]::T` checks of `copyto_typed!`. -/
def check_typed (o : Ops X Y E D CI CF) (T : VType Y) : List (Val X) → PM o Unit
  | [] => pure ()
  | x :: xs => do
    if !VType.eq (yEq o) (← typeofVal o x) T then throwT o .typeError
    check_typed o T xs

/--
Julia source: base/toml/parser.jl:874-885 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

#########
# Array #
#########

function copyto_typed!(a::Vector{T}, b::Vector) where T
    for i in 1:length(b)
        a[i] = b[i]::T
    end
    return nothing
end

```
-/
-- `a[i] = b[i]::T` for every `i`; the fresh `Array{T}(undef, n)` takes `b`'s elements once all
-- assertions hold (an assertion failure leaves an unreachable partially filled array).
def copyto_typed (o : Ops X Y E D CI CF) (a b : Nat) (T : VType Y) : PM o Unit := do
  let bv ← getVector o b
  check_typed o T bv.elems
  let av ← getVector o a
  setVector o a { av with elems := bv.elems }

/-- `new = Array{T}(undef, length(array)); copyto_typed!(new, array)`. -/
def typed_copy (o : Ops X Y E D CI CF) (el : ElType) (T : VType Y) (array : Nat) : PM o Nat := do
  let new ← allocVector o el
  copyto_typed o new array T
  return new

/-- `push!(array, v)` on a `Vector{Any}` object. -/
def pushVector (o : Ops X Y E D CI CF) (r : Nat) (v : Val X) : PM o Unit := do
  let av ← getVector o r
  setVector o r { av with elems := av.elems ++ [v] }

mutual

/--
Julia source: base/toml/parser.jl:847-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

##########
# Values #
##########

function parse_value(l::Parser)
    val = if accept(l, '[')
        parse_array(l)
    elseif accept(l, '{')
        parse_inline_table(l)
    elseif accept(l, '"')
        parse_string_start(l, false)
    elseif accept(l, '\'')
        parse_string_start(l, true)
    elseif accept(l, 't')
        parse_bool(l, true)
    elseif accept(l, 'f')
        parse_bool(l, false)
    else
        parse_number_or_date_start(l)
    end
    if val === nothing
        return ParserError(ErrGenericValueError)
    end
    return val
end

```
-/
def parse_value (o : Ops X Y E D CI CF) : PM o (Val X) := do
  let val ← do
    if (← accept o (chr '[')) then
      let a ← parse_array o
      pure (some (Val.vector a))
    else
      if (← accept o (chr '{')) then
        let t ← parse_inline_table o
        pure (some (Val.table t))
      else
        if (← accept o (chr '"')) then
          let s ← parse_string_start o false
          pure (some (Val.str s))
        else
          if (← accept o (chr '\'')) then
            let s ← parse_string_start o true
            pure (some (Val.str s))
          else
            if (← accept o (chr 't')) then
              let b ← parse_bool o true
              pure (b.map Val.bool)
            else
              if (← accept o (chr 'f')) then
                let b ← parse_bool o false
                pure (b.map Val.bool)
              else
                parse_number_or_date_start o
  match val with
  | none => throwP o (ParserError_1 .ErrGenericValueError)
  | some v => return v
partial_fixpoint

/-- The `while !empty_array` loop of `parse_array`. -/
def parse_array_loop (o : Ops X Y E D CI CF) (array : Nat) : PM o Unit := do
  let v ← parse_value o
  pushVector o array v
  -- There can be an arbitrary number of newlines and comments before a value and before the closing bracket.
  discard (skip_ws_nl o)
  let comma ← accept o (chr ',')
  discard (skip_ws_nl o)
  if (← accept o (chr ']')) then return
  if !comma then
    throwP o (ParserError_1 .ErrExpectedCommaBetweenItemsArray)
  parse_array_loop o array
partial_fixpoint

/--
Julia source: base/toml/parser.jl:886-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_array(l::Parser{Dates})::Err{Vector} where Dates
    skip_ws_nl(l)
    array = Vector{Any}()
    empty_array = accept(l, ']')
    while !empty_array
        v = @try parse_value(l)
        array = push!(array, v)
        # There can be an arbitrary number of newlines and comments before a value and before the closing bracket.
        skip_ws_nl(l)
        comma = accept(l, ',')
        skip_ws_nl(l)
        accept(l, ']') && break
        if !comma
            return ParserError(ErrExpectedCommaBetweenItemsArray)
        end
    end
    # check for static type throughout array
    T = !isempty(array) ? typeof(array[1]) : Union{}
    for el in array
        if typeof(el) != T
            T = Any
            break
        end
    end
    if T === Any
        new = array
    elseif T === String
        new = Array{T}(undef, length(array))
        copyto_typed!(new, array)
    elseif T === Bool
        new = Array{T}(undef, length(array))
        copyto_typed!(new, array)
    elseif T === Int64
        new = Array{T}(undef, length(array))
        copyto_typed!(new, array)
    elseif T === UInt64
        new = Array{T}(undef, length(array))
        copyto_typed!(new, array)
    elseif T === Float64
        new = Array{T}(undef, length(array))
        copyto_typed!(new, array)
    elseif T === Union{}
        new = Any[]
    elseif (T === TOMLDict) || (T === BigInt) || (T === UInt128) || (T === Int128) || (T <: Vector) ||
        (Dates !== nothing && ((T === Dates.Date) || (T === Dates.Time) || (T === Dates.DateTime)))
        # do nothing, leave as Vector{Any}
        new = array
    else error("unexpected type") end
    push!(l.static_arrays, new)
    return new
end

```
-/
def parse_array (o : Ops X Y E D CI CF) : PM o Nat := do
  discard (skip_ws_nl o)
  let array ← allocVector o .any
  let empty_array ← accept o (chr ']')
  if !empty_array then
    parse_array_loop o array
  -- check for static type throughout array
  let elems ← pure (← getVector o array).elems
  let T ← match elems with
    | [] => pure VType.bottom
    | el :: _ => typeofVal o el
  let T ← array_type_loop o T elems
  let eq := VType.eq (yEq o)
  let isDatesType : Bool := match o.dates with
    | some dates => eq T (.dates dates.dateType) || eq T (.dates dates.timeType) || eq T (.dates dates.dateTimeType)
    | none => false
  let new ← do
    if eq T .any then pure array
    else if eq T .string then typed_copy o .string T array
    else if eq T .bool then typed_copy o .bool T array
    else if eq T .int64 then typed_copy o .int64 T array
    else if eq T .uint64 then typed_copy o .uint64 T array
    else if eq T .float64 then typed_copy o .float64 T array
    else if eq T .bottom then allocVector o .any
    else if eq T .table || eq T .bigint || eq T .uint128 || eq T .int128 ||
        (match T with | .vector _ => true | _ => false) || isDatesType then
      -- do nothing, leave as Vector{Any}
      pure array
    else throwT o (.errorException "unexpected type")
  modifyP o fun l => { l with static_arrays := idPush l.static_arrays new }
  return new
partial_fixpoint

/-- The `while true` loop of `parse_inline_table`. -/
def parse_inline_table_loop (o : Ops X Y E D CI CF) (dict : TOMLDictRef) : PM o TOMLDictRef := do
  parse_entry o dict
  -- TOML v1.1: newlines and trailing commas are allowed in inline tables
  discard (skip_ws_nl o)
  if (← accept o (chr '}')) then return dict
  if (← accept o (chr ',')) then
    discard (skip_ws_nl o)
    -- Trailing comma is allowed in TOML v1.1
    if (← accept o (chr '}')) then return dict
  else
    throwP o (ParserError_1 .ErrExpectedCommaBetweenItemsInlineTable)
  parse_inline_table_loop o dict
partial_fixpoint

/--
Julia source: base/toml/parser.jl:938-962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

################
# Inline table #
################

function parse_inline_table(l::Parser)::Err{TOMLDict}
    dict = TOMLDict()
    push!(l.inline_tables, dict)
    skip_ws_nl(l)
    accept(l, '}') && return dict
    while true
        @try parse_entry(l, dict)
        # TOML v1.1: newlines and trailing commas are allowed in inline tables
        skip_ws_nl(l)
        accept(l, '}') && return dict
        if accept(l, ',')
            skip_ws_nl(l)
            # Trailing comma is allowed in TOML v1.1
            accept(l, '}') && return dict
        else
            return ParserError(ErrExpectedCommaBetweenItemsInlineTable)
        end
    end
end

```
-/
def parse_inline_table (o : Ops X Y E D CI CF) : PM o TOMLDictRef := do
  let dict ← allocTable o
  modifyP o fun l => { l with inline_tables := idPush l.inline_tables dict }
  discard (skip_ws_nl o)
  if (← accept o (chr '}')) then return dict
  parse_inline_table_loop o dict
partial_fixpoint

/--
Julia source: base/toml/parser.jl:748-790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_entry(l::Parser, d)::Union{Nothing, ParserError}
    key = @try parse_key(l)
    # `key` aliases `dotted_keys`, which parsing an inline table may overwrite.
    capture_comments = l.comments !== nothing && !(d in l.inline_tables)
    entry_path = (capture_comments && !l.in_array_table) ?
        vcat(l.active_table_path, key) : nothing
    skip_ws(l)
    if !accept(l, '=')
        return ParserError(ErrExpectedEqualAfterKey)
    end
    if length(key) > 1
        d = @try recurse_dict!(l, d, @view(key[1:end-1]), true, true)
    end
    last_key_part = l.dotted_keys[end]

    v = get(d, last_key_part, nothing)
    if v !== nothing
        @try check_allowed_add_key(l, v)
        if v isa TOMLDict && v in l.implicit_tables
            return ParserError(ErrDuplicatedKey)
        end
    end

    skip_ws(l)
    value = @try parse_value(l)
    # Not allowed to overwrite a value with an inline dict
    if value isa Dict && haskey(d, last_key_part)
        return ParserError(ErrInlineTableRedefine)
    end
    # TODO: Performance, hashing `last_key_part` again here
    d[last_key_part] = value
    if capture_comments
        if entry_path === nothing
            empty!(l.pending_comments)
            l.last_item_path = nothing
        else
            attach_pending_comments!(l, entry_path)
            l.last_item_path = entry_path
        end
    end
    return
end

```
-/
def parse_entry (o : Ops X Y E D CI CF) (d : TOMLDictRef) : PM o Unit := do
  let key ← parse_key o
  -- `key` aliases `dotted_keys`, which parsing an inline table may overwrite.
  let l ← getP o
  let capture_comments := l.comments.isSome && !l.inline_tables.contains d
  let entry_path ← pure <| if capture_comments && !l.in_array_table then some (l.active_table_path ++ key) else none
  discard (skip_ws o)
  if !(← accept o (chr '=')) then
    throwP o (ParserError_1 .ErrExpectedEqualAfterKey)
  let d ← if key.length > 1 then recurse_dict o (.table d) key.dropLast true true else pure d
  let last_key_part ← match (← getP o).dotted_keys.getLast? with
    | some k => pure k
    | none => throwT o (.jl .boundsError)
  let v ← pure (o.dict.get (← getTable o d) last_key_part)
  match v with
  | some v =>
    check_allowed_add_key o v
    match v with
    | .table r =>
      if (← getP o).implicit_tables.contains r then
        throwP o (ParserError_1 .ErrDuplicatedKey)
    | _ => pure ()
  | none => pure ()
  discard (skip_ws o)
  let value ← parse_value o
  -- Not allowed to overwrite a value with an inline dict
  if (match value with | .table _ => true | _ => false) && (o.dict.get (← getTable o d) last_key_part).isSome then
    throwP o (ParserError_1 .ErrInlineTableRedefine)
  setTable o d (o.dict.set (← getTable o d) last_key_part value)
  if capture_comments then
    match entry_path with
    | none =>
      modifyP o fun l => { l with pending_comments := [] }
      modifyP o fun l => { l with last_item_path := none }
    | some entry_path =>
      attach_pending_comments o entry_path
      modifyP o fun l => { l with last_item_path := some entry_path }
partial_fixpoint

end

/--
Julia source: base/toml/parser.jl:711-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_array_table(l)::Union{Nothing, ParserError}
    table_key = @try parse_key(l)
    skip_ws(l)
    if !(accept(l, ']') && accept(l, ']'))
        return ParserError(ErrExpectedEndArrayOfTable)
    end
    d = @try recurse_dict!(l, l.root, @view(table_key[1:end-1]), false)
    k = table_key[end]
    old = get!(() -> Any[], d, k)
    if old isa Vector
        if old in l.static_arrays
            return ParserError(ErrAddArrayToStaticArray)
        end
    else
        return ParserError(ErrArrayTreatedAsDictionary)
    end
    d_new = TOMLDict()
    first_element = isempty(old::Vector{Any})
    push!(old::Vector{Any}, d_new)
    push!(l.defined_tables, d_new)
    l.active_table = d_new

    if l.comments !== nothing
        # Only the first header has an unambiguous path.
        if first_element && !path_traverses_array(l, @view(table_key[1:end-1]))
            attach_pending_comments!(l, copy(table_key))
        else
            empty!(l.pending_comments)
        end
        empty!(l.active_table_path)
        append!(l.active_table_path, table_key)
        l.last_item_path = nothing
        l.in_array_table = true
    end
    return
end

```
-/
def parse_array_table (o : Ops X Y E D CI CF) : PM o Unit := do
  let table_key ← parse_key o
  discard (skip_ws o)
  let closed ← do
    if (← accept o (chr ']')) then accept o (chr ']') else pure false
  if !closed then
    throwP o (ParserError_1 .ErrExpectedEndArrayOfTable)
  let d ← recurse_dict o (.table (← getP o).root) table_key.dropLast false
  let k ← match table_key.getLast? with
    | some k => pure k
    | none => throwT o (.jl .boundsError)
  let old ← getBang_vector o d k
  match old with
  | .vector vr =>
    if (← getP o).static_arrays.contains vr then
      throwP o (ParserError_1 .ErrAddArrayToStaticArray)
  | _ => throwP o (ParserError_1 .ErrArrayTreatedAsDictionary)
  let d_new ← allocTable o
  -- `old::Vector{Any}`
  let vr ← match old with
    | .vector vr => pure vr
    | _ => throwT o .typeError
  let ov ← getVector o vr
  if ov.eltype != .any then throwT o .typeError
  let first_element := ov.elems.isEmpty
  pushVector o vr (.table d_new)
  modifyP o fun l => { l with defined_tables := idPush l.defined_tables d_new }
  modifyP o fun l => { l with active_table := d_new }
  if (← getP o).comments.isSome then
    -- Only the first header has an unambiguous path.
    if first_element && !(← path_traverses_array o table_key.dropLast) then
      attach_pending_comments o table_key
    else
      modifyP o fun l => { l with pending_comments := [] }
    modifyP o fun l => { l with active_table_path := table_key }
    modifyP o fun l => { l with last_item_path := none }
    modifyP o fun l => { l with in_array_table := true }

/--
Julia source: base/toml/parser.jl:680-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Can only enter here from toplevel
function parse_table(l)
    if accept(l, '[')
        return parse_array_table(l)
    end
    table_key = @try parse_key(l)
    skip_ws(l)
    if !accept(l, ']')
        return ParserError(ErrExpectedEndOfTable)
    end
    l.active_table = @try recurse_dict!(l, l.root, table_key)
    if l.active_table in l.implicit_tables
        return ParserError(ErrDuplicatedKey)
    end
    push!(l.defined_tables, l.active_table)
    if l.comments !== nothing
        l.in_array_table = path_traverses_array(l, table_key)
        empty!(l.active_table_path)
        append!(l.active_table_path, table_key)
        if l.in_array_table
            empty!(l.pending_comments)
            l.last_item_path = nothing
        else
            path = copy(table_key)
            attach_pending_comments!(l, path)
            l.last_item_path = path
        end
    end
    return
end

```
-/
def parse_table (o : Ops X Y E D CI CF) : PM o Unit := do
  if (← accept o (chr '[')) then
    return (← parse_array_table o)
  let table_key ← parse_key o
  discard (skip_ws o)
  if !(← accept o (chr ']')) then
    throwP o (ParserError_1 .ErrExpectedEndOfTable)
  let active ← recurse_dict o (.table (← getP o).root) table_key
  modifyP o fun l => { l with active_table := active }
  if (← getP o).implicit_tables.contains (← getP o).active_table then
    throwP o (ParserError_1 .ErrDuplicatedKey)
  modifyP o fun l => { l with defined_tables := idPush l.defined_tables l.active_table }
  if (← getP o).comments.isSome then
    let in_array_table ← path_traverses_array o table_key
    modifyP o fun l => { l with in_array_table := in_array_table }
    modifyP o fun l => { l with active_table_path := table_key }
    if (← getP o).in_array_table then
      modifyP o fun l => { l with pending_comments := [] }
      modifyP o fun l => { l with last_item_path := none }
    else
      let path := table_key
      attach_pending_comments o path
      modifyP o fun l => { l with last_item_path := some path }

/--
Julia source: base/toml/parser.jl:618-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Top level can be either a table key, an array of table statement
# or a key/value entry.
function parse_toplevel(l::Parser)::Err{Nothing}
    if accept(l, '[')
        l.active_table = l.root
        @try parse_table(l)
        if skip_ws_comment(l) && l.comments !== nothing
            attach_inline_comment!(l)
        end
        if !(peek(l) == '\n' || peek(l) == '\r' || peek(l) == '#' || peek(l) == EOF_CHAR)
            eat_char(l)
            return ParserError(ErrExpectedNewLineKeyValue)
        end
    else
        @try parse_entry(l, l.active_table)
        if skip_ws_comment(l) && l.comments !== nothing
            attach_inline_comment!(l)
        end
        # SPEC: "There must be a newline (or EOF) after a key/value pair."
        if !(peek(l) == '\n' || peek(l) == '\r' || peek(l) == '#' || peek(l) == EOF_CHAR)
            eat_char(l)
            return ParserError(ErrExpectedNewLineKeyValue)
        end
    end
end

```
-/
def parse_toplevel (o : Ops X Y E D CI CF) : PM o Unit := do
  if (← accept o (chr '[')) then
    modifyP o fun l => { l with active_table := l.root }
    parse_table o
    if (← skip_ws_comment o) && (← getP o).comments.isSome then
      attach_inline_comment o
    let p ← peek o
    if !(p == jc '\n' || p == jc '\r' || p == jc '#' || p == EOF_CHAR) then
      discard (eat_char o)
      throwP o (ParserError_1 .ErrExpectedNewLineKeyValue)
  else
    parse_entry o (← getP o).active_table
    if (← skip_ws_comment o) && (← getP o).comments.isSome then
      attach_inline_comment o
    -- SPEC: "There must be a newline (or EOF) after a key/value pair."
    let p ← peek o
    if !(p == jc '\n' || p == jc '\r' || p == jc '#' || p == EOF_CHAR) then
      discard (eat_char o)
      throwP o (ParserError_1 .ErrExpectedNewLineKeyValue)

/-- The `while true` loop of `tryparse`. -/
def tryparse_loop (o : Ops X Y E D CI CF) : PM o TOMLDictRef := do
  discard (skip_ws_nl_toplevel o)
  if (← peek o) == EOF_CHAR then
    if (← getP o).comments.isSome then flush_pending_comments o
    return (← getP o).root
  let v ← observe o (parse_toplevel o)
  match v with
  | .error v =>
    let l ← getP o
    let v := { v with str := some l.str }
    let v := { v with pos := some (i64 (l.prevpos.val - 1)) }
    let v := { v with table := some l.root }
    let v := { v with filepath := l.filepath }
    let v := { v with line := some l.line }
    let v := { v with column := some (i64 (l.column.val - 1)) }
    throwP o v
  | .ok () => tryparse_loop o
partial_fixpoint

/--
Julia source: base/toml/parser.jl:599-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse(l::Parser)::Err{TOMLDict}
    while true
        skip_ws_nl_toplevel(l)
        peek(l) == EOF_CHAR && break
        v = parse_toplevel(l)
        if v isa ParserError
            v.str      = l.str
            v.pos      = l.prevpos-1
            v.table    = l.root
            v.filepath = l.filepath
            v.line     = l.line
            v.column   = l.column-1
            return v
        end
    end
    l.comments === nothing || flush_pending_comments!(l)
    return l.root
end

```
-/
def tryparse (o : Ops X Y E D CI CF) : PM o TOMLDictRef := tryparse_loop o

/--
Julia source: base/toml/parser.jl:587-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
############
# Toplevel #
############

# Driver, keeps parsing toplevel until we either get
# a `ParserError` or eof.
function parse(l::Parser)::TOMLDict
    v = tryparse(l)
    v isa ParserError && throw(v)
    return v
end

```
-/
def parse (o : Ops X Y E D CI CF) : PM o TOMLDictRef := do
  let v ← observe o (tryparse o)
  match v with
  | .error v => throwT o (.parserError v)
  | .ok v => return v

end

end JuliaLean.base.toml.parser

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

/-!
# TOML strings, `base/toml/parser.jl:1356-1462`

`unescape_string` is `base/strings/io.jl:535-591`. It works on characters, but
every escape is ASCII and a backslash byte is never part of a multi-byte
character (continuation bytes are `≥ 0x80`), so scanning bytes is equivalent.
-/

namespace JuliaLean.Toml

open JuliaLean

/-- Digits of `\x`, `\u`, `\U` as `unescape_string` reads them: at most `m` hex
digits; their value, how many, and the rest. -/
def unescHex : Nat → List Nat → Nat → Nat × Nat × List Nat
  | 0, bs, n => (n, 0, bs)
  | m + 1, b :: bs, n =>
    match hexByte b with
    | some d =>
      let (v, k, r) := unescHex m bs (16 * n + d)
      (v, k + 1, r)
    | none => (n, 0, b :: bs)
  | _ + 1, [], n => (n, 0, [])

/-- Octal digits after the first of an octal escape (at most two more). -/
def unescOct : Nat → List Nat → Nat → Nat × List Nat
  | 0, bs, n => (n, bs)
  | m + 1, b :: bs, n =>
    if 48 ≤ b ∧ b ≤ 55 then unescOct m bs (8 * n + (b - 48)) else (n, b :: bs)
  | _ + 1, [], n => (n, [])

/-- `unescape_string(s)`, `base/strings/io.jl:535-591`, on bytes; the fuel is
the number of bytes left (every step consumes at least one). -/
def unescape_go : Nat → List Nat → Except Exc (List Nat)
  | 0, _ => .error .outOfFuel
  | _ + 1, [] => .ok []
  | _ + 1, [b] => .ok [b]
  | fuel + 1, 92 :: c :: rest =>
    if c = 120 ∨ c = 117 ∨ c = 85 then
      let m := if c = 120 then 2 else if c = 117 then 4 else 8
      let (n, k, rest') := unescHex m rest 0
      if k = 0 ∨ n > 0x10ffff then .error (.jl (.argumentError "invalid escape sequence"))
      else
        let out := if m = 2 then [n] else utf8 n
        (unescape_go fuel rest').map (out ++ ·)
    else if 48 ≤ c ∧ c ≤ 55 then
      let (n, rest') := unescOct 2 rest (c - 48)
      if n > 255 then .error (.jl (.argumentError "octal escape sequence out of range"))
      else (unescape_go fuel rest').map (n :: ·)
    else
      let out : Option Nat :=
        if c = 97 then some 7 else if c = 98 then some 8 else if c = 116 then some 9
        else if c = 110 then some 10 else if c = 118 then some 11 else if c = 102 then some 12
        else if c = 114 then some 13 else if c = 101 then some 27
        else if c = 92 ∨ c = 34 then some c else none
      match out with
      | some o => (unescape_go fuel rest).map (o :: ·)
      | none =>
        -- a non-ASCII `c` would be several bytes; TOML only passes the escapes it validated
        .error (.jl (.argumentError "invalid escape sequence"))
  | fuel + 1, b :: rest => (unescape_go fuel rest).map (b :: ·)

/-- `unescape_string(s)`. -/
def unescape_string (s : List Nat) : Except Exc (List Nat) := unescape_go (s.length + 1) s

/-- `take_chunks`, `base/toml/parser.jl:1447-1462`. -/
def take_chunks (unescape : Bool) : M Str := do
  let l ← get
  let str := l.chunks.foldl (fun acc (a, b) => acc ++ slice l.str a b) []
  set { l with chunks := [] }
  if unescape then
    match unescape_string str with
    | .ok s => return s
    | .error e => throw e
  else return str

/-- `stop_candidates_*`, `base/toml/parser.jl:1378-1381`. -/
def stopCandidates (multiline quoted : Bool) (x : Nat) : Bool :=
  let q := if quoted then ch '\'' else ch '"'
  x != q && x != ch '\\' && (multiline || x != ch '\n')

/-- `parse_string_continue`, `base/toml/parser.jl:1383-1445`; the loop state is
`start_chunk` and `contains_backslash`. -/
def parse_string_loop (multiline quoted : Bool) (fuel : Nat) :
    Nat → Int → Bool → M Str
  | 0, _, _ => throw .outOfFuel
  | k + 1, startChunk, containsBackslash => do
    let q := if quoted then ch '\'' else ch '"'
    let offset : Int := if multiline then 3 else 1
    if (← peek) == EOF then perr .ErrUnexpectedEndString
    discard (accept_batch (stopCandidates multiline quoted) fuel)
    if !multiline && (← peek) == ch '\n' then perr .ErrNewLineInString
    if (← peek) != ch '\\' then
      let a1 ← accept (· == q)
      let closed ← if !a1 then pure false else if !multiline then pure true else do
        let a2 ← accept (· == q)
        if !a2 then pure false else accept (· == q)
      if closed then
        modify fun l => { l with chunks := l.chunks ++ [(startChunk, l.prevpos - offset - 1)] }
        return ← take_chunks containsBackslash
    let c ← eat_char
    if c == ch '\\' && !quoted then
      let p ← peek
      if p == ch '\n' || p == ch '\r' then
        modify fun l => { l with chunks := l.chunks ++ [(startChunk, l.prevpos - 1 - 1)] }
        discard (skip_ws_nl_no_comment fuel)
        return ← parse_string_loop multiline quoted fuel k (← get).prevpos containsBackslash
      else
        let c ← eat_char
        if c == ch 'x' || c == ch 'u' || c == ch 'U' then
          let n := if c == ch 'x' then 2 else if c == ch 'u' then 4 else 8
          set_marker
          if !(← accept_n isvalid_hex n) then perr .ErrInvalidUnicodeScalar
          let codepoint ← parse_int false (some 16)
          if c == ch 'x' then pure ()
          else if !(codepoint ≤ 0xD7FF || (0xE000 ≤ codepoint && codepoint ≤ 0x10FFFF)) then
            perr .ErrInvalidUnicodeScalar
        else if c != ch 'b' && c != ch 't' && c != ch 'n' && c != ch 'f' && c != ch 'r' &&
            c != ch 'e' && c != ch '"' && c != ch '\\' then
          perr .ErrInvalidEscapeCharacter
        return ← parse_string_loop multiline quoted fuel k startChunk true
    parse_string_loop multiline quoted fuel k startChunk containsBackslash

/-- `parse_string_continue(l, multiline, quoted)`. -/
def parse_string_continue (fuel : Nat) (multiline quoted : Bool) : M Str := do
  parse_string_loop multiline quoted fuel fuel (← get).prevpos false

/-- `parse_string_start(l, quoted; allow_multiline)`, `base/toml/parser.jl:1360-1376`,
after the opening quote. -/
def parse_string_start (fuel : Nat) (quoted : Bool) (allowMultiline : Bool := true) : M Str := do
  let c := if quoted then ch '\'' else ch '"'
  let mut multiline := false
  if (← accept (· == c)) then
    if !(← accept (· == c)) then return []
    if !allowMultiline then perr .ErrMultilineStringAsKey
    discard (acceptC '\r')
    discard (acceptC '\n')
    multiline := true
  parse_string_continue fuel multiline quoted

end JuliaLean.Toml

/-!
# TOML keys, values, tables and the driver

`base/toml/parser.jl:593-961` at master `bbfa0ce4150`, without comment capture.
`tryparse` mirrors `Base.TOML.tryparse(::Parser)` (`base/toml/parser.jl:599-616`),
which `TOML.tryparse(str)` (`dates = true`, `Parser{Dates}`) and Base's code
loading (`dates = false`, `Parser{nothing}`) call.
-/

namespace JuliaLean.Toml

open JuliaLean

/-! ### Tables -/

/-- `x in s` for an `IdSet` of heap objects. -/
def memId (v : Val) (s : List Nat) : Bool :=
  match v with
  | .ref k => s.contains k
  | _ => false

/-- `v isa Dict`. -/
def isDict (v : Val) : M Bool := do
  match v with
  | .ref k => match ← getObj k with
    | .table _ => return true
    | _ => return false
  | _ => return false

/-- `check_allowed_add_key`, `base/toml/parser.jl:669-678`. -/
def check_allowed_add_key (d : Val) (checkDefined : Bool := true) : M Unit := do
  let l ← get
  if !(← isDict d) then perr .ErrKeyAlreadyHasValue
  else if memId d l.inline_tables then perr .ErrAddKeyToInlineTable
  else if checkDefined && memId d l.defined_tables then perr .ErrDuplicatedKey

/-- `d::TOMLDict`: the table index, or `TypeError`. -/
def asDict (d : Val) : M Nat := do
  match d with
  | .ref k => match ← getObj k with
    | .table _ => return k
    | _ => throw .typeError
  | _ => throw .typeError

/-- `get!(TOMLDict, d, key)`. -/
def getBangDict (t : Nat) (key : Str) : M Val := do
  match ← dictGet t key with
  | some v => return v
  | none =>
    let k ← alloc (.table [])
    dictSet t key (.ref k)
    return .ref k

/-- `recurse_dict!(l, d, dotted_keys, check, define_implicit)`,
`base/toml/parser.jl:644-667`. `n` is `length(dotted_keys)`. -/
def recurse_dict_loop (keys : List Str) (n : Nat) (check defineImplicit : Bool) :
    Nat → Val → M Val
  | i, d =>
    match keys with
    | [] => do return .ref (← asDict d)
    | key :: rest => do
      let t ← asDict d
      let mut d ← getBangDict t key
      match d with
      | .ref k =>
        match ← getObj k with
        | .array .any xs =>
          match xs.getLast? with
          | none => perr .ErrArrayTreatedAsDictionary
          | some last => d := last
        | .array _ _ => perr .ErrKeyAlreadyHasValue
        | .table _ => pure ()
      | _ => pure ()
      if check then
        let checkDef := if defineImplicit then true else i == n
        check_allowed_add_key d checkDef
      if defineImplicit && (← isDict d) then
        match d with
        | .ref k => modify fun l => { l with implicit_tables := l.implicit_tables ++ [k] }
        | _ => pure ()
      recurse_dict_loop rest n check defineImplicit (i + 1) d

def recurse_dict (d : Val) (keys : List Str) (check : Bool := true)
    (defineImplicit : Bool := false) : M Nat := do
  match ← recurse_dict_loop keys keys.length check defineImplicit 1 d with
  | .ref k => return k
  | _ => throw .typeError

/-! ### Keys, `base/toml/parser.jl:796-845` -/

/-- `isvalid_barekey_char`, `base/toml/parser.jl:800-804`. -/
def isvalid_barekey_char (c : Nat) : Bool :=
  (ch 'a' ≤ c && c ≤ ch 'z') || (ch 'A' ≤ c && c ≤ ch 'Z') || isdigit c ||
    c == ch '-' || c == ch '_'

/-- `_parse_key`, `base/toml/parser.jl:813-845`. -/
def _parse_key (fuel : Nat) : Nat → M (List Str)
  | 0 => throw .outOfFuel
  | k + 1 => do
    discard (skip_ws fuel)
    if (← get).dotted_keys.isEmpty then
      if (← acceptC '=') then perr .ErrEmptyBareKey
    let dq ← acceptC '"'
    let keyval ← if dq then parse_string_start fuel false (allowMultiline := false) else do
      let sq ← acceptC '\''
      if sq then parse_string_start fuel true (allowMultiline := false) else do
        set_marker
        if (← accept_batch isvalid_barekey_char fuel) then
          let p ← peek
          if !(p == ch '.' || iswhitespace p || p == ch ']' || p == ch '=') then
            discard eat_char
            perr .ErrInvalidBareKeyCharacter
          take_substring
        else
          discard eat_char
          perr .ErrInvalidBareKeyCharacter
    modify fun l => { l with dotted_keys := l.dotted_keys ++ [keyval] }
    discard (skip_ws fuel)
    if (← acceptC '.') then
      discard (skip_ws fuel)
      discard (_parse_key fuel k)
    return (← get).dotted_keys

/-- `parse_key`, `base/toml/parser.jl:807-810`. -/
def parse_key (fuel : Nat) : M (List Str) := do
  modify fun l => { l with dotted_keys := [] }
  _parse_key fuel fuel

/-! ### Values, arrays, inline tables and entries -/

/-- The element type `parse_array` gives a homogeneous array of `T`, or
`none` for its final `else error("unexpected type")`,
`base/toml/parser.jl:902-933`. -/
def arrayElTy (dates : Bool) : Option JTy → Option (ElTy × Bool)
  | none => some (.any, true)          -- `Union{}`: a fresh `Any[]`
  | some .string => some (.string, true)
  | some .bool => some (.bool, true)
  | some .i64 => some (.i64, true)
  | some .u64 => some (.u64, true)
  | some .f64 => some (.f64, true)
  | some .dict | some .big | some .u128 | some .i128 | some (.vec _) => some (.any, false)
  | some .date | some .time | some .datetime => if dates then some (.any, false) else none

/-- The type `T` of `parse_array`: `typeof(array[1])` if all elements share it,
`Any` (`none` inside `some`) otherwise, and `Union{}` (`none`) when empty. -/
def commonType (xs : List Val) : M (Option (Option JTy)) := do
  match xs with
  | [] => return none
  | x :: rest =>
    let t ← typeOf x
    let same ← rest.allM fun y => do return (← typeOf y) == t
    return some (if same then some t else none)

/-! The mutually recursive part. `lf` is the fuel of the non-recursive helpers'
loops (more than the input length); the explicit `Nat` argument is the fuel of
the mutual recursion, on which every function recurses structurally. -/

mutual

/-- `parse_value`, `base/toml/parser.jl:852-872`. -/
def parse_value (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    match ← parse_value_dispatch lf fuel with
    | some v => return v
    | none => perr .ErrGenericValueError
termination_by structural fuel

/-- The `if`/`elseif` chain of `parse_value`; `none` is Julia's `nothing`. -/
def parse_value_dispatch (lf : Nat) (fuel : Nat) : M (Option Val) :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    if (← acceptC '[') then return some (← parse_array lf fuel)
    if (← acceptC '{') then return some (← parse_inline_table lf fuel)
    if (← acceptC '"') then return some (.str (← parse_string_start lf false))
    if (← acceptC '\'') then return some (.str (← parse_string_start lf true))
    if (← acceptC 't') then return ← parse_bool true
    if (← acceptC 'f') then return ← parse_bool false
    parse_number_or_date_start lf
termination_by structural fuel

/-- `parse_array`, `base/toml/parser.jl:886-936`, after `[`. -/
def parse_array (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    discard (skip_ws_nl lf lf)
    let emptyArray ← acceptC ']'
    let xs ← if emptyArray then pure [] else parse_array_items lf fuel []
    let dates := (← get).dates
    match ← commonType xs with
    | none =>
      let k ← alloc (.array .any [])
      modify fun l => { l with static_arrays := l.static_arrays ++ [k] }
      return .ref k
    | some t =>
      let el ← match t with
        | none => pure ElTy.any
        | some t => match arrayElTy dates (some t) with
          | some (e, _) => pure e
          | none => throw (.errorException "unexpected type")
      let k ← alloc (.array el xs)
      modify fun l => { l with static_arrays := l.static_arrays ++ [k] }
      return .ref k
termination_by structural fuel

/-- The `while !empty_array` loop of `parse_array`. -/
def parse_array_items (lf : Nat) (fuel : Nat) (acc : List Val) : M (List Val) :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let v ← parse_value lf fuel
    let acc := acc ++ [v]
    discard (skip_ws_nl lf lf)
    let comma ← acceptC ','
    discard (skip_ws_nl lf lf)
    if (← acceptC ']') then return acc
    if !comma then perr .ErrExpectedCommaBetweenItemsArray
    parse_array_items lf fuel acc
termination_by structural fuel

/-- `parse_inline_table`, `base/toml/parser.jl:943-961`, after `{`. -/
def parse_inline_table (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let d ← alloc (.table [])
    modify fun l => { l with inline_tables := l.inline_tables ++ [d] }
    discard (skip_ws_nl lf lf)
    if (← acceptC '}') then return .ref d
    parse_inline_loop lf fuel d
termination_by structural fuel

/-- The `while true` loop of `parse_inline_table`. -/
def parse_inline_loop (lf : Nat) (fuel : Nat) (d : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    parse_entry lf fuel (.ref d)
    discard (skip_ws_nl lf lf)
    if (← acceptC '}') then return .ref d
    if (← acceptC ',') then
      discard (skip_ws_nl lf lf)
      if (← acceptC '}') then return .ref d
      parse_inline_loop lf fuel d
    else perr .ErrExpectedCommaBetweenItemsInlineTable
termination_by structural fuel

/-- `parse_entry(l, d)`, `base/toml/parser.jl:748-789`, without comment capture. -/
def parse_entry (lf : Nat) (fuel : Nat) (d0 : Val) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let key ← parse_key lf
    discard (skip_ws lf)
    if !(← acceptC '=') then perr .ErrExpectedEqualAfterKey
    let mut d := d0
    if key.length > 1 then
      d := .ref (← recurse_dict d key.dropLast true true)
    let lastKeyPart := (← get).dotted_keys.getLastD []
    let t ← asDict d
    match ← dictGet t lastKeyPart with
    | some v =>
      check_allowed_add_key v
      if (← isDict v) && memId v (← get).implicit_tables then perr .ErrDuplicatedKey
    | none => pure ()
    discard (skip_ws lf)
    let value ← parse_value lf fuel
    if (← isDict value) && (← dictGet t lastKeyPart).isSome then perr .ErrInlineTableRedefine
    dictSet t lastKeyPart value
termination_by structural fuel

end

/-- `parse_array_table`, `base/toml/parser.jl:711-746`, after `[[`. -/
def parse_array_table (lf : Nat) : M Unit := do
  let tableKey ← parse_key lf
  discard (skip_ws lf)
  let a1 ← acceptC ']'
  let ok ← if a1 then acceptC ']' else pure false
  if !ok then perr .ErrExpectedEndArrayOfTable
  let d ← recurse_dict (.ref 0) tableKey.dropLast false
  let k := tableKey.getLastD []
  let old ← match ← dictGet d k with
    | some v => pure v
    | none => do
      let a ← alloc (.array .any [])
      dictSet d k (.ref a)
      pure (.ref a)
  let l ← get
  let oldArr ← match old with
    | .ref a => match ← getObj a with
      | .array _ _ =>
        if l.static_arrays.contains a then perr .ErrAddArrayToStaticArray
        pure a
      | _ => perr .ErrArrayTreatedAsDictionary
    | _ => perr .ErrArrayTreatedAsDictionary
  let dNew ← alloc (.table [])
  match ← getObj oldArr with
  | .array .any xs => setObj oldArr (.array .any (xs ++ [.ref dNew]))
  | _ => throw .typeError
  modify fun l => { l with defined_tables := l.defined_tables ++ [dNew], active_table := dNew }

/-- `parse_table`, `base/toml/parser.jl:681-709`, after `[`. -/
def parse_table (lf : Nat) : M Unit := do
  if (← acceptC '[') then return ← parse_array_table lf
  let tableKey ← parse_key lf
  discard (skip_ws lf)
  if !(← acceptC ']') then perr .ErrExpectedEndOfTable
  let t ← recurse_dict (.ref 0) tableKey
  modify fun l => { l with active_table := t }
  if (← get).implicit_tables.contains t then perr .ErrDuplicatedKey
  modify fun l => { l with defined_tables := l.defined_tables ++ [t] }

/-- The end-of-line check of `parse_toplevel`, `base/toml/parser.jl:627-630,637-640`. -/
def expect_newline (lf : Nat) : M Unit := do
  discard (skip_ws_comment lf)
  let p ← peek
  if !(p == ch '\n' || p == ch '\r' || p == ch '#' || p == EOF) then
    discard eat_char
    perr .ErrExpectedNewLineKeyValue

/-- `parse_toplevel`, `base/toml/parser.jl:620-642`. -/
def parse_toplevel (lf fuel : Nat) : M Unit := do
  if (← acceptC '[') then
    modify fun l => { l with active_table := 0 }
    parse_table lf
    expect_newline lf
  else
    parse_entry lf fuel (.ref (← get).active_table)
    expect_newline lf

/-- The loop of `tryparse(l::Parser)`, `base/toml/parser.jl:599-616`. -/
def tryparse_loop (lf fuel : Nat) : Nat → M Unit
  | 0 => throw .outOfFuel
  | k + 1 => do
    discard (skip_ws_nl lf lf)
    if (← peek) == EOF then return
    parse_toplevel lf fuel
    tryparse_loop lf fuel k

/-- `Base.TOML.tryparse(Parser{D}(s))`: the final parser state (whose heap
object `0` is the returned table), or how parsing ended. A `ParserError` is
returned by `tryparse`; every other `Exc` is thrown. -/
def tryparseState (s : Str) (dates : Bool := true) : Except Exc Parser := do
  let l ← Parser.new s dates
  let lf := s.length + 2
  let fuel := 4 * s.length + 16
  ((tryparse_loop lf fuel lf).run l).map (·.2)

end JuliaLean.Toml
