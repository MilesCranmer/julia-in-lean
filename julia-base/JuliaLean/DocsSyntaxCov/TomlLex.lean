import JuliaLean.Toml.Basic
import JuliaLean.DocsSyntaxCov.Ast

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

/-- The bytes `print(io, c::Char)` writes for a raw character value (`write(io, c::Char)`,
`base/io.jl`): the bytes of the big-endian value, stopping at the first zero byte after the
first. -/
def charBytes (u : Nat) : Str :=
  let b3 := u / 2 ^ 24 % 256
  let b2 := u / 2 ^ 16 % 256
  let b1 := u / 2 ^ 8 % 256
  let b0 := u % 256
  b3 :: (if b2 == 0 && b1 == 0 && b0 == 0 then [] else b2 :: (if b1 == 0 && b0 == 0 then [] else
    b1 :: (if b0 == 0 then [] else [b0])))

/-- `thisind(s::String, i)`, `base/strings/string.jl`. -/
def thisind (s : Str) (i : Int) : DJ Int :=
  let n : Int := s.length
  let cu (j : Int) : Nat := s.getD (j - 1).toNat 0
  let cont (b : Nat) : Bool := b / 64 == 2
  if i == 0 then pure 0
  else if i == n + 1 then pure i
  else if !(1 ≤ i && i ≤ n) then .error .boundsError
  else if !(cont (cu i) && i - 1 > 0) then pure i
  else if 0xc0 ≤ cu (i - 1) && cu (i - 1) ≤ 0xf7 then pure (i - 1)
  else if !(cont (cu (i - 1)) && i - 2 > 0) then pure i
  else if 0xe0 ≤ cu (i - 2) && cu (i - 2) ≤ 0xf7 then pure (i - 2)
  else if !(cont (cu (i - 2)) && i - 3 > 0) then pure i
  else if 0xf0 ≤ cu (i - 3) && cu (i - 3) ≤ 0xf7 then pure (i - 3)
  else pure i

/-- `prevind(s, i)` (`prevind(s, i, 1)`, `base/strings/basic.jl`): the previous valid index, or
`0`; a `BoundsError` unless `0 < i ≤ ncodeunits(s) + 1`. -/
def prevind (s : Str) (i : Int) : DJ Int :=
  if !(0 < i && i ≤ s.length + 1) then .error .boundsError
  else go (i.toNat) i
where
  go : Nat → Int → DJ Int
    | 0, _ => pure 0
    | k + 1, i =>
      if 1 < i then do
        let j := i - 1
        if (← thisind s j) == j then pure j else go k j
      else pure (i - 1)

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
