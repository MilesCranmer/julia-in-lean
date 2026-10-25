import JuliaLean.Show.Escape
import JuliaLean.Show.Ops

/-!
# Printing symbols

Models of `Meta.isidentifier` and `is_valid_identifier` (`base/meta.jl`),
`show_sym` and `show(io, ::Symbol)` (`base/show.jl`), `escape_raw_string`
(`base/strings/io.jl`), and the decoder the JuliaSyntax parser applies to the
body of a `var"..."` identifier (`rawDecode`).

A symbol name is a byte string `JStr` (Julia allows any bytes except NUL).
The operator tables are keyed by Lean `String`s; a name that is not valid UTF-8
is in none of them (`opName`).
-/

namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- `is_id_start_char(c)`, `base/meta.jl:25`: a `ccall` whose `UInt32` argument
conversion `UInt32(c)` throws `InvalidCharError` for a malformed `c`. -/
def isIdStartCharJ (d : UData) (c : UInt32) : SJl Bool := do
  let u ← codepoint c
  pure (idStartChar d u)

/-- `is_id_char(c)`, `base/meta.jl:26`, with the same conversion. -/
def isIdCharJ (d : UData) (c : UInt32) : SJl Bool := do
  let u ← codepoint c
  pure (idChar d u)

/-- `all(is_id_char, rest)` (`base/reduce.jl`, `_all`): stops at the first `false`. -/
def allIdChar (d : UData) : List UInt32 → SJl Bool
  | [] => .ok true
  | c :: cs => do
    if ← isIdCharJ d c then allIdChar d cs else pure false

/-- The body of `isidentifier(s::AbstractString)`, `base/meta.jl:48-55`, on the
chars `cs` of `s`: `Iterators.peel(s)` splits off the first char. -/
def isidentifierOf (d : UData) (s : JStr) (cs : List UInt32) : SJl Bool :=
  match cs with
  | [] => .ok false
  | c :: rest =>
    if s.bytes = asc ['t', 'r', 'u', 'e'] ∨ s.bytes = asc ['f', 'a', 'l', 's', 'e'] then .ok false
    else do
      if ← isIdStartCharJ d c then allIdChar d rest else pure false

/-- `isidentifier(s::AbstractString)`, `base/meta.jl:48-55`, and
`isidentifier(s::Symbol) = isidentifier(string(s))` (`:56`). -/
def isidentifier (d : UData) (s : JStr) : SJl Bool := isidentifierOf d s (chars s)

/-- `keyword_syms`, `base/meta.jl:122-126` (char lists, so the kernel never
decodes a `String`). -/
def keywordSyms : List (List UInt8) :=
  [['b', 'a', 'r', 'e', 'm', 'o', 'd', 'u', 'l', 'e'], ['b', 'e', 'g', 'i', 'n'], ['b', 'r', 'e', 'a', 'k'],
    ['c', 'a', 't', 'c', 'h'], ['c', 'o', 'n', 's', 't'], ['c', 'o', 'n', 't', 'i', 'n', 'u', 'e'],
    ['d', 'o'], ['e', 'l', 's', 'e'], ['e', 'l', 's', 'e', 'i', 'f'], ['e', 'n', 'd'],
    ['e', 'x', 'p', 'o', 'r', 't'], ['f', 'a', 'l', 's', 'e'], ['f', 'i', 'n', 'a', 'l', 'l', 'y'],
    ['f', 'o', 'r'], ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n'], ['g', 'l', 'o', 'b', 'a', 'l'], ['i', 'f'],
    ['i', 'm', 'p', 'o', 'r', 't'], ['l', 'e', 't'], ['l', 'o', 'c', 'a', 'l'], ['m', 'a', 'c', 'r', 'o'],
    ['m', 'o', 'd', 'u', 'l', 'e'], ['p', 'u', 'b', 'l', 'i', 'c'], ['q', 'u', 'o', 't', 'e'],
    ['r', 'e', 't', 'u', 'r', 'n'], ['s', 't', 'r', 'u', 'c', 't'], ['t', 'r', 'u', 'e'], ['t', 'r', 'y'],
    ['u', 's', 'i', 'n', 'g'], ['w', 'h', 'i', 'l', 'e']].map asc

/-- The operator-table key of a symbol name: the Lean `String` with the same
UTF-8 bytes, or `none` when the name is not valid UTF-8. The tables
(`src/julia-parser.scm`) only hold valid UTF-8 names, so such a name is not an
operator. -/
def opName (s : JStr) : Option String :=
  if (chars s).all isvalidChar then some (String.ofList ((chars s).map (fun c => Char.ofNat (cpOf c).toNat)))
  else none

/-- `Meta._isoperator(s)`, `base/meta.jl:60` (`jl_is_operator` on the name's bytes). -/
def isOperatorSym (o : OpData) (s : JStr) : Bool :=
  match opName s with
  | some n => o.isOp n
  | none => false

/-- `Meta.is_syntactic_operator(s)`, `base/meta.jl:88`. -/
def isSyntacticSym (o : OpData) (s : JStr) : Bool :=
  match opName s with
  | some n => o.isSyntacticOp n
  | none => false

/-- `is_valid_identifier(sym)`, `base/meta.jl:128-134`. -/
def isValidIdentifier (d : UData) (o : OpData) (s : JStr) : SJl Bool := do
  let isid ← isidentifier d s
  if isid && !decide (s.bytes ∈ keywordSyms) then pure true
  else pure (isOperatorSym o s && !decide (s.bytes ∈ [asc ['\''], asc [':', ':'], asc ['?']]) &&
    !isSyntacticSym o s)

/-- The loop of `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-692`,
from `escapes` pending backslashes: the bytes written and the count `total` of
inserted backslashes. -/
def escRawLoop (delim : UInt32) : Nat → List UInt32 → List UInt8 × Nat
  | escapes, [] => (List.replicate escapes 0x5c, escapes)
  | escapes, c :: cs =>
    if c = ac 0x5c then
      match escRawLoop delim (escapes + 1) cs with
      | (o, t) => (writeChar c ++ o, t)
    else if c = delim then
      match escRawLoop delim 0 cs with
      | (o, t) => (List.replicate (escapes + 1) 0x5c ++ writeChar c ++ o, escapes + 1 + t)
    else
      match escRawLoop delim 0 cs with
      | (o, t) => (writeChar c ++ o, t)

/-- `escape_raw_string(str, delim = '"')`, `base/strings/io.jl:694-697`: `str`
itself when nothing needs escaping, else the escaped copy. -/
def escapeRawString (s : JStr) (delim : UInt32 := ac 0x22) : List UInt8 :=
  let r := escRawLoop delim 0 (chars s)
  if r.2 = 0 then s.bytes else r.1

/-- `show_sym(io, sym; allow_macroname = false)`, `base/show.jl:1867-1878`;
`print(io, sym)` writes the name's bytes. -/
def showSym (d : UData) (o : OpData) (s : JStr) : SJl (List UInt8) := do
  if ← isValidIdentifier d o s then pure s.bytes
  else pure (asc ['v', 'a', 'r', '"'] ++ escapeRawString s ++ [0x22])

/-- `quoted_syms`, `base/show.jl:1676`. -/
def quotedSyms : List (List UInt8) :=
  [[':'], [':', ':'], [':', '='], ['='], ['=', '='], ['=', '=', '='], ['=', '>']].map asc

/-- `show(io, s::Symbol) = show_unquoted_quote_expr(io, s, 0, 0)`, `base/show.jl:1628`,
symbol branch `:1937-1949`; `repr(String(sym))` is `print_quoted` (`base/strings/io.jl:194`). -/
def showSymbol (d : UData) (o : OpData) (s : JStr) : SJl (List UInt8) :=
  if s.bytes ∈ quotedSyms then .ok (asc [':', '('] ++ s.bytes ++ asc [')'])
  else do
    let isid ← isidentifier d s
    if isid || (isOperatorSym o s && s.bytes ≠ asc ['\'']) then pure (asc [':'] ++ s.bytes)
    else pure (asc ['S', 'y', 'm', 'b', 'o', 'l', '('] ++ printQuoted d s ++ asc [')'])

/-! ## Reading `var"..."` back -/

/-- The number of leading backslash bytes. -/
def nBS (l : List UInt8) : Nat := (l.takeWhile (· == 0x5c)).length

/-- Where a non-triple-quoted raw string ends: the raw branch of
`lex_string_chunk` (`JuliaSyntax/src/julia/tokenize.jl:648-723`) with
`string_terminates` (`:1152-1159`). A run of `n` backslashes followed by the
delimiter escapes it when `n` is odd. Returns the input from the closing
delimiter on, or `none` at end of input. Scanning bytes equals scanning chars:
`read(io, Char)` (`base/io.jl:1091-1106`) never joins `"` or `\` to another
byte, and every byte of a multi-byte char is `≥ 0x80`. -/
def rawScan (delim : UInt8) : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: r =>
    if c = delim then some (c :: r)
    else if c = 0x5c then
      let n := 1 + nBS r
      match r.drop (n - 1) with
      | x :: r' => if x = delim ∧ n % 2 = 1 then rawScan delim f r' else rawScan delim f (x :: r')
      | [] => rawScan delim f []
    else rawScan delim f r

/-- `unescape_raw_string(io, txtbuf, firstind, endind, is_cmd)`,
`JuliaSyntax/src/julia/literal_parsing.jl:186-227`, on the body bytes. -/
def unescRaw (delim : UInt8) : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, c :: r =>
    if c ≠ 0x5c then
      if c = 0x0d then
        match r with
        | 0x0a :: r' => 0x0a :: unescRaw delim f r'
        | _ => 0x0a :: unescRaw delim f r
      else c :: unescRaw delim f r
    else
      let n := 1 + nBS r
      match r.drop (n - 1) with
      | [] => List.replicate (n / 2) 0x5c
      | x :: r' => List.replicate (if x = delim then n / 2 else n) 0x5c ++ x :: unescRaw delim f r'

/-- The body of `var"` `e` `"` as JuliaSyntax decodes it, ignoring the token
checks: `none` when the literal ends before the final quote or runs past it. -/
def rawBody (e : List UInt8) : Option (List UInt8) :=
  match rawScan 0x22 (e.length + 2) (e ++ [0x22]) with
  | some [0x22] => some (unescRaw 0x22 (e.length + 1) e)
  | _ => none

/-- `update_bidi_state`, `JuliaSyntax/src/julia/tokenize.jl:591-605`, on the
nesting counts (bounded by the source length, so the `Int`s never wrap). -/
def bidiStep (st : Int × Int) (c : UInt32) : Int × Int :=
  if c = ac 0x0a then (0, 0)
  else if c = 0xe280aa00 ∨ c = 0xe280ab00 ∨ c = 0xe280ad00 ∨ c = 0xe280ae00 then (st.1 + 1, st.2)
  else if c = 0xe280ac00 then (st.1 - 1, st.2)
  else if c = 0xe281a600 ∨ c = 0xe281a700 ∨ c = 0xe281a800 then (st.1, st.2 + 1)
  else if c = 0xe281a900 then (st.1, st.2 - 1)
  else st

/-- The name JuliaSyntax reads from the identifier `var"` `e` `"`
(`JuliaSyntax/src/julia/parser.jl:3763-3807`), before `normalize_identifier`
(`literal_parsing.jl:425`, the identity on ASCII names): `none` when parsing
fails. The string token is `ErrorInvalidUTF8` when a char of the body is
invalid and `ErrorBidiFormatting` when the bidi nesting does not return to zero
(`tokenize.jl:721-722, 760-762`); otherwise the body is decoded by `rawBody`,
and `Symbol(name)` throws for a name containing NUL (`boot.jl:686`). -/
def rawDecode (e : List UInt8) : Option (List UInt8) :=
  if h : e.length < 2 ^ 62 then
    let cs := chars ⟨e, h⟩
    if cs.all isvalidChar && cs.foldl bidiStep (0, 0) == (0, 0) then
      match rawBody e with
      | some n => if 0 ∈ n then none else some n
      | none => none
    else none
  else none

/-! ## A concrete operator table -/

/-- Operator tables that agree with Julia on every fact in `OpData.Faithful`
and list nothing else; used to instantiate counterexamples. -/
def opsFaithful : OpData where
  isOp s := decide (s ∈ ["+", "-", "*", "/", "^", "::", "=", "'", "!", "~", "&&", "||", ".&&", ".",
    "..", "...", "?", "$", "->", "-->", "<:", ">:", "%", "&", "|", "\\", "<<", ">>", ">>>", "==",
    "!=", "<", ">", "<=", ">=", "===", "!==", "=>", "|>", "<|", ":", "+=", ".+", ".=", "√", "∈",
    ".-"])
  isUnaryOp s := decide (s ∈ ["+", "-", "!", "~", "<:", ">:", ".+", "√", ".-"])
  isUnaryAndBinaryOp s := decide (s ∈ ["+", "-"])
  isSyntacticOp s := decide (s ∈ ["=", "&&", "||", ".&&", ".", "...", "->", "+=", ".="])
  prec s := ([("+", 11), ("-", 11), ("*", 12), ("/", 12), ("^", 15), ("::", 16), ("=", 1),
    ("//", 13), (":", 10), ("=>", 2), ("==", 7), ("<", 7), ("&&", 6), ("||", 5), (".", 17),
    (".&&", 6), (".||", 5), ("<:", 7), (".+", 11), ("~", 1), (".-", 11)].lookup s).getD 0
  opSuffix _ := false

theorem opsFaithful_faithful : opsFaithful.Faithful := by
  unfold OpData.Faithful; decide

end JuliaLean.Show
