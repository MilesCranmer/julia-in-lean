import JuliaLean.Show.Ast

/-!
# Julia surface syntax: lexer and parser model of `Meta.parse`

`parse src` models `Meta.parse(String(src))` (`base/meta.jl:406-422`), which on
1.13.2 and master runs JuliaSyntax: the hook `core_parser_hook`
(`JuliaSyntax/src/integration/hooks.jl:195-216`, rule `:statement`), the lexer
`JuliaSyntax/src/julia/tokenize.jl`, the recursive-descent parser
`JuliaSyntax/src/julia/parser.jl` and the conversion to `Expr`
`JuliaSyntax/src/integration/expr.jl`. Every definition below cites the lines it
mirrors (all on master `bbfa0ce4150`).

Results:

* `.ok e` is exactly the `Expr` Julia builds, after `Base.remove_linenums!`
  (`base/expr.jl:1287`), written as a `JE` tree;
* `.error` exactly when `Meta.parse` throws a `ParseError` or returns an
  `Expr(:error)`/`Expr(:incomplete)`;
* `.unknown` whenever the input leaves the modelled fragment. A wrong `.ok` or
  `.error` is a model bug; `.unknown` is always sound.

Conventions for values `JE` has no constructor for:

* The command literal `` `body` `` parses to
  `Expr(:macrocall, GlobalRef(Core, Symbol("@cmd")), LineNumberNode(1, :none), body)`.
  It is written `.node "macrocall" [.node "globalref" [.sym "Core", .sym "@cmd"],
  .node "nothing" [], .str body]`: the fake head `"globalref"` stands for the
  `GlobalRef`, and the macro-call line-number argument (which `remove_linenums!`
  keeps) is replaced by `nothing`, written `.node "nothing" []`. `show`
  (`base/show.jl:2380-2384`) prints such a macro call as `` `body` `` and
  ignores the second argument, so the replacement changes nothing that is
  printed. `body` is the raw-unescaped text (`literal_parsing.jl:186-223`).
* `parse` returns line-number-free trees: blocks never contain
  `LineNumberNode`s. Top-level `a; b` (an `Expr(:toplevel)` whose
  `LineNumberNode`s `remove_linenums!` keeps), docstrings (`"doc" x`), string
  and command macros (`x"s"`, ``x`s` ``) and empty input (`nothing`) give
  `.unknown`.

Fragment: spaces as the only whitespace; ASCII identifiers
`[A-Za-z_][A-Za-z0-9_!]*` other than keywords; decimal `Int64` literals (larger
ones are `Int128`/`BigInt` macro calls, unknown); float literals `d+.d+` whose
value has at most 15 significant digits and prints without an exponent
(`base/ryu/shortest.jl:334-339`), as canonical `JE.flt`; string literals without
`\` or `$`; command literals; the tokens `+ - * / ^ :: ' = ; , ( ) [ ] { } $ & &&
|| .&& .|| .+ .- ! :` (`:` both as quote and as the range operator) and the
invalid operator `--`. Every other token gives `.unknown`.
-/

namespace JuliaLean.Show

namespace Syntax

/-! ## Tokens -/

/-- Token kinds of the fragment (`JuliaSyntax/src/julia/kinds.jl:195-560`).
`int v` is a decimal `Integer` token, `flt ip fp` a `Float` token with the
trailing zeros of the fraction stripped (`[0]` if none remain), `str s` a whole
non-raw string literal `"s"`, `cmd s` a whole command literal with its
unescaped body `s`. `prime` is the adjoint `'`, `dandand`/`doror` the dotted
operators `.&&`/`.||` (a `.` token glued to `&&`/`||`, `julia_parse_stream.jl:250-275`),
`eof` the `EndMarker`. -/
inductive TK where
  | ident (name : String)
  | int (v : Nat)
  | flt (ip : Nat) (fp : List Nat)
  | str (s : String)
  | cmd (s : String)
  | plus | minus | star | slash | caret | colon | dcolon | prime | eq
  | semi | comma | lp | rp | lb | rb | lc | rc
  | dollar | andand | oror | dandand | doror | bang | dplus | dminus | amp | eof
  deriving DecidableEq, Repr, Inhabited

/-- A token and whether whitespace precedes it (`preceding_whitespace`,
`JuliaSyntax/src/core/parse_stream.jl`). -/
structure Tok where
  k : TK
  ws : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Lexer outcome: the token list (ending in `eof`), a certain `ParseError`, or
unknown. -/
inductive LexRes where
  | ok (ts : List Tok)
  | unknown
  | error
  deriving Repr, Inhabited

/-! ## Byte classes -/

def isDigitB (b : UInt8) : Bool := b ≥ 48 && b ≤ 57
def isLetterB (b : UInt8) : Bool := (b ≥ 65 && b ≤ 90) || (b ≥ 97 && b ≤ 122)
/-- `is_identifier_start_char` on ASCII (`tokenize.jl:27`). -/
def isIdStartB (b : UInt8) : Bool := isLetterB b || b == 95
/-- `is_identifier_char` on ASCII (`tokenize.jl:21`); `!` is an identifier character. -/
def isIdCharB (b : UInt8) : Bool := isIdStartB b || isDigitB b || b == 33

/-- An ASCII byte string as a `String`. -/
def asciiStr (bs : List UInt8) : String := String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- Keywords, contextual keywords, word operators and `true`/`false`: the
names `lex_identifier` (`tokenize.jl:1239-1246`) does not emit as plain
`Identifier`s (`kinds.jl:195-230`). Identifiers spelled like these are outside
the fragment. -/
def reservedNames : List String :=
  ["baremodule", "begin", "break", "const", "continue", "do", "export", "for", "function",
   "global", "if", "import", "let", "local", "macro", "module", "quote", "return", "struct",
   "try", "typegroup", "using", "while", "catch", "finally", "else", "elseif", "end",
   "abstract", "as", "doc", "mutable", "outer", "primitive", "public", "type", "var", "VERSION",
   "in", "isa", "where", "true", "false"]

/-- Longest prefix satisfying `p`, and the rest. -/
def spanB (p : UInt8 → Bool) : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: r => if p b then let (x, y) := spanB p r; (b :: x, y) else ([], b :: r)

/-- Identifier characters of `lex_identifier` (`tokenize.jl:1215-1237`): stop at a
non-identifier character, or at `!` followed by `=`. -/
def takeIdent : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: r =>
    if (b == 33 && r.head? == some 61) || !isIdCharB b then ([], b :: r)
    else let (x, y) := takeIdent r; (b :: x, y)

def digitVal (bs : List UInt8) : Nat := bs.foldl (fun n b => 10 * n + (b - 48).toNat) 0

/-- Digits with trailing zeros removed, `[0]` if none remain (`JE.flt` convention). -/
def stripFrac (ds : List Nat) : List Nat :=
  match (ds.reverse.dropWhile (· == 0)).reverse with
  | [] => [0]
  | l => l

/-- The float literal `ip.fp` (source digits, `fp` stripped) is in the fragment:
zero, or at most 15 significant digits (so the decimal is its own shortest
representation) and decimal-point position `pt` with `-4 < pt ≤ 6`, the range
in which `Ryu.writeshortest` prints without an exponent (`base/ryu/shortest.jl:334-339`). -/
def fltOk (ipDigits : List UInt8) (fp : List Nat) : Bool :=
  let ipd := ipDigits.dropWhile (· == 48)
  if ipd.isEmpty then
    if fp == [0] then true
    else
      let lz := (fp.takeWhile (· == 0)).length
      lz ≤ 3 && (fp.length - lz) ≤ 15
  else ipd.length ≤ 6 && ipd.length + fp.length ≤ 15

/-- `compound_assign_follows` (`tokenize.jl:433-436`): the operator is followed by
`=` that is not part of `==`, `===` or `=>`. -/
def compoundFollows : List UInt8 → Bool
  | 61 :: c :: _ => c != 61 && c != 62
  | [61] => true
  | _ => false

/-- Non-raw string body (`lex_string_chunk`, `tokenize.jl:724-758`) up to the
closing `"`. Bodies containing `\` or `$` are outside the fragment; a missing
closing quote is the "unterminated string literal" error (`parser.jl:3583-3587`). -/
def scanStr : List UInt8 → LexRes × List UInt8 × List UInt8
  | [] => (.error, [], [])
  | 34 :: rest => (.ok [], [], rest)
  | b :: rest =>
    if b == 92 || b == 36 then (.unknown, [], [])
    else let (r, body, rest') := scanStr rest; (r, b :: body, rest')

/-- Raw command-literal body (`lex_string_chunk` raw branch, `tokenize.jl:692-723`):
a backtick ends the literal unless preceded by an odd number of backslashes. `nb`
counts the backslashes immediately before the current byte. -/
def scanCmd : Nat → List UInt8 → LexRes × List UInt8 × List UInt8
  | _, [] => (.error, [], [])
  | nb, 96 :: rest =>
    if nb % 2 == 1 then let (r, body, rest') := scanCmd 0 rest; (r, 96 :: body, rest')
    else (.ok [], [], rest)
  | nb, 92 :: rest => let (r, body, rest') := scanCmd (nb + 1) rest; (r, 92 :: body, rest')
  | _, b :: rest => let (r, body, rest') := scanCmd 0 rest; (r, b :: body, rest')

/-- `unescape_raw_string(…, is_cmd=true)` (`literal_parsing.jl:186-223`): a run
of `n` backslashes followed by a backtick or the end of the body becomes `n ÷ 2`
backslashes; other runs are kept. `n` is the length of the current run. -/
def unescRaw : Nat → List UInt8 → List UInt8
  | n, [] => List.replicate (n / 2) 92
  | n, 92 :: r => unescRaw (n + 1) r
  | n, c :: r => List.replicate (if c == 96 then n / 2 else n) 92 ++ c :: unescRaw 0 r

/-- `lexCmdEndGo bs nb i`: index just after the closing backtick, scanning the body
from index `i` (`tokenize.jl:692-723`). -/
def cmdEndGo : List UInt8 → Nat → Nat → Option Nat
  | [], _, _ => none
  | 96 :: rest, nb, i => if nb % 2 == 1 then cmdEndGo rest 0 (i + 1) else some (i + 1)
  | 92 :: rest, nb, i => cmdEndGo rest (nb + 1) (i + 1)
  | _ :: rest, _, i => cmdEndGo rest 0 (i + 1)

end Syntax

open Syntax in
/-- Index just after the closing backtick of the command literal that starts at
index 0 of `src` (`lex_backtick`, `tokenize.jl:1191-1205`, and the raw string
chunk lexer `tokenize.jl:692-723`): the first backtick preceded by an even number
of backslashes. `none` if `src` does not start with a backtick, starts a
triple-backtick literal, or the literal is unterminated. -/
def lexCmdEnd : List UInt8 → Option Nat
  | 96 :: 96 :: 96 :: _ => none
  | 96 :: r => cmdEndGo r 0 1
  | _ => none

namespace Syntax

/-- Outcome of lexing one token: the token, the remaining bytes and whether a
following `'` is the adjoint (`adj`); whitespace; or a certain error / unknown. -/
inductive Step where
  | tok (k : TK) (rest : List UInt8) (adj : Bool)
  | space (rest : List UInt8)
  | unknown
  | error
  deriving Repr, Inhabited

/-- One token of the lexer (`_next_token`, `tokenize.jl:477-585`, and the `lex_*`
functions it calls), starting at byte `b` followed by `r`. `adj`: the previous
token lets `'` be the adjoint operator (`lex_prime`, `tokenize.jl:1106-1124`:
identifiers, literals, `)`, `]`, `}`, `'`, with no whitespace in between);
otherwise `'` starts a character literal, which is outside the fragment.
Identifier-start bytes are tested first; no other branch matches them. -/
def lexStep (b : UInt8) (r : List UInt8) (adj : Bool) : Step :=
  -- lex_identifier, tokenize.jl:1209-1247
  if isIdStartB b then
    let (name, rest) := takeIdent (b :: r)
    let s := asciiStr name
    if reservedNames.contains s then .unknown
    else .tok (.ident s) rest true
  else if b == 32 then .space r
  else if b < 32 || b ≥ 127 then .unknown
  else if b == 40 then .tok .lp r false
  else if b == 41 then .tok .rp r true
  else if b == 91 then .tok .lb r false
  else if b == 93 then .tok .rb r true
  else if b == 123 then .tok .lc r false
  else if b == 125 then .tok .rc r true
  else if b == 59 then .tok .semi r false
  else if b == 44 then .tok .comma r false
  -- lex_plus, tokenize.jl:929-936
  else if b == 43 then
    if r.head? == some 43 || compoundFollows r then .unknown
    else .tok .plus r false
  -- lex_minus, tokenize.jl:938-951: `--` is ErrorInvalidOperator, `-->` and `->` arrows
  else if b == 45 then
    match r with
    | 45 :: 62 :: _ => .unknown
    | 45 :: _ => .error
    | 62 :: _ => .unknown
    | _ => if compoundFollows r then .unknown else .tok .minus r false
  -- lex_star, tokenize.jl:953-960
  else if b == 42 then
    if r.head? == some 42 || compoundFollows r then .unknown
    else .tok .star r false
  -- lex_forwardslash, tokenize.jl:1163-1166
  else if b == 47 then
    if r.head? == some 47 || compoundFollows r then .unknown
    else .tok .slash r false
  -- lex_circumflex, tokenize.jl:962-964
  else if b == 94 then
    if compoundFollows r then .unknown else .tok .caret r false
  -- lex_colon, tokenize.jl:893-901
  else if b == 58 then
    match r with
    | 58 :: r' => .tok .dcolon r' false
    | 61 :: _ => .unknown
    | _ => .tok .colon r false
  -- lex_prime, tokenize.jl:1106-1124
  else if b == 39 then
    if adj then .tok .prime r true else .unknown
  -- lex_equal, tokenize.jl:881-890
  else if b == 61 then
    if r.head? == some 61 || r.head? == some 62 then .unknown
    else .tok .eq r false
  -- lex_dollar, tokenize.jl:970-972
  else if b == 36 then
    if compoundFollows r then .unknown else .tok .dollar r false
  -- lex_amper, tokenize.jl:1126-1132
  else if b == 38 then
    match r with
    | 38 :: r' => .tok .andand r' false
    | _ => if compoundFollows r then .unknown else .tok .amp r false
  -- lex_bar, tokenize.jl:919-927
  else if b == 124 then
    match r with
    | 124 :: r' => .tok .oror r' false
    | _ => .unknown
  -- lex_dot, tokenize.jl:1172-1188; a `.` glued to `&&`, `||`, `+`, `-` is the dotted
  -- operator (`peek_dotted_op_token`, julia_parse_stream.jl:250-275). After `.`,
  -- lex_plus/lex_minus (tokenize.jl:929-951) never form `->`.
  else if b == 46 then
    match r with
    | 38 :: 38 :: r' => .tok .dandand r' false
    | 43 :: r' =>
      if r'.head? == some 43 || compoundFollows r' then .unknown
      else .tok .dplus r' false
    | 45 :: 45 :: 62 :: _ => .unknown
    | 45 :: 45 :: _ => .error
    | 45 :: r' =>
      if compoundFollows r' then .unknown else .tok .dminus r' false
    | 124 :: 124 :: r' => .tok .doror r' false
    | _ => .unknown
  -- lex_exclaim, tokenize.jl:903-913
  else if b == 33 then
    if r.head? == some 61 then .unknown else .tok .bang r false
  -- lex_quote, tokenize.jl:1136-1150 (triple quotes are outside the fragment)
  else if b == 34 then
    match r with
    | 34 :: 34 :: _ => .unknown
    | _ =>
      match scanStr r with
      | (.ok _, body, rest) => .tok (.str (asciiStr body)) rest false
      | (.error, _, _) => .error
      | _ => .unknown
  -- lex_backtick, tokenize.jl:1191-1205
  else if b == 96 then
    match r with
    | 96 :: 96 :: _ => .unknown
    | _ =>
      match scanCmd 0 r with
      | (.ok _, body, rest) =>
        .tok (.cmd (asciiStr (unescRaw 0 body))) rest false
      | (.error, _, _) => .error
      | _ => .unknown
  -- lex_digit, tokenize.jl:994-1104 (decimal only; `_`, exponents, suffixes and
  -- juxtaposed identifiers are outside the fragment)
  else if isDigitB b then
    let (ds, r1) := spanB isDigitB (b :: r)
    match r1 with
    | 46 :: c :: r2 =>
      if isDigitB c then
        let (fs, r3) := spanB isDigitB (c :: r2)
        match r3 with
        | d :: _ =>
          if isIdCharB d || d == 46 then .unknown
          else
            let fp := stripFrac (fs.map fun x => (x - 48).toNat)
            if fltOk ds fp then .tok (.flt (digitVal ds) fp) r3 true
            else .unknown
        | [] =>
          let fp := stripFrac (fs.map fun x => (x - 48).toNat)
          if fltOk ds fp then .tok (.flt (digitVal ds) fp) r3 true
          else .unknown
      else .unknown
    | 46 :: [] => .unknown
    | c :: _ =>
      if isIdStartB c then .unknown
      else .tok (.int (digitVal ds)) r1 true
    | [] => .tok (.int (digitVal ds)) r1 true
  else .unknown

/-- The lexer loop: `ws` records whitespace before the next token. Each step
consumes at least one byte, so `fuel = length + 1` suffices. -/
def lexGo : Nat → List UInt8 → Bool → Bool → List Tok → LexRes
  | 0, _, _, _, _ => .unknown
  | _ + 1, [], ws, _, acc => .ok (acc.reverse ++ [⟨.eof, ws⟩])
  | n + 1, b :: r, ws, adj, acc =>
    match lexStep b r adj with
    | .tok k rest adj' => lexGo n rest false adj' (⟨k, ws⟩ :: acc)
    | .space rest => lexGo n rest true false acc
    | .unknown => .unknown
    | .error => .error

/-- Lex a whole source text. -/
def lex (src : List UInt8) : LexRes := lexGo (src.length + 1) src false false []

/-! ## Concrete syntax trees -/

/-- What `peek_behind` (`parse_stream.jl:620-660`) reports for a leaf: a number
literal, a string, an identifier (including operators remapped to
`Identifier`), the unremapped syntactic unary operators `$` and `::`
(`is_syntactic_unary_op`, `parser.jl:300`), or another token. -/
inductive LK where
  | num | str | ident | synUnary | other
  deriving DecidableEq, Repr, Inhabited

/-- Call flavours (`julia_parse_stream.jl:3-6`): `f(x)`, `a + b`, `-x`, `x'`. -/
inductive CT where
  | prefix | infix | prefixOp | postfix
  deriving DecidableEq, Repr, Inhabited

/-- Node kinds of the green tree (`kinds.jl`): `decl` is infix `::`,
`declPrefix` prefix `::`, `func` the short-form function `f(x) = y`, `lazy h`
the nodes `&&`, `||`, `.&&`, `.||`. -/
inductive NK where
  | call (ct : CT) | juxtapose | parens | block | toplevel | tuple | params | ref | vect
  | hcat | vcat | row | typedHcat | typedVcat | curly | braces | bracescat | quote | dollar
  | decl | declPrefix | amp | assign | func | lazy (h : String)
  | dotcall (ct : CT) | dotop (h : String)
  deriving DecidableEq, Repr, Inhabited

/-- Green-tree nodes after parsing, trivia dropped. A leaf carries its converted
`Expr` value and whether its original token kind is `Identifier` (used by the
string-macro test of `parse_call_chain`, `parser.jl:1832-1836`). -/
inductive Cst where
  | leaf (k : LK) (isId : Bool) (v : JE)
  | node (k : NK) (ch : List Cst)
  deriving Repr, Inhabited

/-- The `peek_behind` kinds the parser branches on. -/
inductive BK where
  | num | str | blockForm | synUnary | other
  deriving DecidableEq, Repr, Inhabited

/-- Kind of the last emitted node (`is_number`, `K"string"`, `is_block_form`
`parser.jl:295`, `is_syntactic_unary_op` `parser.jl:300`). -/
def kindOf : Cst → BK
  | .leaf .num _ _ => .num
  | .leaf .str _ _ => .str
  | .leaf .synUnary _ _ => .synUnary
  | .leaf _ _ _ => .other
  | .node .block _ => .blockForm
  | .node .quote _ => .blockForm
  | .node .dollar _ => .synUnary
  | .node .decl _ => .synUnary
  | .node .declPrefix _ => .synUnary
  | .node .amp _ => .synUnary
  | .node _ _ => .other

/-- `peek_behind(ps)` with its default `skip_parens=true` (`parse_stream.jl:620-660`),
which skips exactly one enclosing `parens` node. -/
def behind : Cst → BK
  | .node .parens [c] => kindOf c
  | c => kindOf c

def isIdLeaf : Cst → Bool
  | .leaf _ true _ => true
  | _ => false

/-- `last_identifier_orig_kind == K"Identifier"` at the start of
`parse_call_chain` (`parser.jl:1555-1556`, one `parens` level skipped). -/
def strmacIdent : Cst → Bool
  | .node .parens [c] => isIdLeaf c
  | c => isIdLeaf c

/-- Loop of `was_eventually_call` (`parser.jl:331-351`): a call after stripping
`parens` and the left side of infix `::`. -/
def wasCallLoop : Cst → Bool
  | .node (.call _) _ => true
  | .node .parens [c] => wasCallLoop c
  | .node .decl (a :: _ :: _) => wasCallLoop a
  | _ => false

/-- `was_eventually_call` (`parser.jl:331-351`), starting from `peek_behind_pos`. -/
def wasEventuallyCall : Cst → Bool
  | .node .parens [c] => wasCallLoop c
  | c => wasCallLoop c

/-- Parse failure: a certain `ParseError`, or a construct outside the fragment. -/
inductive PE where
  | error | unknown
  deriving DecidableEq, Repr, Inhabited

abbrev PR := Except PE (Cst × List Tok)

def eofTok : Tok := ⟨.eof, false⟩
/-- `peek_token(ps, i+1)`. -/
def tokAt (ts : List Tok) (i : Nat) : Tok := (ts.drop i).headD eofTok
def k1 (ts : List Tok) : TK := (tokAt ts 0).k
def k2 (ts : List Tok) : TK := (tokAt ts 1).k

/-- `is_closing_token` (`parser.jl:231-235`) on the fragment's tokens. -/
def isClosing : TK → Bool
  | .comma | .rp | .rb | .rc | .semi | .eof => true
  | _ => false

/-- `is_operator` (`kinds.jl:614`) on the fragment's tokens. -/
def isOpTok : TK → Bool
  | .plus | .minus | .star | .slash | .caret | .colon | .dcolon | .prime | .eq
  | .dollar | .andand | .oror | .dandand | .doror | .bang | .dplus | .dminus | .amp => true
  | _ => false

def isNumTok : TK → Bool
  | .int _ | .flt _ _ => true
  | _ => false

def isStrTok : TK → Bool
  | .str _ => true
  | _ => false

def isCmdTok : TK → Bool
  | .cmd _ => true
  | _ => false

/-- Operators that may start a unary expression in `parse_unary`
(`parser.jl:1219-1225`). -/
def isInitialOp : TK → Bool
  | .plus | .minus | .star | .slash | .caret | .bang | .dplus | .dminus => true
  | _ => false

/-- The dotted operators `.+`, `.-`. -/
def isDotTok : TK → Bool
  | .dplus | .dminus => true
  | _ => false

/-- The operator under a dot. -/
def baseOp : TK → TK
  | .dplus => .plus
  | .dminus => .minus
  | k => k

/-- `is_unary_op` (`parser.jl:308-312`). -/
def isUnaryOp : TK → Bool
  | .plus | .minus | .bang | .dplus | .dminus => true
  | _ => false

/-- `is_both_unary_and_binary` (`parser.jl:315-318`). -/
def bothUB : TK → Bool
  | .plus | .minus | .dollar | .amp | .dplus | .dminus => true
  | _ => false

def opName : TK → String
  | .plus => "+" | .minus => "-" | .star => "*" | .slash => "/" | .caret => "^"
  | .bang => "!" | .dollar => "$" | .dcolon => "::" | .prime => "'" | .colon => ":"
  | .amp => "&" | .dplus => "+" | .dminus => "-" | _ => ""

/-- An operator token bumped with `remap_kind=K"Identifier"`: its value is the
operator's symbol (`literal_parsing.jl:429-432`). -/
def opLeaf (k : TK) : Cst := .leaf .ident false (.sym (opName k))

/-- The command literal's `Expr` (`expr.jl:271-274`, encoding in the module docstring). -/
def cmdJE (s : String) : JE :=
  .node "macrocall" [.node "globalref" [.sym "Core", .sym "@cmd"], .node "nothing" [], .str s]

/-- A signed numeric literal glued by `bump_glue` (`parser.jl:1256`); its value is
`parse_int_literal`/`parse_float_literal` of the signed text (`literal_parsing.jl:14-29`). -/
def glue (neg : Bool) : TK → Cst
  | .int v => .leaf .num false (.int (if neg then -(v : Int) else v))
  | .flt ip fp => .leaf .num false (.flt neg ip fp)
  | _ => .leaf .other false (.sym "")

/-- Accumulated contents of `parse_brackets` (`parser.jl:3314-3391`): elements
before the first `;`, then one list per `;`-section (each `;` starts a
`parameters` section, `parser.jl:3332-3341,3378-3380`). -/
structure BR where
  items : List Cst := []
  secs : List (List Cst) := []
  hadCommas : Bool := false
  numSemis : Nat := 0
  numSub : Nat := 0
  deriving Inhabited

def BR.push (br : BR) (e : Cst) : BR :=
  match br.secs with
  | [] => { br with items := br.items ++ [e], numSub := br.numSub + 1 }
  | _ => { br with secs := br.secs.dropLast ++ [br.secs.getLastD [] ++ [e]],
                   numSub := br.numSub + 1 }

def concatL : List (List Cst) → List Cst
  | [] => []
  | l :: ls => l ++ concatL ls

/-- Children when the sections become `parameters` nodes. -/
def BR.args (br : BR) : List Cst := br.items ++ br.secs.map (fun s => .node .params s)
/-- Children when the sections stay `TOMBSTONE`s, which are transparent
(`tree_cursors.jl:56-61`). -/
def BR.flat (br : BR) : List Cst := br.items ++ concatL br.secs

/-- `bump_closing_token` (`parser.jl:148-174`): any other token is an error. -/
def bumpClosing (closer : TK) (ts : List Tok) : Except PE (List Tok) :=
  if k1 ts == closer then .ok ts.tail else .error .error

/-- Kinds returned by `parse_cat` on the fragment. -/
inductive CatK where
  | vect | hcat | vcat
  deriving DecidableEq, Repr, Inhabited

/-- `parse_array_separator` (`parser.jl:3079-3158`) for the separators of the
fragment: `none` is `typemin(Int)`, `some (-1)` a single `;`, `some 0`
whitespace. `;;` is outside the fragment; `; ;` and `,` are errors. -/
def arraySep (ts : List Tok) : Except PE (Option Int × List Tok) :=
  let t := tokAt ts 0
  if t.k == .semi then
    let ts := ts.tail
    let t' := tokAt ts 0
    if t'.k == .semi then (if t'.ws then .error .error else .error .unknown)
    else .ok (some (-1), ts)
  else if t.k == .comma then .error .error
  else if t.ws && !isClosing t.k then .ok (some 0, ts)
  else .ok (none, ts)

mutual

/-- `parse_assignment`/`parse_assignment_with_initial_ex` (`parser.jl:594-647`)
with `down` = `parse_comma` (`comma`, from `parse_eq`, `parser.jl:572`) or
`parse_pair` (`parse_eq_star`, `parser.jl:579-589`). `parse_pair`, `parse_cond`
and `parse_arrow` (`parser.jl:677-768`) reduce to `parse_or` on the fragment.
`ss` is `ps.space_sensitive`. -/
def parseAssignment (f : Nat) (comma ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (lhs, ts) ← if comma then parseComma f ss ts else parseOr f ss ts
    if k1 ts == .eq then
      let (rhs, ts) ← parseAssignment f comma ss ts.tail
      .ok (.node (if wasEventuallyCall lhs then .func else .assign) [lhs, rhs], ts)
    else .ok (lhs, ts)
  termination_by structural f

/-- `parse_comma` (`parser.jl:652-672`). -/
def parseComma (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseOr f ss ts
    commaLoop f ss [a] false ts
  termination_by structural f

/-- Loop of `parse_comma` (`parser.jl:656-671`). -/
def commaLoop (f : Nat) (ss : Bool) (items : List Cst) (any : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    if k1 ts != .comma then
      .ok (if any then .node .tuple items else (match items with | a :: _ => a | [] => .node .tuple []), ts)
    else
      let ts := ts.tail
      if k1 ts == .eq then commaLoop f ss items true ts
      else do
        let (b, ts) ← parseOr f ss ts
        commaLoop f ss (items ++ [b]) true ts
  termination_by structural f

/-- `parse_or` via `parse_lazy_cond` (`parser.jl:785-807`): right associative
`||`/`.||`. -/
def parseOr (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseAnd f ss ts
    match k1 ts with
    | .oror => do
      let (b, ts) ← parseOr f ss ts.tail
      .ok (.node (.lazy "||") [a, b], ts)
    | .doror => do
      let (b, ts) ← parseOr f ss ts.tail
      .ok (.node (.lazy ".||") [a, b], ts)
    | _ => .ok (a, ts)
  termination_by structural f

/-- `parse_and` via `parse_lazy_cond` (`parser.jl:785-816`); `parse_comparison`,
`parse_pipe_lt` and `parse_pipe_gt` (`parser.jl:821-880`) reduce to
`parse_range` on the fragment. -/
def parseAnd (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseRange f ss ts
    match k1 ts with
    | .andand => do
      let (b, ts) ← parseAnd f ss ts.tail
      .ok (.node (.lazy "&&") [a, b], ts)
    | .dandand => do
      let (b, ts) ← parseAnd f ss ts.tail
      .ok (.node (.lazy ".&&") [a, b], ts)
    | _ => .ok (a, ts)
  termination_by structural f

/-- `parse_range` (`parser.jl:890-977`): `a:b`, `a:b:c` (one call), longer chains
nest to the left. `parse_invalid_ops` (`parser.jl:985-994`) reduces to
`parse_expr` since `--` is rejected by the lexer; `..` and `...` are outside the
fragment. -/
def parseRange (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseChains f false ss ts
    rangeLoop f ss a [] ts
  termination_by structural f

/-- Loop of `parse_range` (`parser.jl:905-966`): `pend` holds the operands after the
colons of the current group (`n_colons` = its length). In space-sensitive context
`[a :b]` the `:` starts a quote instead (`parser.jl:909-916`). -/
def rangeLoop (f : Nat) (ss : Bool) (cur : Cst) (pend : List Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    if k1 ts == .colon && !(ss && (tokAt ts 0).ws && !(tokAt ts 1).ws) then
      if isClosing (k2 ts) then .error .error
      else do
        let (b, ts) ← parseChains f false ss ts.tail
        match pend with
        | [] => rangeLoop f ss cur [b] ts
        | p :: _ => rangeLoop f ss (.node (.call .infix) [cur, opLeaf .colon, p, b]) [] ts
    else
      match pend with
      | [] => .ok (cur, ts)
      | ps => .ok (.node (.call .infix) (cur :: opLeaf .colon :: ps), ts)
  termination_by structural f

/-- `parse_with_chains` (`parser.jl:1015-1042`) for `parse_expr` (`times = false`:
`+ - $ .+ .-`, chaining undotted `+`, `parser.jl:1001-1003`) and `parse_term`
(`times = true`: `* / &`, chaining `*`, `parser.jl:1008-1010`). `parse_rational`,
`parse_shift`, `parse_unary_subtype` and `parse_where` (`parser.jl:1066-1145`)
reduce to `parse_juxtapose`. -/
def parseChains (f : Nat) (times ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← if times then parseJuxtapose f ss ts else parseChains f true ss ts
    chainsLoop f times ss a ts
  termination_by structural f

/-- Loop of `parse_with_chains` (`parser.jl:1018-1041`); a dotted operator gives a
`dotcall` and does not chain. -/
def chainsLoop (f : Nat) (times ss : Bool) (a : Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    let isOp := if times then (t.k == .star || t.k == .slash || t.k == .amp)
      else (t.k == .plus || t.k == .minus || t.k == .dollar || t.k == .dplus || t.k == .dminus)
    if !isOp then .ok (a, ts)
    -- for a dotted operator `preceding_whitespace(t)` is about the operator after the
    -- `.`, which never has whitespace before it
    else if ss && t.ws && !isDotTok t.k && bothUB t.k && !(tokAt ts 1).ws then .ok (a, ts)
    else do
      let (b, ts) ← if times then parseJuxtapose f ss ts.tail else parseChains f true ss ts.tail
      let chainOp : TK := if times then .star else .plus
      let (rest, ts) ← if t.k == chainOp then chainLoop f times ss t.k ts else .ok ([], ts)
      let k : NK := if isDotTok t.k then .dotcall .infix else .call .infix
      chainsLoop f times ss (.node k (a :: opLeaf t.k :: b :: rest)) ts
  termination_by structural f

/-- `parse_chain` (`parser.jl:1047-1062`): further operands of `a + b + c` /
`a * b * c`. -/
def chainLoop (f : Nat) (times ss : Bool) (op : TK) (ts : List Tok) :
    Except PE (List Cst × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    if t.k != op then .ok ([], ts)
    else if ss && t.ws && bothUB op && !(tokAt ts 1).ws then .ok ([], ts)
    else do
      let (b, ts) ← if times then parseJuxtapose f ss ts.tail else parseChains f true ss ts.tail
      let (rest, ts) ← chainLoop f times ss op ts
      .ok (b :: rest, ts)
  termination_by structural f

/-- `parse_juxtapose` (`parser.jl:1150-1207`). -/
def parseJuxtapose (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseUnary f ss ts
    juxtLoop f ss [a] a ts
  termination_by structural f

/-- Loop of `parse_juxtapose` (`parser.jl:1154-1206`). -/
def juxtLoop (f : Nat) (ss : Bool) (terms : List Cst) (last : Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    let prev := behind last
    let cond := !t.ws &&
      (prev == .num || (!isNumTok t.k && !(prev == .blockForm || prev == .synUnary))) &&
      !isOpTok t.k && !isClosing t.k
    if cond then
      if prev == .str || isStrTok t.k then .error .error
      else do
        let (b, ts) ← parseFactor f ss ts
        juxtLoop f ss (terms ++ [b]) b ts
    else .ok (if terms.length > 1 then .node .juxtapose terms else last, ts)
  termination_by structural f

/-- `parse_unary` (`parser.jl:1214-1394`), including the signed literal rule
(`parser.jl:1235-1261`, undotted `+`/`-` only) and the `+(a;b)` block-or-call
heuristic (`parser.jl:1276-1367`). A dotted operator keeps its `.` node in a
prefix call `.+(a, b)` and gives a `dotcall` otherwise (`parser.jl:1359-1362,1391`). -/
def parseUnary (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    if !isInitialOp t.k then parseFactor f ss ts
    else
      let t2 := tokAt ts 1
      if (t.k == .plus || t.k == .minus) && !t2.ws && isNumTok t2.k then
        let t3 := tokAt ts 2
        if t3.k == .caret || t3.k == .lb || t3.k == .lc then do
          let (x, ts) ← parseFactor f ss ts.tail
          .ok (.node (.call .prefixOp) [opLeaf t.k, x], ts)
        else parseFactorWithInitialEx f ss (glue (t.k == .minus) t2.k) (ts.drop 2)
      else if isClosing t2.k || t2.k == .eq then parseAtom f ss true ts
      else if t2.k == .lc || (!isUnaryOp t.k && t2.k == .lp) then parseFactor f ss ts
      else if t2.k == .lp then do
        let ts := ts.drop 2
        let initSemi := k1 ts == .semi
        let (br, ts) ← bracketsLoop f .rp {} ts
        let ts ← bumpClosing .rp ts
        let isCall := br.hadCommas || (initSemi && br.numSub > 0) ||
          (initSemi && br.numSemis == 1) || (br.numSemis == 0 && br.numSub == 0)
        if isCall then
          if t2.ws then .error .error
          else do
            let opC : Cst := if isDotTok t.k then .node (.dotop (opName t.k)) [] else opLeaf t.k
            let (c, ts) ← parseCallChain f ss (.node (.call .prefix) (opC :: br.args)) ts
            parseFactorWithInitialEx f ss c ts
        else do
          let inner : Cst := if br.numSemis > 0 then .node .block br.flat else .node .parens br.items
          let (inner, ts) ← parseCallChain f ss inner ts
          let (inner, ts) ← parseFactorWithInitialEx f ss inner ts
          .ok (.node (if isDotTok t.k then .dotcall .prefixOp else .call .prefixOp) [opLeaf t.k, inner], ts)
      else if isUnaryOp t.k then do
        let (x, ts) ← parseUnary f ss ts.tail
        .ok (.node (if isDotTok t.k then .dotcall .prefixOp else .call .prefixOp) [opLeaf t.k, x], ts)
      else .error .error
  termination_by structural f

/-- `parse_factor` (`parser.jl:1404-1408`). -/
def parseFactor (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseCall f ss ts
    parseFactorWithInitialEx f ss a ts
  termination_by structural f

/-- `parse_factor_with_initial_ex` (`parser.jl:1411-1418`). -/
def parseFactorWithInitialEx (f : Nat) (ss : Bool) (a : Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← declLoop f ss a ts
    if k1 ts == .caret then do
      let (b, ts) ← parseFactorAfter f ss ts.tail
      .ok (.node (.call .infix) [a, opLeaf .caret, b], ts)
    else .ok (a, ts)
  termination_by structural f

/-- `parse_factor_after` = `parse_RtoL(parse_juxtapose, is_prec_power)`
(`parser.jl:386-395,1421-1423`). -/
def parseFactorAfter (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseJuxtapose f ss ts
    if k1 ts == .caret then do
      let (b, ts) ← parseFactorAfter f ss ts.tail
      .ok (.node (.call .infix) [a, opLeaf .caret, b], ts)
    else .ok (a, ts)
  termination_by structural f

/-- `parse_decl_with_initial_ex` (`parser.jl:1430-1458`): `a::b::c`; `->` is
outside the fragment. -/
def declLoop (f : Nat) (ss : Bool) (a : Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    if k1 ts == .dcolon then do
      let (b, ts) ← parseCall f ss ts.tail
      declLoop f ss (.node .decl [a, b]) ts
    else .ok (a, ts)
  termination_by structural f

/-- `parse_call` (`parser.jl:1464-1474`). -/
def parseCall (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (a, ts) ← parseUnaryPrefix f ss ts
    parseCallChain f ss a ts
  termination_by structural f

/-- `parse_unary_prefix` (`parser.jl:1483-1512`): `$a`, `&a`, `::a`, a bare `$` or `&`. -/
def parseUnaryPrefix (f : Nat) (ss : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    match k1 ts with
    | .dollar =>
      if isClosing (k2 ts) then .ok (.leaf .synUnary false (.sym "$"), ts.tail)
      else do
        let (x, ts) ← parseUnaryPrefix f ss ts.tail
        .ok (.node .dollar [x], ts)
    | .dcolon => do
      let (x, ts) ← parseCall f ss ts.tail
      .ok (.node .declPrefix [x], ts)
    | .amp =>
      if isClosing (k2 ts) then .ok (.leaf .synUnary false (.sym "&"), ts.tail)
      else do
        let (x, ts) ← parseCall f ss ts.tail
        .ok (.node .amp [x], ts)
    | _ => parseAtom f ss true ts
  termination_by structural f

/-- `parse_call_chain` (`parser.jl:1542-1547`): `2(x)` is juxtaposition. -/
def parseCallChain (f : Nat) (ss : Bool) (a : Cst) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    if behind a == .num && k1 ts == .lp then .ok (a, ts)
    else callChainLoop f ss a (strmacIdent a) ts
  termination_by structural f

/-- Loop of `parse_call_chain` (`parser.jl:1557-1870`): calls, indexing, curly
braces and adjoint; a string or command literal right after an identifier is a
string/command macro, outside the fragment. -/
def callChainLoop (f : Nat) (ss : Bool) (a : Cst) (strmac : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    if ss && t.ws && (t.k == .lp || t.k == .lb || t.k == .lc || isStrTok t.k || isCmdTok t.k) then
      .ok (a, ts)
    else
      match t.k with
      | .lp =>
        if t.ws then .error .error
        else do
          let (br, ts) ← bracketsLoop f .rp {} ts.tail
          let ts ← bumpClosing .rp ts
          callChainLoop f ss (.node (.call .prefix) (a :: br.args)) false ts
      | .lb =>
        if t.ws then .error .error
        else do
          let (ck, es, ts) ← parseCat f .rb ts.tail
          let k : NK := match ck with
            | .vect => .ref
            | .hcat => .typedHcat
            | .vcat => .typedVcat
          callChainLoop f ss (.node k (a :: es)) false ts
      | .prime =>
        if t.ws then .ok (a, ts)
        else callChainLoop f ss (.node (.call .postfix) [a, opLeaf .prime]) false ts.tail
      | .lc =>
        if t.ws then .error .error
        else do
          let (br, ts) ← bracketsLoop f .rc {} ts.tail
          let ts ← bumpClosing .rc ts
          callChainLoop f ss (.node .curly (a :: br.args)) false ts
      | .str _ => if !t.ws && strmac then .error .unknown else .ok (a, ts)
      | .cmd _ => if !t.ws && strmac then .error .unknown else .ok (a, ts)
      | _ => .ok (a, ts)
  termination_by structural f

/-- `parse_atom` (`parser.jl:3631-3856`) on the fragment's tokens. `check` is
`check_identifiers`. A dotted operator is a `.` node (`parser.jl:3637-3638,3742`),
invalid as an identifier only for the syntactic `.&&`/`.||` (`parser.jl:3758`). -/
def parseAtom (f : Nat) (ss check : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let t := tokAt ts 0
    match t.k with
    | .dandand => if check then .error .error else .ok (.node (.dotop "&&") [], ts.tail)
    | .doror => if check then .error .error else .ok (.node (.dotop "||") [], ts.tail)
    | .dplus => .ok (.node (.dotop "+") [], ts.tail)
    | .dminus => .ok (.node (.dotop "-") [], ts.tail)
    | .prime => .error .unknown
    | .colon =>
      let t2 := tokAt ts 1
      if isClosing t2.k then .ok (.leaf .other false (.sym ":"), ts.tail)
      else if t2.ws then .error .error
      else do
        let (q, ts) ← parseAtom f ss false ts.tail
        .ok (.node .quote [q], ts)
    | .eq => if check then .error .error else .ok (.leaf .other false (.sym "="), ts.tail)
    | .andand => if check then .error .error else .ok (.leaf .other false (.sym "&&"), ts.tail)
    | .oror => if check then .error .error else .ok (.leaf .other false (.sym "||"), ts.tail)
    | .ident s => .ok (.leaf .ident true (.sym s), ts.tail)
    | .plus | .minus | .star | .slash | .caret | .bang | .dollar | .dcolon | .amp =>
      .ok (opLeaf t.k, ts.tail)
    | .str s => .ok (.leaf .str false (.str s), ts.tail)
    | .cmd s => .ok (.leaf .other false (cmdJE s), ts.tail)
    | .int v => .ok (.leaf .num false (.int v), ts.tail)
    | .flt ip fp => .ok (.leaf .num false (.flt false ip fp), ts.tail)
    | .lp => parseParen f check ts
    | .lb => do
      let (ck, es, ts) ← parseCat f .rb ts.tail
      let k : NK := match ck with
        | .vect => .vect
        | .hcat => .hcat
        | .vcat => .vcat
      .ok (.node k es, ts)
    | .lc => do
      -- emit_braces, parser.jl:3611-3623
      let (ck, es, ts) ← parseCat f .rc ts.tail
      let c : Cst := match ck with
        | .vect => .node .braces es
        | .hcat => .node .bracescat [.node .row es]
        | .vcat => .node .bracescat es
      .ok (c, ts)
    | _ => .error .error
  termination_by structural f

/-- `parse_paren` (`parser.jl:3224-3296`). -/
def parseParen (f : Nat) (check : Bool) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let ts := ts.tail
    let k := k1 ts
    if k == .rp then .ok (.node .tuple [], ts.tail)
    else if k == .eq || k == .andand || k == .oror || k == .dandand || k == .doror then do
      let (x, ts) ← parseAtom f false check ts
      let ts ← bumpClosing .rp ts
      .ok (.node .parens [x], ts)
    else if !check && k == .dcolon && k2 ts == .rp then
      .ok (.node .parens [.leaf .synUnary false (.sym "::")], ts.drop 2)
    else do
      let initSemi := k == .semi
      let (br, ts) ← bracketsLoop f .rp {} ts
      let ts ← bumpClosing .rp ts
      let isTuple := br.hadCommas || (initSemi && (br.numSemis == 1 || br.numSub > 0))
      if isTuple then .ok (.node .tuple br.args, ts)
      else if br.numSemis > 0 then .ok (.node .block br.flat, ts)
      else .ok (.node .parens br.items, ts)
  termination_by structural f

/-- Loop of `parse_brackets` (`parser.jl:3314-3380`, space-insensitive). The
caller bumps the closing token. -/
def bracketsLoop (f : Nat) (closer : TK) (br : BR) (ts : List Tok) :
    Except PE (BR × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let k := k1 ts
    if k == closer then .ok (br, ts)
    else if k == .semi then
      bracketsLoop f closer { br with secs := br.secs ++ [[]], numSemis := br.numSemis + 1 } ts.tail
    else if isClosing k then .ok (br, ts)
    else do
      let (e, ts) ← parseAssignment f false false ts
      let br := br.push e
      let k := k1 ts
      if k == .comma then bracketsLoop f closer { br with hadCommas := true } ts.tail
      else if k == .semi || k == closer then bracketsLoop f closer br ts
      else .ok (br, ts)
  termination_by structural f

/-- `parse_cat` (`parser.jl:3164-3211`), the opening bracket consumed; includes
`parse_vect` (`parser.jl:2897-2912`). Space sensitive. -/
def parseCat (f : Nat) (closer : TK) (ts : List Tok) :
    Except PE (CatK × List Cst × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    let k := k1 ts
    if k == closer then .ok (.vect, [], ts.tail)
    else if k == .semi then .error .unknown
    else do
      let (first, ts) ← parseAssignment f false true ts
      let k := k1 ts
      if k == .comma || (isClosing k && k != .semi) then do
        let ts := if k == .comma then ts.tail else ts
        let (br, ts) ← bracketsLoop f closer {} ts
        let ts ← bumpClosing closer ts
        .ok (.vect, first :: br.args, ts)
      else arrayStart f closer first ts
  termination_by structural f

/-- `parse_array` (`parser.jl:2982-3021`) up to its loop. -/
def arrayStart (f : Nat) (closer : TK) (first : Cst) (ts : List Tok) :
    Except PE (CatK × List Cst × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (bp, ts) ← arraySep ts
    match bp with
    | none => do
      let ts ← bumpClosing closer ts
      .ok (.hcat, [first], ts)
    | some b => arrayOuter f closer b [first] ts
  termination_by structural f

/-- Loop of `parse_array` (`parser.jl:3004-3020`); `nrow`/`ncat` are outside the
fragment. -/
def arrayOuter (f : Nat) (closer : TK) (bp : Int) (acc : List Cst) (ts : List Tok) :
    Except PE (CatK × List Cst × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (sub, nb, ts) ← arrayInner f bp (some bp) [] ts
    match nb with
    | none => do
      let ts ← bumpClosing closer ts
      .ok ((if bp == -1 then .vcat else .hcat), acc ++ sub, ts)
    | some nbp =>
      if bp == 0 then arrayOuter f closer nbp [.node .row (acc ++ sub)] ts
      else .error .unknown
  termination_by structural f

/-- `parse_array_inner` (`parser.jl:3036-3069`): elements joined by separators
of binding power at least `bp0`; returns them and the next binding power
(`none` = `typemin(Int)`). -/
def arrayInner (f : Nat) (bp0 : Int) (bp : Option Int) (acc : List Cst) (ts : List Tok) :
    Except PE (List Cst × Option Int × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    match bp with
    | none => .ok (acc, none, ts)
    | some b =>
      if b < bp0 then .ok (acc, some b, ts)
      else if isClosing (k1 ts) then .ok (acc, none, ts)
      else if b == bp0 then do
        let (e, ts) ← parseAssignment f false true ts
        let (nb, ts) ← arraySep ts
        arrayInner f bp0 nb (acc ++ [e]) ts
      else do
        let (sub, nb, ts) ← arrayInner f b (some b) [] ts
        if b == 0 then
          match acc.getLast? with
          | some lst => arrayInner f bp0 nb (acc.dropLast ++ [.node .row (lst :: sub)]) ts
          | none => .error .unknown
        else .error .unknown
  termination_by structural f

/-- `parse_docstring` (`parser.jl:530-561`) with `down = parse_eq`; a docstring
(`"doc" x`) is outside the fragment. `parse_public` (`parser.jl:514-525`)
reduces to it. -/
def parseDocstring (f : Nat) (ts : List Tok) : PR :=
  match f with
  | 0 => .error .unknown
  | f + 1 => do
    let (e, ts) ← parseAssignment f true false ts
    if behind e == .str && !isClosing (k1 ts) then .error .unknown else .ok (e, ts)

/-- Loop of `parse_Nary` for `parse_stmts` (`parser.jl:420-433,490-492`): returns
the statements and the number of `;` delimiters. -/
def stmtsLoop (f : Nat) (items : List Cst) (nd : Nat) (ts : List Tok) :
    Except PE (List Cst × Nat × List Tok) :=
  match f with
  | 0 => .error .unknown
  | f + 1 =>
    if k1 ts == .semi then
      let ts := ts.tail
      let k := k1 ts
      if k == .eof then .ok (items, nd + 1, ts)
      else if k == .semi then stmtsLoop f items (nd + 1) ts
      else do
        let (e, ts) ← parseDocstring f ts
        stmtsLoop f (items ++ [e]) (nd + 1) ts
    else .ok (items, nd, ts)
  termination_by structural f

end

/-- `parse_stmts` (`parser.jl:490-507`): trailing tokens are the error "extra
tokens after end of expression"; a `toplevel` node (any `;`) is outside the
fragment because its `LineNumberNode`s survive `remove_linenums!`. -/
def parseStmts (f : Nat) (ts : List Tok) : Except PE Cst := do
  let (items, ts) ← if k1 ts == .semi then .ok ([], ts) else do
    let (e, ts) ← parseDocstring f ts
    .ok ([e], ts)
  let (items, nd, ts) ← stmtsLoop f items 0 ts
  if k1 ts != .eof then .error .error
  else if nd != 0 then .error .unknown
  else match items with
    | [e] => .ok e
    | _ => .error .unknown

/-! ## Conversion to `Expr` (`JuliaSyntax/src/integration/expr.jl`) -/

def isParamsJE : JE → Bool
  | .node "parameters" _ => true
  | _ => false

def eqToKw : JE → JE
  | .node "=" as => .node "kw" as
  | e => e

/-- `fixup_Expr_child` (`expr.jl:146-175`) after `_strip_parens` (`parens` nodes
convert to their child directly): `=` becomes `kw` in a prefix call or `ref`
argument other than the first (`kwCall`); `=` inside `parameters` becomes `kw`
unless the parent is `vect`, `curly`, `braces` or `ref` (`kwParams`). -/
def fixupChild (kwCall kwParams first : Bool) : JE → JE
  | .node "=" as => if kwCall && !first then .node "kw" as else .node "=" as
  | .node "parameters" ps => .node "parameters" (if kwParams then ps.map eqToKw else ps)
  | e => e

/-- `parseargs!` (`expr.jl:198-216`): fix up every child; `first` is the first
child in source order. -/
def fixArgs (kwCall kwParams : Bool) : List JE → List JE
  | [] => []
  | a :: as => fixupChild kwCall kwParams true a :: as.map (fixupChild kwCall kwParams false)

def prependArg (acc : JE) : JE → JE
  | .node h qs => .node h (acc :: qs)
  | e => e

/-- `_reorder_parameters!(args, pos)` (`expr.jl:31-49`): nest the trailing
`parameters` blocks (each into the one before it) and move the result to
position `pos` (1-based). -/
def reorderParams (pos : Nat) (args : List JE) : List JE :=
  let rev := args.reverse
  match rev.takeWhile isParamsJE with
  | [] => args
  | last :: before =>
    let nested := before.foldl prependArg last
    let pre := (rev.dropWhile isParamsJE).reverse
    pre.take (pos - 1) ++ nested :: pre.drop (pos - 1)

def swap12 : List JE → List JE
  | a :: b :: r => b :: a :: r
  | l => l

/-- A leaf's value; integer literals outside `Int64` become `Int128`/`BigInt`
macro calls (`expr.jl:248-256`), outside the fragment. -/
def leafOk : JE → Option JE
  | .int v => if -9223372036854775808 ≤ v ∧ v < 9223372036854775808 then some (.int v) else none
  | e => some e

/-- `_node_to_expr` (`expr.jl:325-677`) for one node, given its converted
children. -/
def convNode : NK → List JE → Option JE
  | .call ct, as =>
    -- expr.jl:395-425: infix and postfix calls swap the first two children;
    -- `x'` gets head `'`
    let fx := fixArgs (ct == .prefix) true as
    let sw := if ct == .infix || ct == .postfix then swap12 fx else fx
    match ct, sw with
    | .postfix, .sym "'" :: rest => some (.node "'" (reorderParams 2 rest))
    | _, _ => some (.node "call" (reorderParams 2 sw))
  | .juxtapose, as => some (.node "call" (.sym "*" :: fixArgs false true as))    -- expr.jl:627-629
  | .parens, [a] => some a                                                         -- expr.jl:51-64
  | .block, as => some (.node "block" (fixArgs false true as))                     -- expr.jl:283-297
  | .toplevel, as => some (.node "toplevel" (fixArgs false true as))
  | .tuple, as => some (.node "tuple" (reorderParams 1 (fixArgs false true as)))   -- expr.jl:449-451
  | .params, as => some (.node "parameters" (fixArgs false true as))
  | .ref, as => some (.node "ref" (reorderParams 2 (fixArgs true false as)))       -- expr.jl:437-439
  | .vect, as => some (.node "vect" (reorderParams 1 (fixArgs false false as)))
  | .hcat, as => some (.node "hcat" (fixArgs false true as))
  | .vcat, as => some (.node "vcat" (fixArgs false true as))
  | .row, as => some (.node "row" (fixArgs false true as))
  | .typedHcat, as => some (.node "typed_hcat" (fixArgs false true as))
  | .typedVcat, as => some (.node "typed_vcat" (fixArgs false true as))
  | .curly, as => some (.node "curly" (reorderParams 2 (fixArgs false false as)))
  | .braces, as => some (.node "braces" (reorderParams 1 (fixArgs false false as)))
  | .bracescat, as => some (.node "bracescat" (fixArgs false true as))
  | .quote, [a] =>                                                                 -- expr.jl:588-596
    match a with
    | .node _ _ => some (.node "quote" [a])
    | .qn _ => some (.node "quote" [a])
    | _ => some (.qn a)
  | .dollar, as => some (.node "$" (fixArgs false true as))
  | .decl, as => some (.node "::" (fixArgs false true as))
  | .declPrefix, as => some (.node "::" (fixArgs false true as))
  | .assign, as => some (.node "=" (fixArgs false true as))
  | .func, [a1, a2] =>                                                             -- expr.jl:555-580
    let a2' := match a2, a1 with
      | .node "block" _, _ => a2
      | _, .node "'" _ => a2
      | _, _ => .node "block" [a2]
    some (.node "=" [a1, a2'])
  | .lazy h, as => some (.node h (fixArgs false true as))
  | .amp, as => some (.node "&" (fixArgs false true as))
  | .dotcall ct, as =>
    -- expr.jl:410-421: an operator dotcall is a call of the dotted symbol
    let fx := fixArgs false true as
    let sw := if ct == .infix || ct == .postfix then swap12 fx else fx
    match reorderParams 2 sw with
    | .sym s :: rest => some (.node "call" (.sym ("." ++ s) :: rest))
    | _ => none
  | _, _ => none

/-- Parents whose `.` operator children coalesce to one symbol
(`coalesce_dot`, `expr.jl:153-154`). -/
def coalesces : NK → Bool
  | .call _ | .dotcall _ | .curly | .quote => true
  | _ => false

mutual
/-- `node_to_expr` (`expr.jl:231-306`) of a child, including the part of
`fixup_Expr_child` (`expr.jl:155-164`) that depends on the child's syntax: `co`
is `coalesce_dot` of the parent, `first` whether the child is the first, `wp`
whether parentheses were stripped. A dotted operator `(. op)` (`expr.jl:432-436`)
becomes the symbol `.op` if it is the unparenthesized first child of a coalescing
parent or `op` is syntactic, and `Expr(:., op)` otherwise. -/
def convKid (co first wp : Bool) : Cst → Option JE
  | .leaf _ _ v => leafOk v
  | .node .parens [c] => convKid co first true c
  | .node (.dotop h) _ =>
    if (!wp && co && first) || h == "&&" || h == "||" then some (.sym ("." ++ h))
    else some (.node "." [.sym h])
  | .node k ch => do
    let as ← convKids (coalesces k) true ch
    convNode k as
def convKids (co first : Bool) : List Cst → Option (List JE)
  | [] => some []
  | c :: cs => do
    let a ← convKid co first false c
    let r ← convKids co false cs
    some (a :: r)
end

/-- The whole tree, as a child of the top-level wrapper (`expr.jl:687-705`). -/
def conv (c : Cst) : Option JE := convKid false false false c

/-- Fuel for the parser: every recursive call consumes one unit and the
recursion depth is bounded by a small multiple of the token count. Running out
gives `.unknown`. -/
def parseFuel (n : Nat) : Nat := 40 * n + 40

end Syntax

open Syntax in
/-- `Meta.parse(String(src))` on 1.13.2 and master (`base/meta.jl:406-422`,
`JuliaSyntax/src/integration/hooks.jl:195-216`), see the module docstring for the
fragment and the encodings. Whitespace-only input returns `nothing` in Julia and
`.unknown` here. -/
def parse (src : List UInt8) : PResult :=
  match lex src with
  | .unknown => .unknown
  | .error => .error
  | .ok ts =>
    if k1 ts == .eof then .unknown
    else
      match parseStmts (parseFuel ts.length) ts with
      | .error .error => .error
      | .error .unknown => .unknown
      | .ok c =>
        match conv c with
        | some e => .ok e
        | none => .unknown

/-! ## Lemmas -/

namespace Syntax

/-- `n` is the bytes of an identifier of the fragment: `[A-Za-z_][A-Za-z0-9_!]*`, not a
keyword (`reservedNames`). -/
def identOk : List UInt8 → Bool
  | b :: bs => isIdStartB b && bs.all isIdCharB && !reservedNames.contains (asciiStr (b :: bs))
  | [] => false

/-- `rest` cannot continue an identifier (`lex_identifier`, `tokenize.jl:1215-1237`). -/
def stopOk : List UInt8 → Bool
  | [] => true
  | c :: _ => !isIdCharB c && c != 61

theorem idChar_ne_61 {c : UInt8} (h : isIdCharB c = true) : c ≠ 61 := by
  rintro rfl; exact absurd h (by decide)

theorem takeIdent_append (n rest : List UInt8) (hn : n.all isIdCharB = true)
    (hr : stopOk rest = true) : takeIdent (n ++ rest) = (n, rest) := by
  induction n with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r =>
      simp only [stopOk, Bool.and_eq_true, Bool.not_eq_true'] at hr
      simp [takeIdent, hr.1]
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    obtain ⟨hb, hbs⟩ := hn
    have hne : ((b == 33 && (bs ++ rest).head? == some 61) || !isIdCharB b) = false := by
      cases bs with
      | nil =>
        cases rest with
        | nil => simp [hb]
        | cons c r =>
          simp only [stopOk, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hr
          simp [hb, hr.2]
      | cons c cs =>
        simp only [List.all_cons, Bool.and_eq_true] at hbs
        simp [hb, idChar_ne_61 hbs.1]
    rw [List.cons_append, takeIdent, hne]
    simp [ih hbs]

theorem lexGo_succ (n : Nat) (b : UInt8) (r : List UInt8) (ws adj : Bool) (acc : List Tok) :
    lexGo (n + 1) (b :: r) ws adj acc =
      (match lexStep b r adj with
        | .tok k rest adj' => lexGo n rest false adj' (⟨k, ws⟩ :: acc)
        | .space rest => lexGo n rest true false acc
        | .unknown => .unknown
        | .error => .error) := rfl

theorem lexStep_ident (b : UInt8) (bs rest : List UInt8) (adj : Bool)
    (hn : identOk (b :: bs) = true) (hr : stopOk rest = true) :
    lexStep b (bs ++ rest) adj = .tok (.ident (asciiStr (b :: bs))) rest true := by
  simp only [identOk, Bool.and_eq_true, Bool.not_eq_true'] at hn
  obtain ⟨⟨hb, hbs⟩, hres⟩ := hn
  unfold lexStep
  simp only [hb, ↓reduceIte]
  rw [← List.cons_append,
    takeIdent_append (b :: bs) rest (by simp [List.all_cons, hbs, isIdCharB, hb]) hr]
  simp only [hres, Bool.false_eq_true, ↓reduceIte]

theorem ne_of_idStart {b k : UInt8} (h : isIdStartB b = true) (hk : isIdStartB k = false) :
    b ≠ k := by
  rintro rfl; simp_all

theorem compoundFollows_idStart {b : UInt8} (r : List UInt8) (h : isIdStartB b = true) :
    compoundFollows (b :: r) = false := by
  have h61 := ne_of_idStart (k := 61) h (by decide)
  unfold compoundFollows
  split <;> simp_all

theorem lexStep_minus (b : UInt8) (r : List UInt8) (adj : Bool) (hb : isIdStartB b = true) :
    lexStep 45 (b :: r) adj = .tok .minus (b :: r) false := by
  have h45 := ne_of_idStart (k := 45) hb (by decide)
  have h62 := ne_of_idStart (k := 62) hb (by decide)
  have e : lexStep 45 (b :: r) adj = (match b :: r with
      | 45 :: 62 :: _ => Step.unknown
      | 45 :: _ => .error
      | 62 :: _ => .unknown
      | _ => if compoundFollows (b :: r) then .unknown else .tok .minus (b :: r) false) := rfl
  rw [e, compoundFollows_idStart r hb]
  split <;> simp_all

theorem lexStep_plus (b : UInt8) (r : List UInt8) (adj : Bool) (hb : isIdStartB b = true) :
    lexStep 43 (b :: r) adj = .tok .plus (b :: r) false := by
  have h43 := ne_of_idStart (k := 43) hb (by decide)
  have e : lexStep 43 (b :: r) adj =
      (if (b :: r).head? == some 43 || compoundFollows (b :: r) then .unknown
       else .tok .plus (b :: r) false) := rfl
  rw [e, compoundFollows_idStart r hb]
  simp [h43]

theorem lexStep_bang (b : UInt8) (r : List UInt8) (adj : Bool) (hb : isIdStartB b = true) :
    lexStep 33 (b :: r) adj = .tok .bang (b :: r) false := by
  have h61 := ne_of_idStart (k := 61) hb (by decide)
  have e : lexStep 33 (b :: r) adj =
      (if (b :: r).head? == some 61 then .unknown else .tok .bang (b :: r) false) := rfl
  rw [e]
  simp [h61]

theorem identOk_cons {n : List UInt8} (h : identOk n = true) :
    ∃ b bs, n = b :: bs ∧ isIdStartB b = true := by
  match n, h with
  | b :: bs, h =>
    simp only [identOk, Bool.and_eq_true] at h
    exact ⟨b, bs, rfl, h.1.1⟩

theorem lex_prefix (op : UInt8) (k : TK) (n : List UInt8) (hn : identOk n = true)
    (hop : ∀ b r adj, isIdStartB b = true → lexStep op (b :: r) adj = .tok k (b :: r) false) :
    lex (op :: n) = .ok [⟨k, false⟩, ⟨.ident (asciiStr n), false⟩, ⟨.eof, false⟩] := by
  obtain ⟨b, bs, rfl, hb⟩ := identOk_cons hn
  unfold lex
  rw [show (op :: b :: bs).length + 1 = (bs.length + 1) + 1 + 1 by simp]
  rw [lexGo_succ, hop b bs false hb]
  dsimp only
  have h := lexStep_ident b bs [] false hn rfl
  rw [List.append_nil] at h
  rw [lexGo_succ, h]
  rfl

/-- `-n` parses to `Expr(:call, :-, n)` for an identifier `n`. -/
theorem parse_neg_ident (n : List UInt8) (hn : identOk n = true) :
    parse (45 :: n) = .ok (.node "call" [.sym "-", .sym (asciiStr n)]) := by
  unfold parse
  rw [lex_prefix 45 .minus n hn (fun b r adj hb => lexStep_minus b r adj hb)]
  rfl

/-- `+n` parses to `Expr(:call, :+, n)`. -/
theorem parse_plus_ident (n : List UInt8) (hn : identOk n = true) :
    parse (43 :: n) = .ok (.node "call" [.sym "+", .sym (asciiStr n)]) := by
  unfold parse
  rw [lex_prefix 43 .plus n hn (fun b r adj hb => lexStep_plus b r adj hb)]
  rfl

/-- `!n` parses to `Expr(:call, :!, n)`. -/
theorem parse_not_ident (n : List UInt8) (hn : identOk n = true) :
    parse (33 :: n) = .ok (.node "call" [.sym "!", .sym (asciiStr n)]) := by
  unfold parse
  rw [lex_prefix 33 .bang n hn (fun b r adj hb => lexStep_bang b r adj hb)]
  rfl


theorem lexStep_space (r : List UInt8) (adj : Bool) : lexStep 32 r adj = .space r := rfl

theorem lex_binary (op : UInt8) (k : TK) (n1 n2 : List UInt8) (h1 : identOk n1 = true)
    (h2 : identOk n2 = true) (hop : ∀ r adj, lexStep op (32 :: r) adj = .tok k (32 :: r) false) :
    lex (n1 ++ 32 :: op :: 32 :: n2) = .ok [⟨.ident (asciiStr n1), false⟩, ⟨k, true⟩,
      ⟨.ident (asciiStr n2), true⟩, ⟨.eof, false⟩] := by
  obtain ⟨b1, bs1, rfl, _⟩ := identOk_cons h1
  obtain ⟨b2, bs2, rfl, _⟩ := identOk_cons h2
  unfold lex
  rw [show (b1 :: bs1 ++ 32 :: op :: 32 :: b2 :: bs2).length + 1 =
      (bs1.length + bs2.length) + 1 + 1 + 1 + 1 + 1 + 1 by simp; omega]
  rw [List.cons_append, lexGo_succ, lexStep_ident b1 bs1 _ false h1 rfl]
  dsimp only
  rw [lexGo_succ, lexStep_space]
  dsimp only
  rw [lexGo_succ, hop]
  dsimp only
  rw [lexGo_succ, lexStep_space]
  dsimp only
  have h := lexStep_ident b2 bs2 [] false h2 rfl
  rw [List.append_nil] at h
  rw [lexGo_succ, h]
  rfl

/-- `n1 + n2` parses to `Expr(:call, :+, n1, n2)` for identifiers `n1`, `n2`. -/
theorem parse_add_ident (n1 n2 : List UInt8) (h1 : identOk n1 = true) (h2 : identOk n2 = true) :
    parse (n1 ++ 32 :: 43 :: 32 :: n2) =
      .ok (.node "call" [.sym "+", .sym (asciiStr n1), .sym (asciiStr n2)]) := by
  unfold parse; rw [lex_binary 43 .plus n1 n2 h1 h2 (fun _ _ => rfl)]; rfl

/-- `n1 - n2` parses to `Expr(:call, :-, n1, n2)`. -/
theorem parse_sub_ident (n1 n2 : List UInt8) (h1 : identOk n1 = true) (h2 : identOk n2 = true) :
    parse (n1 ++ 32 :: 45 :: 32 :: n2) =
      .ok (.node "call" [.sym "-", .sym (asciiStr n1), .sym (asciiStr n2)]) := by
  unfold parse; rw [lex_binary 45 .minus n1 n2 h1 h2 (fun _ _ => rfl)]; rfl

/-- `n1 * n2` parses to `Expr(:call, :*, n1, n2)`. -/
theorem parse_mul_ident (n1 n2 : List UInt8) (h1 : identOk n1 = true) (h2 : identOk n2 = true) :
    parse (n1 ++ 32 :: 42 :: 32 :: n2) =
      .ok (.node "call" [.sym "*", .sym (asciiStr n1), .sym (asciiStr n2)]) := by
  unfold parse; rw [lex_binary 42 .star n1 n2 h1 h2 (fun _ _ => rfl)]; rfl

/-- `n1 / n2` parses to `Expr(:call, :/, n1, n2)`. -/
theorem parse_div_ident (n1 n2 : List UInt8) (h1 : identOk n1 = true) (h2 : identOk n2 = true) :
    parse (n1 ++ 32 :: 47 :: 32 :: n2) =
      .ok (.node "call" [.sym "/", .sym (asciiStr n1), .sym (asciiStr n2)]) := by
  unfold parse; rw [lex_binary 47 .slash n1 n2 h1 h2 (fun _ _ => rfl)]; rfl

/-- `n1 ^ n2` parses to `Expr(:call, :^, n1, n2)`. -/
theorem parse_pow_ident (n1 n2 : List UInt8) (h1 : identOk n1 = true) (h2 : identOk n2 = true) :
    parse (n1 ++ 32 :: 94 :: 32 :: n2) =
      .ok (.node "call" [.sym "^", .sym (asciiStr n1), .sym (asciiStr n2)]) := by
  unfold parse; rw [lex_binary 94 .caret n1 n2 h1 h2 (fun _ _ => rfl)]; rfl

/-- An identifier parses to its symbol. -/
theorem parse_ident (n : List UInt8) (hn : identOk n = true) : parse n = .ok (.sym (asciiStr n)) := by
  obtain ⟨b, bs, rfl, _⟩ := identOk_cons hn
  have hl : lex (b :: bs) = .ok [⟨.ident (asciiStr (b :: bs)), false⟩, ⟨.eof, false⟩] := by
    unfold lex
    rw [show (b :: bs).length + 1 = bs.length + 1 + 1 by simp]
    have h := lexStep_ident b bs [] false hn rfl
    rw [List.append_nil] at h
    rw [lexGo_succ, h]
    rfl
  unfold parse; rw [hl]; rfl


/-- ASCII bytes of a string (each character's code point, truncated to a byte). -/
def asciiBytes (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

/-- `s` is an ASCII identifier of the fragment (`identOk`). -/
def IdentName (s : String) : Prop :=
  s.toList.all (fun c => decide (c.toNat < 128)) = true ∧ identOk (asciiBytes s) = true

theorem asciiStr_asciiBytes (s : String)
    (h : s.toList.all (fun c => decide (c.toNat < 128)) = true) : asciiStr (asciiBytes s) = s := by
  unfold asciiStr asciiBytes
  rw [List.map_map]
  have hc : ∀ c ∈ s.toList, ((fun b : UInt8 => Char.ofNat b.toNat) ∘ (fun c : Char => c.toNat.toUInt8)) c = c := by
    intro c hmem
    have hlt : c.toNat < 128 := by simpa using List.all_eq_true.mp h c hmem
    simp only [Function.comp]
    have : (c.toNat.toUInt8).toNat = c.toNat := by
      simp [Nat.toUInt8]
      omega
    rw [this, Char.ofNat_toNat]
  rw [List.map_congr_left hc]
  simp only [List.map_id']
  exact String.ofList_toList

theorem asciiBytes_append (s t : String) : asciiBytes (s ++ t) = asciiBytes s ++ asciiBytes t := by
  simp [asciiBytes, String.toList_append]

/-- `op n` for `op ∈ - + !` and an identifier `n` parses to `Expr(:call, op, n)`. -/
theorem parse_unary_ident (op : String) (hop : op ∈ ["-", "+", "!"]) (n : String)
    (hn : IdentName n) : parse (asciiBytes (op ++ n)) = .ok (.node "call" [.sym op, .sym n]) := by
  obtain ⟨hasc, hid⟩ := hn
  rw [asciiBytes_append]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl
  · rw [show asciiBytes "-" = [45] by decide, List.singleton_append, parse_neg_ident _ hid,
      asciiStr_asciiBytes n hasc]
  · rw [show asciiBytes "+" = [43] by decide, List.singleton_append, parse_plus_ident _ hid,
      asciiStr_asciiBytes n hasc]
  · rw [show asciiBytes "!" = [33] by decide, List.singleton_append, parse_not_ident _ hid,
      asciiStr_asciiBytes n hasc]

/-- `a op b` (single spaces) for `op ∈ + - * / ^` and identifiers `a`, `b` parses to
`Expr(:call, op, a, b)`. -/
theorem parse_binary_ident (op : String) (hop : op ∈ ["+", "-", "*", "/", "^"]) (a b : String)
    (ha : IdentName a) (hb : IdentName b) :
    parse (asciiBytes (a ++ " " ++ op ++ " " ++ b)) = .ok (.node "call" [.sym op, .sym a, .sym b]) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  simp only [asciiBytes_append, List.append_assoc, show asciiBytes " " = [32] by decide,
    List.cons_append]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · rw [show asciiBytes "+" = [43] by decide]
    simp only [List.nil_append, List.cons_append]
    rw [parse_add_ident _ _ ha2 hb2,
      asciiStr_asciiBytes a ha1, asciiStr_asciiBytes b hb1]
  · rw [show asciiBytes "-" = [45] by decide]
    simp only [List.nil_append, List.cons_append]
    rw [parse_sub_ident _ _ ha2 hb2,
      asciiStr_asciiBytes a ha1, asciiStr_asciiBytes b hb1]
  · rw [show asciiBytes "*" = [42] by decide]
    simp only [List.nil_append, List.cons_append]
    rw [parse_mul_ident _ _ ha2 hb2,
      asciiStr_asciiBytes a ha1, asciiStr_asciiBytes b hb1]
  · rw [show asciiBytes "/" = [47] by decide]
    simp only [List.nil_append, List.cons_append]
    rw [parse_div_ident _ _ ha2 hb2,
      asciiStr_asciiBytes a ha1, asciiStr_asciiBytes b hb1]
  · rw [show asciiBytes "^" = [94] by decide]
    simp only [List.nil_append, List.cons_append]
    rw [parse_pow_ident _ _ ha2 hb2,
      asciiStr_asciiBytes a ha1, asciiStr_asciiBytes b hb1]

end Syntax

/-! ## Concrete checks against Julia outputs -/

example : parse "-1".toUTF8.toList = .ok (.int (-1)) := by decide +kernel
example : parse [45, 49] = .ok (.int (-1)) := by decide
example : parse "--1".toUTF8.toList = .error := by decide +kernel
example : parse "-0.0 ^ 2".toUTF8.toList =
    .ok (.node "call" [.sym "-", .node "call" [.sym "^", .flt false 0 [0], .int 2]]) := by
  decide +kernel
example : parse "-1'".toUTF8.toList = .error := by decide +kernel
example : parse "x::-T".toUTF8.toList = .error := by decide +kernel
example : parse "+(b; a = 1)".toUTF8.toList =
    .ok (.node "call" [.sym "+", .node "block" [.sym "b", .node "=" [.sym "a", .int 1]]]) := by
  decide +kernel
example : parse "`echo \\`x\\``".toUTF8.toList =
    .ok (.node "macrocall" [.node "globalref" [.sym "Core", .sym "@cmd"], .node "nothing" [],
      .str "echo `x`"]) := by decide +kernel
example : parse "(.-)(x)".toUTF8.toList = .ok (.node "call" [.node "." [.sym "-"], .sym "x"]) := by
  decide +kernel
example : parse "a : :b".toUTF8.toList = .ok (.node "call" [.sym ":", .sym "a", .qn (.sym "b")]) := by
  decide +kernel
example : lexCmdEnd "`echo `x``".toUTF8.toList = some 7 := by decide +kernel

end JuliaLean.Show
