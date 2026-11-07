import JuliaLean.Proofs.base.strings.io.literalParser
import JuliaLean.Proofs.base.show.operatorFacts


namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

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
