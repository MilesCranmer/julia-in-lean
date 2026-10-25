import JuliaLean.Markdown.Ast

/-!
# Markdown: inline readers

Models of `readuntil`, `peekprev`, `parse_inline_wrapper`
(`stdlib/Markdown/src/parse/util.jl`), `read_code_span` and `inline_code`
(`Common/inline.jl`) at master `bbfa0ce4150`.

`isword` (`parse/util.jl:194-202`) needs the Unicode punctuation and symbol
categories; `parse_inline_wrapper` takes it as the argument `isword`. It is only
called when `intraword = false` (the `_` delimiters), so the `*`, `~` and `$`
readers do not depend on it.
-/

namespace JuliaLean.Markdown

/-- Raw values of the code points in Unicode category Zs (space separators). -/
def zsChars : List Nat :=
  ([0x20, 0xA0, 0x1680, 0x202F, 0x205F, 0x3000] ++ (List.range 11).map (0x2000 + ·)).map Toml.rawOf

/-- `isspace(c::Char)`, `base/strings/unicode.jl`: `' '`, `'\t'`–`'\r'`, U+0085, or category Zs. -/
def isspace (c : Nat) : Bool :=
  c == C ' ' || (C '\t' ≤ c && c ≤ C '\r') || c == Toml.rawOf 0x85 || c ∈ zsChars

/-- `ismarkdownspace(c)`, `parse/util.jl:187-188`. -/
def ismarkdownspace (c : Nat) : Bool :=
  c == C '\t' || c == C '\n' || c == C '\x0c' || c == C '\r' || c ∈ zsChars

/-- The characters of a string together with the bytes each one spans. -/
def segments (s : Bytes) : List (Nat × Bytes) :=
  go 1 (s.length + 1)
where
  go (i : Int) : Nat → List (Nat × Bytes)
    | 0 => []
    | n + 1 => match Toml.iterate s i with
      | none => []
      | some (c, j) => (c, Toml.slice s i (j - 1)) :: go j n

/-- `strip(s)`: drop leading and trailing characters satisfying `isspace`. -/
def strip (s : Bytes) : Bytes :=
  (((segments s).dropWhile (isspace ·.1)).reverse.dropWhile (isspace ·.1)).reverse.flatMap (·.2)

/-- `replace(s, '\n' => ' ')`. -/
def replaceNewlines (s : Bytes) : Bytes := s.map fun b => if b == 10 then 32 else b

/-- `read(io, n)`: up to `n` bytes. -/
def readBytes (n : Nat) : M Bytes := do
  let s ← get
  let bs := (s.data.drop s.pos).take n
  set { s with pos := s.pos + bs.length }
  return bs

/-- The loop of `readuntil(stream, delimiter; newlines, match)`, `parse/util.jl:137-157`,
for a string delimiter given as its characters `delim` (bytes `delimB`). -/
def readuntilLoop (delim : List Nat) (delimB : Bytes) (newlines : Bool) (mtch : Option Nat) :
    Bytes → Nat → Nat → M (Option Bytes)
  | _, _, 0 => throw .outOfFuel
  | buf, count, fuel + 1 => do
    if ← eof then return none
    if ← startsWithStr delim then
      if count == 0 then return some buf
      else return ← readuntilLoop delim delimB newlines mtch (buf ++ delimB) (count - 1) fuel
    let char ← readChar
    let count := if some char == mtch then count + 1 else count
    if !newlines && char == C '\n' then return none
    readuntilLoop delim delimB newlines mtch (buf ++ charBytes char) count fuel

/-- `readuntil(stream, delimiter; newlines, match)`, `parse/util.jl:137-157`. Returns
`nothing` (and restores the position) when the delimiter is not found. -/
def readuntil (delim : List Nat) (newlines : Bool := false) (mtch : Option Nat := none) :
    M (Option Bytes) := withstreamOpt do
  let s ← get
  readuntilLoop delim (delim.flatMap charBytes) newlines mtch [] 0 (2 * (s.data.length - s.pos) + 2)

/-- Number of leading backtick bytes of a line. -/
def tickRun : Bytes → Nat
  | b :: bs => if b == 0x60 then tickRun bs + 1 else 0
  | [] => 0

/-- `read(stream, Char)` repeated `k` times (`matchstart` with `eat = true`). -/
def readChars : Nat → M Unit
  | 0 => return
  | k + 1 => do let _ ← readChar; readChars k

/-- `matchstart(stream, r"^(`+)")` returning the matched run length (the `::AbstractMatch`
assertion of `read_code_span` throws `TypeError` when there is none). -/
def matchTicks : M Nat := do
  let start ← position
  let line ← readline
  seek start
  let n := tickRun line
  if n == 0 then throw .typeError
  readChars n
  return n

/-- `read_code_span(stream)`, `Common/inline.jl:64-70`: the tick count and the text up to
the next run of the same ticks. -/
def readCodeSpan : M (Option (Nat × Bytes)) := withstreamOpt do
  let n ← matchTicks
  let result ← readuntil (List.replicate n (C '`')) (newlines := true)
  return result.map (n, ·)

/-- `inline_code(stream, md)`, `Common/inline.jl:73-94`. -/
def inlineCode : M (Option Inline) := withstreamOpt do
  match ← readCodeSpan with
  | none => return none
  | some (n, result) =>
    let result := replaceNewlines (strip result)
    return some (if n % 2 == 1 then .code [] result else .latex result)

/-- The backward scan of `peekprev`: step back over UTF-8 continuation bytes. -/
def peekprevBack (i : Nat) : Nat → M Nat
  | 0 => return i
  | k + 1 => do
    if i > 0 then
      seek i
      if (← peekByte) / 64 == 2 then return ← peekprevBack (i - 1) k
    return i

/-- `peekprev(stream)`, `parse/util.jl:168-182`. -/
def peekprev : M (Option Nat) := do
  let pos ← position
  if pos == 0 then return none
  let i ← peekprevBack (pos - 1) pos
  seek i
  let c ← readChar
  seek pos
  return some c

/-- `while startswith(stream, delimiter); n += 1; end` for a one-character delimiter. -/
def countRun (d : Nat) (n : Nat) : Nat → M Nat
  | 0 => throw .outOfFuel
  | k + 1 => do
    if ← startsWithStr [d] then countRun d (n + 1) k else return n

/-- The character loop of `parse_inline_wrapper` (`parse/util.jl:235-265`); `none` when the
stream ends without a closing run. -/
def wrapperLoop (isword : Nat → Bool) (d : Nat) (n : Nat) (intraword : Bool) :
    Bytes → Nat → M (Option Bytes)
  | _, 0 => throw .outOfFuel
  | buf, fuel + 1 => do
    if ← eof then return none
    let char ← readChar
    let escaped ← do
      if char == C '\\' then
        if ← eof then pure false
        else let c ← peekChar; pure (c == C '\\' || c == C '`')
      else pure false
    let buf ← do
      if escaped then
        let c2 ← readChar
        pure (buf ++ charBytes char ++ charBytes c2)
      else if char == C '`' then
        skip (-1)
        let start ← position
        if (← readCodeSpan).isNone then skip 1
        let stop ← position
        seek start
        let bs ← readBytes (stop - start)
        pure (buf ++ bs)
      else pure (buf ++ charBytes char)
    if !(ismarkdownspace char || char == d) then
      if ← startsWithStr (List.replicate n d) then
        let s ← get
        let trailing ← countRun d 0 (s.data.length - s.pos + 1)
        if trailing == 0 then
          if intraword then return some buf
          if ← eof then return some buf
          if !isword (← peekChar) then return some buf
          return ← wrapperLoop isword d n intraword (buf ++ (List.replicate n d).flatMap charBytes) fuel
        else
          return ← wrapperLoop isword d n intraword
            (buf ++ (List.replicate (n + trailing) d).flatMap charBytes) fuel
    wrapperLoop isword d n intraword buf fuel

/-- `parse_inline_wrapper(stream, delimiter; rep, intraword)`, `parse/util.jl:217-267`,
for `delimiter` = `nmin` copies of the character `d`. -/
def parseInlineWrapper (isword : Nat → Bool) (d : Nat) (nmin : Nat) (rep : Bool := false)
    (intraword : Bool := true) : M (Option Bytes) := withstreamOpt do
  let prev ← peekprev
  if let some p := prev then
    if p == d then return none
    if !intraword && isword p then return none
  if !(← startsWithStr (List.replicate nmin d)) then return none
  let s ← get
  let n ← countRun d nmin (s.data.length - s.pos + 1)
  if !rep && n > nmin then return none
  if !(← eof) then
    if ismarkdownspace (← peekChar) then return none
  let s ← get
  wrapperLoop isword d n intraword [] (s.data.length - s.pos + 1)

/-- `tex(stream, md)`, `IPython/IPython.jl:7-11`: the formula of a `$`-delimited `LaTeX`. -/
def tex (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '$') 1 (rep := true)

/-- The text that `asterisk_italic` (`Common/inline.jl:11-15`) wraps in `Italic`. -/
def asteriskItalic (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '*') 1

/-- The text that `asterisk_bold` (`Common/inline.jl:27-31`) wraps in `Bold`. -/
def asteriskBold (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '*') 2

end JuliaLean.Markdown
