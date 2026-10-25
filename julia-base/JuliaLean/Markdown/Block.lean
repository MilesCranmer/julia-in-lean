import JuliaLean.Markdown.Inline

/-!
# Markdown: block parsers

Models of the block parsers `hashheader`, `fencedcode`, `list`
(`stdlib/Markdown/src/Common/block.jl`), `github_paragraph` (`GitHub/GitHub.jl`)
and `blocktex` (`IPython/IPython.jl`) at master `bbfa0ce4150`.

A block parser returns `true` after `push!`ing an element, `false` otherwise
(and `withstream` restores the position). The models return `some x` for `true`,
where `x` is what was pushed, and `none` for `false`.

Calls into the rest of the parser are arguments: `inl b` is
`parseinline(IOBuffer(b), md)`, `doc b` is `parse(b).content`, and `brk` is
`_parse(stream, md, breaking = true)`. The properties quantify over them.
-/

namespace JuliaLean.Markdown

/-- Lift a pure Julia call into the stream monad. -/
def liftExcept {α} : Except Err α → M α
  | .ok a => pure a
  | .error e => throw e

/-- `while startswith(stream, '#') level += 1 end`. -/
def countHashes (level : Nat) : Nat → M Nat
  | 0 => throw .outOfFuel
  | k + 1 => do
    if ← startsWithChar (C '#') then countHashes (level + 1) k else return level

/-- Does `t` match ` +#+` in full? -/
def isClosingSeq (t : Bytes) : Bool :=
  match t with
  | 32 :: rest => let r := rest.dropWhile (· == 32); !r.isEmpty && r.all (· == 35)
  | _ => false

/-- `(match(r"(.*?)( +#+)?$", h)::AbstractMatch).captures[1]`: the shortest prefix whose
remainder is empty or a closing sequence ` +#+`. -/
def stripClosing (h : Bytes) : Bytes :=
  match (List.range (h.length + 1)).find? (fun k => (h.drop k).isEmpty || isClosingSeq (h.drop k)) with
  | some k => h.take k
  | none => h

/-- `hashheader(stream, md)`, `Common/block.jl:50-79`. Pushes `Header(text, level)`;
`text` is `""` (`none`) for an empty header. -/
def hashheader {α} (inl : Bytes → Except Err α) : M (Option (Nat × Option α)) := withstreamOpt do
  if !(← eatindent) then return none
  let s ← get
  let level ← countHashes 0 (s.data.length - s.pos + 1)
  if level < 1 || level > 6 then return none
  let mut c := C ' '
  if !(← eof) then
    c ← readChar
    if !(c == C ' ' || c == C '\t' || c == C '\n' || c == C '\r') then return none
  if c == C '\r' then
    if (← peekChar) == C '\n' then
      let _ ← readChar
    c := C '\n'
  if c != C '\n' then
    let h := stripClosing (strip (← readline))
    let x ← liftExcept (inl h)
    return some (level, some x)
  else
    return some (level, none)

/-- The character loop of `github_paragraph`, `GitHub/GitHub.jl:10-26`. -/
def githubParagraphLoop (brk : M Bool) : Bytes → Nat → M Bytes
  | _, 0 => throw .outOfFuel
  | buf, fuel + 1 => do
    if ← eof then return buf
    let mut char ← readChar
    if char == C '\r' then
      if (← peekChar) == C '\n' then
        let _ ← readChar
      char := C '\n'
    if char == C '\n' then
      if ← eof then return buf
      if ← blankline then return buf
      if ← brk then return buf
      githubParagraphLoop brk (buf ++ [10]) fuel
    else
      githubParagraphLoop brk (buf ++ charBytes char) fuel

/-- `github_paragraph(stream, md)`, `GitHub/GitHub.jl:5-28`: the paragraph content. -/
def githubParagraph {α} (brk : M Bool) (inl : Bytes → Except Err α) : M α := do
  skipwhitespace
  let s ← get
  let buf ← githubParagraphLoop brk [] (s.data.length - s.pos + 1)
  liftExcept (inl buf)

/-! ## Lists -/

/-- Code points matched by PCRE's `\d` under Julia's default `UCP` compile option (Unicode
category Nd), as inclusive ranges; obtained on master by testing `occursin(r"^\d$", string(c))`
for every valid character. -/
def ndRanges : List (Nat × Nat) :=
  [(0x30, 0x39), (0x660, 0x669), (0x6f0, 0x6f9), (0x7c0, 0x7c9), (0x966, 0x96f), (0x9e6, 0x9ef),
   (0xa66, 0xa6f), (0xae6, 0xaef), (0xb66, 0xb6f), (0xbe6, 0xbef), (0xc66, 0xc6f), (0xce6, 0xcef),
   (0xd66, 0xd6f), (0xde6, 0xdef), (0xe50, 0xe59), (0xed0, 0xed9), (0xf20, 0xf29), (0x1040, 0x1049),
   (0x1090, 0x1099), (0x17e0, 0x17e9), (0x1810, 0x1819), (0x1946, 0x194f), (0x19d0, 0x19d9),
   (0x1a80, 0x1a89), (0x1a90, 0x1a99), (0x1b50, 0x1b59), (0x1bb0, 0x1bb9), (0x1c40, 0x1c49),
   (0x1c50, 0x1c59), (0xa620, 0xa629), (0xa8d0, 0xa8d9), (0xa900, 0xa909), (0xa9d0, 0xa9d9),
   (0xa9f0, 0xa9f9), (0xaa50, 0xaa59), (0xabf0, 0xabf9), (0xff10, 0xff19), (0x104a0, 0x104a9),
   (0x10d30, 0x10d39), (0x10d40, 0x10d49), (0x11066, 0x1106f), (0x110f0, 0x110f9),
   (0x11136, 0x1113f), (0x111d0, 0x111d9), (0x112f0, 0x112f9), (0x11450, 0x11459),
   (0x114d0, 0x114d9), (0x11650, 0x11659), (0x116c0, 0x116c9), (0x116d0, 0x116e3),
   (0x11730, 0x11739), (0x118e0, 0x118e9), (0x11950, 0x11959), (0x11bf0, 0x11bf9),
   (0x11c50, 0x11c59), (0x11d50, 0x11d59), (0x11da0, 0x11da9), (0x11de0, 0x11de9),
   (0x11f50, 0x11f59), (0x16130, 0x16139), (0x16a60, 0x16a69), (0x16ac0, 0x16ac9),
   (0x16b50, 0x16b59), (0x16d70, 0x16d79), (0x1ccf0, 0x1ccf9), (0x1d7ce, 0x1d7ff),
   (0x1e140, 0x1e149), (0x1e2f0, 0x1e2f9), (0x1e4f0, 0x1e4f9), (0x1e5f1, 0x1e5fa),
   (0x1e950, 0x1e959), (0x1fbf0, 0x1fbf9)]

/-- PCRE `\d` on a raw character. Each range lies within one UTF-8 lead/continuation prefix,
so comparing raw values compares code points. -/
def isNd (c : Nat) : Bool := ndRanges.any fun (a, b) => Toml.rawOf a ≤ c && c ≤ Toml.rawOf b

/-- An ASCII digit `'0'`–`'9'` as a raw character. -/
def isAsciiDigit (c : Nat) : Bool := C '0' ≤ c && c ≤ C '9'

/-- `Base.parse(Int, s)` for `s` a run of `\d` characters (base/parse.jl:250-256,
`parseint_utf8`, `throw_parseint_error`): the first problem from the left is reported, an
`OverflowError` if the leading ASCII digits exceed `typemax(Int)`, else an `ArgumentError`
at the first non-ASCII digit. -/
def parseIntDigits (ds : List Nat) : Except Err Int :=
  let pre := ds.takeWhile isAsciiDigit
  let v : Nat := pre.foldl (fun acc c => acc * 10 + (c / 2 ^ 24 - 48)) 0
  if !pre.isEmpty && v > 2 ^ 63 - 1 then .error .overflowError
  else if pre.length == ds.length then .ok v
  else .error .argumentError

/-- A match of a list-marker regex: `length(m.match)` in characters, the bullet
character (`captures[1]` of an unordered marker), the digits (`captures[2]`) and the
delimiter `.`/`)` (`captures[3]`). -/
structure Marker where
  len : Nat
  bullet : Nat
  digits : List Nat
  delim : Option Nat
  deriving Repr, DecidableEq

/-- The `( |$)` tail of the marker regexes: the number of characters it consumes. -/
def markerTail : List Nat → Option Nat
  | [] => some 0
  | c :: _ => if c == C ' ' then some 1 else none

/-- `NUM_OR_BULLETS = r"^ {0,3}(\*|\+|-|(\d+)(\.|\)))( |$)"`, `Common/block.jl:316`, on the
characters of a line (`readline` strips the `'\n'`, so `$` is the end). -/
def matchNumOrBullets (line : List Nat) : Option Marker :=
  let sp := (line.takeWhile (· == C ' ')).length
  if sp > 3 then none else
  let rest := line.drop sp
  match rest with
  | [] => none
  | c :: cs =>
    if c == C '*' || c == C '+' || c == C '-' then
      (markerTail cs).map fun t => ⟨sp + 1 + t, c, [], none⟩
    else
      let ds := rest.takeWhile isNd
      match rest.drop ds.length with
      | d :: tl =>
        if !ds.isEmpty && (d == C '.' || d == C ')') then
          (markerTail tl).map fun t => ⟨sp + ds.length + 1 + t, 0, ds, some d⟩
        else none
      | [] => none

/-- The per-list item regex chosen at `Common/block.jl:325-344`. -/
inductive ItemRe where
  /-- `Regex("^ {0,3}(\\$(bullet))( |\$)")` -/
  | bullet (b : Nat)
  /-- `r"^ {0,3}(\d+)\.( |$)"` -/
  | dot
  /-- `r"^ {0,3}(\d+)\)( |$)"` -/
  | paren
  deriving Repr, DecidableEq

/-- Match an item regex on the characters of a line: `length(m.match)`. -/
def matchItem (re : ItemRe) (line : List Nat) : Option Nat :=
  let sp := (line.takeWhile (· == C ' ')).length
  if sp > 3 then none else
  let rest := line.drop sp
  match re with
  | .bullet b => match rest with
    | c :: cs => if c == b then (markerTail cs).map (sp + 1 + ·) else none
    | [] => none
  | .dot | .paren =>
    let d := if re == .dot then C '.' else C ')'
    let ds := rest.takeWhile isNd
    match rest.drop ds.length with
    | e :: tl => if !ds.isEmpty && e == d then (markerTail tl).map (sp + ds.length + 1 + ·) else none
    | [] => none

/-- `matchstart(stream, regex)` with `eat = true`, `parse/util.jl:90-103`. -/
def matchstartItem (re : ItemRe) : M Bool := do
  let start ← position
  let line ← readline
  seek start
  match matchItem re (decode line) with
  | some k => readChars k; return true
  | none => return false

/-- State of the `list` loop: buffer, `loose`, `count`, items so far. -/
structure ListSt (β : Type) where
  buf : Bytes
  loose : Bool
  count : Nat
  items : List β

/-- `pushitem!(list, buffer)`, `Common/block.jl:375`. -/
def pushitem {β} (doc : Bytes → Except Err β) (st : ListSt β) : M (ListSt β) := do
  let x ← liftExcept (doc st.buf)
  return { st with buf := [], items := st.items ++ [x] }

/-- The `while !eof(stream)` loop of `list`, `Common/block.jl:349-370`. -/
def listLoop {β} (doc : Bytes → Except Err β) (indent : Nat) (re : ItemRe) :
    ListSt β → Nat → M (ListSt β)
  | _, 0 => throw .outOfFuel
  | st, fuel + 1 => do
    if ← eof then return st
    if ← blankline then
      listLoop doc indent re { st with buf := st.buf ++ [10], loose := true } fuel
    else if ← startsWithStr (List.replicate indent (C ' ')) then
      let l ← readline (keep := true)
      listLoop doc indent re { st with buf := st.buf ++ l } fuel
    else
      if !(← matchstartItem re) then
        return ← pushitem doc st
      let st := { st with count := st.count + 1 }
      let st ← if st.count > 1 then pushitem doc st else pure st
      let l ← readline (keep := true)
      listLoop doc indent re { st with buf := st.buf ++ l } fuel

/-- `list(stream, block)`, `Common/block.jl:319-374`. Pushes `List(items, ordered, loose)`. -/
def listP {β} (doc : Bytes → Except Err β) : M (Option (List β × Int × Bool)) := withstreamOpt do
  let start ← position
  let line ← readline
  seek start
  match matchNumOrBullets (decode line) with
  | none => return none
  | some m =>
    let indent := m.len
    let (initial, re) ← match m.delim with
      | none => pure ((-1 : Int), ItemRe.bullet m.bullet)
      | some d =>
        if d == C '.' then do pure ((← liftExcept (parseIntDigits m.digits)), ItemRe.dot)
        else do pure ((← liftExcept (parseIntDigits m.digits)), ItemRe.paren)
    let s ← get
    let st ← listLoop doc indent re ⟨[], false, 0, []⟩ (s.data.length - s.pos + 1)
    let st ← if st.count == st.items.length then pure st else pushitem doc st
    return some (st.items, initial, st.loose)

/-! ## Fenced code and display math -/

/-- `lstrip(s, ch)` on characters. -/
def lstripChar (ch : Nat) (cs : List Nat) : List Nat := cs.dropWhile (· == ch)

/-- `chomp(s)`: drop one trailing `"\r\n"` or `"\n"`. -/
def chomp (s : Bytes) : Bytes :=
  if s.reverse.take 2 == [10, 13] then s.take (s.length - 2)
  else if s.reverse.take 1 == [10] then s.take (s.length - 1)
  else s

/-- The closing-fence loop of `fencedcode`, `Common/block.jl:154-171`; `none` = `return false`. -/
def fenceLoop (ch : Nat) (n : Nat) : Bytes → Nat → M (Option Bytes)
  | _, 0 => throw .outOfFuel
  | buf, fuel + 1 => do
    if ← eof then return none
    let lineStart ← position
    if ← startsWithStr (List.replicate n ch) then
      if !(← startsWithStr [ch]) then return some (chomp buf)
      else seek lineStart
    let l ← readline
    fenceLoop ch n (buf ++ l ++ [10]) fuel

/-- `fencedcode(stream, block)`, `Common/block.jl:131-174`. Pushes `LaTeX` for a `math`
fence and `Code(flavor, code)` otherwise. -/
def fencedcode : M (Option Block) := withstreamOpt do
  if !(← startsWithStr [C '~', C '~', C '~'] (padding := true)) then
    if !(← startsWithStr [C '`', C '`', C '`'] (padding := true)) then return none
  skip (-1)
  let ch ← readChar
  let trailing := decode (strip (← readline))
  let flavor := lstripChar ch trailing
  let n := 3 + trailing.length - flavor.length
  if flavor.contains ch then return none
  let flavorB := flavor.flatMap charBytes
  let s ← get
  match ← fenceLoop ch n [] (s.data.length - s.pos + 1) with
  | none => return none
  | some code => return some (if flavorB == bytes% "math" then .latex code else .code flavorB code)

/-- `blocktex(stream, md)`, `IPython/IPython.jl:13-23`. Pushes `LaTeX(formula)`. -/
def blocktex (isword : Nat → Bool) : M (Option Bytes) := withstreamOpt (tex isword)

end JuliaLean.Markdown
