import JuliaLean.Toml.Numbers

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
