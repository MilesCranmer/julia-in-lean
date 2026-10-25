import JuliaLean.ShellCmd.Basic

/-!
# Reference parsers the escaping functions promise to invert

These are not Julia code; each models a documented external parsing rule.

* `posixWords`: POSIX.1-2024 (IEEE Std 1003.1-2024), Shell Command Language
  (XCU) 2.2 Quoting (2.2.1 Escape Character, 2.2.2 Single-Quotes,
  2.2.3 Double-Quotes), 2.3 Token Recognition and 2.6.7 Quote Removal, for
  text made of words, blanks (space and tab) and quoting. Any construct
  beyond these makes it return `none`: an unquoted operator character
  (`|&;<>()` or newline), a parameter expansion or command substitution
  (`$`, backquote, also inside double quotes), a pathname-expansion pattern
  character (`*?[`), a comment (`#` at the start of a word), a tilde prefix
  (`~` at the start of a word), an unquoted `=` in the first word (a possible
  assignment, XCU 2.9.1), a trailing backslash or an unterminated quote.
  Reserved words (XCU 2.4) are a grammar-level rule and are checked
  separately (`isReservedWord`).
* `msParse`: the Microsoft C runtime rules for the arguments after `argv[0]`,
  "Parsing C command-line arguments",
  https://learn.microsoft.com/en-us/cpp/c-language/parsing-c-command-line-arguments
  (2021-12-09). `argv[0]` follows different rules that the page lists first;
  `escape_microsoft_c_args` is used for the arguments.
* `cmdPhase2`: the caret and quote phase of `cmd.exe` as described in the
  source `shell_escape_wincmd` cites (https://stackoverflow.com/a/4095133):
  outside quotes `^` makes the next character literal and is removed, `"`
  toggles the quote state and is kept, and `()!<>&|` are operators; inside
  quotes every character is literal. It returns `none` when an operator
  character is unescaped outside quotes, a `^` ends the line, or the line
  starts with an unescaped `@`. Percent expansion happens before this phase
  and is excluded by the callers (`shell_escape_wincmd` documents that it does
  not handle `%`).
* `lexCmd`: the lexing of a command literal `` `...` `` by the Julia parser
  (`JuliaSyntax/src/julia/literal_parsing.jl:186-223`, `unescape_raw_string`
  with `is_cmd = true`): a run of `n` backslashes before a backtick stands for
  `n ÷ 2` backslashes, followed by a literal backtick if `n` is odd and by the
  end of the literal if `n` is even; other runs of backslashes are literal and
  the character after them is copied as is; elsewhere `\r\n` and `\r` become
  `\n`. Invalid UTF-8 is a parse error.
-/

namespace JuliaLean.ShellCmd

/-! ### POSIX sh -/

/-- The inside of a double-quoted string, after the opening `"` (XCU 2.2.3):
the characters after quote removal and the text after the closing `"`. -/
def dqScan : Nat → JS → Option (JS × JS)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: cs =>
    if c == A '"' then some ([], cs)
    else if c == A '\\' then
      match cs with
      | [] => none
      | d :: ds =>
        if d == A '$' || d == A '`' || d == A '"' || d == A '\\' then
          (dqScan n ds).map (fun r => (d :: r.1, r.2))
        else if d == A '\n' then dqScan n ds
        else (dqScan n ds).map (fun r => (c :: d :: r.1, r.2))
    else if c == A '$' || c == A '`' then none
    else (dqScan n cs).map (fun r => (c :: r.1, r.2))

/-- Word recognition and quote removal (XCU 2.2, 2.3, 2.6.7); `ws` are the
finished words, `cur` the word being built (`none` between words). -/
def posixWords : Nat → JS → List JS → Option JS → Option (List JS)
  | 0, _, _, _ => none
  | _ + 1, [], ws, cur => some (ws ++ cur.toList)
  | n + 1, c :: cs, ws, cur =>
    if c == A ' ' || c == A '\t' then posixWords n cs (ws ++ cur.toList) none
    else if c == A '\\' then
      match cs with
      | [] => none
      | d :: ds =>
        if d == A '\n' then posixWords n ds ws cur
        else posixWords n ds ws (some (cur.getD [] ++ [d]))
    else if c == A '\'' then
      if cs.contains (A '\'') then
        let q := cs.takeWhile (· != A '\'')
        posixWords n (cs.drop (q.length + 1)) ws (some (cur.getD [] ++ q))
      else none
    else if c == A '"' then
      match dqScan (cs.length + 1) cs with
      | some (q, rest) => posixWords n rest ws (some (cur.getD [] ++ q))
      | none => none
    else if cin c (S "|&;<>()$`*?[") || c == A '\n' then none
    else if cur.isNone && (c == A '#' || c == A '~') then none
    else if ws.isEmpty && c == A '=' then none
    else posixWords n cs ws (some (cur.getD [] ++ [c]))

/-- The words POSIX sh recognizes in `text`. -/
def posixSplit (text : JS) : Option (List JS) := posixWords (text.length + 1) text [] none

/-- The reserved words of XCU 2.4. -/
def reservedWords : List JS :=
  ["!", "{", "}", "case", "do", "done", "elif", "else", "esac", "fi", "for", "if", "in",
    "then", "until", "while"].map S

/-- The first word of `text` as written (up to the first blank) is a reserved
word, so it is recognized as one in command-name position (XCU 2.4: only
unquoted words are reserved words, and a reserved word is spelled without quotes). -/
def firstWordReserved (text : JS) : Bool :=
  reservedWords.contains (text.takeWhile (fun c => c != A ' ' && c != A '\t'))

/-! ### Microsoft C runtime -/

/-- The quote rule at a `"` that is a delimiter: inside quotes, `""` is a literal
`"` (and the quoted string continues); otherwise the quote state toggles. -/
def msQuote (ds : JS) (cur : JS) (inq : Bool) : JS × JS × Bool :=
  match ds with
  | d :: ds' => if inq && d == A '"' then (ds', cur ++ [A '"'], true) else (ds, cur, !inq)
  | [] => (ds, cur, !inq)

/-- The argument parser for the arguments after `argv[0]`; `cur` is the
argument being built (`none` between arguments), `inq` the quote state. An
unterminated quoted string ends the last argument. -/
def msWords : Nat → JS → List JS → Option JS → Bool → List JS
  | 0, _, ws, cur, _ => ws ++ cur.toList
  | _ + 1, [], ws, cur, _ => ws ++ cur.toList
  | n + 1, c :: cs, ws, cur, inq =>
    if !inq && (c == A ' ' || c == A '\t') then msWords n cs (ws ++ cur.toList) none false
    else if c == A '\\' then
      let k := ((c :: cs).takeWhile (· == A '\\')).length
      let rest := (c :: cs).drop k
      match rest with
      | d :: ds =>
        if d == A '"' then
          let cur' := cur.getD [] ++ List.replicate (k / 2) (A '\\')
          if k % 2 == 1 then msWords n ds ws (some (cur' ++ [A '"'])) inq
          else
            let (ds', cur'', inq') := msQuote ds cur' inq
            msWords n ds' ws (some cur'') inq'
        else msWords n rest ws (some (cur.getD [] ++ List.replicate k (A '\\'))) inq
      | [] => msWords n [] ws (some (cur.getD [] ++ List.replicate k (A '\\'))) inq
    else if c == A '"' then
      let (ds', cur', inq') := msQuote cs (cur.getD []) inq
      msWords n ds' ws (some cur') inq'
    else msWords n cs ws (some (cur.getD [] ++ [c])) inq

/-- The arguments the Microsoft C runtime parses from a command line (after `argv[0]`). -/
def msParse (text : JS) : List JS := msWords (text.length + 1) text [] none false

/-! ### `cmd.exe` -/

/-- The caret/quote phase of `cmd.exe`; `inq` is the quote state. -/
def cmdPhase2 : JS → Bool → Option JS
  | [], _ => some []
  | c :: cs, true => (cmdPhase2 cs (c != A '"')).map (c :: ·)
  | c :: cs, false =>
    if c == A '^' then
      match cs with
      | [] => none
      | d :: ds => (cmdPhase2 ds false).map (d :: ·)
    else if c == A '"' then (cmdPhase2 cs true).map (c :: ·)
    else if cin c (S "()!<>&|") then none
    else (cmdPhase2 cs false).map (c :: ·)

/-- The text a program receives from the `cmd.exe` line `line`. -/
def cmdLine (line : JS) : Option JS :=
  if line.head? == some (A '@') then none else cmdPhase2 line false

/-! ### Julia command literals -/

/-- The content of a command literal, given the text after its opening
backtick: the unescaped content and the text after the closing backtick. -/
def lexCmd : Nat → JS → JS → Option (JS × JS)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | n + 1, c :: cs, acc =>
    if c == A '\\' then
      let k := ((c :: cs).takeWhile (· == A '\\')).length
      let rest := (c :: cs).drop k
      match rest with
      | d :: ds =>
        if d == A '`' then
          if k % 2 == 0 then some (acc ++ List.replicate (k / 2) (A '\\'), ds)
          else lexCmd n ds (acc ++ List.replicate (k / 2) (A '\\') ++ [A '`'])
        else if !Strings.isvalidChar d then none
        else lexCmd n ds (acc ++ List.replicate k (A '\\') ++ [d])
      | [] => none
    else if c == A '`' then some (acc, cs)
    else if c == A '\r' then
      match cs with
      | d :: ds => if d == A '\n' then lexCmd n ds (acc ++ [A '\n']) else lexCmd n cs (acc ++ [A '\n'])
      | [] => lexCmd n [] (acc ++ [A '\n'])
    else if !Strings.isvalidChar c then none
    else lexCmd n cs (acc ++ [c])

/-- Lex the command literal at the start of `text` (which must begin with a backtick). -/
def lexCmdLiteral (text : JS) : Option (JS × JS) :=
  match text with
  | c :: cs => if c == A '`' then lexCmd (cs.length + 1) cs [] else none
  | [] => none

end JuliaLean.ShellCmd
