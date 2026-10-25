import JuliaLean.ShellCmd.Basic

/-!
# The shell escaping functions of `base/shell.jl`

Master `bbfa0ce4150`: `print_shell_word`, `shell_escape`,
`shell_escape_posixly`, `shell_escape_csh`, `shell_escape_wincmd`,
`escape_microsoft_c_args`, and `escape_raw_string` from `base/strings/io.jl`.

`Char` comparisons such as `'0' <= c <= '9'` compare raw bits, as in Julia.
The regular expressions of `shell_escape_csh` and `shell_escape_wincmd` use the
`a` flag, so they match bytes; their character classes contain only ASCII
bytes, so on the characters of a string they select the same characters as the
character-level tests used here (a non-ASCII character consists of bytes
`≥ 0x80`, none of which is in or equal to an ASCII class member).
-/

namespace JuliaLean.ShellCmd

/-- `replace(s, c => r)` for a character `c`. -/
def replaceC (s : JS) (c : JC) (r : JS) : JS := s.flatMap (fun x => if x == c then r else [x])

/-- `join(words, ' ')`. -/
def joinSp : List JS → JS
  | [] => []
  | w :: ws => w ++ ws.flatMap (fun a => A ' ' :: a)

/-- The special-character test of `print_shell_word`, `base/shell.jl:398`. -/
def wordSpecial (special : JS) (c : JC) : Bool :=
  isspace c || c == A '\\' || c == A '\'' || c == A '"' || c == A '$' || cin c special

/-- `print_shell_word(io, word, special)`, `base/shell.jl:394-422`. -/
def printShellWord (word special : JS) : JS :=
  let hasSingle := word.any (fun c => wordSpecial special c && c == A '\'')
  let hasSpecial := word.any (wordSpecial special)
  if word.isEmpty then S "''"
  else if !hasSpecial then word
  else if !hasSingle then A '\'' :: word ++ [A '\'']
  else
    A '"' :: word.flatMap (fun c =>
      if c == A '"' || c == A '$' || c == A '\\' then [A '\\', c] else [c]) ++ [A '"']

/-- `shell_escape(args...; special)`, `base/shell.jl:424-453`: the words printed
by `print_shell_word`, separated by spaces (`""` for no arguments). -/
def shellEscape (xs : List JS) (special : JS) : JS := joinSp (xs.map (printShellWord · special))

/-! ### `shell_escape_posixly`, `base/shell.jl:456-520` -/

/-- `'0' <= c <= '9' || 'a' <= c <= 'z' || 'A' <= c <= 'Z'`. -/
def isAlnum (c : JC) : Bool :=
  (A '0' ≤ c && c ≤ A '9') || (A 'a' ≤ c && c ≤ A 'z') || (A 'A' ≤ c && c ≤ A 'Z')

/-- `c == '_' || c == '/' || c == '+' || c == '-' || c == '.'`. -/
def isCommon (c : JC) : Bool :=
  c == A '_' || c == A '/' || c == A '+' || c == A '-' || c == A '.'

/-- The scan `for c in arg`, `base/shell.jl:468-488`: returns
`(have_single, have_double, isword)`. -/
def posixScan (first : Bool) : JS → Bool → Bool → Bool × Bool × Bool
  | [], hs, hd => (hs, hd, true)
  | c :: cs, hs, hd =>
    if isAlnum c then posixScan first cs hs hd
    else if isCommon c then posixScan first cs hs hd
    else if c == A '\'' then posixScan first cs true hd
    else if c == A '"' then
      if hd then (hs, hd, false) else posixScan first cs hs true
    else if !first && c == A '=' then posixScan first cs hs hd
    else (hs, hd, false)

/-- One argument of `print_shell_escaped_posixly`, `base/shell.jl:462-496`. -/
def posixWord (first : Bool) (arg : JS) : JS :=
  if arg.isEmpty then S "''"
  else
    let (hs, hd, isword) := posixScan first arg false false
    if isword then
      let a := if hs then replaceC arg (A '\'') (S "\\'") else arg
      if hd then replaceC a (A '"') (S "\\\"") else a
    else A '\'' :: replaceC arg (A '\'') (S "'\\''") ++ [A '\'']

/-- `shell_escape_posixly(args...)`, `base/shell.jl:456-520`. -/
def shellEscapePosixly : List JS → JS
  | [] => []
  | x :: xs => posixWord true x ++ xs.flatMap (fun a => A ' ' :: posixWord false a)

/-! ### `shell_escape_csh`, `base/shell.jl:544-568` -/

/-- `[A-Za-z0-9/\._-]`. -/
def cshPlain (c : JC) : Bool :=
  isAlnum c || c == A '/' || c == A '.' || c == A '_' || c == A '-'

/-- `[^\$\`\"]`. -/
def notDqSpecial (c : JC) : Bool := c != A '$' && c != A '`' && c != A '"'

/-- The `while true` loop for one argument, `base/shell.jl:549-563`, on the
remaining text `SubString(arg, i)`. The five patterns are tried in order; for a
nonempty remainder one of the last two always matches, and every match of a
non-final pattern is nonempty, so the bound `length(arg) + 1` is never
exhausted. -/
def cshLoop : Nat → JS → JS
  | 0, _ => []
  | n + 1, rest =>
    let (seg, e, rest') :=
      if !rest.isEmpty && rest.all cshPlain then (rest, ([] : JS), ([] : JS))
      else if !rest.contains (A '\'') then (rest, [A '\''], [])
      else if rest.all notDqSpecial then (rest, [A '"'], [])
      else
        let p := rest.takeWhile (· != A '\'')
        if !p.isEmpty then (p, [A '\''], rest.drop p.length)
        else
          let q := rest.takeWhile notDqSpecial
          (q, [A '"'], rest.drop q.length)
    e ++ replaceC seg (A '\n') [A '\\', A '\n'] ++ e ++
      (if rest'.isEmpty then [] else cshLoop n rest')

/-- `shell_escape_csh(io, args...)`, `base/shell.jl:544-565`. -/
def cshIO (xs : List JS) : JS := joinSp (xs.map (fun a => cshLoop (a.length + 1) a))

/-- The `ArgumentError` of `sum(sizeof, ())`: `mapreduce` over an empty tuple
without `init` (`base/reduce.jl`). -/
def emptyReduceErr : ShErr :=
  .jl (.argumentError "reducing over an empty collection is not allowed; consider supplying `init` to the reducer")

/-- `shell_escape_csh(args...)`, `base/shell.jl:566-568`: the `sizehint` computes
`sum(sizeof, args)` before anything is printed. -/
def shellEscapeCsh (xs : List JS) : SH JS :=
  if xs.isEmpty then .error emptyReduceErr else .ok (cshIO xs)

/-! ### `shell_escape_wincmd`, `base/shell.jl:648-673` -/

/-- `c in ('"', '(', ')', '!', '^', '<', '>', '&', '|')`. -/
def wincmdSpecial (c : JC) : Bool := cin c (S "\"()!^<>&|")

/-- The `while i <= len` loop, `base/shell.jl:657-670`, on the remaining characters:
a `"` with a later `"` is copied with everything up to that `"`. -/
def wincmdLoop : Nat → JS → JS
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: cs =>
    if c == A '"' && cs.contains (A '"') then
      let inner := cs.takeWhile (· != A '"')
      (c :: inner ++ [A '"']) ++ wincmdLoop n (cs.drop (inner.length + 1))
    else (if wincmdSpecial c then [A '^', c] else [c]) ++ wincmdLoop n cs

/-- `shell_escape_wincmd(s)`, `base/shell.jl:648-673`. -/
def shellEscapeWincmd (s : JS) : SH JS :=
  if s.any (fun c => c == A '\r' || c == A '\n' || c == A '\x00') then
    .error (.jl (.argumentError "control character unsupported by CMD.EXE"))
  else .ok ((if s.head? == some (A '@') then [A '^'] else []) ++ wincmdLoop (s.length + 1) s)

/-! ### `escape_microsoft_c_args`, `base/shell.jl:696-718` -/

/-- `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-693`; `esc` is
the number of backslashes since the last other character. -/
def escapeRawString (delim : JC) : JS → Nat → JS
  | [], esc => List.replicate esc (A '\\')
  | c :: cs, esc =>
    if c == A '\\' then c :: escapeRawString delim cs (esc + 1)
    else if c == delim then List.replicate (esc + 1) (A '\\') ++ c :: escapeRawString delim cs 0
    else c :: escapeRawString delim cs 0

/-- One argument of `escape_microsoft_c_args(io, args...)`, `base/shell.jl:705-713`. -/
def msArg (arg : JS) : JS :=
  if arg.isEmpty || arg.any (fun c => c == A ' ' || c == A '\t' || c == A '"') then
    A '"' :: escapeRawString (A '"') arg 0 ++ [A '"']
  else arg

/-- `escape_microsoft_c_args(io, args...)`, `base/shell.jl:696-715`. -/
def msIO (xs : List JS) : JS := joinSp (xs.map msArg)

/-- `escape_microsoft_c_args(args...)`, `base/shell.jl:716-718` (with `sizehint`). -/
def escapeMicrosoftCArgs (xs : List JS) : SH JS :=
  if xs.isEmpty then .error emptyReduceErr else .ok (msIO xs)

end JuliaLean.ShellCmd
