import JuliaLean.ShellCmd.Basic

/-!
# `shell_parse(str, false)` and `shell_split`, `base/shell.jl:20-392`

Master `bbfa0ce4150`. With `interpolate = false` (the `shell_split` path) the
`$`, pipeline, redirection and tilde branches of the loop are never taken, so
they are not modelled. `last_arg` only feeds REPL completion and is not part
of the result, so it is omitted too.

The input is `str`; the parsed text is the SubString `s` of `str` left after
`lstrip` and `rstrip_shell`. `s` keeps its own one-based byte indices, which
is what `pairs(s)`, `s[i:j]` and `prevind(s, j)` use; the index arithmetic of
the loop is done on these indices exactly as in Julia, including the call
`nextind(str, i)` at `base/shell.jl:225`, which uses the indices of `str`.

`Iterators.Stateful(pairs(s))` is the list `st` of remaining (index, char)
pairs; `peek(st)` is its head and `popfirst!(st)` drops it. The `for` loop is
recursion on a bound on the number of remaining iterations: every iteration
pops at least one pair, so the bound `length(st) + 1` is never exhausted.
-/

namespace JuliaLean.ShellCmd

/-- `lstrip(s)` (`base/strings/util.jl:416-423`): the characters left after the
leading `isspace` ones, and the byte offset of the result in `s`. -/
def lstripOff (s : JS) : Nat × JS :=
  let pre := s.takeWhile isspace
  (ncu pre, s.drop pre.length)

/-- The loop of `rstrip_shell(s)`, `base/shell.jl:20-29`, over the characters of
`s` from the end (`r` is the reversed prefix still to scan, `cOld` the
previously scanned character). Returns the number of characters kept:
`SubString(s, 1, i+1)` keeps the backslash and the space after it;
`SubString(s, 1, i)` keeps everything up to the non-space character. -/
def rstripKeep : Option JC → List JC → Nat
  | _, [] => 0
  | cOld, c :: rest =>
    if c == A '\\' && cOld == some (A ' ') then rest.length + 2
    else if !isspace c then rest.length + 1
    else rstripKeep (some c) rest

/-- `rstrip_shell(s)`, `base/shell.jl:20-29`. -/
def rstripShell (s : JS) : JS := s.take (rstripKeep none s.reverse)

/-- `push_nonempty!(list, x)` for a string `x`, `base/shell.jl:63-68`. -/
def pushNonempty (l : List JS) (x : JS) : List JS := if x.isEmpty then l else l ++ [x]

/-- `something(peek(st), lastindex(s)+1 => '\0').first`. -/
def peekIdx (s : JS) : List (Nat × JC) → Int
  | (p, _) :: _ => p
  | [] => lastindex s + 1

/-- `consume_upto!(list, s, i, j)`, `base/shell.jl:69-72`: push `s[i:prevind(s, j)]`
if nonempty, return the index of the next pair (`st` is the iterator state at
the call). -/
def consumeUpto (s : JS) (st : List (Nat × JC)) (arg : List JS) (i j : Int) :
    SH (List JS × Int) := do
  let x ← slice s i (prevind s j)
  pure (pushNonempty arg x, peekIdx s st)

/-- `append_2to1!(list, innerlist)`, `base/shell.jl:73-77`: an empty word is `[""]`. -/
def append2to1 (args : List (List JS)) (arg : List JS) : List (List JS) :=
  args ++ [if arg.isEmpty then [[]] else arg]

/-- The whitespace-skipping loop of `base/shell.jl:134-140`: `i` becomes the
index of each peeked pair, and spaces are popped. -/
def skipSpaces (i : Int) : List (Nat × JC) → Int × List (Nat × JC)
  | [] => (i, [])
  | (p, c) :: rest => if isspace c then skipSpaces p rest else (p, (p, c) :: rest)

/-- The indentation-skipping loop after a line continuation,
`base/shell.jl:224-227`: `i = nextind(str, i)` for each popped space or tab. -/
def skipIndent (str : JS) (i : Int) : List (Nat × JC) → SH (Int × List (Nat × JC))
  | [] => .ok (i, [])
  | (p, c) :: rest =>
    if c == A ' ' || c == A '\t' then do
      let i' ← nextindStr str i
      skipIndent str i' rest
    else .ok (i, (p, c) :: rest)

/-- The parser state: `in_single_quotes`, `in_double_quotes`, `args`, `arg`,
`i`, `word_has_special`. -/
structure PState where
  inSQ : Bool
  inDQ : Bool
  args : List (List JS)
  arg : List JS
  i : Int
  whs : Bool
  deriving Repr, DecidableEq

/-- The main loop `for (j, c) in st`, `base/shell.jl:116-296`, with
`interpolate = false`. -/
def parseLoop (str s special : JS) : Nat → List (Nat × JC) → PState → SH PState
  | _, [], σ => .ok σ
  | 0, _ :: _, _ => .error .fuel
  | n + 1, (j, c) :: st, σ =>
    if !σ.inSQ && !σ.inDQ && isspace c then do
      -- `base/shell.jl:118-140`; `redirect_mode` is always `:none`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      let (args, arg) :=
        if !arg.isEmpty || σ.whs then (append2to1 σ.args arg, []) else (σ.args, arg)
      let (i, st) := skipSpaces i st
      parseLoop str s special n st { σ with args := args, arg := arg, i := i, whs := false }
    else if !σ.inDQ && c == A '\'' then do
      -- `base/shell.jl:208-211`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      parseLoop str s special n st { σ with inSQ := !σ.inSQ, whs := true, arg := arg, i := i }
    else if !σ.inSQ && c == A '"' then do
      -- `base/shell.jl:212-215`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      parseLoop str s special n st { σ with inDQ := !σ.inDQ, whs := true, arg := arg, i := i }
    else if !σ.inSQ && c == A '\\' then
      -- `base/shell.jl:216-239`
      match st with
      | (_, c') :: st' =>
        if c' == A '\n' || c' == A '\r' then do
          let (arg, i) ← consumeUpto s st σ.arg σ.i j
          let i := i + 1
          -- `if popfirst!(st)[2] == '\r' && (peek(st)::P)[2] == '\n'`
          let (i, st'') ←
            if c' == A '\r' then
              match st' with
              | (_, c'') :: st'' =>
                if c'' == A '\n' then (pure (i + 1, st'') : SH _) else pure (i, st')
              | [] => .error .typeError
            else pure (i, st')
          let (i, st''') ← skipIndent str i st''
          parseLoop str s special n st''' { σ with whs := true, arg := arg, i := i }
        else if σ.inDQ then
          if c' == A '"' || c' == A '$' || c' == A '\\' then do
            let (arg, i) ← consumeUpto s st σ.arg σ.i j
            parseLoop str s special n st' { σ with whs := true, arg := arg, i := i }
          else parseLoop str s special n st { σ with whs := true }
        else do
          let (arg, i) ← consumeUpto s st σ.arg σ.i j
          parseLoop str s special n st' { σ with whs := true, arg := arg, i := i }
      | [] =>
        if σ.inDQ then .error (.error "unterminated double quote")
        else .error (.error "dangling backslash")
    else if !σ.inSQ && !σ.inDQ && cin c special then
      -- `base/shell.jl:292-293`
      .error (.error "special characters must be quoted in commands")
    else parseLoop str s special n st σ

/-- `shell_parse(str, false; special)[1]`, `base/shell.jl:31-41,116-313`: the
words, each a list of string parts. -/
def shellParse (str special : JS) : SH (List (List JS)) :=
  let s := rstripShell (lstripOff str).2
  if s.isEmpty then .ok []
  else do
    let st := pairsFrom 1 s
    let σ ← parseLoop str s special (st.length + 1) st
      { inSQ := false, inDQ := false, args := [], arg := [], i := 1, whs := false }
    if σ.inSQ then .error (.error "unterminated single quote")
    else if σ.inDQ then .error (.error "unterminated double quote")
    else do
      let x ← slice s σ.i (lastindex s)
      let arg := pushNonempty σ.arg x
      pure (if !arg.isEmpty || σ.whs then append2to1 σ.args arg else σ.args)

/-- `shell_split(s)`, `base/shell.jl:385-392`: `string(arg...)` of each word. -/
def shellSplit (s : JS) : SH (List JS) := do
  let words ← shellParse s []
  pure (words.map List.flatten)

end JuliaLean.ShellCmd
