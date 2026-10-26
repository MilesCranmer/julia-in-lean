import JuliaLean.ShellCmd.Parse

/-!
# `__repl_entry_shell_parse(str, interpolate, special, filename)`, `base/shell.jl:36-368`

Master `bbfa0ce4150`, including the `interpolate = true` branches (`$`, `|`, `<`, `>`
and `~`) that `JuliaLean.ShellCmd.Parse` leaves out. Strings, characters, byte
indices, `pairs(s)`, `s[i:j]`, `prevind` and `nextind` are those of
`JuliaLean.ShellCmd.Basic`: a string is the list of characters iteration yields,
and indices are Julia's byte indices.

`s` is a `SubString` of `str`; the model keeps its characters and its byte offset
`s.offset` in `str` (used only for `last_arg`). `Meta.parseatom(s, i; filename)` is
an input `pa` of the model: it returns the parsed atom and the index after it, or
throws. Expressions built by the parser are `SEx` values.
-/

namespace JuliaLean.MiscCov.Shell

open JuliaLean JuliaLean.ShellCmd

/-- The values `shell_parse` puts into its result: `String`s, atoms returned by
`Meta.parseatom`, the symbol `:var`, and `Expr`s. `call f args` is
`Expr(:call, f, args...)` with `f` a `GlobalRef` or function name; `tildeLet parts`
is the `let _u = string(parts...); isempty(_u) ? "~" : expanduser(string('~', _u)) end`
expression of `base/shell.jl:282`. -/
inductive SEx where
  | lit (s : JS)
  | atom (a : Nat)
  | varSym
  | call (f : String) (args : List SEx)
  | tuple (args : List SEx)
  | params (args : List SEx)
  | kw (k : String) (v : SEx)
  | btrue
  | tildeLet (parts : List SEx)
  deriving Repr, Inhabited, BEq

/-- `Meta.parseatom(s, i; filename)`: the atom and the index after it. -/
abbrev ParseAtom := JS → Int → SH (SEx × Int)

/-- `push_nonempty!(list, x)`, `base/shell.jl:63-68`: push unless `x` is an empty string. -/
def pushNonempty (l : List SEx) (x : SEx) : List SEx :=
  match x with
  | .lit v => if v.isEmpty then l else l ++ [x]
  | _ => l ++ [x]

/-- `consume_upto!(list, s, i, j)`, `base/shell.jl:69-72`: push `s[i:prevind(s, j)]`,
return the index of the next pair of the iterator `st` (or `lastindex(s) + 1`). -/
def consumeUpto (s : JS) (st : List (Nat × JC)) (arg : List SEx) (i j : Int) : SH (List SEx × Int) := do
  let x ← slice s i (prevind s j)
  pure (pushNonempty arg (.lit x), peekIdx s st)

/-- `append_2to1!(list, innerlist)`, `base/shell.jl:73-77`: an empty word becomes `[""]`. -/
def append2to1 (args : List (List SEx)) (arg : List SEx) : List (List SEx) :=
  args ++ [if arg.isEmpty then [.lit []] else arg]

/-- `startswith(SubString(s, p), "var\"")` for a character index `p`. -/
def startsWithVar (s : JS) (p : Nat) : Bool :=
  (((pairsFrom 1 s).filter (fun q => p ≤ q.1)).map (·.2)).take 4 == S "var\""

/-- `SubString(s, j)` of a `SubString` `s` with offset `off`: its characters and
offset (`base/strings/substring.jl:37-49`; an empty result has offset 0). -/
def subFrom (s : JS) (off : Nat) (j : Int) : SH (JS × Nat) := do
  let t ← slice s j (lastindex s)
  pure (t, if t.isEmpty then 0 else off + (j - 1).toNat)

/-- `parse_dollar_interp(st, s)`, `base/shell.jl:86-103`: the atom, the new `s` (with its
offset), `interp_pos`, and the reset iterator `pairs(s)`. -/
def parseDollar (pa : ParseAtom) (st : List (Nat × JC)) (s : JS) (off : Nat) :
    SH (SEx × (JS × Nat) × Int × List (Nat × JC)) :=
  match st with
  | [] => .error (.error "$ right before end of command")
  | (stpos, c) :: _ =>
    if isspace c then .error (.error "space not allowed right after $")
    else do
      let (atom, j) ← if startsWithVar s stpos then pure (SEx.varSym, (stpos : Int) + 3) else pa s stpos
      let interpPos : Int := stpos + off
      let (s', off') ← subFrom s off j
      pure (atom, (s', off'), interpPos, pairsFrom 1 s')

/-- `redirect_word_expr(word)`, `base/shell.jl:106-114`. -/
def redirectWordExpr (word : List SEx) : SEx :=
  match word with
  | [.lit w] => .lit w
  | [w] => .call "Base.cmd_redirect_target" [w]
  | ws => .call "Base.cmd_interpolate" ws

/-- `redirect_mode`. -/
inductive RMode where
  | none | stdin | stdout | stderr
  deriving DecidableEq, Repr

/-- A finished pipeline segment: `(seg_tuple, stdin, stdout, stdout_append, stderr,
stderr_append)`. -/
abbrev Seg := SEx × Option SEx × Option SEx × Bool × Option SEx × Bool

/-- The local variables of the parser. -/
structure PS where
  inSQ : Bool
  inDQ : Bool
  args : List (List SEx)
  arg : List SEx
  i : Int
  s : JS
  off : Nat
  lastArg : Int
  upd : Bool
  whs : Bool
  parts : List Seg
  sin : Option SEx
  sout : Option SEx
  soutApp : Bool
  serr : Option SEx
  serrApp : Bool
  mode : RMode

/-- `if redirect_mode === :stdin; seg_stdin = re elseif ... :stdout ... else seg_stderr = re`. -/
def setRedirect (σ : PS) (re : SEx) : PS :=
  if σ.mode = .stdin then { σ with sin := some re }
  else if σ.mode = .stdout then { σ with sout := some re }
  else { σ with serr := some re }

/-- `isdigit(c)`: `'0' <= c <= '9'` on the raw bits. -/
def isdigitC (c : JC) : Bool := A '0' ≤ c && c ≤ A '9'

/-- `parse(Int, w)` for a nonempty word of ASCII digits: `OverflowError` above `typemax(Int)`. -/
def parseFd (w : JS) : SH Int :=
  let v : Nat := w.foldl (fun a c => a * 10 + (c.toNat / 2 ^ 24 - 48)) 0
  if v > 2 ^ 63 - 1 then .error (.jl (.overflowError "")) else .ok v

/-- `Expr(:tuple, (Expr(:tuple, a...) for a in args)...)`. -/
def tupleOf (args : List (List SEx)) : SEx := .tuple (args.map .tuple)

/-- The redirect-or-word step shared by whitespace and `|` (`base/shell.jl:121-129,
152-159`): the pending word becomes the redirect target (and, after whitespace,
`redirect_mode = :none`), or a new argument. -/
def finishWord (resetMode : Bool) (σ : PS) : PS :=
  if σ.mode ≠ .none && (!σ.arg.isEmpty || σ.whs) then
    { setRedirect σ (redirectWordExpr σ.arg) with arg := [], mode := if resetMode then .none else σ.mode }
  else if σ.mode = .none && (!σ.arg.isEmpty || σ.whs) then { σ with args := append2to1 σ.args σ.arg, arg := [] }
  else σ

/-- The `while !isempty(st)` loop of the tilde branch, `base/shell.jl:247-276`: returns
the user-name parts, `s` with its offset, `i`, `user_lit_start` and the iterator. -/
def tildeLoop (pa : ParseAtom) : Nat → List SEx → JS → Nat → Int → Int → List (Nat × JC) →
    SH (List SEx × (JS × Nat) × Int × Int × List (Nat × JC))
  | _, parts, s, off, i, uls, [] => .ok (parts, (s, off), i, uls, [])
  | 0, _, _, _, _, _, _ :: _ => .error .fuel
  | n + 1, parts, s, off, i, uls, (p, nc) :: st =>
    let nextIsNl : Bool := match st with
      | (_, c2) :: _ => c2 == A '\n' || c2 == A '\r'
      | [] => false
    if nc == A '\\' && nextIsNl then do
      -- `nextind(s, nxt[1]) <= lastindex(s) && s[nextind(s, nxt[1])] in ('\n', '\r')`
      let lit ← slice s uls (prevind s p)
      let parts := pushNonempty parts (.lit lit)
      match st with
      | (_, c2) :: st2 =>
        let st3 := if c2 == A '\r' then
            (match st2 with
             | (_, c3) :: st4 => if c3 == A '\n' then st4 else st2
             | [] => st2)
          else st2
        let st5 := st3.dropWhile (fun q => q.2 == A ' ' || q.2 == A '\t')
        tildeLoop pa n parts s off i (peekIdx s st5) st5
      | [] => .error .fuel
    else if nc == A '/' || isspace nc || nc == A '\'' || nc == A '"' || nc == A '\\' ||
        nc == A '|' || nc == A '<' || nc == A '>' then
      .ok (parts, (s, off), i, uls, (p, nc) :: st)
    else if nc == A '$' then do
      let lit ← slice s uls (prevind s p)
      let parts := pushNonempty parts (.lit lit)
      let (atom, (s', off'), _, st') ← parseDollar pa st s off
      tildeLoop pa n (parts ++ [atom]) s' off' 1 1 st'
    else tildeLoop pa n parts s off i uls st

/-- The loop `for (j, c) in st`, `base/shell.jl:116-296`. -/
def parseLoop (pa : ParseAtom) (interp : Bool) (str special : JS) : Nat → List (Nat × JC) → PS → SH PS
  | _, [], σ => .ok σ
  | 0, _ :: _, _ => .error .fuel
  | n + 1, (j, c) :: st, σ =>
    if !σ.inSQ && !σ.inDQ && isspace c then do
      -- `base/shell.jl:118-140`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let σ := finishWord true { σ with upd := true, arg := arg, i := i }
      let σ := { σ with whs := false }
      let (i, st) := skipSpaces σ.i st
      parseLoop pa interp str special n st { σ with i := i }
    else if interp && !σ.inSQ && c == A '$' then do
      -- `base/shell.jl:141-148`
      let (arg, _) ← consumeUpto σ.s st σ.arg σ.i j
      let (atom, (s, off), pos, st) ← parseDollar pa st σ.s σ.off
      parseLoop pa interp str special n st
        { σ with arg := arg ++ [atom], s := s, off := off, lastArg := pos, upd := true, i := 1 }
    else if interp && !σ.inSQ && !σ.inDQ && c == A '|' then do
      -- `base/shell.jl:149-169`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let σ := finishWord false { σ with arg := arg, i := i }
      let seg : Seg := (tupleOf σ.args, σ.sin, σ.sout, σ.soutApp, σ.serr, σ.serrApp)
      parseLoop pa interp str special n st
        { σ with parts := σ.parts ++ [seg], args := [], sin := none, sout := none, soutApp := false,
                 serr := none, serrApp := false, mode := .none, whs := false, upd := true }
    else if interp && !σ.inSQ && !σ.inDQ && (c == A '<' || c == A '>') then do
      -- `base/shell.jl:170-201`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let (fd, σ) ← (match arg with
        | [.lit w] =>
          if !σ.whs && !w.isEmpty && w.all isdigitC then do
            let v ← parseFd w
            pure (some v, { σ with arg := [], i := i, whs := false })
          else pure (none, { σ with args := append2to1 σ.args arg, arg := [], i := i })
        | [] => pure (none, { σ with arg := [], i := i })
        | _ => pure (none, { σ with args := append2to1 σ.args arg, arg := [], i := i }) : SH (Option Int × PS))
      if c == A '>' then do
        let (append, i, st) := match st with
          | (_, c2) :: st2 => if c2 == A '>' then (true, peekIdx σ.s st2, st2) else (false, σ.i, st)
          | [] => (false, σ.i, st)
        let σ := { σ with i := i }
        let σ ← (if fd = none || fd = some 1 then pure { σ with mode := .stdout, soutApp := append }
          else if fd = some 2 then pure { σ with mode := .stderr, serrApp := append }
          else .error (.error "unsupported fd in redirection") : SH PS)
        parseLoop pa interp str special n st { σ with upd := true }
      else do
        if fd = none || fd = some 0 then
          parseLoop pa interp str special n st { σ with mode := .stdin, upd := true }
        else .error (.error "unsupported fd in redirection")
    else do
      -- `base/shell.jl:202-294`
      let σ := if σ.upd then { σ with lastArg := σ.i + σ.off, upd := false } else σ
      if !σ.inDQ && c == A '\'' then do
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        parseLoop pa interp str special n st { σ with inSQ := !σ.inSQ, whs := true, arg := arg, i := i }
      else if !σ.inSQ && c == A '"' then do
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        parseLoop pa interp str special n st { σ with inDQ := !σ.inDQ, whs := true, arg := arg, i := i }
      else if !σ.inSQ && c == A '\\' then
        let σ := { σ with whs := true }
        match st with
        | (_, c') :: st' =>
          if c' == A '\n' || c' == A '\r' then do
            let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
            let i := i + 1
            let (i, st'') ←
              if c' == A '\r' then
                match st' with
                | (_, c'') :: st'' => if c'' == A '\n' then (pure (i + 1, st'') : SH _) else pure (i, st')
                | [] => .error .typeError
              else pure (i, st')
            let (i, st''') ← skipIndent str i st''
            parseLoop pa interp str special n st''' { σ with arg := arg, i := i }
          else if σ.inDQ then
            if c' == A '"' || c' == A '$' || c' == A '\\' then do
              let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
              parseLoop pa interp str special n st' { σ with arg := arg, i := i }
            else parseLoop pa interp str special n st σ
          else do
            let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
            parseLoop pa interp str special n st' { σ with arg := arg, i := i }
        | [] =>
          if σ.inDQ then .error (.error "unterminated double quote")
          else .error (.error "dangling backslash")
      else if interp && !σ.inSQ && !σ.inDQ && c == A '~' && σ.i == j && σ.arg.isEmpty then do
        -- `base/shell.jl:240-290`
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        let (parts, (s, off), i, uls, st) ← tildeLoop pa (st.length + 1) [] σ.s σ.off i i st
        let userEnd := peekIdx s st
        let lit ← slice s uls (prevind s userEnd)
        let parts := pushNonempty parts (.lit lit)
        let quoted : Bool := match st with
          | (_, c2) :: _ => c2 == A '\'' || c2 == A '"' || c2 == A '\\'
          | [] => false
        let arg :=
          if quoted then arg ++ [.lit (S "~")] ++ parts
          else match parts with
            | [] => arg ++ [.call "expanduser" [.lit (S "~")]]
            | [.lit u] => arg ++ [.call "expanduser" [.lit (S "~" ++ u)]]
            | ps => arg ++ [.tildeLet ps]
        let _ := i
        parseLoop pa interp str special n st { σ with arg := arg, s := s, off := off, i := userEnd }
      else if !σ.inSQ && !σ.inDQ && cin c special then
        .error (.error "special characters must be quoted in commands")
      else parseLoop pa interp str special n st σ

/-- `build_seg_expr(seg_tuple, s_in, s_out, s_out_app, s_err, s_err_app)`,
`base/shell.jl:328-343`. -/
def buildSeg (seg : SEx) (sIn sOut : Option SEx) (sOutApp : Bool) (sErr : Option SEx) (sErrApp : Bool) : SEx :=
  let cmd := SEx.call "Base.cmd_gen" [seg]
  let cmd :=
    if sIn.isSome || sOut.isSome then
      let kwargs := (match sIn with | some x => [SEx.kw "stdin" x] | none => []) ++
        (match sOut with | some x => [SEx.kw "stdout" x] | none => []) ++
        (if sOutApp then [SEx.kw "append" .btrue] else [])
      SEx.call "Base.pipeline" [.params kwargs, cmd]
    else cmd
  match sErr with
  | some e =>
    let kwargs := [SEx.kw "stderr" e] ++ (if sErrApp then [SEx.kw "append" .btrue] else [])
    SEx.call "Base.pipeline" [.params kwargs, cmd]
  | none => cmd

/-- The value of `shell_parse`: the words (`interpolate = false`) or the expression
(`interpolate = true`), with `last_arg`. -/
inductive Out where
  | words (w : List (List SEx)) (lastArg : Int)
  | expr (e : SEx) (lastArg : Int)
  deriving Repr, Inhabited

/-- `__repl_entry_shell_parse(str, interpolate, special, filename)`, `base/shell.jl:36-368`. -/
def shellParse (pa : ParseAtom) (str : JS) (interp : Bool) (special : JS) : SH Out :=
  let (off, s0) := lstripOff str
  let s := rstripShell s0
  if s.isEmpty then .ok (if interp then .expr (.tuple [.tuple []]) 1 else .words [] 1)
  else do
    let st := pairsFrom 1 s
    let σ ← parseLoop pa interp str special (st.length + 1) st
      { inSQ := false, inDQ := false, args := [], arg := [], i := 1, s := s, off := off, lastArg := 1,
        upd := false, whs := false, parts := [], sin := none, sout := none, soutApp := false,
        serr := none, serrApp := false, mode := .none }
    if σ.inSQ then .error (.error "unterminated single quote")
    else if σ.inDQ then .error (.error "unterminated double quote")
    else do
      let x ← slice σ.s σ.i (lastindex σ.s)
      let σ := { σ with arg := pushNonempty σ.arg (.lit x) }
      let σ ← (if interp && σ.mode ≠ .none then
          if σ.arg.isEmpty then .error (.error "redirect operator without filename")
          else pure { setRedirect σ (redirectWordExpr σ.arg) with arg := [] }
        else if !σ.arg.isEmpty || σ.whs then pure { σ with args := append2to1 σ.args σ.arg, arg := [] }
        else pure σ : SH PS)
      if !interp then .ok (.words σ.args σ.lastArg)
      else if σ.parts.isEmpty && σ.sin.isNone && σ.sout.isNone && σ.serr.isNone then
        .ok (.expr (tupleOf σ.args) σ.lastArg)
      else
        let final := buildSeg (tupleOf σ.args) σ.sin σ.sout σ.soutApp σ.serr σ.serrApp
        match σ.parts with
        | [] => .ok (.expr final σ.lastArg)
        | (a, i, o, oa, e, ea) :: rest =>
          let r := rest.foldl (fun r (p : Seg) =>
            SEx.call "Base.pipeline" [r, buildSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2])
            (buildSeg a i o oa e ea)
          .ok (.expr (.call "Base.pipeline" [r, final]) σ.lastArg)

/-! ## Properties -/

/-- A `Meta.parseatom` that always throws; the commands below contain no `$`. -/
def paFail : ParseAtom := fun _ _ => .error (.error "parse error")

/-- The value of an all-digit word. -/
def digitsVal (w : JS) : Nat := w.foldl (fun a c => a * 10 + (c.toNat / 2 ^ 24 - 48)) 0

/-- `ErrorException` (a parse error), as opposed to other exceptions. -/
def isParseError : SH Out → Bool
  | .error (.error _) => true
  | _ => false

def isError : SH Out → Bool
  | .error _ => true
  | _ => false

/-- The argument tuple of a parsed command: the expression with its `pipeline` redirect
wrappers and `cmd_gen` removed. -/
def cmdTuple : SEx → Option SEx
  | .call "Base.pipeline" [.params _, inner] =>
    match inner with
    | .call "Base.pipeline" [.params _, .call "Base.cmd_gen" [t]] => some t
    | .call "Base.cmd_gen" [t] => some t
    | _ => none
  | .call "Base.cmd_gen" [t] => some t
  | .tuple ts => some (.tuple ts)
  | _ => none

def outTuple : SH Out → Option SEx
  | .ok (.expr e _) => cmdTuple e
  | _ => none

/-- The number of arguments in an argument tuple. -/
def argCount : Option SEx → Nat
  | some (.tuple ts) => ts.length
  | _ => 0

/-- `base/shell.jl:195,199`: a redirect from or to a file descriptor other than 0, 1
and 2 is rejected with the parse error "unsupported fd N in redirection", for every
digit word. -/
def FdErrorType : Prop :=
  ∀ (pa : ParseAtom) (w : JS), w ≠ [] → w.all isdigitC = true → digitsVal w ≠ 1 → digitsVal w ≠ 2 →
    isParseError (shellParse pa (S "echo " ++ w ++ S ">x") true []) = true

theorem fdErrorType_refuted : ¬ FdErrorType := by
  intro h
  have := h paFail (S "99999999999999999999") (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- `base/shell.jl:302-303`: a redirect operator with no filename word after it is a
parse error; here the operator is followed directly by a pipe. -/
def RedirectNeedsFilename : Prop :=
  ∀ (pa : ParseAtom) (a b : JS), a ≠ [] → b ≠ [] → (a ++ b).all (fun c => A 'a' ≤ c && c ≤ A 'z') = true →
    isError (shellParse pa (S "echo " ++ a ++ S " > | " ++ b) true []) = true

theorem redirectNeedsFilename_refuted : ¬ RedirectNeedsFilename := by
  intro h
  have := h paFail (S "a") (S "cat") (by decide) (by decide) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- An empty quoted word (`''` or `""`) is an argument (`base/shell.jl:129,307`), whether
or not a redirect operator follows it directly: `echo ''>f` and `echo '' >f` run `echo`
with the same number of arguments. -/
def EmptyWordBeforeRedirect : Prop :=
  ∀ (pa : ParseAtom) (q : JC) (f : JS), (q = A '\'' ∨ q = A '"') → f ≠ [] →
    f.all (fun c => A 'a' ≤ c && c ≤ A 'z') = true →
    argCount (outTuple (shellParse pa (S "echo " ++ [q, q] ++ S ">" ++ f) true [])) =
      argCount (outTuple (shellParse pa (S "echo " ++ [q, q] ++ S " >" ++ f) true []))

theorem emptyWordBeforeRedirect_refuted : ¬ EmptyWordBeforeRedirect := by
  intro h
  have := h paFail (A '\'') (S "x") (Or.inl rfl) (by decide) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- `push_nonempty!`, `consume_upto!` and `append_2to1!` (`base/shell.jl:63-77`): an
empty string is never pushed and every other value is appended; `consume_upto!` pushes
`s[i:prevind(s, j)]` and returns the index of the next character (`lastindex(s) + 1` at
the end); `append_2to1!` appends the word, an empty word as `[""]`. -/
def WordHelpers : Prop :=
  (∀ (l : List SEx) (x : SEx), pushNonempty l x = if (match x with | .lit v => v.isEmpty | _ => false) then l else l ++ [x]) ∧
  (∀ (s : JS) (st : List (Nat × JC)) (arg : List SEx) (i j : Int) (x : JS), slice s i (prevind s j) = .ok x →
    consumeUpto s st arg i j = .ok (if x.isEmpty then arg else arg ++ [.lit x], peekIdx s st)) ∧
  (∀ (s : JS) (st : List (Nat × JC)) (arg : List SEx) (i j : Int) (e : ShErr), slice s i (prevind s j) = .error e →
    consumeUpto s st arg i j = .error e) ∧
  (∀ (s : JS) (p : Nat) (c : JC) (st : List (Nat × JC)), peekIdx s ((p, c) :: st) = p) ∧
  (∀ (s : JS), peekIdx s [] = lastindex s + 1) ∧
  (∀ (args : List (List SEx)) (arg : List SEx), append2to1 args arg = args ++ [if arg.isEmpty then [.lit []] else arg])

theorem wordHelpers_proven : WordHelpers := by
  refine ⟨?_, ?_, ?_, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  · intro l x; cases x <;> simp [pushNonempty]
  · intro s st arg i j x h
    simp only [consumeUpto, h, bind, Except.bind, pure, Except.pure, pushNonempty]
  · intro s st arg i j e h
    simp [consumeUpto, h, bind, Except.bind]

/-- `parse_dollar_interp(st, s)` (`base/shell.jl:86-103`): a `$` at the end of the command
and a `$` followed by whitespace are parse errors; `var"` gives the symbol `:var` and
resumes three bytes later; otherwise `Meta.parseatom` parses the atom; parsing resumes
at `SubString(s, j)` with the iterator reset to its `pairs`, and `interp_pos` is the
position of the atom in the original string. -/
def DollarInterp : Prop :=
  (∀ (pa : ParseAtom) (s : JS) (off : Nat), (parseDollar pa [] s off).toOption.isNone) ∧
  (∀ (pa : ParseAtom) (s : JS) (off p : Nat) (c : JC) (st : List (Nat × JC)), isspace c = true →
    parseDollar pa ((p, c) :: st) s off = .error (.error "space not allowed right after $")) ∧
  (∀ (pa : ParseAtom) (s : JS) (off p : Nat) (c : JC) (st : List (Nat × JC)) (t : JS) (o : Nat),
    isspace c = false → startsWithVar s p = true → subFrom s off ((p : Int) + 3) = .ok (t, o) →
    parseDollar pa ((p, c) :: st) s off = .ok (.varSym, (t, o), (p : Int) + off, pairsFrom 1 t)) ∧
  (∀ (pa : ParseAtom) (s : JS) (off p : Nat) (c : JC) (st : List (Nat × JC)) (a : SEx) (j : Int) (t : JS) (o : Nat),
    isspace c = false → startsWithVar s p = false → pa s p = .ok (a, j) → subFrom s off j = .ok (t, o) →
    parseDollar pa ((p, c) :: st) s off = .ok (a, (t, o), (p : Int) + off, pairsFrom 1 t)) ∧
  (∀ (pa : ParseAtom) (s : JS) (off p : Nat) (c : JC) (st : List (Nat × JC)) (e : ShErr),
    isspace c = false → startsWithVar s p = false → pa s p = .error e →
    parseDollar pa ((p, c) :: st) s off = .error e)

theorem dollarInterp_proven : DollarInterp := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro pa s off p c st h; simp [parseDollar, h]
  · intro pa s off p c st t o h1 h2 h3
    simp [parseDollar, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro pa s off p c st a j t o h1 h2 h3 h4
    simp [parseDollar, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro pa s off p c st e h1 h2 h3
    simp [parseDollar, h1, h2, h3, bind, Except.bind]

/-- `redirect_word_expr(word)` (`base/shell.jl:106-114`): a word that is one string is the
file name itself, a single interpolated value goes through `cmd_redirect_target`, and
any other word is concatenated by `cmd_interpolate`. -/
def RedirectWord : Prop :=
  (∀ w : JS, redirectWordExpr [.lit w] = .lit w) ∧
  (∀ x : SEx, (match x with | .lit _ => false | _ => true) = true →
    redirectWordExpr [x] = .call "Base.cmd_redirect_target" [x]) ∧
  (∀ ws : List SEx, ws.length ≠ 1 → redirectWordExpr ws = .call "Base.cmd_interpolate" ws)

theorem redirectWord_proven : RedirectWord := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro x hx; cases x <;> simp_all [redirectWordExpr]
  · intro ws h
    match ws with
    | [] => rfl
    | [_] => simp at h
    | a :: _ :: _ => cases a <;> rfl

/-- `build_seg_expr` (`base/shell.jl:328-343`): a segment without redirects is
`cmd_gen(seg_tuple)`; otherwise it is wrapped in `pipeline(cmd; stdin, stdout, append)`
when `stdin` or `stdout` is redirected and then in `pipeline(cmd; stderr, append)` when
`stderr` is, and the command inside is always `cmd_gen(seg_tuple)`. -/
def BuildSegShape : Prop :=
  (∀ (seg : SEx) (oa ea : Bool), buildSeg seg none none oa none ea = .call "Base.cmd_gen" [seg]) ∧
  (∀ (seg : SEx) (i o : Option SEx) (oa : Bool) (e : Option SEx) (ea : Bool),
    cmdTuple (buildSeg seg i o oa e ea) = some seg) ∧
  (∀ (seg x : SEx) (oa : Bool), buildSeg seg none (some x) oa none false =
    .call "Base.pipeline" [.params ([.kw "stdout" x] ++ if oa then [.kw "append" .btrue] else []),
      .call "Base.cmd_gen" [seg]]) ∧
  (∀ (seg x : SEx) (ea : Bool), buildSeg seg none none false (some x) ea =
    .call "Base.pipeline" [.params ([.kw "stderr" x] ++ if ea then [.kw "append" .btrue] else []),
      .call "Base.cmd_gen" [seg]])

theorem buildSegShape_proven : BuildSegShape := by
  refine ⟨fun _ _ _ => rfl, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  intro seg i o oa e ea
  cases i <;> cases o <;> cases e <;> rfl

end JuliaLean.MiscCov.Shell
