import JuliaLean.base.shell

/-!
# `__repl_entry_shell_parse(str, interpolate, special, filename)`, `base/shell.jl:36-368`

Master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, including the `interpolate = true` branches (`$`, `|`, `<`, `>`
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
