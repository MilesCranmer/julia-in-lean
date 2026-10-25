import JuliaLean.ShellCmd.Parse
import JuliaLean.ShellCmd.Escape
import JuliaLean.ShellCmd.Oracles
import JuliaLean.ShellCmd.Cmd

/-! # Properties of `base/shell.jl` and `base/cmd.jl` -/

namespace JuliaLean.ShellCmd

/-- `shell_split(shell_escape(xs...; special))` gives back the words
(`base/shell.jl:437-441`: "it takes a string or command object and escapes any
special characters in such a way that calling `Base.shell_split()` on it would
give back the array of words in the original command"). -/
def ShellSplitEscape : Prop :=
  ∀ (xs : List JS) (special : JS), shellSplit (shellEscape xs special) = .ok xs

/-- `shell_split` reports the documented errors for an unterminated quote:
`'` followed by text without `'`, and `"` followed by text without `"` and `\`. -/
def SplitUnterminatedQuote : Prop :=
  (∀ t : JS, A '\'' ∉ t → shellSplit (A '\'' :: t) = .error (.error "unterminated single quote")) ∧
  (∀ t : JS, A '"' ∉ t → A '\\' ∉ t →
    shellSplit (A '"' :: t) = .error (.error "unterminated double quote"))

/-- An escaped whitespace character at the end of the input is part of the last
word, as an escaped space is (`base/shell.jl:10`, `:235-238`). -/
def SplitEscapedTrailingWhitespace : Prop :=
  ∀ c : JC, isspace c = true → shellSplit [A 'a', A '\\', c] = .ok [[A 'a', c]]

/-- A character that is valid, not whitespace, not a quote and not a backslash. -/
def plainChar (c : JC) : Bool :=
  Strings.isvalidChar c && !isspace c && c != A '\'' && c != A '"' && c != A '\\'

/-- A backslash-newline followed by indentation joins the two lines
(`base/shell.jl:216-227`), whatever whitespace precedes the text. -/
def LineContinuationJoins : Prop :=
  ∀ (k : Nat) (w1 ind w2 : JS), w1.all plainChar → w2.all plainChar → w2 ≠ [] →
    ind.all (fun c => c == A ' ' || c == A '\t') →
    shellSplit (List.replicate k (A ' ') ++ w1 ++ [A '\\', A '\n'] ++ ind ++ w2) =
      .ok [w1 ++ w2]

/-- The output of `shell_escape_posixly` is split by POSIX sh into the original
words (`base/shell.jl:502-506`: "escapes any special characters in such a way
that it is safe to pass it as an argument to a posix shell"). -/
def PosixlyRoundTrip : Prop :=
  ∀ xs : List JS, posixSplit (shellEscapePosixly xs) = some xs

/-- The command name printed by `shell_escape_posixly` is never an unquoted
reserved word, which POSIX sh would parse as syntax (XCU 2.4). -/
def PosixlyNoReservedWord : Prop :=
  ∀ (x : JS) (xs : List JS), firstWordReserved (shellEscapePosixly (x :: xs)) = false

/-- `escape_microsoft_c_args` output is parsed back into the arguments by the
Microsoft C runtime rules (`base/shell.jl:679-692`). -/
def MsArgsRoundTrip : Prop :=
  ∀ xs : List JS, xs ≠ [] → ∃ e, escapeMicrosoftCArgs xs = .ok e ∧ msParse e = xs

/-- The string escapers accept any argument list, including none and the empty
`Cmd` (`base/shell.jl:523-524,676-677`: `args::Union{Cmd,AbstractString...}`). -/
def EscapeEmptyArgs : Prop :=
  ∀ xs : List JS, (∃ e, shellEscapeCsh xs = .ok e) ∧ (∃ e, escapeMicrosoftCArgs xs = .ok e)

/-- `shell_escape_wincmd` output, after the `cmd.exe` caret/quote phase, is the
input (`base/shell.jl:574-596`), for input without `%` and control characters. -/
def WincmdRoundTrip : Prop :=
  ∀ s : JS, A '%' ∉ s → A '\r' ∉ s → A '\n' ∉ s → A '\x00' ∉ s →
    ∃ e, shellEscapeWincmd s = .ok e ∧ cmdLine e = some s

/-- `shell_escape_wincmd` throws `ArgumentError` for input with NUL, CR or LF
(`base/shell.jl:586-587`). -/
def WincmdControlThrows : Prop :=
  ∀ s : JS, (A '\r' ∈ s ∨ A '\n' ∈ s ∨ A '\x00' ∈ s) →
    ∃ msg, shellEscapeWincmd s = .error (.jl (.argumentError msg))

/-- `shell_escape_wincmd` throws `ArgumentError` for input containing `%`
(`base/shell.jl:589-592`: "if the input does not contain `%` (else this function
will fail with an ArgumentError)"). -/
def WincmdPercentThrows : Prop :=
  ∀ s : JS, A '%' ∈ s → A '\r' ∉ s → A '\n' ∉ s → A '\x00' ∉ s →
    ∃ msg, shellEscapeWincmd s = .error (.jl (.argumentError msg))

/-- The command literal printed by `show(::Cmd)` lexes to exactly the
shell-quoted words (`base/cmd.jl:201-210`), for arguments of valid UTF-8 without
carriage returns and backslashes. -/
def ShowLexesPlain : Prop :=
  ∀ exec : List JS, (∀ w ∈ exec, ∀ c ∈ w, Strings.isvalidChar c = true ∧ c ≠ A '\r' ∧ c ≠ A '\\') →
    lexCmdLiteral (showExec exec) = some (showBody exec, [])

/-- As `ShowLexesPlain`, allowing backslashes. -/
def ShowLexesBackslash : Prop :=
  ∀ exec : List JS, (∀ w ∈ exec, ∀ c ∈ w, Strings.isvalidChar c = true ∧ c ≠ A '\r') →
    lexCmdLiteral (showExec exec) = some (showBody exec, [])

/-- As `ShowLexesPlain`, allowing carriage returns. -/
def ShowLexesCR : Prop :=
  ∀ exec : List JS, (∀ w ∈ exec, ∀ c ∈ w, Strings.isvalidChar c = true ∧ c ≠ A '\\') →
    lexCmdLiteral (showExec exec) = some (showBody exec, [])

/-- As `ShowLexesPlain`, allowing invalid UTF-8. -/
def ShowLexesUtf8 : Prop :=
  ∀ exec : List JS, (∀ w ∈ exec, ∀ c ∈ w, c ≠ A '\r' ∧ c ≠ A '\\') →
    lexCmdLiteral (showExec exec) = some (showBody exec, [])

/-- `show(::Cmd)` does not throw for a command with a uid set by `setuid`
(`base/cmd.jl:469` stores any `UInt32`). -/
def ShowUidTotal : Prop :=
  ∀ (exec : List JS) (u : UInt32), (showCmdNoEnv { cmdOf exec with uid := some u }).toOption.isSome

/-- `show(::Cmd)` does not throw for a command whose environment was set by
`setenv(cmd, k => v)` with a nonempty name without `=`. -/
def ShowEnvTotal : Prop :=
  ∀ (exec : List JS) (k v : JS) (mode : ShowEnvMode) (sens : JS → Bool) (c : CmdM),
    k ≠ [] → A '=' ∉ k → setenvPairs (cmdOf exec) [(k, v)] = .ok c → showCmdEnvOk mode sens c = true

/-- `==` on `Cmd` compares every setting: equal commands have equal fields. -/
def CmdEqFieldwise : Prop := ∀ x y : CmdM, cmdEq x y = true → x = y

/-- `addenv(setenv(cmd, k0 => v0), k => v)` succeeds and sets `k` to `v`
(`base/cmd.jl:373-378`), for nonempty names without `=` and text without NUL. -/
def AddenvSets : Prop :=
  ∀ (envENV : List (JS × JS)) (exec : List JS) (k0 v0 k v : JS) (c : CmdM),
    k0 ≠ [] → k ≠ [] → A '=' ∉ k0 → A '=' ∉ k → A '\x00' ∉ k0 ++ v0 ++ k ++ v →
    setenvPairs (cmdOf exec) [(k0, v0)] = .ok c →
    ∃ c', addenv envENV true c [(k, some v)] = .ok c' ∧
      ∃ env, c'.env = some env ∧ (k ++ [A '='] ++ v) ∈ env

/-- Interpolating a collection splices its elements as separate arguments,
attaches surrounding text to each, and forms the Cartesian product of several
collections in one word, the first varying slowest
(`doc/src/manual/running-external-programs.md:142-188`). -/
def InterpSplice : Prop :=
  ∀ (pre post sep : JS) (xs ys : List JS), (∀ w ∈ pre :: post :: sep :: xs ++ ys, A '\x00' ∉ w) →
    argGen [.iter (xs.map .val)] = .ok xs ∧
    argGen [.str pre, .iter (xs.map .val), .str post] = .ok (xs.map (fun x => pre ++ x ++ post)) ∧
    argGen [.iter (xs.map .val), .str sep, .iter (ys.map .val)] =
      .ok (xs.flatMap (fun x => ys.map (fun y => x ++ sep ++ y)))

end JuliaLean.ShellCmd
