import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ShellCmd.Refute
import JuliaLean.ShellCmd.ProofQuote
import JuliaLean.ShellCmd.ProofPosix
import JuliaLean.ShellCmd.ProofMS
import JuliaLean.ShellCmd.ProofWin
import JuliaLean.ShellCmd.ProofShow
import JuliaLean.ShellCmd.ProofSplit

namespace JuliaLean.ShellCmd

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "shellcmd-split-escape-roundtrip", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape", "Base.shell_split", "Base.shell_parse"]
    statement := "shell_split(shell_escape(xs...; special)) == xs for every list of strings xs (any characters, including empty strings, quotes, backslashes, \\$, newlines, non-ASCII and invalid UTF-8) and every special."
    source := "base/shell.jl:437-441 (shell_escape docstring: inverse of shell_split)", status := .proven
    prop := ``ShellSplitEscape, thm := some ``shellSplitEscape_proven
    notes := "Fails on 1.13.2 for words containing both ' and \\ (the double-quote path did not escape backslashes); fixed on master by #61113." },
  { id := "shellcmd-split-escaped-trailing-space", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_split", "Base.rstrip_shell"]
    statement := "shell_split(\"a\\\\\" * c) == [\"a\" * c] for every whitespace character c, as for c = ' '."
    source := "base/shell.jl:10 (rstrip_shell docstring), :235-238 (escaped characters are literal)", status := .refuted
    prop := ``SplitEscapedTrailingWhitespace, thm := some ``splitEscapedTrailingWhitespace_refuted
    issue := "none found (queries: rstrip_shell, dangling backslash, shell_split tab, backslash trailing whitespace command)"
    notes := "shell_split(\"a\\\\\\t\") throws \"dangling backslash\"; rstrip_shell keeps only an escaped trailing ' '. Same on 1.13.2." },
  { id := "shellcmd-line-continuation-index", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_parse", "Base.shell_split", "@cmd"]
    statement := "A backslash-newline followed by spaces/tabs joins the two lines: shell_split(\" \"^k * w1 * \"\\\\\\n\" * ind * w2) == [w1 * w2] for plain words w1, w2."
    source := "base/shell.jl:216-227 (line continuation)", status := .refuted
    prop := ``LineContinuationJoins, thm := some ``lineContinuationJoins_refuted
    issue := "none found (queries: shell_parse line continuation, shell_split backslash newline, line continuation backtick command, cmd line continuation, nextind shell_parse)"
    notes := "shell_split(\"    é\\\\\\n x\") == [\"é\"]; in a command literal `ls é $x \\<newline> --flag` gives \"-flag\". nextind(str, i) is applied to an index of the SubString s. Same on 1.13.2." },
  { id := "shellcmd-posixly-reserved-word", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_posixly"]
    statement := "The command name printed by shell_escape_posixly is never an unquoted POSIX reserved word."
    source := "base/shell.jl:502-506 (docstring: safe to pass to a posix shell); POSIX XCU 2.4", status := .refuted
    prop := ``PosixlyNoReservedWord, thm := some ``posixlyNoReservedWord_refuted
    issue := "none found (queries: shell_escape_posixly, posixly reserved word, shell escape reserved word)"
    notes := "shell_escape_posixly(\"done\", \"x\") == \"done x\", a syntax error in sh. Same on 1.13.2." },
  { id := "shellcmd-escape-empty-args", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_csh", "Base.escape_microsoft_c_args"]
    statement := "shell_escape_csh(xs...) and escape_microsoft_c_args(xs...) return a string for every argument list, including none and the empty Cmd."
    source := "base/shell.jl:523-524,676-677 (signatures args::Union{Cmd,AbstractString...})", status := .refuted
    prop := ``EscapeEmptyArgs, thm := some ``escapeEmptyArgs_refuted
    issue := "none found (queries: escape empty Cmd, reducing over an empty collection shell, shell_escape empty, shell_escape_csh, escape_microsoft_c_args)"
    notes := "sum(sizeof, args) in the sizehint throws for zero arguments; shell_escape and shell_escape_posixly return \"\". Same on 1.13.2." },
  { id := "shellcmd-wincmd-percent-doc", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_wincmd"]
    statement := "shell_escape_wincmd(s) throws ArgumentError when s contains %."
    source := "base/shell.jl:589-592 (docstring: \"else this function will fail with an ArgumentError\")", status := .refuted
    prop := ``WincmdPercentThrows, thm := some ``wincmdPercentThrows_refuted
    issue := "none found (queries: shell_escape_wincmd, wincmd percent ArgumentError)"
    notes := "shell_escape_wincmd(\"100%\") == \"100%\"; the docstring contradicts itself. Same on 1.13.2." },
  { id := "shellcmd-show-backslash-backtick", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)"]
    statement := "For arguments of valid UTF-8 without CR, the command literal printed by show(::Cmd) lexes to exactly the shell-quoted words."
    source := "base/cmd.jl:201-210; show docstring (parseable output)", status := .refuted
    prop := ``ShowLexesBackslash, thm := some ``showLexesBackslash_refuted
    issue := "none found (queries: show Cmd backtick, Cmd show roundtrip, show Cmd escape, repr Cmd parse, Cmd literal backslash backtick)"
    notes := "Cmd([\"\\\\`\"]) prints `'\\\\\\\\`'`, which ends after '\\\\. Same on 1.13.2." },
  { id := "shellcmd-show-carriage-return", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)"]
    statement := "For arguments of valid UTF-8 without backslash, the command literal printed by show(::Cmd) lexes to exactly the shell-quoted words."
    source := "base/cmd.jl:201-210; show docstring (parseable output)", status := .refuted
    prop := ``ShowLexesCR, thm := some ``showLexesCR_refuted
    issue := "none found (queries: Cmd carriage return, show Cmd escape, repr Cmd parse, Cmd show roundtrip)"
    notes := "A raw CR in the printed literal is read back as LF. Same on 1.13.2." },
  { id := "shellcmd-show-invalid-utf8", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)"]
    statement := "For arguments without CR and backslash, the command literal printed by show(::Cmd) lexes to exactly the shell-quoted words."
    source := "base/cmd.jl:201-210; show docstring (parseable output)", status := .refuted
    prop := ``ShowLexesUtf8, thm := some ``showLexesUtf8_refuted
    issue := "none found (queries: Cmd invalid UTF-8 show, Cmd show non-UTF-8, show Cmd escape, repr Cmd parse)"
    notes := "Cmd([\"\\xff\"]) prints a raw invalid byte; Meta.parse rejects it. Same on 1.13.2." },
  { id := "shellcmd-show-uid-inexact", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)", "setuid(::Cmd, ::Integer)", "setgid(::Cmd, ::Integer)"]
    statement := "show(::Cmd) does not throw for any uid stored by setuid."
    source := "invariant (show of a valid object); base/cmd.jl:469 stores any UInt32 uid", status := .refuted
    prop := ``ShowUidTotal, thm := some ``showUidTotal_refuted
    issue := "none found (queries: Cmd show uid, setuid Cmd show, setuid show, setgid Int32, show Cmd Int32)"
    notes := "show converts with Int32(cmd.uid): InexactError for uid >= 2^31 (gid likewise). Same on 1.13.2." },
  { id := "shellcmd-show-env-nonascii-key", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)", "Base.show_env"]
    statement := "show(::Cmd) does not throw for a command whose environment was set by setenv(cmd, k => v) with a nonempty name without '='."
    source := "invariant (show of a valid object)", status := .refuted
    prop := ``ShowEnvTotal, thm := some ``showEnvTotal_refuted
    issue := "none found (queries: show_env, Redact sensitive env vars, environment variable non-ASCII Cmd, setenv StringIndexError); related #61287"
    notes := "findnext('=', e, 2) throws StringIndexError for a multi-byte first character. Regression on master (show_env from #61287); 1.13.2 prints the Cmd." },
  { id := "shellcmd-eq-ignores-cpus", juliaFile := "base/cmd.jl"
    juliaFns := ["==(::Cmd, ::Cmd)", "hash(::Cmd, ::UInt)"]
    statement := "Two Cmds that are == have equal fields."
    source := "invariant (== on a settings struct); base/cmd.jl:99-101", status := .refuted
    prop := ``CmdEqFieldwise, thm := some ``cmdEqFieldwise_refuted
    issue := "none found (queries: Cmd cpus equality, setcpuaffinity, Cmd hash, Cmd equality, Cmd isequal, cpus Cmd)"
    notes := "setcpuaffinity(`ls`, [1]) == `ls`; hash also ignores cpus. Same on 1.13.2." },
  { id := "shellcmd-addenv-nonascii-key", juliaFile := "base/cmd.jl"
    juliaFns := ["addenv(::Cmd, ...)", "Base.splitenv"]
    statement := "addenv(setenv(cmd, k0 => v0), k => v) succeeds and sets k to v, for nonempty names without '=' and text without NUL."
    source := "base/cmd.jl:373-378 (addenv docstring)", status := .refuted
    prop := ``AddenvSets, thm := some ``addenvSets_refuted
    issue := "none found (queries: splitenv, addenv StringIndexError, addenv unicode, setenv StringIndexError, environment variable non-ASCII Cmd, addenv); related #44212"
    notes := "splitenv uses findnext('=', e, 2): StringIndexError when the name starts with a multi-byte character. Same on 1.13.2." },
  { id := "shellcmd-split-unterminated-quote", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_split", "Base.shell_parse"]
    statement := "shell_split(\"'\" * t) throws \"unterminated single quote\" when t has no '; shell_split(\"\\\"\" * t) throws \"unterminated double quote\" when t has no \" and no backslash."
    source := "base/shell.jl:229,298-299", status := .proven
    prop := ``SplitUnterminatedQuote, thm := some ``splitUnterminatedQuote_proven },
  { id := "shellcmd-posixly-roundtrip", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_posixly"]
    statement := "POSIX sh word recognition and quote removal (XCU 2.2, 2.3, 2.6.7) of shell_escape_posixly(xs...) gives back xs, and the text uses no expansion, operator, comment or assignment."
    source := "base/shell.jl:502-506 (shell_escape_posixly docstring)", status := .proven
    prop := ``PosixlyRoundTrip, thm := some ``posixlyRoundTrip_proven },
  { id := "shellcmd-msargs-roundtrip", juliaFile := "base/shell.jl"
    juliaFns := ["Base.escape_microsoft_c_args", "Base.escape_raw_string"]
    statement := "The Microsoft C runtime argument rules (arguments after argv[0]) parse escape_microsoft_c_args(xs...) back into xs, for nonempty xs."
    source := "base/shell.jl:679-692 (escape_microsoft_c_args docstring); learn.microsoft.com Parsing C command-line arguments", status := .proven
    prop := ``MsArgsRoundTrip, thm := some ``msArgsRoundTrip_proven },
  { id := "shellcmd-wincmd-roundtrip", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_wincmd"]
    statement := "For s without %, CR, LF and NUL, the cmd.exe caret/quote phase of shell_escape_wincmd(s) yields s and sees no unescaped operator."
    source := "base/shell.jl:574-596 (shell_escape_wincmd docstring)", status := .proven
    prop := ``WincmdRoundTrip, thm := some ``wincmdRoundTrip_proven },
  { id := "shellcmd-wincmd-control-throws", juliaFile := "base/shell.jl"
    juliaFns := ["Base.shell_escape_wincmd"]
    statement := "shell_escape_wincmd(s) throws ArgumentError when s contains NUL, CR or LF."
    source := "base/shell.jl:586-587", status := .proven
    prop := ``WincmdControlThrows, thm := some ``wincmdControlThrows_proven },
  { id := "shellcmd-show-lexes-plain", juliaFile := "base/cmd.jl"
    juliaFns := ["show(::IO, ::Cmd)", "Base.print_shell_word"]
    statement := "For arguments of valid UTF-8 without CR and backslash, the command literal printed by show(::Cmd) lexes to exactly the shell-quoted words."
    source := "base/cmd.jl:201-210; show docstring (parseable output)", status := .proven
    prop := ``ShowLexesPlain, thm := some ``showLexesPlain_proven },
  { id := "shellcmd-interp-splice", juliaFile := "base/cmd.jl"
    juliaFns := ["Base.arg_gen", "Base.cmd_gen", "Base.cmd_interpolate"]
    statement := "Interpolating a collection splices its elements as separate arguments, surrounding text attaches to each, and several collections in one word give their Cartesian product with the first varying slowest."
    source := "doc/src/manual/running-external-programs.md:142-188", status := .proven
    prop := ``InterpSplice, thm := some ``interpSplice_proven }
]

end JuliaLean.ShellCmd
