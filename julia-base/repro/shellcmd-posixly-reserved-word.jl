# shell_escape_posixly leaves a reserved word unquoted in command position, so the
# shell parses it as syntax instead of a command name.
e = Base.shell_escape_posixly("done", "x")
println("shell_escape_posixly(\"done\", \"x\") = ", repr(e))
p = run(pipeline(ignorestatus(`sh -c $e`), stderr=devnull))
println("sh -c exit code: ", p.exitcode, " (127 = command not found, 2 = syntax error)")
p.exitcode == 2 && println("REPRODUCED shellcmd-posixly-reserved-word")
