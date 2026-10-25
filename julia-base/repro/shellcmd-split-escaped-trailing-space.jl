# An escaped trailing space is kept as part of the last word, but any other escaped
# trailing whitespace character (tab, no-break space) is stripped first, leaving a
# dangling backslash.
r1 = try Base.shell_split("a\\ ") catch e; e end
r2 = try Base.shell_split("a\\\t") catch e; e end
r3 = try Base.shell_split("a\\\tb") catch e; e end
println("shell_split(\"a\\\\ \") = ", repr(r1))
println("shell_split(\"a\\\\\\t\") = ", repr(r2))
println("shell_split(\"a\\\\\\tb\") = ", repr(r3))
r2 != ["a\t"] && println("REPRODUCED shellcmd-split-escaped-trailing-space")
