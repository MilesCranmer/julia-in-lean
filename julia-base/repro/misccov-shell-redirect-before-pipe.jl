# A backtick command whose `>` redirect has no filename throws at the end of the
# command, but is silently dropped when a `|` follows (base/shell.jl:149-169).
r1 = try Base.shell_parse("echo a >")[1] catch e; e end
r2 = try Base.shell_parse("echo a > | cat")[1] catch e; e end
println("shell_parse(\"echo a >\")       => ", r1 isa Exception ? sprint(showerror, r1) : repr(r1))
println("shell_parse(\"echo a > | cat\") => ", r2 isa Exception ? sprint(showerror, r2) : repr(r2))
if r1 isa ErrorException && !(r2 isa Exception) && !occursin("stdout", repr(r2))
    println("REPRODUCED misccov-shell-redirect-before-pipe")
end
