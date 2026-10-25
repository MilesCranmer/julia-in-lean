# shell_escape_csh and escape_microsoft_c_args throw on an empty argument list or an
# empty Cmd, while shell_escape and shell_escape_posixly return "".
res = Dict()
for f in (Base.shell_escape, Base.shell_escape_posixly, Base.shell_escape_csh, Base.escape_microsoft_c_args)
    r1 = try f() catch e; e end
    r2 = try f(``) catch e; e end
    println(f, "() = ", repr(r1), "; ", f, "(``) = ", repr(r2))
    res[f] = (r1, r2)
end
if any(v -> v[1] isa Exception || v[2] isa Exception, values(res))
    println("REPRODUCED shellcmd-escape-empty-args")
end
