# show(::Cmd) prints invalid UTF-8 bytes raw, so the output cannot be parsed.
c = Cmd(["echo", "\xff"])
s = repr(c)
println("repr(c) = ", repr(s))
r = try eval(Meta.parse(s)) catch e; e end
println("reparse: ", r isa Cmd ? repr(r.exec) : typeof(r))
(r isa Cmd && r == c) || println("REPRODUCED shellcmd-show-invalid-utf8")
