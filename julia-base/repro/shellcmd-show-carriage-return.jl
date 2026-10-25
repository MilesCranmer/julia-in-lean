# show(::Cmd) prints a carriage return raw; the parser normalizes it to a linefeed.
c = Cmd(["printf", "a\rb"])
s = repr(c)
println("repr(c) = ", repr(s))
r = eval(Meta.parse(s))
println("reparsed exec = ", repr(r.exec))
r == c || println("REPRODUCED shellcmd-show-carriage-return")
