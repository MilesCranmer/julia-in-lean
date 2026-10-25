# show(::Cmd) escapes backticks as \` but does not double a backslash in front of them,
# so an argument containing a backslash followed by a backtick prints as an invalid literal.
c = Cmd(["echo", "\\`"])
s = repr(c)
println("repr(c) = ", s)
r = try eval(Meta.parse(s)) catch e; e end
println("eval(Meta.parse(repr(c))) = ", repr(r))
if !(r isa Cmd && r == c)
    println("REPRODUCED shellcmd-show-backslash-backtick")
end
