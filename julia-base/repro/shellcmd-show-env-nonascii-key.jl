# show(::Cmd) looks for the '=' of each environment entry with findnext('=', e, 2), which
# throws StringIndexError when the variable name starts with a multi-byte character.
c = setenv(`env`, "é" => "1")
println("c.env = ", repr(c.env))
r = try repr(c) catch e; e end
println("repr(c) = ", repr(r))
r isa Exception && println("REPRODUCED shellcmd-show-env-nonascii-key")
