# addenv splits each existing "key=value" entry with findnext('=', e, 2); byte 2 is inside
# a multi-byte first character, so a non-ASCII variable name throws StringIndexError.
c = setenv(`env`, "é" => "1")
println("c.env = ", repr(c.env))
r = try addenv(c, "A" => "2") catch e; e end
println("addenv(c, \"A\" => \"2\") = ", repr(r))
r2 = try addenv(`env`, ["éa=1"]) catch e; e end
println("addenv(`env`, [\"éa=1\"]) = ", repr(r2))
(r isa StringIndexError || r2 isa StringIndexError) && println("REPRODUCED shellcmd-addenv-nonascii-key")
