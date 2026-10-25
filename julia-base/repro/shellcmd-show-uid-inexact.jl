# show(::Cmd) converts uid/gid to Int32 and throws for ids at or above 2^31.
c = setuid(`id -u`, 0x80000000)
println("c.uid = ", repr(c.uid))
r = try repr(c) catch e; e end
println("repr(c) = ", repr(r))
r2 = try repr(setgid(`id -g`, typemax(UInt32))) catch e; e end
println("repr(setgid(`id -g`, typemax(UInt32))) = ", repr(r2))
(r isa Exception || r2 isa Exception) && println("REPRODUCED shellcmd-show-uid-inexact")
