# ==(::Cmd, ::Cmd) and hash(::Cmd) ignore the cpus field set by setcpuaffinity.
a = setcpuaffinity(`ls`, [1])
b = `ls`
println("a = ", repr(a), "; b = ", repr(b))
println("a.cpus = ", repr(a.cpus), "; b.cpus = ", repr(b.cpus))
println("a == b: ", a == b, "; hash equal: ", hash(a) == hash(b), "; isequal: ", isequal(a, b))
println("Dict keys: ", length(Dict(a => 1, b => 2)))
(a == b && a.cpus != b.cpus) && println("REPRODUCED shellcmd-eq-ignores-cpus")
