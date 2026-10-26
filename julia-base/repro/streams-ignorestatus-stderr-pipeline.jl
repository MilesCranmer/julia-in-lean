cmd = pipeline(`/bin/sh -c 'echo error >&2; exit 7'`; stderr=`/bin/cat`)
result = try
    ignorestatus(cmd)
catch err
    err
end

println("typeof(cmd) = ", typeof(cmd))
println("ignorestatus(cmd) = ", repr(result))
result isa MethodError && println("REPRODUCED streams-ignorestatus-stderr-pipeline")
