cmd = pipeline(`/bin/true`, `/bin/cat`)
result = try
    detach(cmd)
catch err
    err
end

println("typeof(cmd) = ", typeof(cmd))
println("detach(cmd) = ", repr(result))
result isa MethodError && println("REPRODUCED streams-detach-pipeline")
