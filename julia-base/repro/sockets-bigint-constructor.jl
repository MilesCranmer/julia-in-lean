using Sockets

results = Bool[]
for T in (IPv4, IPv6)
    n = BigInt(1)
    result = try
        T(n)
    catch e
        e
    end
    ordinary = T(1)
    println(T, "(1) = ", ordinary)
    println(T, "(big(1)) threw ", result isa Exception ? nameof(typeof(result)) : "nothing")
    if result isa MethodError
        println("missing method = ", result.f, "(", join(string.(result.args), ", "), ")")
    end
    push!(results, result isa MethodError && result.f === typemax)
end
println(all(results) ? "REPRODUCED sockets-bigint-constructor" : "not reproduced")
