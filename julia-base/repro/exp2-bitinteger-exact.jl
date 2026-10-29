using Test

println("VERSION ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)

const types = (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)

function expected_exp2(x::Integer)
    n = BigInt(x)
    n > 1023 && return Inf
    n < -1074 && return 0.0
    return ldexp(1.0, Int(n))
end

@testset "exp2 BitInteger exact" begin
    for T in types
        values = Set{T}((typemin(T), typemax(T)))
        for n in -1075:1024
            typemin(T) <= n <= typemax(T) && push!(values, T(n))
        end
        for n in (-(big(2)^64)-1069, -(big(2)^64), big(2)^64, big(2)^127-1)
            typemin(T) <= n <= typemax(T) && push!(values, T(n))
        end
        for x in values
            @test isequal(exp2(x), expected_exp2(x))
        end
    end
end
println("EXP2 BITINTEGER EXACT OK")
