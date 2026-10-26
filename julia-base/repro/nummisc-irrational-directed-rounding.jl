struct TinyAboveOne <: AbstractIrrational end
struct TinyBelowOne <: AbstractIrrational end

Base.BigFloat(::TinyAboveOne; precision=precision(BigFloat)) =
    setprecision(BigFloat, precision) do
        BigFloat(1) + sqrt(BigFloat(2)) * BigFloat(2)^(-1000)
    end
Base.BigFloat(::TinyBelowOne; precision=precision(BigFloat)) =
    setprecision(BigFloat, precision) do
        BigFloat(1) - sqrt(BigFloat(2)) * BigFloat(2)^(-1000)
    end
Base.Float64(::Union{TinyAboveOne,TinyBelowOne}) = 1.0
Base.Float32(::Union{TinyAboveOne,TinyBelowOne}) = 1.0f0
Base.:(==)(::TinyAboveOne, ::TinyAboveOne) = true
Base.:(==)(::TinyBelowOne, ::TinyBelowOne) = true
Base.hash(::TinyAboveOne, h::UInt) = hash(:TinyAboveOne, h)
Base.hash(::TinyBelowOne, h::UInt) = hash(:TinyBelowOne, h)

above = Float64(TinyAboveOne(), RoundUp)
below = Float64(TinyBelowOne(), RoundDown)
println("Float64(TinyAboveOne(), RoundUp) = ", above)
println("expected above = ", nextfloat(1.0))
println("Float64(TinyBelowOne(), RoundDown) = ", below)
println("expected below = ", prevfloat(1.0))
if above == 1.0 && below == 1.0
    println("REPRODUCED nummisc-irrational-directed-rounding")
end
