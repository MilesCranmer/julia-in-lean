# Docstring of Base.Ryu.pow5invsplit (base/ryu/utils.jl:271-278): "The result is an
# unsigned integer twice as wide as T ... with `pow5_inv_bitcount(T)` significant bits."
# For i = 0 the result is 2^pow5_inv_bitcount(T) + 1, one bit more.
for T in (Float64, Float32, Float16)
    v = Base.Ryu.pow5invsplit(T, 0)
    println(T, ": pow5invsplit(T, 0) = ", repr(v), ", significant bits = ", ndigits(v, base = 2),
            ", pow5_inv_bitcount(T) = ", Base.Ryu.pow5_inv_bitcount(T))
end
if all(T -> ndigits(Base.Ryu.pow5invsplit(T, 0), base = 2) != Base.Ryu.pow5_inv_bitcount(T), (Float64, Float32, Float16))
    println("REPRODUCED misccov-ryu-pow5invsplit-bitcount")
end
