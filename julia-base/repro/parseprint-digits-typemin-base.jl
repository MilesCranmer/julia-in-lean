# digits!/digits reject bases with abs(base) < 2, saying "base must be ≥ 2 or ≤ -2".
b = typemin(Int)
@assert b <= -2
println("ndigits(5; base=b) = ", ndigits(5; base=b))
threw = try
    println("digits(5; base=b) = ", digits(5; base=b))
    false
catch e
    println("digits(5; base=b) threw ", typeof(e), ": ", sprint(showerror, e))
    e isa DomainError
end
threw && println("REPRODUCED parseprint-digits-typemin-base")
