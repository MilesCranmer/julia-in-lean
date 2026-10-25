# string(n; base) supports negative bases; digits handles the same unsigned n.
n = UInt8(200)
d = digits(n; base=-2)
println("digits(n; base=-2) = ", d, ", value ", sum(d[k] * (-2)^(k-1) for k in eachindex(d)))
threw = try
    println("string(n; base=-2) = ", string(n; base=-2))
    false
catch e
    println("string(n; base=-2) threw ", typeof(e), ": ", sprint(showerror, e))
    e isa InexactError
end
threw && println("REPRODUCED parseprint-string-negative-base-unsigned")
