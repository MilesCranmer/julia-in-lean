a = sincospi(missing)
b = sincos(missing)
c = sincosd(missing)
println("sincospi(missing) = ", repr(a))
println("sincos(missing)   = ", repr(b))
println("sincosd(missing)  = ", repr(c))
r = try
    s, co = sincospi(missing)
    "ok"
catch e
    sprint(showerror, e; context=:limit => true) |> l -> first(split(l, '\n'))
end
println("s, c = sincospi(missing): ", r)
a === missing && b === (missing, missing) && c === (missing, missing) && println("REPRODUCED missingchar-sincospi-missing")
