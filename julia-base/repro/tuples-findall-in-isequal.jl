z1 = findall(in([0.0]), (-0.0,))
z2 = findall(x -> x in [0.0], (-0.0,))
n1 = findall(in([NaN]), (NaN,))
n2 = findall(x -> x in [NaN], (NaN,))
println(z1, " ", z2, " ", n1, " ", n2, " ", -0.0 in [0.0], " ", NaN in [NaN])
if z1 != z2 && n1 != n2
    println("REPRODUCED tuples-findall-in-isequal")
end
