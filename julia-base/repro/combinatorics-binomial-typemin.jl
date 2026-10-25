types = (Int8, Int16, Int32, Int64, Int128)
wrong = true

for T in types
    n = typemin(T)
    actual = binomial(n, one(T))
    println("binomial(typemin(", T, "), one(", T, ")) = ", actual,
            "; expected ", n)
    global wrong &= actual == zero(T)
end

if wrong
    println("REPRODUCED combinatorics-binomial-typemin")
end
