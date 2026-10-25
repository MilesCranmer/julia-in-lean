# range(a, b; length=n) throws InexactError for finite endpoints when 0 lies far
# outside [a, b]: the index of the smallest-magnitude element is rounded to Int
# before it is clamped to 1:n.
bug = false
for (a, b, n) in ((1.0, nextfloat(1.0), 4096), (1.0e15, 1.0e15 + 1, 10_000))
    try
        r = range(a, b; length=n)
        println("range($a, $b; length=$n) = ", r)
    catch e
        println("range($a, $b; length=$n) throws ", sprint(showerror, e))
        global bug = e isa InexactError && a == 1.0e15
    end
end
bug && println("REPRODUCED floatranges-linspace-imin-overflow")
