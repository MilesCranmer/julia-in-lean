id = "bitarray-findnext-fixed-machine"
ok = try
    a = falses(1)
    alias = vec(reshape(a, 1, 1))
    resize!(alias, 2)
    alias[2] = true
    length(a) == 1 && a[1] == false && findnext(isequal(true), a, 1) == 2
catch
    false
end
let confirmed = ok
    println(confirmed ? "REPRODUCED $id" : "NOT_REPRODUCED $id")
    confirmed
end
