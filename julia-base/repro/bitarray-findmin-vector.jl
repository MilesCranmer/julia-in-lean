id = "bitarray-findmin-vector"
ok = try
    a = trues(1)
    alias = vec(reshape(a, 1, 1))
    resize!(alias, 65)
    fill!(alias, false)
    alias[1] = true
    length(a) == 1 && a[1] == true && findmin(a) == (false, 2)
catch
    false
end
let confirmed = ok
    println(confirmed ? "REPRODUCED $id" : "NOT_REPRODUCED $id")
    confirmed
end
