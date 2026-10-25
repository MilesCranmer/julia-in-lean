s = "abc"
a = findnext("", s, 4)
b = findprev("", s, 4)
println("findnext(\"\", \"abc\", 4) = ", repr(a))
println("findprev(\"\", \"abc\", 4) = ", repr(b))
println("findall(\"\", \"abc\") = ", repr(findall("", s)))
a == 4:3 && b == 0:-1 && println("REPRODUCED strings-findprev-empty-end")
