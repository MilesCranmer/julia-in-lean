s = "\x82\xe2"
a = collect(reverse(s))
b = reverse(collect(s))
println("collect(reverse(s)) = ", repr(a))
println("reverse(collect(s)) = ", repr(b))
a != b && println("REPRODUCED strings-reverse-malformed")
