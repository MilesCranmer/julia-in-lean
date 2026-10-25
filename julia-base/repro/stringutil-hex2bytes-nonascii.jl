show_result(x) = try repr(hex2bytes(x)) catch e sprint(showerror, e) end
println("hex2bytes(\"ĀĀ\")                = ", show_result("ĀĀ"))
println("hex2bytes(SubString(\"ĀĀ\"))     = ", show_result(SubString("ĀĀ")))
println("hex2bytes(\"\\xff\\xff\")            = ", show_result("\xff\xff"))
println("hex2bytes(SubString(\"\\xff\\xff\")) = ", show_result(SubString("\xff\xff")))
println("hex2bytes(SubString(\"éé\"))     = ", show_result(SubString("éé")))
a = try hex2bytes(SubString("ĀĀ")) catch e e end
b = try hex2bytes(SubString("\xff\xff")) catch e e end
a isa InexactError && b isa Base.InvalidCharError && println("REPRODUCED stringutil-hex2bytes-nonascii")
