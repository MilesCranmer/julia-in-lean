show_result(f) = try repr(f()) catch e sprint(showerror, e)[1:findfirst('\n', sprint(showerror, e) * "\n")-1] end
println("split(\"a,b,c\", ','; limit=2)         = ", show_result(() -> split("a,b,c", ','; limit=2)))
println("split(\"a,b,c\", ','; limit=UInt(2))   = ", show_result(() -> split("a,b,c", ','; limit=UInt(2))))
println("rsplit(\"a,b,c\", ','; limit=Int32(2)) = ", show_result(() -> rsplit("a,b,c", ','; limit=Int32(2))))
println("eachsplit(\"a,b,c\", ','; limit=0x02)  = ", show_result(() -> collect(eachsplit("a,b,c", ','; limit=0x02))))
r = try split("a,b,c", ','; limit=UInt(2)) catch e e end
r isa MethodError && println("REPRODUCED stringutil-split-limit-type")
