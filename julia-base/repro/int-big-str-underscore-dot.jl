# @big_str is meant to reject `_` right before or after a `.` ("Do not allow '_' right before or
# after dot", base/int.jl), but the check skips the last character, so big"1_." parses as 1.0.
bigstr(s) = try
    eval(Meta.parse("big\"" * s * "\""))
catch e
    e isa LoadError ? e.error : e
end
a = bigstr("1_.")
b = bigstr("1_.0")
c = bigstr("1._5")
println("big\"1_.\"  => ", repr(a))
println("big\"1_.0\" => ", repr(b))
println("big\"1._5\" => ", repr(c))
if a isa BigFloat && b isa ArgumentError && c isa ArgumentError
    println("REPRODUCED int-big-str-underscore-dot")
else
    println("NOT REPRODUCED int-big-str-underscore-dot")
end
