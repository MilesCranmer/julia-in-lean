input = "a,b,c"
int_result = split(input, ','; limit=Int(2))
@assert int_result == ["a", "b,c"]

int8_result = try
    split(input, ','; limit=Int8(2))
    nothing
catch err
    err
end
@assert int8_result isa MethodError
println("REPRODUCED stringutil-split-limit-type")
