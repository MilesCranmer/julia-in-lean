using Base.MultiplicativeInverses: multiplicativeinverse
q = div(typemin(Int8), multiplicativeinverse(Int8(-1)))
base_result = try
    div(typemin(Int8), Int8(-1))
catch e
    typeof(e)
end
println("inverse division = ", q, "; ordinary division = ", base_result)
@assert q == typemin(Int8) && base_result == DivideError
println("REPRODUCED multinverses-zero-argumenterror")
