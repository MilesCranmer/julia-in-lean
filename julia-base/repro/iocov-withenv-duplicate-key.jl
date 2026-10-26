haskey(ENV, "IOCOV_DUP") && delete!(ENV, "IOCOV_DUP")
withenv("IOCOV_DUP" => "1", "IOCOV_DUP" => "2") do
    println("inside: ", ENV["IOCOV_DUP"])
end
after = get(ENV, "IOCOV_DUP", nothing)
println("after withenv: ", repr(after))
if after !== nothing
    println("REPRODUCED iocov-withenv-duplicate-key")
end
