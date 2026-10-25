using Logging

buffer = IOBuffer()
stream = IOContext(buffer, :displaysize => (30, 80), :color => false)
logger = ConsoleLogger(stream)
with_logger(logger) do
    for _ in 1:3
        @warn "limited" _id=:bigint_limit _module=Main _file="fake.jl" _line=7 maxlog=big(1)
    end
end
output = String(take!(buffer))
emissions = length(findall("Warning: limited", output))
println("emissions with maxlog=big(1) = ", emissions)
println("output = ", repr(output))
reproduced = emissions == 3
println(reproduced ? "REPRODUCED logging-maxlog-bigint" :
    "NOT REPRODUCED logging-maxlog-bigint")
