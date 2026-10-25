using Logging

buffer = IOBuffer()
stream = IOContext(buffer, :color => false)
logger = SimpleLogger(stream)
with_logger(logger) do
    @warn "message" value="one\ntwo" _module=Main _file="fake.jl" _line=7
end
output = String(take!(buffer))
println("output = ", repr(output))
reproduced = occursin("│   value = one\ntwo\n└ @ Main fake.jl:7", output) &&
    !occursin("\n│ two\n", output)
println(reproduced ? "REPRODUCED logging-simplelogger-multiline-value" :
    "NOT REPRODUCED logging-simplelogger-multiline-value")
