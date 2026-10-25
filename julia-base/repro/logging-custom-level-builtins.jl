using Logging

struct CustomLevel end
Base.convert(::Type{Logging.LogLevel}, ::CustomLevel) = Logging.Info

buffer = IOBuffer()
stream = IOContext(buffer, :displaysize => (30, 80), :color => false)
logger = ConsoleLogger(stream)
with_logger(logger) do
    @logmsg CustomLevel() "custom message"
end
output = String(take!(buffer))
println("contains custom message = ", occursin("Info: custom message", output))
println("contains logging error = ", occursin("Exception while generating log record", output))
reproduced = !occursin("Info: custom message", output) &&
    occursin("MethodError: no method matching handle_message(::ConsoleLogger, ::CustomLevel", output)
println(reproduced ? "REPRODUCED logging-custom-level-builtins" :
    "NOT REPRODUCED logging-custom-level-builtins")
