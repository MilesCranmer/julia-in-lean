using Logging

function render(splatted)
    buffer = IOBuffer()
    stream = IOContext(buffer, :displaysize => (30, 80), :color => false)
    logger = ConsoleLogger(stream)
    with_logger(logger) do
        if splatted
            @warn "message" (; _module=Main, _file="fake.jl", _line=7)...
        else
            @warn "message" _module=Main _file="fake.jl" _line=7
        end
    end
    return String(take!(buffer))
end

direct = render(false)
splatted = render(true)
direct_uses_fake_location = occursin("└ @ Main fake.jl:7", direct)
splatted_uses_fake_location = occursin("└ @ Main fake.jl:7", splatted)
splatted_prints_file_metadata = occursin("│   _file = \"fake.jl\"", splatted)
println("direct uses fake location = ", direct_uses_fake_location)
println("splatted uses fake location = ", splatted_uses_fake_location)
println("splatted prints _file as ordinary metadata = ", splatted_prints_file_metadata)
reproduced = direct_uses_fake_location && !splatted_uses_fake_location &&
    splatted_prints_file_metadata
println(reproduced ? "REPRODUCED logging-splat-special-keys" :
    "NOT REPRODUCED logging-splat-special-keys")
