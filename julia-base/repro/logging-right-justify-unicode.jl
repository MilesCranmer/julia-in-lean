using Logging

function render(message)
    buffer = IOBuffer()
    stream = IOContext(buffer, :displaysize => (30, 20), :color => false)
    logger = ConsoleLogger(stream, Logging.Debug;
        meta_formatter=(args...) -> (:normal, "PREFIX", "SUFFIX"),
        right_justify=20)
    with_logger(logger) do
        @warn message
    end
    return String(take!(buffer))
end

ascii = render("xxx")
wide = render("界")
combining = render("e\u0301")
println("ASCII textwidth = ", textwidth(chomp(ascii)), ": ", repr(ascii))
println("wide textwidth = ", textwidth(chomp(wide)), ": ", repr(wide))
println("combining textwidth = ", textwidth(chomp(combining)), ": ", repr(combining))
reproduced = textwidth(chomp(ascii)) == 20 && textwidth(chomp(wide)) == 21 &&
    textwidth(chomp(combining)) == 19
println(reproduced ? "REPRODUCED logging-right-justify-unicode" :
    "NOT REPRODUCED logging-right-justify-unicode")
