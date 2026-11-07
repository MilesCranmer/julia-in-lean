using TOML

const input = "@\n"
const reproduced = try
    result = TOML.tryparse(input)
    result isa TOML.ParserError && result.str == input &&
        result.line == 2 && result.column == -1
catch
    false
end
println(reproduced ? "REPRODUCED toml-r1-tryparse-error-location" :
                     "NOT_REPRODUCED toml-r1-tryparse-error-location")
