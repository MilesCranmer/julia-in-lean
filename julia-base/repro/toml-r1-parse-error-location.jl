using TOML

const input = "@\n"
const observed = try
    TOML.parse(input)
    nothing
catch error
    error
end
const reproduced = try
    observed isa TOML.ParserError && observed.str == input &&
        observed.line == 2 && observed.column == -1
catch
    false
end
println(reproduced ? "REPRODUCED toml-r1-parse-error-location" :
                     "NOT_REPRODUCED toml-r1-parse-error-location")
