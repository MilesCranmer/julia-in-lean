using Logging

level = Logging.LogLevel(typemax(Int32))
println("level = ", level)
result = try
    Logging.disable_logging(level)
    "returned normally"
catch err
    sprint(showerror, err)
end
println("disable_logging = ", result)
reproduced = startswith(result, "InexactError:")
println(reproduced ? "REPRODUCED logging-disable-typemax" :
    "NOT REPRODUCED logging-disable-typemax")
