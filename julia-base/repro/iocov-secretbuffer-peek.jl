s = Base.SecretBuffer("héllo")
println("peek(s, UInt8) = ", peek(s, UInt8))
try
    println("peek(s, Char) = ", repr(peek(s, Char)))
catch e
    println("peek(s, Char) threw ", typeof(e), ": ", first(sprint(showerror, e), 80))
    e isa FieldError && println("REPRODUCED iocov-secretbuffer-peek")
end
Base.shred!(s)
