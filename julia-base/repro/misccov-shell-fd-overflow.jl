# A redirect fd number that is not 0, 1 or 2 is rejected with a parse ErrorException
# ("unsupported fd"), except when it does not fit in an Int, where `parse(Int, ...)` at
# base/shell.jl:178 throws OverflowError instead.
r1 = try Base.shell_parse("echo 3>x")[1] catch e; e end
r2 = try Base.shell_parse("echo 99999999999999999999>x")[1] catch e; e end
println("shell_parse(\"echo 3>x\")                    => ", r1 isa Exception ? "$(typeof(r1)): " * sprint(showerror, r1) : repr(r1))
println("shell_parse(\"echo 99999999999999999999>x\") => ", r2 isa Exception ? "$(typeof(r2)): " * sprint(showerror, r2) : repr(r2))
if r1 isa ErrorException && r2 isa OverflowError
    println("REPRODUCED misccov-shell-fd-overflow")
end
