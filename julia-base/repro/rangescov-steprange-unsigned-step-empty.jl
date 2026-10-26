println("StepRange(-5, 1, -10) = ", repr(StepRange(-5, 1, -10)), " (empty)")
bug = false
try
    r = StepRange(-5, UInt(1), -10)
    println("StepRange(-5, UInt(1), -10) = ", repr(r), ", isempty = ", isempty(r))
catch e
    println("StepRange(-5, UInt(1), -10) throws ", sprint(showerror, e))
    global bug = e isa InexactError
end
bug && println("REPRODUCED rangescov-steprange-unsigned-step-empty")
