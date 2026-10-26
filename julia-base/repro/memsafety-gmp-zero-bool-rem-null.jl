code = "rem(Base.GMP.ZERO, Bool)"
cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $code`
proc = run(pipeline(ignorestatus(cmd), stdout=devnull, stderr=devnull))

println("call: ", code)
println("child exit code: ", proc.exitcode)
println("child termination signal: ", proc.termsignal)
if proc.termsignal != 0
    println("REPRODUCED memsafety-gmp-zero-bool-rem-null")
end
