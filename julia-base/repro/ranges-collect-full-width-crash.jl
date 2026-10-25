r = typemin(Int):typemax(Int)
println("length(r) = ", length(r), ", isempty(r) = ", isempty(r))
cmd = `$(Base.julia_cmd()) --startup-file=no -e 'collect(typemin(Int):typemax(Int)); println("collect returned")'`
p = run(pipeline(ignorestatus(cmd); stdout=devnull, stderr=devnull))
println("child exit code = ", p.exitcode, ", signal = ", p.termsignal)
length(r) == 0 && !isempty(r) && (p.termsignal != 0 || p.exitcode != 0) &&
    println("REPRODUCED ranges-collect-full-width-crash")
