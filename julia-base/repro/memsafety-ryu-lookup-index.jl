function checked_output(call)
    cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $call`
    io = IOBuffer()
    proc = run(pipeline(ignorestatus(cmd); stdout=io, stderr=io))
    return String(take!(io)), proc
end

inv_output, inv_proc = checked_output("Base.Ryu.pow5invsplit_lookup(Float64, -1)")
split_output, split_proc = checked_output("Base.Ryu.pow5split_lookup(Float64, -1)")
println("pow5invsplit_lookup child:")
print(inv_output)
println("child exit code = ", inv_proc.exitcode, ", signal = ", inv_proc.termsignal)
println("pow5split_lookup child:")
print(split_output)
println("child exit code = ", split_proc.exitcode, ", signal = ", split_proc.termsignal)
if occursin("BoundsError", inv_output) && occursin("index [0]", inv_output) &&
        occursin("pow5invsplit_lookup", inv_output) && occursin("BoundsError", split_output) &&
        occursin("index [0]", split_output) && occursin("pow5split_lookup", split_output)
    println("REPRODUCED memsafety-ryu-lookup-index")
end
