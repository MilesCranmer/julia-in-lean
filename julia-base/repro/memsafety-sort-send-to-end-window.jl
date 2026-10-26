code = "Base.Sort.send_to_end!(iszero, [1, 2]; lo=0, hi=2)"
cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $code`
io = IOBuffer()
proc = run(pipeline(ignorestatus(cmd); stdout=io, stderr=io))
out = String(take!(io))
print(out)
println("child exit code = ", proc.exitcode, ", signal = ", proc.termsignal)
if occursin("BoundsError", out) && occursin("index [0]", out) && occursin("send_to_end!", out)
    println("REPRODUCED memsafety-sort-send-to-end-window")
end
