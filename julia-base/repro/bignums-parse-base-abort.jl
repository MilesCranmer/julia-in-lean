# tryparse(BigFloat, s; base) with a base outside 2..62 must return nothing (and parse must
# throw). Instead MPFR's mpfr_set_str fails an assertion and aborts the whole process.
# Run the call in a child process so the abort can be observed.
code = "println(repr(tryparse(BigFloat, \"1\"; base=1)))"
cmd = `$(Base.julia_cmd()) --startup-file=no -e $code`
err = IOBuffer()
p = run(pipeline(ignorestatus(cmd); stdout=devnull, stderr=err))
msg = String(take!(err))
line = something(findfirst(l -> occursin("assertion", l), split(msg, '\n')), 0)
println("child exit code ", p.exitcode, ", signal ", p.termsignal)
line > 0 && println(split(msg, '\n')[line])
println("tryparse(Float64, \"1\") with no base: ", tryparse(Float64, "1"))
println("tryparse(Int, \"1\"; base=1) throws ", try tryparse(Int, "1"; base=1); "nothing" catch e; typeof(e) end)
if p.termsignal == 6 && occursin("MPFR assertion failed", msg)
    println("REPRODUCED bignums-parse-base-abort")
end
