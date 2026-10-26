function checked_output(expr)
    code = """
    s = Base.Slices(Int[11, 22], (1,), (Base.OneTo(3),))
    $expr
    """
    cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $code`
    io = IOBuffer()
    proc = run(pipeline(ignorestatus(cmd); stdout=io, stderr=io))
    return String(take!(io)), proc
end

get_output, get_proc = checked_output("s[3]")
set_output, set_proc = checked_output("s[3] = 99")
println("getindex child:")
print(get_output)
println("child exit code = ", get_proc.exitcode, ", signal = ", get_proc.termsignal)
println("setindex! child:")
print(set_output)
println("child exit code = ", set_proc.exitcode, ", signal = ", set_proc.termsignal)
if occursin("BoundsError", get_output) && occursin("slicearray.jl:242", get_output) &&
        occursin("BoundsError", set_output) && occursin("slicearray.jl:246", set_output)
    println("REPRODUCED memsafety-slices-constructor-axes")
end
