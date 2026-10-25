# partition of a range: state + n - 1 wraps for indices near typemax(Int)
r = Base.IdentityUnitRange(typemax(Int)-2:typemax(Int))
p = Iterators.partition(r, 2)
chunks = Any[]
for c in p
    push!(chunks, c)
    length(chunks) == 4 && break
end
println("length(partition(r, 2)) = ", length(p))
println("first 4 chunks = ", chunks)
println("expected chunks = ", [typemax(Int)-2:typemax(Int)-1, typemax(Int):typemax(Int)])
cmd = `$(Base.julia_cmd()) --startup-file=no -e 'collect(Iterators.partition(Base.IdentityUnitRange(typemax(Int)-2:typemax(Int)), 2)); println("collect returned")'`
proc = run(pipeline(ignorestatus(cmd); stdout=devnull, stderr=devnull))
println("collect(partition(r, 2)) in a child process: exit code = ", proc.exitcode, ", signal = ", proc.termsignal)
if length(chunks) == 4 && isempty(chunks[2]) && (proc.termsignal != 0 || proc.exitcode != 0)
    println("REPRODUCED iterators-partition-range-overflow")
end
