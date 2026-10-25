M = falses(2, 2)
push!(vec(M), true)
c1 = (M == falses(2, 2), count(M), any(M), collect(M) == falses(2, 2))
N = falses(65, 1)
pop!(vec(N))
c2 = (length(N), length(N.chunks), Base.num_bit_chunks(length(N)))
A = zeros(Bool, 2, 2); push!(vec(A), true)
println(c1, " ", c2, " ", A == zeros(Bool, 2, 2))
# N[65] reads chunk 2 with @inbounds; with forced bounds checks the read throws.
code = "N = falses(65, 1); pop!(vec(N)); try; N[65]; println(\"no error\"); catch e; println(sprint(showerror, e)); end"
out = readchomp(`$(Base.julia_cmd()) --startup-file=no --check-bounds=yes -e $code`)
println(out)
if c1 == (false, 1, true, true) && c2[2] < c2[3] && occursin("BoundsError", out)
    println("REPRODUCED bitarrays-vec-resize-alias")
end
