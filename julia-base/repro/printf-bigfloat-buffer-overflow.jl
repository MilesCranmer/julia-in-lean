using Printf
# The output of a large BigFloat after literal text: mpfr_snprintf writes past the
# end of the resized buffer. Run in a child process because the heap can be corrupted.
code = """
using Printf
s = @sprintf("%s%f", "a"^100, big"1e400")
expected = "a"^100 * @sprintf("%f", big"1e400")
println("length = ", ncodeunits(s), ", expected length = ", ncodeunits(expected), ", equal = ", s == expected)
println("first differing byte = ", findfirst(i -> codeunit(s, i) != codeunit(expected, i), 1:min(ncodeunits(s), ncodeunits(expected))))
"""
out = IOBuffer()
p = run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no -e $code`), stdout=out, stderr=devnull))
text = String(take!(out))
print(text)
println("exit code = ", p.exitcode, ", signal = ", p.termsignal)
(occursin("equal = false", text) || p.termsignal != 0) && println("REPRODUCED printf-bigfloat-buffer-overflow")
