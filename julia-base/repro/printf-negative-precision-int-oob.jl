using Printf
# A negative dynamic precision shrinks the buffer estimate below the number of digits;
# the digit stores are @inbounds, so they write past the end of the buffer.
code = """
using Printf
print(repr(@sprintf("%.*d", -24, typemax(Int64))))
"""
for flag in ("--check-bounds=yes", "--check-bounds=auto")
    out = IOBuffer()
    run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no $flag -e $code`), stdout=out, stderr=out))
    text = String(take!(out))
    println(flag, ": ", first(split(text, '\n')))
end
s = @sprintf("%.*d", -6, 42)
println("%.*d with precision -6 and 42: ", repr(s), "; C99 expected \"42\"")
s != "42" && println("REPRODUCED printf-negative-precision-int-oob")
