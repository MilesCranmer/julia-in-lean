# utf8proc_map sizes its buffer with a first utf8proc_decompose call and then calls it
# again; a chartransform that answers differently the second time overflows the buffer.
code = """
n = Ref(0)
f = ch -> (n[] += 1; n[] <= 2 ? ch : Char(0xfdfa))   # U+FDFA has an 18-code-point compatibility decomposition
r = Base.Unicode.normalize("ab"; compat=true, chartransform=f)
println("returned ", repr(r))
"""
out = IOBuffer()
p = run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no -e $code`), stdout=out, stderr=out))
s = String(take!(out))
println(first(s, 400))
println("child exit code ", p.exitcode, ", signal ", p.termsignal)
(occursin("ConcurrencyViolationError", s) || p.termsignal != 0) &&
    println("REPRODUCED stringscovb-normalize-impure-chartransform")
