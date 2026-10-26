# Limited Dict/Set display truncates each entry to the terminal width with
# Base._truncate_at_width_or_chars, but an entry whose last character is wide
# is returned untruncated and overflows the line (base/show.jl:104-135).
function lines(x, rows, cols)
    io = IOBuffer()
    show(IOContext(io, :limit => true, :displaysize => (rows, cols)), MIME"text/plain"(), x)
    split(String(take!(io)), '\n')
end

d = lines(Dict(:k => Symbol("ab中")), 24, 12)
s = lines(Set([Symbol("abcd中")]), 24, 8)
println("Dict lines: ", d, " widths ", textwidth.(d), " (display width 12)")
println("Set lines:  ", s, " widths ", textwidth.(s), " (display width 8)")

t = Base._truncate_at_width_or_chars(false, "ab中", 3)
println("_truncate_at_width_or_chars(false, \"ab中\", 3) = ", repr(t), ", textwidth ", textwidth(t))
p = Base._truncate_at_width_or_chars(false, "abc\n", 10, true)
println("_truncate_at_width_or_chars(false, \"abc\\n\", 10, true) = ", repr(p), ", textwidth ", textwidth(p))

if textwidth(d[2]) > 12 && textwidth(s[2]) > 8 && textwidth(t) > 3 && textwidth(p) > 10
    println("REPRODUCED showcov-truncate-width-overflow")
end
