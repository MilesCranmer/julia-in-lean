# _truncate_at_width_or_chars is meant to append "\e[0m" only when the last
# ANSI sequence before the cut is not already "\e[0m" (base/show.jl:110,114),
# but it compares an ANSIDelimiter with a String, which is never equal.
plain = "ab\e[0mcdefgh"           # the only escape sequence is a reset
r = Base._truncate_at_width_or_chars(true, plain, 4)
println(repr(r))

# The same through limited Dict display with color on:
io = IOBuffer()
show(IOContext(io, :limit => true, :color => true, :displaysize => (24, 14)), MIME"text/plain"(),
     Dict(1 => Text("ab\e[0mcdefghij")))
out = String(take!(io))
println(repr(out))

if r == "ab\e[0mc\e[0m…"
    println("REPRODUCED showcov-truncate-ansi-reset")
end
