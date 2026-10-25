using Markdown
s = "12345678901234567890. item"
try
    println(repr(Markdown.parse(s).content))
catch e
    println("Markdown.parse(", repr(s), ") throws ", sprint(showerror, e))
    e isa OverflowError && println("REPRODUCED markdown-list-number-overflow")
end
