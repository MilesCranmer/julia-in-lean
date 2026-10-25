using Markdown
# A one-character header line "#" ended by a lone carriage return at the end of input.
for s in ["#\r\n", "#\n", "#\r"]
    try
        println(repr(s), " -> ", repr(Markdown.parse(s).content))
    catch e
        println(repr(s), " -> throws ", typeof(e))
        s == "#\r" && e isa EOFError && println("REPRODUCED markdown-hashheader-cr-eof")
    end
end
