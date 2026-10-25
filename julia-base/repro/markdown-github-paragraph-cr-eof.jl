using Markdown
# A paragraph whose last line ends in a lone carriage return, github flavor.
for s in ["a\r\n", "a\n", "a\r"]
    try
        println(repr(s), " -> ", repr(Markdown.parse(s, flavor = :github).content))
    catch e
        println(repr(s), " -> throws ", typeof(e))
        s == "a\r" && e isa EOFError && println("REPRODUCED markdown-github-paragraph-cr-eof")
    end
end
