using Markdown
# Fullwidth digit one (U+FF11) and Persian digit one (U+06F1) used as list numbers.
for s in ["１. item", "۱. item"]
    try
        println(repr(s), " -> ", repr(Markdown.parse(s).content))
    catch e
        println(repr(s), " -> throws ", sprint(showerror, e))
        s == "۱. item" && e isa ArgumentError && println("REPRODUCED markdown-list-unicode-digit")
    end
end
