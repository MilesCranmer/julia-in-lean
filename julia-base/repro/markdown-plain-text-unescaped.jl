using Markdown
md = Markdown.parse("\\*not emphasis\\*")
p = Markdown.plain(md)
md2 = Markdown.parse(p)
println("plain   = ", repr(p))
println("html    = ", repr(Markdown.html(md)))
println("reparse = ", repr(Markdown.html(md2)))
md2 != md && println("REPRODUCED markdown-plain-text-unescaped")
