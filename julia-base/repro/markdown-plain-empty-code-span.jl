using Markdown
md = Markdown.parse("a ` ` b")
p = Markdown.plain(md)
md2 = Markdown.parse(p)
println("content = ", repr(md.content))
println("plain   = ", repr(p))
println("html    = ", repr(Markdown.html(md)), " vs ", repr(Markdown.html(md2)))
md2 != md && println("REPRODUCED markdown-plain-empty-code-span")
