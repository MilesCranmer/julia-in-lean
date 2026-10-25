using Markdown
md = Markdown.parse("- a\n\n- b")
p = Markdown.plain(md)
md2 = Markdown.parse(p)
println("loose = ", md.content[1].loose, ", plain = ", repr(p), ", reparsed loose = ", md2.content[1].loose)
println(repr(Markdown.html(md)))
println(repr(Markdown.html(md2)))
md2 != md && println("REPRODUCED markdown-plain-loose-list")
