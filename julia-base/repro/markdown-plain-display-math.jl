using Markdown
md = Markdown.parse("```math\nx^2\n```")
p = Markdown.plain(md)
md2 = Markdown.parse(p)
println("content = ", repr(md.content))
println("plain   = ", repr(p))
println("reparse = ", repr(md2.content))
md2 != md && println("REPRODUCED markdown-plain-display-math")
