using Markdown
md = Markdown.parse("- a\n- b\n\nText")
list = md.content[1]
println("loose = ", list.loose)
print(Markdown.html(md))
tight = Markdown.parse("- a\n- b\n")
println("without the trailing blank line: loose = ", tight.content[1].loose)
list.loose && !tight.content[1].loose && println("REPRODUCED markdown-list-trailing-blank-loose")
