using Markdown
md = Markdown.parse("0. zero\n1. one")
println("ordered = ", md.content[1].ordered)
h = Markdown.html(md)
print(h)
startswith(h, "<ol>") && println("REPRODUCED markdown-html-ordered-start-zero")
