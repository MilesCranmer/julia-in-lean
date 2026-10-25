using Markdown
md = Markdown.parse("!!! note \"50% of x_1\"\n    Body.")
t = Markdown.latex(md)
print(t)
occursin("50% of x_1", t) && println("REPRODUCED markdown-latex-admonition-title")
