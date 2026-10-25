using Markdown
for l in 1:6
    print(Markdown.latex(Markdown.parse("#"^l * " Title")))
end
occursin("\\subsubparagraph", Markdown.latex(Markdown.parse("###### Title"))) && println("REPRODUCED markdown-latex-h6-invalid")
