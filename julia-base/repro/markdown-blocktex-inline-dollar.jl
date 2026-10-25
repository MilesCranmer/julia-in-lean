using Markdown
md = Markdown.parse("\$x\$ is positive")
println(repr(md.content))
print(Markdown.html(md))
println(repr(Markdown.parse("Here \$x\$ is positive").content))
length(md.content) == 2 && md.content[2] isa Markdown.Paragraph && println("REPRODUCED markdown-blocktex-inline-dollar")
