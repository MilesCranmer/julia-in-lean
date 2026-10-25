using Markdown
md = Markdown.parse("!!! warning \"x < y & <script>alert(1)</script>\"\n    Body.")
h = Markdown.html(md)
print(h)
occursin("<script>alert(1)</script>", h) && println("REPRODUCED markdown-html-admonition-title")
