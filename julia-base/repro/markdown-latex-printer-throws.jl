using Markdown
x = 42
md = md"The answer is $x."
println(repr(md.content))
ok = try
    print(Markdown.latex(md)); true
catch e
    println("latex throws ", sprint(showerror, e)[1:80]); false
end
try
    print(Markdown.latex(Markdown.parse("a <span>b</span>")))
catch e
    println("latex of raw HTML throws ", sprint(showerror, e)[1:80])
end
ok || println("REPRODUCED markdown-latex-printer-throws")
