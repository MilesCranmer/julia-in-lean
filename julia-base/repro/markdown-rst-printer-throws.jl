using Markdown
md = Markdown.parse("![alt text](image.png)")
ok = try
    print(Markdown.rst(md)); true
catch e
    println("rst throws ", sprint(showerror, e)[1:80]); false
end
for s in ["~~struck~~", "a <span>b</span>"]
    try
        print(Markdown.rst(Markdown.parse(s)))
    catch e
        println("rst of ", repr(s), " throws ", sprint(showerror, e)[1:80])
    end
end
ok || println("REPRODUCED markdown-rst-printer-throws")
