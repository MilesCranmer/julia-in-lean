# Docs.Text and Docs.HTML define `==` and `hash` from their content, so isequal (which
# falls back to `==`) can hold while the hashes differ: Text(-0.0) and Text(0.0).
using Base.Docs: Text, HTML
a, b = Text(-0.0), Text(0.0)
println("isequal(Text(-0.0), Text(0.0)) = ", isequal(a, b))
println("hash equal = ", hash(a) == hash(b))
println("length(Set([Text(-0.0), Text(0.0)])) = ", length(Set([a, b])))
println("isequal(HTML(-0.0), HTML(0.0)) = ", isequal(HTML(-0.0), HTML(0.0)),
        ", hash equal = ", hash(HTML(-0.0)) == hash(HTML(0.0)))
if isequal(a, b) && hash(a) != hash(b)
    println("REPRODUCED docssyntaxcov-text-hash-isequal")
end
