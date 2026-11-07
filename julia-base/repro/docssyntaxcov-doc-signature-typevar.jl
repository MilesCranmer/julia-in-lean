module PublicDocProbe
    "g vec" g(x::Vector{T}) where T = 1
    "g int" g(x::Int) = 2
end
d = (@doc PublicDocProbe.g(::Int))
println("@doc g(::Int) = ", repr(d.text))
if d.text == Core.svec("g vec")
    println("REPRODUCED docssyntaxcov-doc-signature-typevar")
end
