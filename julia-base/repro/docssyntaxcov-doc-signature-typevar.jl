# Docs.signature adds `Tuple{T}` to the signature of a method with a `where T`
# clause, so the docstring of g(x::Vector{T}) where T also matches the call
# signature Tuple{Int} and is returned for g(::Int).
"g vec" g(x::Vector{T}) where T = 1
"g int" g(x::Int) = 2
sig = Base.Docs.signature(:(g(x::Vector{T}) where T))
println("signature = ", sig)
d = Base.Docs._doc(Base.Docs.Binding(@__MODULE__, :g), Tuple{Int})
println("_doc(g, Tuple{Int}) text = ", repr(d.text))
if d.text == Core.svec("g vec")
    println("REPRODUCED docssyntaxcov-doc-signature-typevar")
end
