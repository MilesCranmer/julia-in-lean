# Docs.metadata collects field docstrings only before `Symbol` or `x::T` field
# declarations, so the docstring of a `const` field is kept and attached to the
# next ordinary field instead.
"S doc"
mutable struct S
    "doc for a"
    const a::Int
    b::Int
end
fields = Base.Docs.meta(@__MODULE__)[Base.Docs.Binding(@__MODULE__, :S)].docs[Union{}].data[:fields]
println("fields = ", repr(fields))
if get(fields, :b, nothing) == "doc for a" && !haskey(fields, :a)
    println("REPRODUCED docssyntaxcov-field-doc-const")
end
