# A field docstring before a const field is attached to the next ordinary field.
"S doc"
mutable struct S
    "doc for a"
    const a::Int
    b::Int
end
d = (@doc S)
fields = d.data[:fields]
println("@doc S field docs = ", repr(fields))
if fields == Dict(:b => "doc for a")
    println("REPRODUCED docssyntaxcov-field-doc-const")
end
