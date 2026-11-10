# tuple_tfunc turns a `Type{T}` argument into a valid tuple parameter (DataType, Type, ...), but
# leaves a `Vararg{Type{T}}` tail as it is. No tuple value has type `Tuple{Vararg{Type{Int}}}`:
# `(Int, Int)` is a `Tuple{DataType, DataType}`. Inference then folds an `isa` the wrong way.
id = "compiler-tfuncs-tuple-vararg-type"
h(v::Vector{Type{Int}}) = tuple(v...)
k(v::Vector{Type{Int}}) = tuple(v...) isa Tuple{Vararg{Type{Int}}}
v = Type{Int}[Int, Int]
rt = only(Base.return_types(h, (Vector{Type{Int}},)))
r = h(v)
println("return_types(h, (Vector{Type{Int}},)) = ", rt)
println("h(v) = ", r, " :: ", typeof(r), "; h(v) isa ", rt, " = ", r isa rt)
println("k(v) = ", k(v), "; tuple(v...) isa Tuple{Vararg{Type{Int}}} at run time = ",
        Base.inferencebarrier(r) isa Tuple{Vararg{Type{Int}}})
println(!(r isa rt) && k(v) === true ? "REPRODUCED $id" : "NOT REPRODUCED $id")
