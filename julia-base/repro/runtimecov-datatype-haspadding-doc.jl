struct WithPadding
    a::Int8
    b::Int64
end
struct Packed
    a::Int64
    b::Int64
end
docstr(name) = join(first(values(Base.Docs.meta(Base)[Base.Docs.Binding(Base, name)].docs)).text)
doc = docstr(:datatype_haspadding)
foreach(println, split(strip(doc), "\n\n")[1:2])
p = Base.datatype_haspadding(WithPadding)
q = Base.datatype_haspadding(Packed)
println("sizeof(WithPadding) = ", sizeof(WithPadding), ", datatype_haspadding(WithPadding) = ", p)
println("sizeof(Packed) = ", sizeof(Packed), ", datatype_haspadding(Packed) = ", q)
# The docstring says the result is whether the fields are packed with no padding.
if occursin("no intervening padding", doc) && p && !q
    println("REPRODUCED runtimecov-datatype-haspadding-doc")
end
