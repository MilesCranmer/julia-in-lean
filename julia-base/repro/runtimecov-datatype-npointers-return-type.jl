docstr(name) = join(first(values(Base.Docs.meta(Base)[Base.Docs.Binding(Base, name)].docs)).text)
doc = docstr(:datatype_npointers)
foreach(println, split(strip(doc), "\n\n")[1:2])
n = Base.datatype_npointers(Pair{String,String})
println("datatype_npointers(Pair{String,String}) = ", repr(n), " :: ", typeof(n))
if occursin("::Int", doc) && !(n isa Int)
    println("REPRODUCED runtimecov-datatype-npointers-return-type")
end
