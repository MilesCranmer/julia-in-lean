docstr(name) = join(first(values(Base.Docs.meta(Base)[Base.Docs.Binding(Base, name)].docs)).text)
doc = docstr(:iskindtype)
foreach(println, split(strip(doc), "\n\n")[1:2])
if !isdefined(Core, :AnyType)
    println("Core.AnyType does not exist in ", VERSION)
else
    k = Core.AnyType
    println("iskindtype(Core.AnyType) = ", Base.iskindtype(k))
    println("isconcretetype(Core.AnyType) = ", isconcretetype(k))
    println("isabstracttype(Core.AnyType) = ", isabstracttype(k))
    if Base.iskindtype(k) && !isconcretetype(k) && occursin("All kinds are [concrete]", doc)
        println("REPRODUCED runtimecov-iskindtype-abstract-kind")
    end
end
