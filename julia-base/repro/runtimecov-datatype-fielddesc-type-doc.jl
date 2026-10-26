struct TwoInts
    a::Int64
    b::Int64
end
docstr(name) = join(first(values(Base.Docs.meta(Base)[Base.Docs.Binding(Base, name)].docs)).text)
doc = docstr(:datatype_fielddesc_type)
foreach(println, split(strip(doc), "\n\n")[1:2])
code = Base.datatype_fielddesc_type(TwoInts)
# Each entry of the layout array is a pair (ptrsize, offset) of UInt8, UInt16 or
# UInt32 for codes 0, 1, 2: 2, 4 or 8 bytes.
entry_bytes = Dict(0 => 2, 1 => 4, 2 => 8)
println("datatype_fielddesc_type(TwoInts) = ", code)
println("bytes per field-description entry = ", get(entry_bytes, code, "foreign"))
if occursin("size in bytes", doc) && code == 0
    println("REPRODUCED runtimecov-datatype-fielddesc-type-doc")
end
