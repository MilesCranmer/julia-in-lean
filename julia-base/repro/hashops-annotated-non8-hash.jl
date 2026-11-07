using Base: AnnotatedString

struct UTF32TestString <: AbstractString
    chars::Vector{Char}
end

Base.ncodeunits(s::UTF32TestString) = length(s.chars)
Base.codeunit(::UTF32TestString) = UInt32
Base.codeunit(s::UTF32TestString, i::Integer) = UInt32(s.chars[i])
Base.isvalid(s::UTF32TestString, i::Integer) = 1 <= i <= length(s.chars)
Base.getindex(s::UTF32TestString, i::Integer) = s.chars[i]
Base.iterate(s::UTF32TestString, i::Integer=1) =
    i > length(s.chars) ? nothing : (s.chars[i], i + 1)

s = UTF32TestString(['a'])
a = AnnotatedString(s)
println("isequal(a, s) = ", isequal(a, s))
@assert isequal(a, s)
println("hash(s, 0) = ", hash(s, UInt(0)))
@assert hash(s, UInt(0)) isa UInt
try
    hash(a, UInt(0))
    error("wrapper hash unexpectedly succeeded")
catch err
    err isa ArgumentError || rethrow()
    println("hash(a, 0) error = ", sprint(showerror, err))
    println("REPRODUCED hashops-annotated-non8-hash")
end
