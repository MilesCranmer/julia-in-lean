using Base: AnnotatedString

struct UTF32String <: AbstractString
    chars::Vector{Char}
end

Base.ncodeunits(s::UTF32String) = length(s.chars)
Base.codeunit(::UTF32String) = UInt32
Base.codeunit(s::UTF32String, i::Integer) = reinterpret(UInt32, s.chars[i])
Base.isvalid(s::UTF32String, i::Integer) = checkbounds(Bool, s.chars, i)
Base.iterate(s::UTF32String, i::Int=1) = i > length(s.chars) ? nothing : (s.chars[i], i + 1)
Base.firstindex(::UTF32String) = 1
Base.lastindex(s::UTF32String) = length(s.chars)
Base.getindex(s::UTF32String, i::Integer) = s.chars[i]

s = UTF32String(['h', 'é'])
a = AnnotatedString(s)
threw = try
    hash(a, UInt(0))
    false
catch err
    println("hash(a, 0) error = ", sprint(showerror, err))
    err isa ArgumentError
end

println("isequal(a, s) = ", isequal(a, s))
println("hash(s, 0) = ", hash(s, UInt(0)))

if isequal(a, s) && threw
    println("REPRODUCED hashops-annotated-non8-hash")
else
    println("NOT REPRODUCED")
end
