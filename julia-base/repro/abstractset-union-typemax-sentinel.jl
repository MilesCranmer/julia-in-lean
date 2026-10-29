mutable struct HugeIntSet <: AbstractSet{Int}
    extra::Set{Int}
end
Base.length(s::HugeIntSet) = isempty(s.extra) ? typemax(Int) : throw(OverflowError("cardinality exceeds typemax(Int)"))
Base.in(x::Int, s::HugeIntSet) = x > 0 || x in s.extra
function Base.iterate(s::HugeIntSet, state=(false, 1))
    extras, next = state
    if !extras
        return (next, next == typemax(Int) ? (true, nothing) : (false, next + 1))
    end
    item = next === nothing ? iterate(s.extra) : iterate(s.extra, next)
    item === nothing && return nothing
    x, following = item
    return (x, (true, following))
end
function Base.push!(s::HugeIntSet, x::Int)
    x <= 0 && push!(s.extra, x)
    return s
end
s = HugeIntSet(Set{Int}())
result = union!(s, [1, 0])
reference = HugeIntSet(Set{Int}())
foreach(x -> push!(reference, x), [1, 0])
println("length before = ", typemax(Int))
println("0 in union! result = ", 0 in result)
println("0 after pushing both inputs = ", 0 in reference)
if !(0 in result) && (0 in reference)
    println("REPRODUCED abstractset-union-typemax-sentinel")
else
    error("Early exit did not omit zero")
end
