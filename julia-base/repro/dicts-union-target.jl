using Test

struct Counted{T}
    values::Vector{T}
    calls::Base.RefValue{Int}
end
Base.IteratorSize(::Type{<:Counted}) = Base.HasLength()
Base.eltype(::Type{Counted{T}}) where T = T
Base.length(it::Counted) = length(it.values)
function Base.iterate(it::Counted, i=1)
    it.calls[] += 1
    i > length(it.values) ? nothing : (it.values[i], i + 1)
end

println("VERSION ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
for newset in (() -> Set{Bool}(), () -> Base.IdSet{Bool}())
    s = newset()
    union!(s, Bool[])
    @test isempty(s)
    calls = Ref(0)
    union!(s, Counted(Bool[false, true, false], calls))
    @test length(s) == 2 && false in s && true in s
    @test calls[] == 2
    calls = Ref(0)
    union!(s, Counted(Bool[true, false], calls))
    @test calls[] == 1
    @test length(s) == 2
end

s = Set{Bool}([false])
it = Counted(Any[true, 2], Ref(0))
if VERSION >= v"1.15.0-DEV"
    @test_throws InexactError union!(s, it)
    @test it.calls[] == 2
else
    union!(s, it)
    @test it.calls[] == 1
end
@test s == Set([false, true])

s = Base.IdSet{Bool}([false])
it = Counted(Any[true, 2], Ref(0))
union!(s, it)
if VERSION >= v"1.15.0-DEV"
    @test it.calls[] == 3 && 2 in s
else
    @test it.calls[] == 1 && !(2 in s)
end
println("DICTS UNION CHECKS PASSED")
