# filter(f, d::AbstractDict) (base/abstractdict.jl:479-488) and
# copy(a::AbstractDict) (base/abstractdict.jl:197) build the result with
# empty(d) and `df[k] = v`. empty(::ImmutableDict) and empty(::PersistentDict)
# return the same immutable type, which has no setindex!, so both calls throw
# MethodError, even with an always-true predicate.
results = Dict{String,Any}()
for (name, f) in [
        ("filter(p -> true, ImmutableDict(:a => 1))", () -> filter(p -> true, Base.ImmutableDict(:a => 1))),
        ("copy(ImmutableDict(:a => 1))", () -> copy(Base.ImmutableDict(:a => 1))),
        ("filter(p -> true, PersistentDict(:a => 1))", () -> filter(p -> true, Base.PersistentDict(:a => 1))),
        ("copy(PersistentDict(:a => 1))", () -> copy(Base.PersistentDict(:a => 1))),
    ]
    r = try
        f()
    catch e
        e
    end
    results[name] = r
    println(name, " -> ", r isa Exception ? sprint(showerror, r)[1:min(end, 110)] : repr(r))
end
if all(r -> r isa MethodError && r.f === setindex!, values(results))
    println("REPRODUCED dictscov-immutable-filter-copy")
end
