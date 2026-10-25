# WeakValueIdDict{K,V} setindex! (base/weakdict.jl:302-315) stores WeakRef(v)
# without checking or converting v against V; every read then throws
# TypeError at a ::V cast. The type exists only on master.
if !isdefined(Base, :WeakValueIdDict)
    println("WeakValueIdDict does not exist in this version")
else
    tryT(f) = try
        f(); "no error"
    catch e
        typeof(e)
    end
    v = [1.0]                                   # kept alive for the whole script
    w = Base.WeakValueIdDict{Any,Vector{Int}}()
    w[:k] = v
    println("w[:k] = [1.0] accepted: haskey = ", haskey(w, :k), ", length = ", length(w))
    reads = [
        "w[:k]" => tryT(() -> w[:k]),
        "get(w, :k, nothing)" => tryT(() -> get(w, :k, nothing)),
        "get!(w, :k, [0])" => tryT(() -> get!(w, :k, [0])),
        "collect(w)" => tryT(() -> collect(w)),
        "pop!(w, :k)" => tryT(() -> pop!(w, :k)),
    ]
    for (name, r) in reads
        println(name, " threw: ", r)
    end
    println("haskey(w, :k) after pop!: ", haskey(w, :k))
    w2 = Base.WeakValueIdDict{Any,Vector{Int}}()
    r = tryT(() -> get!(w2, :k, v))
    println("get!(empty, :k, [1.0]) threw: ", r, "; stored anyway: ", haskey(w2, :k))
    if all(p -> p.second === TypeError, reads) && r === TypeError && haskey(w2, :k)
        println("REPRODUCED iddicts-weakvalue-eltype")
    end
end
