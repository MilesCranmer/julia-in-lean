# ImmutableDict{K,V}(parent, key, value) = new(parent, key, value) converts the key
# without an isequal check, so the key just added is not found.
const ID = Base.ImmutableDict
d = ID(ID{Float32,Int}(), 0.1 => 1)
println("d = ImmutableDict(ImmutableDict{Float32,Int}(), 0.1 => 1) = ", d, "; haskey(d, 0.1) = ", haskey(d, 0.1))
ok = !haskey(d, 0.1)
if isdefined(Base, :setindex) && hasmethod(Base.setindex, Tuple{ID, Any, Any})
    d2 = Base.setindex(ID{Float32,Int}(), 1, 0.1)
    println("Base.setindex(ImmutableDict{Float32,Int}(), 1, 0.1) = ", d2, "; get(d2, 0.1, nothing) = ", get(d2, 0.1, nothing))
    ok &= get(d2, 0.1, nothing) === nothing
end
e = try; Dict{Float32,Int}(0.1 => 1); "no error"; catch err; sprint(showerror, err); end
println("Dict{Float32,Int}(0.1 => 1) throws: ", e)
ok && startswith(e, "TypeError") && println("REPRODUCED dicts-immutabledict-lossy-key")
