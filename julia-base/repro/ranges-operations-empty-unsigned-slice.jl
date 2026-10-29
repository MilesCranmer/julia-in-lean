r = UInt8(0):UInt8(3)
for s in (1:0, 1:2:0)
    @assert checkbounds(Bool, r, s) && isempty(s)
    failure = try
        r[s]
        nothing
    catch e
        e
    end
    @assert failure isa Union{InexactError,OverflowError}
end
println("REPRODUCED ranges-operations-empty-unsigned-slice")
