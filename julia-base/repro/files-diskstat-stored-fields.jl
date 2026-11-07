T = typeof(diskstat(pwd()))
z = UInt64(0)
s = T(z, UInt64(1), typemax(UInt64), z, z, z, z, (z, z, z, z))
@assert :bsize in propertynames(s)
@assert getfield(s, :bsize) == UInt64(1)
@assert BigInt(getfield(s, :bsize)) * BigInt(getfield(s, :bavail)) == 0

stored_result = try
    getproperty(s, :bsize)
catch err
    err
end
available_result = try
    getproperty(s, :available)
catch err
    err
end
println("bsize result type: ", typeof(stored_result))
println("available result type: ", typeof(available_result))
@assert stored_result isa InexactError
@assert available_result isa InexactError
println("REPRODUCED files-diskstat-stored-fields")
