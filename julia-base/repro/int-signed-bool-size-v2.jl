if signed(Bool) <: Signed && sizeof(signed(Bool)) != sizeof(Bool)
    println("REPRODUCED int-signed-bool-size-v2")
else
    println("NOT_REPRODUCED int-signed-bool-size-v2")
end
