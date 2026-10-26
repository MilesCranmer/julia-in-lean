reproduced = mktemp() do _, io
    close(io)
    open_state = isopen(io)
    writable_state = iswritable(io)
    string_result = write(io, "x")
    byte_result = write(io, UInt8('x'))
    println("isopen(io) = ", open_state)
    println("iswritable(io) = ", writable_state)
    println("write(io, \"x\") = ", string_result)
    println("write(io, UInt8('x')) = ", byte_result)
    !open_state && writable_state && string_result == 0 && byte_result == 0
end

reproduced && println("REPRODUCED streams-iostream-closed-write")
