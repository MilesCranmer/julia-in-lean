empty = @views "12345"[4:3]
println("value = ", repr(empty))
println("stored offset = ", empty.offset)
println("expected offset = 3")
empty.offset == 0 && println("REPRODUCED stringscova-substring-empty-offset")
