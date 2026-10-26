using Base.Unicode: isassigned
r = try isassigned(-1) catch e e end
println("isassigned(-1) -> ", repr(r))
println("isassigned(0x110000) -> ", isassigned(0x110000))
r isa InexactError && println("REPRODUCED stringscovb-isassigned-negative")
