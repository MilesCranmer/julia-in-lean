r = Int8(120):Int8(127)
s = Int8(8):Int8(8)
failed = try
    r[s]
    false
catch e
    e isa InexactError
end
if failed && [r[i] for i in s] == Int8[127]
    println("REPRODUCED ranges-operations-slice-overflow")
else
    error("range slicing overflow did not reproduce")
end
