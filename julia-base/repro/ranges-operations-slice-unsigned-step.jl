r = UInt(1):UInt(1):UInt(4)
s = 4:-1:1
if isempty(r[s]) && [r[i] for i in s] == UInt[4,3,2,1]
    println("REPRODUCED ranges-operations-slice-unsigned-step")
else
    error("unsigned stepped slicing did not reproduce")
end
