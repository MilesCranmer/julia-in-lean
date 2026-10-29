members(n) = [Val{i} for i in 1:n]
small = Union{members(126)...}
large = Union{members(127)...}
println("all members isbitstype: ", all(isbitstype, members(127)))
println("isbitsunion with 126 members: ", Base.isbitsunion(small))
println("isbitsunion with 127 members: ", Base.isbitsunion(large))
if all(isbitstype, members(127)) && Base.isbitsunion(small) && !Base.isbitsunion(large)
    println("REPRODUCED multidimcov-isbitsunion-many-members")
else
    println("NOT REPRODUCED multidimcov-isbitsunion-many-members")
end
