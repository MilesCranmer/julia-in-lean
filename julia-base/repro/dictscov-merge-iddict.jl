# merge / mergewith of IdDicts build their result with _typeddict
# (base/abstractdict.jl:413-417), which is always a Dict{K,V}: keys are then
# compared with isequal instead of ===, so distinct IdDict keys collapse and
# entries are lost.
a = IdDict{Any,Any}(1 => :a, 1.0 => :b)
m1 = merge(a)
println("merge(a) = ", m1, " (", typeof(m1), "), length ", length(m1), "; length(a) = ", length(a))
m2 = merge(IdDict{Any,Any}(1 => :a), IdDict{Any,Any}(1.0 => :b))
println("merge(IdDict(1 => :a), IdDict(1.0 => :b)) = ", m2)
m3 = mergewith(+, IdDict{Any,Int}(1 => 1), IdDict{Any,Int}(1.0 => 2))
println("mergewith(+, IdDict(1 => 1), IdDict(1.0 => 2)) = ", m3)
ref = merge!(copy(IdDict{Any,Any}(1 => :a)), IdDict{Any,Any}(1.0 => :b))
println("merge!(copy(IdDict(1 => :a)), IdDict(1.0 => :b)) = ", ref, ", length ", length(ref))
if length(m1) == 1 && length(m2) == 1 && length(m3) == 1 && length(ref) == 2
    println("REPRODUCED dictscov-merge-iddict")
end
