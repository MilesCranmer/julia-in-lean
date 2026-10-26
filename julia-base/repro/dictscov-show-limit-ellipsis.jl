# show(io, t::AbstractDict) with :limit => true (base/dict.jl:3-23) prints "…"
# after the 10th pair even when the dictionary has exactly 10 entries, so nothing
# was omitted.
d = Dict(i => i for i in 1:10)
s = repr(d; context = :limit => true)
println(s)
shown = count("=>", s)
println("pairs shown: ", shown, " of ", length(d), "; ends with an ellipsis: ", endswith(s, "…)"))
d9 = Dict(i => i for i in 1:9)
println(repr(d9; context = :limit => true))
if shown == length(d) && endswith(s, "…)")
    println("REPRODUCED dictscov-show-limit-ellipsis")
end
