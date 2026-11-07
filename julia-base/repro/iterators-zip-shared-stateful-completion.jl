using Base.Iterators: Stateful

# Both inputs use only Base's ordinary finite, stateful iteration protocol.
a = Stateful{<:Any,Any}([10, 20])
s = Stateful{<:Any,Any}([1])
inner = zip(s, s)
println("inner isdone before iteration = ", Base.isdone(inner))
println("independent input before = ", peek(a))
row = iterate(zip(a, inner))
println("outer iterate = ", repr(row))
println("independent input after = ", peek(a))
remaining = collect(a)
println("independent input remaining = ", repr(remaining))

# Empty independent factors are detected before advancing the unrelated input.
control = Stateful{<:Any,Any}([10, 20])
empty_inner = zip(Stateful{<:Any,Any}([1]), Stateful{<:Any,Any}(Int[]))
control_row = iterate(zip(control, empty_inner))
control_remaining = collect(control)
println("independent empty-factor control = ", repr((control_row, control_remaining)))

if row === nothing && remaining == [20] && control_row === nothing && control_remaining == [10, 20]
    println("REPRODUCED iterators-zip-shared-stateful-completion")
else
    error("shared Stateful completion counterexample did not reproduce")
end
