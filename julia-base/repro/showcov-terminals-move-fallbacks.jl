# TextTerminal's relative cursor-move fallbacks (base/Terminals.jl:52-70) call
# cmove(x, y) without the terminal, so a TextTerminal subtype that defines the
# documented interface (cmove(t, x, y), getX, getY, displaysize) gets a MethodError.
const T = Base.Terminals

mutable struct GridTerm <: T.TextTerminal
    x::Int
    y::Int
end
T.cmove(t::GridTerm, x, y) = (t.x = x; t.y = y; nothing)
T.getX(t::GridTerm) = t.x
T.getY(t::GridTerm) = t.y
Base.displaysize(::GridTerm) = (24, 80)

t = GridTerm(5, 5)
err = try
    T.cmove_up(t, 1)
    nothing
catch e
    e
end
println("cmove_up(t, 1) threw: ", typeof(err))
println("cursor after cmove_up: ", (t.x, t.y))

# The targets the fallbacks compute, captured by a two-argument cmove method:
targets = Any[]
T.cmove(x::Int, y::Int) = (push!(targets, (x, y)); nothing)
T.cmove_down(t, 1)
T.cmove_right(t, 1)
println("cmove_down(t, 1) target from (5, 5) on a 24x80 terminal: ", targets[1])
println("cmove_right(t, 1) target from (5, 5) on a 24x80 terminal: ", targets[2])

if err isa MethodError && targets == [(5, 24), (80, 5)]
    println("REPRODUCED showcov-terminals-move-fallbacks")
end
