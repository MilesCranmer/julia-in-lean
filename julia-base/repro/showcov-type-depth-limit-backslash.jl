# Base.type_depth_limit (used to shorten types in stack traces) tracks quotes
# so that braces inside '...' and "..." are not counted, but an escaped
# backslash leaves it in the "after backslash" state, so the closing quote is
# ignored and every later brace is treated as quoted (base/show.jl:2744-2782).
ok  = Base.type_depth_limit("A{'a'}B{C}", 0; maxdepth = 1)
bad = Base.type_depth_limit("A{'\\\\'}B{C}", 0; maxdepth = 1)
println("A{'a'}B{C}    -> ", ok)
println("A{'\\\\'}B{C}  -> ", bad)

# The same through the width limit used for stack traces:
sig = "f(::Val{'\\\\'}, ::Vector{Vector{Int64}})"
println(repr(sig), " -> ", repr(Base.type_depth_limit(sig, 10)))
sym = "f(::Val{Symbol(\"\\\\\")}, ::Vector{Vector{Int64}})"
println(repr(sym), " -> ", repr(Base.type_depth_limit(sym, 10)))

if ok == "A{…}B{…}" && bad == "A{…"
    println("REPRODUCED showcov-type-depth-limit-backslash")
end
