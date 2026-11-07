println("JULIA ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
for T in (Core.PhiNode, Core.PhiCNode)
    for mask in 0:7
        values = Vector{Any}(undef, 3)
        for i in 1:3
            if mask & (1 << (i - 1)) != 0
                values[i] = Expr(:call, :+, i, 1)
            end
        end
        node = T === Core.PhiNode ? T(Int32[1, 2, 3], values) : T(values)
        copied = copy(node)
        @assert length(copied.values) == 3
        for i in 1:3
            @assert isassigned(copied.values, i) == isassigned(values, i)
            if isassigned(values, i)
                @assert copied.values[i] == values[i]
                @assert copied.values[i] !== values[i]
            end
        end
    end
end
for n in (0, 1, 3)
    args = Any[Expr(:call, :+, i, 1) for i in 1:n]
    copied = Base.copy_exprargs(args)
    @assert copied == args && copied !== args
    @assert all(copied[i] !== args[i] for i in eachindex(args))
    expr = Expr(:block, args...)
    @assert copy(expr) == expr
end
ci = first(code_lowered(identity, Tuple{Int}))
@assert copy(ci) == ci
println("PASS expression arguments and CodeInfo callers")
println("PASS PhiNode and PhiCNode assigned and unassigned copy branches")
