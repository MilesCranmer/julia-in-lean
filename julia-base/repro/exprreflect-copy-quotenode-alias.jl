inner = Expr(:call, :f, :x)
original = Expr(:tuple, QuoteNode(inner))
copied = copy(original)

shared = copied.args[1].value === original.args[1].value
push!(copied.args[1].value.args, :y)
changed = original.args[1].value.args == Any[:f, :x, :y]

println("copy(original) == original: ", copied == original)
println("quoted Expr shared: ", shared)
println("original after mutating copy: ", sprint(Meta.show_sexpr, original))

if shared && changed
    println("REPRODUCED exprreflect-copy-quotenode-alias")
else
    println("NOT REPRODUCED exprreflect-copy-quotenode-alias")
end
