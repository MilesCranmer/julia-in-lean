# The positional method runtests(tests) calls the keyword body with the keyword
# defaults in declaration order: ncores, exit_on_error, revise, propagate_project, ...
doc = string(@doc(Base.runtests))
println("docstring signature mentions: ", match(r"propagate_project=\w+", doc).match)
ci = code_lowered(Base.runtests, Tuple{Vector{String}})[1]
call = only(filter(ex -> Meta.isexpr(ex, :call) && length(ex.args) == 9, ci.code))
defaults = call.args[3:5]
println("lowered defaults of exit_on_error, revise, propagate_project: ", defaults)
if occursin("propagate_project=true", doc) && defaults[3] === false
    println("REPRODUCED iocov-runtests-propagate-doc")
end
