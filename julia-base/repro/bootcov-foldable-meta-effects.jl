# Base.@_foldable_meta (base/essentials.jl:210-224) is documented as usable "in place of
# `@assume_effects :foldable`", but it also asserts :notaskstate and :inaccessiblememonly,
# which :foldable does not (base/expr.jl:1019-1021).
Base.eval(quote
    function __bootcov_meta_f()
        @_foldable_meta
        return current_task()
    end
    @assume_effects :foldable function __bootcov_assume_f()
        return current_task()
    end
end)
e_meta = Base.infer_effects(Base.__bootcov_meta_f, ())
e_assume = Base.infer_effects(Base.__bootcov_assume_f, ())
println("@_foldable_meta            : ", e_meta)
println("@assume_effects :foldable  : ", e_assume)
println("notaskstate          meta = ", e_meta.notaskstate, ", assume = ", e_assume.notaskstate)
println("inaccessiblememonly  meta = ", e_meta.inaccessiblememonly, ", assume = ", e_assume.inaccessiblememonly)
if e_meta.notaskstate !== e_assume.notaskstate || e_meta.inaccessiblememonly !== e_assume.inaccessiblememonly
    println("REPRODUCED bootcov-foldable-meta-effects")
end
