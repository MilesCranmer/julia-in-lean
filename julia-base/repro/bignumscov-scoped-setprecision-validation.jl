function outcome(f)
    try
        return repr(f())
    catch err
        return "throws " * string(typeof(err))
    end
end

global_precision = outcome(() -> setprecision(BigFloat, 0))
scoped_precision = outcome(() -> setprecision(() -> 7, BigFloat, 0))
global_base = outcome(() -> setprecision(BigFloat, 10; base=1))
scoped_base = outcome(() -> setprecision(() -> 7, BigFloat, 10; base=1))

println("setprecision(BigFloat, 0) -> ", global_precision)
println("setprecision(() -> 7, BigFloat, 0) -> ", scoped_precision)
println("setprecision(BigFloat, 10; base=1) -> ", global_base)
println("setprecision(() -> 7, BigFloat, 10; base=1) -> ", scoped_base)

if global_precision == "throws DomainError" && scoped_precision == "7" &&
        global_base == "throws DomainError" && scoped_base == "7"
    println("REPRODUCED bignumscov-scoped-setprecision-validation")
end
