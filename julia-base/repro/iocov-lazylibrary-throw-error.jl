using Base.Libc.Libdl
println("dlopen(name; throw_error=false) = ", dlopen("libiocov_missing_lib"; throw_error=false))
ll = LazyLibrary("libiocov_missing_lib")
try
    r = dlopen(ll; throw_error=false)
    println("dlopen(::LazyLibrary; throw_error=false) = ", r)
catch e
    println("dlopen(::LazyLibrary; throw_error=false) threw ", typeof(e), ": ", first(sprint(showerror, e), 90))
    e isa MethodError && println("REPRODUCED iocov-lazylibrary-throw-error")
end
