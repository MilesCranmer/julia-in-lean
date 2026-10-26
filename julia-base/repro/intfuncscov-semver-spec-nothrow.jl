if !isdefined(Base, :semver_spec)
    println("Base.semver_spec is not defined in this version")
else
    res(f) = try f() catch e; sprint(showerror, e) end
    a = res(() -> Base.semver_spec("< 0"; throw = false))
    b = res(() -> Base.semver_spec("0.0.0"; throw = false))
    c = res(() -> Base.semver_spec("> 1"; throw = false))
    println("semver_spec(\"< 0\"; throw=false) = ", a)
    println("semver_spec(\"0.0.0\"; throw=false) = ", b)
    println("semver_spec(\"> 1\"; throw=false) = ", c)
    if c === nothing && a isa String && startswith(a, "InexactError") && b isa String
        println("REPRODUCED intfuncscov-semver-spec-nothrow")
    else
        println("not reproduced")
    end
end
