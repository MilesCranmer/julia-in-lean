if !isdefined(Base, :matches_spec_range!)
    println("Base.matches_spec_range! is not defined in this version")
else
    spec = Base.VersionSpec("1.0 - 1.5")
    versions = [v"2.0.0", v"1.2.0"]
    dest = falses(2)
    Base.matches_spec_range!(dest, versions, spec, 2)
    expected = [v in spec for v in versions]
    println("versions = ", versions)
    println("matches_spec_range! = ", collect(dest))
    println("in(v, spec)        = ", expected)
    if collect(dest) != expected
        println("REPRODUCED intfuncscov-matches-spec-unsorted")
    else
        println("not reproduced")
    end
end
