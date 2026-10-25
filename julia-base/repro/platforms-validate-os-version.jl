using Base.BinaryPlatforms
p = Platform("x86_64", "macos"; os_version = "foo", validate_strict = true)
println("accepted with validate_strict=true: ", repr(p))
r = try
    triplet(p)
catch e
    e
end
println("triplet(p) => ", r isa Exception ? sprint(showerror, r) : repr(r))
g = try
    Platform("x86_64", "linux"; libgfortran_version = "foo", validate_strict = true)
catch e
    e
end
println("libgfortran_version = \"foo\" for comparison => ", g isa Exception ? sprint(showerror, g) : repr(g))
if r isa ArgumentError && g isa ArgumentError
    println("REPRODUCED platforms-validate-os-version")
end
