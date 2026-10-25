using Base.BinaryPlatforms
# The Platform docstring allows periods in tag names; show prints tags as keyword arguments.
p = Platform("x86_64", "linux", Dict{String,Any}("cuda.version" => "11.8"); validate_strict = true)
s = repr(p)
println("repr(p) = ", s)
r = try
    eval(Meta.parse(s))
catch e
    e
end
println("eval(Meta.parse(repr(p))) => ", r isa Exception ? sprint(showerror, r) : repr(r))
if !(r isa Platform && r == p)
    println("REPRODUCED platforms-show-tag-names")
end
