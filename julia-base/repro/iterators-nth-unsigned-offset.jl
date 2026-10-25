# nth(A, n) computes begin + n - 1 in UInt when n is unsigned, so negative firstindex breaks
A = Base.IdentityUnitRange(-5:-3)
ri = Iterators.nth(A, 1)
ru = try Iterators.nth(A, UInt(1)) catch e; e end
println("nth(A, 1) = ", ri, ", nth(A, UInt(1)) = ", ru isa Exception ? sprint(showerror, ru) : repr(ru))
ri == -5 && ru isa BoundsError && println("REPRODUCED iterators-nth-unsigned-offset")
