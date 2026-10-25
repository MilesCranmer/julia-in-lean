# A negative integer exponent is valid only for the integer units +1 and -1.
# checked_pow instead mistakes wrapping unsigned negation for mathematical -1.
x = UInt8(255)
p = Int8(-1)
r = Base.Checked.checked_pow(x, p)
if r == x && BigInt(x)^BigInt(-p) * BigInt(r) != 1
    println("actual = ", repr(r), " :: ", typeof(r))
    println("REPRODUCED intarith-checked-negative-pow")
else
    error("Expected the unsigned negative-exponent counterexample; got $(repr(r))")
end
