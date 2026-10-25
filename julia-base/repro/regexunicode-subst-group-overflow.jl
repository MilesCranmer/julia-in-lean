# A substitution group number wraps around Int: \18446744073709551617 refers to group 1.
got = try
    replace("ab", r"(a)" => s"[\18446744073709551617]")
catch e
    sprint(showerror, e)
end
println("replace(\"ab\", r\"(a)\" => s\"[\\18446744073709551617]\") = ", repr(got))
println("group 2 for comparison: ", try replace("ab", r"(a)" => s"[\2]") catch e; sprint(showerror, e) end)
got == "[a]b" && println("REPRODUCED regexunicode-subst-group-overflow")
