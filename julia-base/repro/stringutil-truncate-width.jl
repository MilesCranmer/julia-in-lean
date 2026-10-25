for (f, w) in ((rtruncate, 0), (ltruncate, 0), (ctruncate, 0))
    r = f("abc", w)
    println(f, "(\"abc\", ", w, ") = ", repr(r), ", textwidth = ", textwidth(r))
end
r = rtruncate("abcdef", 2, "...")
println("rtruncate(\"abcdef\", 2, \"...\") = ", repr(r), ", textwidth = ", textwidth(r))
textwidth(rtruncate("abc", 0)) > 0 && textwidth(r) > 2 && println("REPRODUCED stringutil-truncate-width")
