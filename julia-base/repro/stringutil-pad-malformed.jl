s = "\x80"                 # one (malformed) character, textwidth 1
r = lpad(s, 3, "\xe0")     # pad with the one-character string "\xe0" (textwidth 1)
println("lpad(\"\\x80\", 3, \"\\xe0\") = ", repr(r), ", textwidth = ", textwidth(r),
        ", chars = ", collect(r), ", endswith(r, s) = ", endswith(r, s))
q = rpad("\xe0", 3, "\x80")
println("rpad(\"\\xe0\", 3, \"\\x80\") = ", repr(q), ", textwidth = ", textwidth(q),
        ", startswith(q, \"\\xe0\") = ", startswith(q, "\xe0"))
textwidth(r) < 3 && !endswith(r, s) && textwidth(q) < 3 && println("REPRODUCED stringutil-pad-malformed")
