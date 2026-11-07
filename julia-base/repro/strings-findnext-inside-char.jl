s = "éx"            # bytes c3 a9 78
t = "\xa9x"         # bytes a9 78
r = findfirst(t, s)
println("findfirst(\"\\xa9x\", \"éx\") = ", repr(r))
println("occursin(\"\\xa9\", \"éx\") = ", occursin("\xa9", s))
g = try
    s[r]
catch e
    e
end
println("s[r] = ", g isa Exception ? sprint(showerror, g) : repr(g))
r == 2:3 && g isa StringIndexError && println("REPRODUCED strings-findnext-inside-char")

let needle = String(UInt8[0x80, 0x61]), haystack = String(UInt8[0xc2, 0x80, 0x61])
    @assert !isvalid(haystack, 2)
    forward = findnext(needle, haystack, 1)
    backward = findprev(needle, haystack, lastindex(haystack))
    first_match = findfirst(needle, haystack)
    last_match = findlast(needle, haystack)
    all_matches = findall(needle, haystack)
    overlapping = findall(needle, haystack; overlap=true)
    @assert forward == backward == first_match == last_match == 2:3
    @assert all_matches == overlapping == [2:3]
    @assert occursin(needle, haystack) && occursin(haystack)(needle)
    sliced = try
        haystack[forward]
    catch err
        err
    end
    @assert sliced isa StringIndexError
    println("needle bytes = ", collect(codeunits(needle)), "; haystack bytes = ", collect(codeunits(haystack)))
    println("findnext/findprev/findfirst/findlast = ", (forward, backward, first_match, last_match))
    println("findall = ", all_matches, "; overlap=true = ", overlapping, "; occursin = true; slice = StringIndexError")
    for id in ("strings-search-forward-first-range", "strings-search-reverse-last-range",
               "strings-search-first-last-string", "strings-search-occursin-first-match",
               "strings-search-all-pattern-ranges")
        println("REPRODUCED ", id)
    end
end
