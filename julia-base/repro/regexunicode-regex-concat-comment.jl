# Regex * and ^ wrap the pattern in "(?:...)" on one line, so a free-spacing (x) pattern
# that ends in a comment swallows the closing parenthesis.
r = r"a  # the letter a"x
println("match(r, \"a\") = ", match(r, "a"))
results = String[]
for (name, f) in [("r * \"b\"", () -> r * "b"), ("r^2", () -> r^2), ("r * r\"b\"x", () -> r * r"b"x)]
    out = try
        string(f())
    catch e
        sprint(showerror, e)
    end
    println(name, " -> ", out)
    push!(results, out)
end
all(startswith("PCRE compilation error"), results) && println("REPRODUCED regexunicode-regex-concat-comment")
