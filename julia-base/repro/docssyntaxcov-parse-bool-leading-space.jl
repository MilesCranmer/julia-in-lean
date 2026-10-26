# parse(Bool, s) accepts trailing but not leading whitespace around a numeric Bool:
# it tests isnumeric(s[1]) on the first character, before skipping whitespace.
r(s) = try parse(Bool, s) catch e; e end
for s in ("1 ", " 1", " true", "0 ", " 0")
    println(repr(s), " => ", repr(r(s)))
end
println("parse(Int, \" 1\") => ", parse(Int, " 1"))
if r("1 ") === true && r(" true") === true && r(" 1") isa ArgumentError
    println("REPRODUCED docssyntaxcov-parse-bool-leading-space")
end
