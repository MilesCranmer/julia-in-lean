using Base: AnnotatedString, AnnotatedChar, annotatedstring, annotations
c = AnnotatedChar('é', [(:a, 1)])        # 'é' is 2 code units
alone = annotatedstring(c)
after = annotatedstring("x", c)
println("annotatedstring(c) regions      = ", [a.region for a in annotations(alone)])
println("annotatedstring(\"x\", c) regions = ", [a.region for a in annotations(after)], " for string ", repr(after.string))
println("annotations(annotatedstring(\"x\", c), 3) = ", annotations(after, 3))
first(annotations(alone)).region == 1:2 && first(annotations(after)).region == 2:2 &&
    println("REPRODUCED stringscovb-annotatedstring-char-region")
