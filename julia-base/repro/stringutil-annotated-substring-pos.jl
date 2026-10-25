using Base: AnnotatedString, annotations
s = AnnotatedString("abcdef", [(1:6, :A, 1)])
ss = SubString(s, 3, 4)   # "cd"
println("annotations(ss)      regions = ", [a.region for a in annotations(ss)])
println("annotations(ss, 1)   regions = ", [a.region for a in annotations(ss, 1)])
println("annotations(ss, 1:2) regions = ", [a.region for a in annotations(ss, 1:2)])
if [a.region for a in annotations(ss)] == [1:2] && [a.region for a in annotations(ss, 1:2)] == [3:4]
    println("REPRODUCED stringutil-annotated-substring-pos")
end
