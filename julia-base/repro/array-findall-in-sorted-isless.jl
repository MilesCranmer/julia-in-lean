x = [-0.0]
b = [0.0]
r = findall(in(b), x)
merged = Base._sortedfindin(x, b)
unsorted = findall(in([NaN, 0.0]), x)
nan = findall(in([NaN]), [NaN])
if r == Int[] && (-0.0 in b) && merged == Int[] && findall(y -> y in b, x) == [1] &&
        unsorted == Int[] && (-0.0 in [NaN, 0.0]) && nan == [1] && !(NaN in [NaN])
    println("REPRODUCED array-findall-in-sorted-isless")
else
    error("findall(in(b), Float64 array) did not reproduce: $r $merged $unsorted $nan")
end
