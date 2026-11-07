x = [-0.0]
r = findall(in((0.0,)), x)
member = -0.0 in (0.0,)
direct = Base._findin(x, (0.0,))
nan = findall(in((NaN,)), [NaN])
if r == Int[] && member && direct == Int[] && findall(y -> y in (0.0,), x) == [1] &&
        nan == [1] && !(NaN in (NaN,))
    println("REPRODUCED array-findall-in-array-isequal")
else
    error("findall(in(b), array) membership did not reproduce: $r $member $direct $nan")
end
