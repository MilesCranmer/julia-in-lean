a = collect(1:100)
empty!(a)

reproduced = try
    sizehint!(a, 10; first=true)
    println("result = ", repr(a))
    false
catch err
    println("error = ", sprint(showerror, err))
    err isa BoundsError
end

println(reproduced ? "REPRODUCED multidimcov-sizehint-first-empty" : "NOT REPRODUCED")

if !reproduced
  let
    for initial in (Int[], [1, 2, 3]), first in (false, true), shrink in (false, true), hint in (-1, 0, 2, 10, 200)
        v = copy(initial)
        sizehint!(v, 100)
        before = copy(v)
        @assert sizehint!(v, hint; first, shrink) === v
        @assert v == before
    end
    v = [1, 2, 3]
    try
        sizehint!(v, big(typemax(Int)) + 1; first=true, shrink=true)
        error("expected InexactError")
    catch err
        @assert err isa InexactError
        @assert v == [1, 2, 3]
    end
    println("sizehint preservation and conversion error: OK")
  end
end
