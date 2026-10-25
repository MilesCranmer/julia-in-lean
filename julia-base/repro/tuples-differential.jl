# Differential oracle for JuliaLean/Tuples/Validation.lean: prints the same
# cases in the same format as `JuliaLean.Tuples.Validation.differential`.
fmt(x::Integer) = string(BigInt(x))
fmt(x::Bool) = x ? "true" : "false"
fmt(::Missing) = "missing"
fmt(::Nothing) = "nothing"
fmt(x::Union{Tuple,AbstractVector}) = "[" * join(map(fmt, collect(x)), ",") * "]"
fmtnt(nt::NamedTuple) = "(" * join(["$k=$(fmt(v))" for (k, v) in pairs(nt)], ",") * ")"
function res(f, g=fmt)
    try
        g(f())
    catch e
        "E:" * string(nameof(typeof(e)))
    end
end
tup(n) = ntuple(k -> 10k, n)
const TYS = (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)
cands(T, len) = unique(filter(x -> typemin(T) <= x <= typemax(T),
    BigInt[typemin(T), typemax(T), -1, 0, 1, 2, len, len + 1]))

function idxline(len, i, name)
    t = tup(len)
    println("IDX $len $name $(fmt(BigInt(i))) => get:", res(() -> t[i]), " set:", res(() -> Base.setindex(t, 0, i)),
        " getd:", res(() -> get(t, i, -1)), " isas:", res(() -> isassigned(t, i)))
end
for len in (0, 1, 3)
    for T in TYS, x in cands(T, len)
        idxline(len, T(x), string(T))
    end
    for b in (false, true)
        idxline(len, b, "Bool")
    end
end
rangeends(len) = unique([-1, 0, 1, 2, 3, len - 2, len - 1, len, len + 1, len + 2])
for len in (0, 1, 3, 11, 12, 13, 33), a in rangeends(len), b in rangeends(len)
    t = tup(len)
    println("RNG $len $a $b => ", res(() -> t[a:b]))
end
for len in 0:3, (lo, n) in ((false, 1), (false, 2), (true, 0), (true, 1))
    t = tup(len)
    r = n == 0 ? (true:false) : (lo:(n == 1 ? lo : true))
    println("BRNG $len $(fmt(lo)) $n => ", res(() -> t[r]), " | ", res(() -> t[collect(r)]))
end
mknt(names, vals) = NamedTuple{Tuple(Symbol.(names))}(Tuple(vals))
ntof(names) = mknt(names, [10k for k in 1:length(names)])
for len in 0:4
    for n in (0, 1, 2, 3, 5), i in 1:len+2
        t = tup(len)
        a = res(() -> Base.split_rest(t, n, i), ((x, y),) -> fmt(x) * fmt(y))
        L = max(0, len - i + 1)
        b = res(() -> Base.split_rest(Int[t...], n, i),
            ((x, y),) -> "[" * join([k <= L ? fmt(x[k]) : "U" for k in 1:length(x)], ",") * "]" * fmt(y))
        nt = ntof(["a", "b", "c", "d"][1:len])
        c = res(() -> Base.split_rest(nt, n, i), ((x, y),) -> fmtnt(x) * fmtnt(y))
        println("SPLIT $len $n $i => $a | $b | $c")
    end
    for i in 0:6
        println("REST $len $i => ", res(() -> Base.rest(tup(len), i)))
    end
    d = res(() -> begin
            a, b..., c = tup(len)
            (a, b, c)
        end, ((a, b, c),) -> fmt(a) * fmt(b) * fmt(c))
    println("DESTR $len => $d")
end
for T in TYS, x in filter(x -> x <= 12 || x > typemax(Int), cands(T, 3))
    println("NTUP $(string(T)) $(fmt(x)) => ", res(() -> length(ntuple(identity, T(x)))))
end
for n in (-2, -1, 0, 1, 5, 10, 11, 12)
    println("NTUPV $n => ", res(() -> ntuple(identity, Val(n))))
end
for len in 0:3, n in (-1, 0, 1, 2, 3, 5)
    println("FILL $len $n => ", res(() -> Base.fill_to_length(tup(len), 0, Val(n))))
end
for len in (0, 1, 2, 5, 33)
    println("REV $len => ", res(() -> Base.revargs(tup(len)...)), " ", res(() -> reverse(tup(len))))
end
for len in (0, 1, 2, 31, 32, 33, 34)
    t = tup(len)
    println("FRONT $len => ", res(() -> Base.front(t)), " ", res(() -> Base.tail(t)), " ", res(() -> first(t)), " ", res(() -> last(t)))
end
for t in ((), (3,), (2, 5), (2, 4611686018427387904, 3))
    println("PROD $(fmt(t)) => ", res(() -> prod(t)), " ", res(() -> prod(identity, t)))
end
const LENS = (0, 1, 2, 3, 31, 32, 33, 34)
tupb(n) = ntuple(k -> 100k, n)
tupc(n) = ntuple(k -> 1000k, n)
pat(n) = ntuple(k -> ((k - 1) * 7 + 3) % 5, n)
for a in LENS
    println("MAP1 $a => ", res(() -> map(x -> x + 1, tup(a))))
    for b in LENS
        println("MAP2 $a $b => ", res(() -> map(+, tup(a), tupb(b))))
        for c in (0, 2, 33)
            println("MAP3 $a $b $c => ", res(() -> map((x, y, z) -> x + y + z, tup(a), tupb(b), tupc(c))))
        end
    end
end
for n in (0, 1, 2, 3, 4, 5, 6, 31, 32, 33, 34, 40)
    p = pat(n)
    println("FIND $n => ", res(() -> findfirst(iseven, p)), " ", res(() -> findlast(iseven, p)), " ",
        res(() -> findfirst(iszero, p)), " ", res(() -> findlast(iszero, p)), " ", res(() -> filter(iseven, p)))
end
const FV = (missing, NaN, -0.0, 0.0, 1.0, 2.0)
small = Any[()]
append!(small, [(i,) for i in 0:5])
append!(small, [(i, j) for i in 0:5 for j in 0:5])
vals(t) = map(i -> FV[i+1], t)
fmtt(t) = "[" * join(["v$i" for i in t], ",") * "]"
for pre in (0, 31)
    for a in small, b in small
        x = (ntuple(_ -> 1.0, pre)..., vals(a)...)
        y = (ntuple(_ -> 1.0, pre)..., vals(b)...)
        println("CMP $pre $(fmtt(a)) $(fmtt(b)) => ", res(() -> isequal(x, y)), " ", res(() -> x == y), " ",
            res(() -> x < y), " ", res(() -> isless(x, y)), " ", res(() -> cmp(x, y)))
    end
    for xi in 0:5, a in small
        x = FV[xi+1]
        y = (ntuple(_ -> 1.0, pre)..., vals(a)...)
        println("IN $pre v$xi $(fmtt(a)) => ", res(() -> x in y))
    end
end
fl = filter(t -> !(0 in t), small)
for a in fl, b in fl
    x = (Float64[vals(a)...]...,)
    y = Float64[vals(b)...]
    println("FINDIN $(fmtt(a)) $(fmtt(b)) => ", res(() -> findall(in(y), x)), " ", res(() -> findall(z -> z in y, x)))
end
const NTS = ([], ["a"], ["b"], ["a", "b"], ["b", "a"], ["a", "b", "c"], ["c", "a"])
const NAMELISTS = ([], ["a"], ["c"], ["d"], ["a", "b"], ["b", "a"], ["a", "a"], ["c", "d"])
keycases = Any[(:a, "Symbol a"), (:d, "Symbol d")]
for T in (Int64, Int32, UInt8, Int128), x in 0:3
    push!(keycases, (T(x), "$(string(T)) $x"))
end
push!(keycases, (true, "Bool 1"))
for an in NTS
    a = ntof(an)
    for bn in NTS
        b = mknt(bn, [100k for k in 1:length(bn)])
        println("MERGE $(fmtnt(a)) $(fmtnt(b)) => ", res(() -> merge(a, b), fmtnt))
    end
    for ks in NAMELISTS
        sel = res(() -> a[Tuple(Symbol.(ks))], fmtnt)
        sd = allunique(ks) ? res(() -> Base.structdiff(a, NamedTuple{Tuple(Symbol.(ks))}), fmtnt) : "-"
        println("NTSEL $(fmtnt(a)) [", join(ks, ","), "] => $sel $sd")
    end
    for k in ("a", "b", "d")
        println("NTDEL $(fmtnt(a)) $k => ", res(() -> Base.delete(a, Symbol(k)), fmtnt), " ",
            res(() -> Base.setindex(a, 7, Symbol(k)), fmtnt))
    end
    for (k, name) in keycases
        println("HASKEY $(fmtnt(a)) $name => ", res(() -> haskey(a, k)), " ", res(() -> get(a, k, -1)))
    end
end
