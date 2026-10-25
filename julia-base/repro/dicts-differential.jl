# Differential oracle for JuliaLean/Dicts/Validation.lean: the same LCG draws the
# same Dict/Set operations; prints a digest of the full table state after each.
struct K
    x::Int
end
const HF = Ref(0)
function myhash(x::Int)
    f = HF[]
    f == 0 && return UInt(x) * 0x9E3779B97F4A7C15
    f == 1 && return UInt(x % 5)
    f == 2 && return UInt(0x1234)
    f == 3 && return (UInt(x % 3) << 60) + UInt(x % 7)
    return UInt(x ÷ 4) * 0x9E3779B97F4A7C15
end
Base.hash(k::K, h::UInt) = myhash(k.x)

const RELEASE = !hasfield(Dict{Int,Int}, :popcursor)
const P = Int128(2305843009213693951)
mix(h, x) = (h * 1000003 + Int128(x)) % P

function digest(d::Dict{K,V}, res) where V
    h = Int128(0)
    for x in (length(d.slots), d.ndel, d.count, d.age, d.idxfloor, d.maxprobe, res)
        h = mix(h, x)
    end
    for i in 1:length(d.slots)
        h = mix(h, d.slots[i])
        if d.slots[i] & 0x80 != 0
            h = mix(h, d.keys[i].x + 1)
            h = mix(h, (V === Nothing ? 0 : d.vals[i]) + 1)
        end
    end
    for (k, v) in d
        h = mix(h, k.x + 7)
    end
    h
end

const S = Ref(UInt64(0))
function rnd(n)
    S[] = S[] * 0x5851f42d4c957f2d + 0x14057b7ef767814f
    return Int((S[] >> 33) % UInt64(n))
end
function rndpairs(m)
    ps = Tuple{Int,Int}[]
    for _ in 1:m
        k = rnd(41); v = rnd(1000)
        push!(ps, (k, v))
    end
    ps
end
function build(ps)
    d = Dict{K,Int}()
    for (k, v) in ps
        d[K(k)] = v
    end
    d
end
const HINTS = (0, 3, 10, 20, 40, 100, 300)

function step!(d)
    r = rnd(100)
    k = rnd(41)
    if r < 35
        d[K(k)] = rnd(1000); return 0
    elseif r < 55
        delete!(d, K(k)); return 0
    elseif r < 62
        x = get(d, K(k), nothing); return x === nothing ? 1 : x + 2
    elseif r < 67
        return try; pop!(d, K(k)) + 2; catch e; e isa KeyError || rethrow(); 1; end
    elseif r < 70
        return pop!(d, K(k), rnd(1000)) + 2
    elseif r < 74
        return get!(d, K(k), rnd(1000)) + 2
    elseif r < 80
        v = rnd(1000); k2 = rnd(41); v2 = rnd(1000); k3 = rnd(41)
        return get!(d, K(k)) do
            d[K(k2)] = v2
            delete!(d, K(k3))
            v
        end + 2
    elseif r < 84
        n = HINTS[rnd(7) + 1]; s = rnd(2) == 1
        sizehint!(d, n; shrink = s); return 0
    elseif r < 85
        empty!(d); return 0
    elseif r < 88
        filter!(p -> (p.first.x + p.second) % 3 != 0, d); return 0
    elseif r < 91
        merge!(d, build(rndpairs(rnd(13)))); return 0
    elseif r < 94
        mergewith!(+, d, build(rndpairs(rnd(13)))); return 0
    elseif r < 97
        if RELEASE
            d[K(k)] = rnd(1000); return 0
        end
        isempty(d) && return 1
        p = pop!(d); return p.first.x * 1000 + p.second + 2
    else
        d[K(k)] = rnd(1000); return 0
    end
end

rndlist(n, m) = [rnd(m) for _ in 1:n]

function setcase()
    a = rndlist(rnd(26), 31)
    b = rndlist(rnd(26), 31)
    dels = rndlist(rnd(7), 31)
    which = rnd(7) + 1
    x = rnd(31)
    s = Set{K}(K.(a))
    for y in dels; delete!(s, K(y)); end
    t = Set{K}(K.(b))
    res = 0
    if which == 1; union!(s, t)
    elseif which == 2; intersect!(s, t)
    elseif which == 3; setdiff!(s, t)
    elseif which == 4; symdiff!(s, t)
    elseif which == 5; res = issubset(s, t) ? 2 : 1
    elseif which == 6; res = (s == t) ? 2 : 1
    else; res = in!(K(x), s) ? 2 : 1
    end
    digest(s.dict, res)
end

for f in 0:4
    HF[] = f
    for sq in 1:3
        S[] = UInt64(1000 * f + sq)
        d = Dict{K,Int}()
        for i in 1:150
            res = step!(d)
            println("D $f $sq $i $(digest(d, res))")
        end
    end
    S[] = UInt64(77 + f)
    for c in 1:60
        println("S $f $c $(setcase())")
    end
end
