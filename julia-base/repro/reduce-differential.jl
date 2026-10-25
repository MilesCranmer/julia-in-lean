# Differential oracle for JuliaLean/Reduce/Validation.lean: prints the same
# cases in the same format as `JuliaLean.Reduce.Validation.differential`.
fmt(x::Bool) = x ? "Bool:true" : "Bool:false"
fmt(x::Integer) = string(typeof(x)) * ":" * string(x)
fmt(x::Float64) = isnan(x) ? "Float64:NaN" : "Float64:0x" * string(reinterpret(UInt64, x), base=16)
fmt(::Missing) = "missing"
fmtlist(xs) = "[" * join(map(fmt, collect(xs)), ",") * "]"
tyname(T) = T === Union{} ? "Union{}" :
    T isa Union ? "Union{" * join(sort(string.(Base.uniontypes(T))), ",") * "}" : string(T)
fmtarr(A) = "$(tyname(eltype(A)))[$(size(A, 1))x$(size(A, 2))]" * fmtlist(vec(A))
fmtmat(A) = "[$(size(A, 1))x$(size(A, 2))]" * fmtlist(vec(A))
fmtpair((a, b)) = "(" * fmt(a) * "," * fmt(b) * ")"
fmtfind((v, inds)) = fmtarr(v) * " [" * join(["($(I[1]),$(I[2]))" for I in vec(inds)], ",") * "]"
function res(f, g=fmt)
    try
        g(f())
    catch e
        "E:" * string(nameof(typeof(e)))
    end
end

const ATOMS = reinterpret.(Float64, UInt64[0x3FB999999999999A, 0x3FF8000000000000, 0xC00A000000000000,
    0x4000000000000000, 0x0, 0x8000000000000000, 0x7FF8000000000000, 0x7FF0000000000000,
    0xFFF0000000000000, 0x7FE1CCF385EBC8A0])
atom(i) = ATOMS[i+1]
cyc(xs, k) = atom(xs[(k-1)%length(xs)+1])

function genelt(name, k)
    name == "i64" && return Int64((k * 37) % 11 - 5)
    name == "i64big" && return typemax(Int64) - (k % 3)
    name == "i64min" && return isodd(k) ? typemin(Int64) : Int64(-1)
    name == "i8" && return k == 1 ? Int8(127) : k == 2 ? Int8(-128) : Int8((k * 77) % 256 - 128)
    name == "u8" && return k == 1 ? 0xff : UInt8((k * 97 + 200) % 256)
    name == "u64" && return typemax(UInt64) - UInt64(k)
    name == "i8small" && return Int8(k % 3 - 1)
    name == "u8two" && return UInt8(2)
    name == "f64" && return cyc([0, 1, 2, 3, 0, 4, 5], k)
    name == "f64nan" && return cyc([1, 6, 5, 7, 4, 8, 3], k)
    name == "f64z" && return cyc([5, 4], k)
    name == "f64negz" && return atom(5)
    name == "f64big" && return atom(9)
    name == "bool" && return k % 3 == 0
    name == "booltrue" && return true
    name == "mi" && return k % 4 == 0 ? missing : Int64(k)
    name == "mb" && return k % 3 == 0 ? missing : (k % 3 == 2)
    name == "mbf" && return isodd(k) ? missing : false
    name == "miss" && return missing
    name == "if" && return isodd(k) ? Int64(3k) : Float64(-k)
    error("unknown generator $name")
end

const GENTY = Dict("i64" => Int64, "i64big" => Int64, "i64min" => Int64, "i8" => Int8,
    "i8small" => Int8, "u8" => UInt8, "u8two" => UInt8, "u64" => UInt64, "f64" => Float64,
    "f64nan" => Float64, "f64z" => Float64, "f64negz" => Float64, "f64big" => Float64,
    "bool" => Bool, "booltrue" => Bool, "mi" => Union{Missing,Int64}, "mb" => Union{Missing,Bool},
    "mbf" => Union{Missing,Bool}, "miss" => Missing, "if" => Union{Int64,Float64})

gen(name, n) = GENTY[name][genelt(name, k) for k in 1:n]

const VECGENS = ["i64", "i64big", "i64min", "i8", "u8", "u64", "i8small", "u8two", "f64", "f64nan",
    "f64z", "f64negz", "f64big", "bool", "booltrue", "mi", "mb", "mbf", "miss", "if"]
const VECLENS = [0, 1, 2, 15, 16, 17, 40]
const LONGGENS = ["f64", "f64z", "i8", "u8", "bool", "mi"]
vecinputs = vcat([(g, n) for g in VECGENS for n in VECLENS], [(g, n) for g in LONGGENS for n in (1025, 2100)])
const INITS = [("i8_0", Int8(0)), ("i8_m1", Int8(-1)), ("u8_0", UInt8(0)), ("u8_1", UInt8(1)),
    ("i64_0", Int64(0)), ("f_negz", -0.0), ("b_t", true), ("u64_max", typemax(UInt64))]

for (g, n) in vecinputs
    v = gen(g, n)
    h = "$g $n =>"
    println("SUM $h ", res(() -> sum(v)))
    println("PROD $h ", res(() -> prod(v)))
    println("MAX $h ", res(() -> maximum(v)))
    println("MIN $h ", res(() -> minimum(v)))
    println("EXTREMA $h ", res(() -> extrema(v), fmtpair))
    println("FINDMAX $h ", res(() -> findmax(v), fmtpair))
    println("FINDMIN $h ", res(() -> findmin(v), fmtpair))
    println("MAXABS $h ", res(() -> maximum(abs, v)))
    println("ANY $h ", res(() -> any(v)))
    println("ALL $h ", res(() -> all(v)))
    println("FOLDR $h ", res(() -> foldr(+, v)))
    for (iname, init) in INITS
        println("SUMINIT $iname $h ", res(() -> sum(v; init=init)))
        println("PRODINIT $iname $h ", res(() -> prod(v; init=init)))
    end
end

const COUNTINITS = [("i64_0", Int64(0)), ("i8_0", Int8(0)), ("i8_120", Int8(120)), ("u8_250", UInt8(250)),
    ("u64_max", typemax(UInt64)), ("i64_max", typemax(Int64)), ("f_0", 0.0), ("b_t", true)]
for n in vcat(VECLENS, [100]), (iname, init) in COUNTINITS
    xs = Bool[k % 3 != 1 for k in 1:n]
    println("COUNT $iname $n => ", res(() -> count(xs; init=init)), " ", res(() -> count(x -> x, Tuple(xs); init=init)))
end

const FLATTEN = [("empty", Vector{Int64}[]), ("one_empty", [Int64[]]), ("two_empty", [Int64[], Int64[]]),
    ("single", [Int64[5]]), ("mixed", [Int64[], Int64[1, 2], Int64[], Int64[3]]),
    ("i8", [Int8[100, 100], Int8[100]]), ("bool", [Bool[true, true], Bool[true]]),
    ("f64", [[atom(0), atom(0)], [atom(0)]]), ("negz", [[atom(5)], [atom(5)]]),
    ("wrap", [Int64[typemax(Int64)], Int64[1]])]
for (name, vs) in FLATTEN
    println("FLATTEN $name => ", res(() -> sum(Iterators.flatten(vs))))
end

const SHAPES = [(0, 0), (0, 3), (3, 0), (1, 1), (1, 20), (2, 3), (20, 2), (3, 2)]
const MATGENS = ["i64", "i64big", "i8", "u8", "f64", "f64nan", "f64z", "bool", "mi", "mb", "miss", "if"]
mat(g, m, n) = reshape(gen(g, m * n), m, n)
const DIMSINITS = [("i8_0", Int8(0)), ("u8_0", UInt8(0)), ("i64_0", Int64(0)), ("f_negz", -0.0)]

for g in MATGENS, (m, n) in SHAPES
    A = mat(g, m, n)
    for d in 1:3
        h = "$g $(m)x$(n) $d =>"
        println("SUMD $h ", res(() -> sum(A; dims=d), fmtarr))
        println("PRODD $h ", res(() -> prod(A; dims=d), fmtarr))
        println("MAXD $h ", res(() -> maximum(A; dims=d), fmtarr))
        println("MIND $h ", res(() -> minimum(A; dims=d), fmtarr))
        println("MAXABSD $h ", res(() -> maximum(abs, A; dims=d), fmtarr))
        println("ANYD $h ", res(() -> any(A; dims=d), fmtarr))
        println("ALLD $h ", res(() -> all(A; dims=d), fmtarr))
        println("COUNTD i64_0 $h ", res(() -> count(identity, A; dims=d, init=Int64(0)), fmtarr))
        println("COUNTD i8_0 $h ", res(() -> count(identity, A; dims=d, init=Int8(0)), fmtarr))
        println("FINDMAXD $h ", res(() -> findmax(A; dims=d), fmtfind))
        println("FINDMIND $h ", res(() -> findmin(A; dims=d), fmtfind))
        for (iname, init) in DIMSINITS
            println("MRDI $iname $h ", res(() -> mapreduce(identity, Base.add_sum, A; dims=d, init=init), fmtarr))
        end
    end
end

for g in ["i64", "i8", "f64", "bool"]
    for (m, n) in SHAPES
        A = mat(g, m, n)
        for d in 0:3
            h = "$g $(m)x$(n) $d =>"
            println("ACCD none $h ", res(() -> accumulate(+, A; dims=d), fmtmat))
            println("ACCD i64_10 $h ", res(() -> accumulate(+, A; dims=d, init=10), fmtmat))
        end
    end
    for n in VECLENS
        v = gen(g, n)
        for d in -1:3
            h = "$g $n $d =>"
            println("ACCV none $h ", res(() -> accumulate(+, v; dims=d), fmtlist))
            println("ACCV i64_10 $h ", res(() -> accumulate(+, v; dims=d, init=10), fmtlist))
        end
    end
end
for g in ["i64", "i64big", "i8", "u8", "bool"], n in VECLENS
    v = gen(g, n)
    for d in -1:2
        println("CUMSUM $g $n $d => ", res(() -> cumsum(v; dims=d), fmtlist))
    end
end
