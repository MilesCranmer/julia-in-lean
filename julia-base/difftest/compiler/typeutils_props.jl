# Smoke test, on the pinned Julia, of the statements proven in
# JuliaLean/Proofs/Compiler/src/typeutils/ before proving them. Random argument lists of plain
# types and Unions (no MustAlias, no fargs), as the proven statements assume.
# Usage: julia typeutils_props.jl [--cases N] [--seed S]
# Run 2026-11-09 on 1.15.0-DEV.184 f755f49a9e: seeds 1, 2 x 5000 cases, 0 failures.
# The later groups add fargs, MustAlias and Const arguments on typeinf_lattice (alias groups and
# widening) and Vararg/Const arguments for argtypes_to_type. Rerun with them 2026-11-09 on the same
# build: seeds 1, 2 x 5000 cases per group, 0 failures.
using Random
const CC = Base.Compiler
cases = 5000; seed = 1
for (i, a) in enumerate(ARGS)
    a == "--cases" && (global cases = parse(Int, ARGS[i+1]))
    a == "--seed" && (global seed = parse(Int, ARGS[i+1]))
end
Random.seed!(seed)
abstract type AR end
abstract type R{T} <: AR end
const ATOMS = Any[Int8, Int16, Int32, Int64, Nothing, Missing, String, Symbol, Float64, Vector{Int},
                  Integer, Real, AbstractString, Any, Type{Int}, R{Int}, Tuple{Int}, Vararg{Int}]
randunion() = (k = rand(1:5); Union{rand(ATOMS[1:end-1], k)...})
randarg() = rand() < 0.5 ? randunion() : rand(ATOMS)
ulen(t) = t isa Union ? length(Base.uniontypes(t)) : 1
fails = Ref(0)
check(c, msg) = c || (fails[] += 1; fails[] <= 20 && println("FAIL ", msg); false)
for L in (CC.JLTypeLattice(), CC.typeinf_lattice(CC.NativeInterpreter()))
    for _ in 1:cases
        n = rand(0:5)
        a = Any[randarg() for _ in 1:n]
        any(CC.isvarargtype, a[1:end-1]) && continue
        lens = map(ulen, a)
        c = CC.unionsplitcost(L, a)
        expect = min(typemax(Int), div(2 * prod(lens; init = 1), max(2, maximum(lens; init = 2))))
        check(c == expect, "cost formula $a: $c vs $expect")
        check(CC.unionsplitcost(L, shuffle(a)) == c, "order $a")
        # shrink one union by dropping members
        if n > 0
            i = rand(1:n)
            if a[i] isa Union
                ms = Base.uniontypes(a[i]); b = copy(a); b[i] = Union{ms[1:rand(1:length(ms))]...}
                check(CC.unionsplitcost(L, b) <= c, "monotone $a -> $b")
            end
        end
        rs = CC.switchtupleunion(L, a)
        check(length(rs) == prod(lens; init = 1), "count $a")
        check(all(r -> !any(x -> x isa Union, r), rs), "no union $a")
        choices = [x isa Union ? Base.uniontypes(x) : Any[x] for x in a]
        prodlist = vec([collect(Any, t) for t in Iterators.product(choices...)])
        n > 0 && check(rs == prodlist, "order of splits $a")
        if L isa CC.JLTypeLattice && !any(CC.isvarargtype, a)
            T = Tuple{a...}
            check(length(CC.switchtupleunion(T)) == prod(lens; init = 1), "type count $a")
            att = CC.argtypes_to_type(a)
            valid = all(x -> CC.valid_as_lattice(x, true), a)
            check(valid ? att == T : att === Union{}, "argtypes_to_type $a: $att")
        end
    end
end
# Alias groups and widened arguments (typeutils/Alias.lean, Groups.lean, SplitGroups.lean, Final.lean).
const FARGS = Any[Core.SlotNumber(1), Core.SlotNumber(2), Core.SSAValue(1), Core.SSAValue(2), :x, 1]
const TL = CC.typeinf_lattice(CC.NativeInterpreter())
function randelt()
    r = rand()
    r < 0.45 && return randunion()
    r < 0.65 && return CC.MustAlias(rand(1:2), 0, Any, rand(1:2), randunion())
    r < 0.8 && return CC.Const(rand(Int8))
    return rand(ATOMS[1:end-1])
end
for _ in 1:cases
    n = rand(1:5)
    a = Any[randelt() for _ in 1:n]
    fargs = Any[rand(FARGS) for _ in 1:n]
    f = rand(Bool) ? fargs : nothing
    sh = f !== nothing && any(i -> (fargs[i] isa Core.SlotNumber || fargs[i] isa Core.SSAValue) &&
                                   any(j -> fargs[j] === fargs[i], 1:i-1), 1:n)
    ma = count(x -> x isa CC.MustAlias, a) >= 2
    check(CC.any_alias_candidate(n, f, a) == (sh || ma), "any_alias_candidate $fargs $a")
    g = CC.compute_alias_groups(n, f, a)
    check((g === nothing) == !(sh || ma), "compute_alias_groups $fargs $a")
    lead(i) = g === nothing || g[i] == i
    wlen(x) = (w = CC.widenconst_split(x); w isa Union ? length(Base.uniontypes(w)) : 1)
    lens = [lead(i) ? wlen(a[i]) : 1 for i in 1:n]
    expect = min(typemax(Int), div(2 * prod(lens; init = 1), max(2, maximum(lens; init = 2))))
    check(CC.unionsplitcost(TL, a; fargs = f) == expect, "cost with groups $fargs $a")
    parts(x) = x isa Union ? length(Base.uniontypes(x)) :
        (!(x isa CC.Const) && !CC.isvarargtype(x) && CC.widenconst(x) isa Union) ?
            length(Base.uniontypes(CC.widenconst(x))) : 1
    rs = CC.switchtupleunion(TL, a; fargs = f)
    check(length(rs) == prod((lead(i) ? parts(a[i]) : 1 for i in 1:n); init = 1),
          "split count with groups $fargs $a")
    if g !== nothing
        for r in rs, i in 1:n
            g[i] != i && parts(a[g[i]]) > 1 && check(r[i] === r[g[i]], "follower $i of $(g[i]): $fargs $a")
        end
    end
end
for _ in 1:cases
    a = Any[rand() < 0.3 ? CC.Const(rand(Int8)) : rand(ATOMS[1:end-1]) for _ in 1:rand(0:3)]
    rand() < 0.5 && push!(a, rand(Any[Vararg{Int}, Vararg{Union{}}, Vararg{Any}]))
    w = Any[CC.isvarargtype(x) ? x : CC.widenconst_split(x) for x in a]
    fs = filter(x -> !CC.isvarargtype(x) || CC.valid_as_lattice(CC.unwrapva(x), true), w)
    ok = all(x -> CC.isvarargtype(x) || CC.valid_as_lattice(x, true), fs)
    att = CC.argtypes_to_type(a)
    check(ok ? att == Tuple{fs...} : att === Union{}, "argtypes_to_type with Const/Vararg $a: $att")
end
for _ in 1:cases
    t = randunion()
    check(CC.unioncomplexity(t) + 1 >= ulen(t), "unioncomplexity $t")
    a, b = rand(ATOMS[1:end-1]), rand(ATOMS[1:end-1])
    check(CC._typename(Union{a, b}) === CC._typename(Union{b, a}), "typename $a $b")
end
println("seed $seed, $cases cases per group, failures: ", fails[])
