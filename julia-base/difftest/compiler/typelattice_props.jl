# Smoke tests of the properties stated in JuliaLean/Proofs/Compiler/src/typelattice.lean, run on
# the pinned Julia before they are proved or refuted. Reuses the element generator of
# typelattice.jl (everything but its final `exit(main())`).
#
#     $JULIA \
#         difftest/compiler/typelattice_props.jl --cases 20000 --seed 1
#
# Prints, per property, the number of cases checked, violated and skipped (an exception in one of
# the calls), and the first few counterexamples.
#
# Runs:
#   2026-11-09, pinned Julia 1.15.0-DEV.184 f755f49a9e, seed 1, 600 cases x 3 lattices:
#   no violation of refl, is_lattice_equal = ⊑∧⊒, is_lattice_equal symmetric, widenconst
#   monotone, is_lattice_bool => widenconst <: Bool, on any lattice; typeinf trans 111/111.
#   Violations, all explained:
#   - opt trans (PartialTypeVar ⊑ TypeVar ⊑ Any): bug compiler-tl-sqsub-widenconst-upper.
#   - opt tmeet lower bound (Union{} ⋢ PartialStruct/Const/PartialTypeVar): bug
#     compiler-tl-sqsub-bottom-least-optimizer.
#   - tmeet lower bound on typeinf/ipo: types with free type variables, where tmeet returns `v`
#     on purpose (typelattice.jl:646,670,679), and generator PartialStructs whose fields are not
#     below their declared types.
#   - "⊑ widenconst" and "nontrivial => strictly below": Const of a type with a free TypeVar
#     (isa(v, Type{v}) is false for such v); not an inference-reachable value.
#   - slotwrapper upper, widenlattice upper, narrow_mustalias below x, extract_const_bool: a
#     MustAlias on the ipo/opt lattices or an InterMustAlias/Conditional on the lattice that
#     does not own it; not inputs inference builds.
#   - trivial info => equal to widenconst: Conditional/MustAlias, which has_nontrivial_extended_info
#     does not look at; every caller applies widenslotwrapper first.

let src = read(joinpath(@__DIR__, "typelattice.jl"), String)
    src = replace(src, r"\nexit\(main\(\)\)\s*$" => "\n")
    include_string(Main, src, joinpath(@__DIR__, "typelattice.jl"))
end

const ⊑ = CC.:⊑
const TRACE = Ref(false)
const STATS = Dict{String,Vector{Int}}()
const EXAMPLES = Dict{String,Vector{String}}()

function check(f, name::String)
    st = get!(STATS, name, [0, 0, 0, 0])
    t0 = time_ns()
    TRACE[] && (println(stderr, "    ", name); flush(stderr))
    r = try
        f()
    catch err
        st[3] += 1
        return
    finally
        st[4] += (time_ns() - t0) ÷ 1000000
    end
    if r === nothing
        return            # precondition not met
    end
    st[1] += 1
    if r !== true
        st[2] += 1
        ex = get!(EXAMPLES, name, String[])
        length(ex) < 4 && push!(ex, sprint(show, r))
    end
    return
end

function props(g::Gen, L, lname)
    a = rand_elt(g); b = related(g, a); c = related(g, b)
    t = randtype(g.rng)
    TRACE[] && (println(stderr, "  ", (a, b, c, t)); flush(stderr))
    check("$lname refl") do
        ⊑(L, a, a) ? true : (a,)
    end
    check("$lname trans") do
        (⊑(L, a, b) && ⊑(L, b, c)) || return nothing
        ⊑(L, a, c) ? true : (a, b, c)
    end
    check("$lname is_lattice_equal = ⊑∧⊒") do
        e = CC.is_lattice_equal(L, a, b)
        e == (⊑(L, a, b) && ⊑(L, b, a)) ? true : (a, b, e)
    end
    check("$lname ⊑ widenconst") do
        a isa CC.LimitedAccuracy && return nothing
        ⊑(L, a, CC.widenconst(a)) ? true : (a,)
    end
    check("$lname widenconst monotone") do
        (a isa CC.LimitedAccuracy || b isa CC.LimitedAccuracy) && return nothing
        ⊑(L, a, b) || return nothing
        CC.widenconst(a) <: CC.widenconst(b) ? true : (a, b)
    end
    check("$lname tmeet lower bound") do
        m = CC.tmeet(L, a, t)
        (⊑(L, m, a) && ⊑(L, m, t)) ? true : (a, t, m)
    end
    check("$lname tmeet greatest") do
        # every b ⊑ a with b ⊑ t is ⊑ tmeet(a, t)
        (⊑(L, b, a) && ⊑(L, b, t)) || return nothing
        m = CC.tmeet(L, a, t)
        ⊑(L, b, m) ? true : (a, t, b, m)
    end
    check("$lname widenlattice upper") do
        w = CC.widenlattice(L, a)
        ⊑(L, a, w) ? true : (a, w)
    end
    check("$lname slotwrapper upper") do
        a isa CC.LimitedAccuracy && return nothing
        w = CC.widenslotwrapper(a)
        ⊑(L, a, w) ? true : (a, w)
    end
    check("$lname is_lattice_bool => widenconst <: Bool") do
        CC.is_lattice_bool(L, a) || return nothing
        a isa CC.LimitedAccuracy && return nothing
        CC.widenconst(a) <: Bool ? true : (a,)
    end
    check("$lname extract_const_bool => ⊑ Const") do
        v = CC.maybe_extract_const_bool(a)
        v isa Bool || return nothing
        ⊑(L, a, Core.Const(v)) ? true : (a, v)
    end
    check("$lname trivial info => equal to widenconst") do
        a isa CC.LimitedAccuracy && return nothing
        CC.has_nontrivial_extended_info(L, a) && return nothing
        CC.is_lattice_equal(L, a, CC.widenconst(a)) ? true : (a,)
    end
    check("$lname nontrivial info => strictly below widenconst") do
        a isa CC.LimitedAccuracy && return nothing
        CC.has_nontrivial_extended_info(L, a) || return nothing
        CC.:⊏(L, a, CC.widenconst(a)) ? true : (a,)
    end
    check("$lname narrow_mustalias below x") do
        n = CC.narrow_mustalias(L, a, b)
        ⊑(L, n, a) ? true : (a, b, n)
    end
    check("$lname is_lattice_equal symmetric") do
        CC.is_lattice_equal(L, a, b) == CC.is_lattice_equal(L, b, a) ? true : (a, b)
    end
end

function main_props(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    g = Gen(Random.Xoshiro(seed))
    trace = get(opts, "trace", "0") == "1"
    TRACE[] = trace
    for k in 1:n
        for (lname, L) in LATTICES
            trace && (println(stderr, "CASE ", k, " ", lname); flush(stderr))
            props(g, L, lname)
        end
        k % 500 == 0 && (println(stderr, "PROGRESS ", k); flush(stderr))
    end
    for (name, st) in sort(collect(STATS))
        println(rpad(name, 52), " checked=", st[1], " violated=", st[2], " threw=", st[3], " ms=", st[4])
        for ex in get(EXAMPLES, name, String[])
            println("    ", first(ex, 600))
        end
    end
end

main_props()
