# Checks of the properties stated in JuliaLean/Proofs/Compiler/src/ssair/EscapeAnalysis.lean, run on
# the pinned Julia. Reuses the `EscapeInfo` generators of escape.jl.
#
#     $JULIA difftest/compiler/escape_props.jl --cases 20000 --seed 5
#
# Prints, per property, the number of cases checked, violated and skipped (an exception in one of
# the calls), and the first few counterexamples.
#
# Runs (2026-11-10):
#   pinned 1.15.0-DEV.184 f755f49a9e, seed 5, 20000 rounds: no violation of any property. The
#   upper-bound check skips zero-field objects (18427 checked). `⊏ₑ` threw in 103 rounds, each the
#   known `⊑ₑ` BoundsError (compiler-escape-join-upper-bound).
#   julia +nightly 1.15.0-DEV.304 290d5bb5f5, seed 7, 5000 rounds: no violation; `⊏ₑ` threw in 20.

include(joinpath(@__DIR__, "escape.jl"))

const STATS = Dict{String,Vector{Int}}()
const EXAMPLES = Dict{String,Vector{String}}()

function check(f, name::String)
    st = get!(STATS, name, [0, 0, 0])
    r = try
        f()
    catch err
        st[3] += 1
        return
    end
    r === nothing && return
    st[1] += 1
    if r !== true
        st[2] += 1
        ex = get!(EXAMPLES, name, String[])
        length(ex) < 4 && push!(ex, sprint(show, r))
    end
    return
end

aset(a) = Set{Any}(collect(a))
fld(xs, i) = i ≤ length(xs) ? aset(xs[i]) : Set{Any}()

# The exact merge (AliasExact in the Lean file).
function alias_exact(xa, ya, r)
    (xa === true || ya === true) && return r === true
    xa === false && return r === ya
    ya === false && return r === xa
    if xa isa EA.IndexableFields && ya isa EA.IndexableFields
        r isa EA.IndexableFields || return false
        n = max(length(xa.infos), length(ya.infos))
        length(r.infos) == n || return false
        return all(i -> aset(r.infos[i]) == union(fld(xa.infos, i), fld(ya.infos, i)), 1:n)
    end
    r isa EA.Unindexable || return false
    all_of(a) = a isa EA.Unindexable ? aset(a.info) :
        reduce(union, (aset(s) for s in a.infos); init=Set{Any}())
    return aset(r.info) == union(all_of(xa), all_of(ya))
end

function alias_equiv(a, b)
    a isa Bool && return a === b
    if a isa EA.IndexableFields
        b isa EA.IndexableFields || return false
        length(a.infos) == length(b.infos) || return false
        return all(i -> aset(a.infos[i]) == aset(b.infos[i]), 1:length(a.infos))
    end
    b isa EA.Unindexable || return false
    return aset(a.info) == aset(b.info)
end

# The right-hand side of EqSpec.
function eq_fields(x, y)
    x.Analyzed === y.Analyzed || return false
    x.ReturnEscape === y.ReturnEscape || return false
    xt, yt = x.ThrownEscape, y.ThrownEscape
    (xt === EA.TOP_THROWN_ESCAPE) == (yt === EA.TOP_THROWN_ESCAPE) || return false
    xt === EA.TOP_THROWN_ESCAPE || Set(xt) == Set(yt) || return false
    alias_equiv(x.AliasInfo, y.AliasInfo) || return false
    xl, yl = x.Liveness, y.Liveness
    (xl === EA.TOP_LIVENESS) == (yl === EA.TOP_LIVENESS) || return false
    xl === EA.TOP_LIVENESS || Set(xl) == Set(yl) || return false
    return true
end

zero_fields(a) = a isa EA.IndexableFields && isempty(a.infos)

const CONSTANT_SETS = (EA.BOT_LIVENESS, EA.TOP_LIVENESS, EA.ARG_LIVENESS)
isconstset(s) = any(c -> c === s, CONSTANT_SETS)

function props(rng)
    c = LatCtx()
    x = rand_info(rng, c)
    y = rand(rng) < 0.3 ? raise(rng, x, c) : rand_info(rng, c)
    z = rand_info(rng, c)
    pc = rand(rng, -1:6)
    snap = [copy(s) for s in (x.Liveness, y.Liveness, x.ThrownEscape, y.ThrownEscape)]
    j = EA.:⊔ₑ(x, y)

    check("join exact (field by field)") do
        j.Analyzed === (x.Analyzed | y.Analyzed) || return (x, y, j)
        j.ReturnEscape === (x.ReturnEscape | y.ReturnEscape) || return (x, y, j)
        tt = x.ThrownEscape === EA.TOP_THROWN_ESCAPE || y.ThrownEscape === EA.TOP_THROWN_ESCAPE
        (j.ThrownEscape === EA.TOP_THROWN_ESCAPE) == tt || return (x, y, j)
        tt || Set(j.ThrownEscape) == union(Set(x.ThrownEscape), Set(y.ThrownEscape)) || return (x, y, j)
        alias_exact(x.AliasInfo, y.AliasInfo, j.AliasInfo) || return (x, y, j)
        lt = x.Liveness === EA.TOP_LIVENESS || y.Liveness === EA.TOP_LIVENESS
        (j.Liveness === EA.TOP_LIVENESS) == lt || return (x, y, j)
        lt || Set(j.Liveness) == union(Set(x.Liveness), Set(y.Liveness)) || return (x, y, j)
        # no argument set was changed
        all(((a, b),) -> a == b, zip(snap, (x.Liveness, y.Liveness, x.ThrownEscape, y.ThrownEscape))) ||
            return (x, y, j)
        true
    end
    check("join commutative (==)") do
        (j == EA.:⊔ₑ(y, x)) ? true : (x, y)
    end
    check("join idempotent (==)") do
        (EA.:⊔ₑ(x, x) == x) ? true : x
    end
    check("join absorbs (==)") do
        (EA.:⊔ₑ(j, y) == j) ? true : (x, y)
    end
    check("join upper bound, no zero-field object") do
        (zero_fields(x.AliasInfo) || zero_fields(y.AliasInfo)) && return nothing
        (EA.:⊑ₑ(x, j) && EA.:⊑ₑ(y, j)) ? true : (x, y, j)
    end
    check("== exact (field sets)") do
        w = rand(rng) < 0.5 ? y : EA.EscapeInfo(x; Liveness=copy(x.Liveness))
        ((x == w) == eq_fields(x, w)) ? true : (x, w)
    end
    check("⊏ₑ exact") do
        a, b = EA.:⊑ₑ(x, y), EA.:⊑ₑ(y, x)
        (EA.:⊏ₑ(x, y) == (a && !b)) ? true : (x, y)
    end
    check("query join laws") do
        EA.has_no_escape(j) == (EA.has_no_escape(x) && EA.has_no_escape(y)) || return ("no", x, y)
        EA.has_arg_escape(j) == (EA.has_arg_escape(x) || EA.has_arg_escape(y)) || return ("arg", x, y)
        EA.has_return_escape(j) == (EA.has_return_escape(x) || EA.has_return_escape(y)) || return ("ret", x, y)
        EA.has_thrown_escape(j) == (EA.has_thrown_escape(x) || EA.has_thrown_escape(y)) || return ("thr", x, y)
        EA.has_thrown_escape(j, pc) == (EA.has_thrown_escape(x, pc) || EA.has_thrown_escape(y, pc)) ||
            return ("thrpc", x, y, pc)
        (!(EA.has_return_escape(x, pc) || EA.has_return_escape(y, pc)) || EA.has_return_escape(j, pc)) ||
            return ("retpc", x, y, pc)
        EA.has_no_escape(x) == (!EA.has_return_escape(x) && !EA.has_thrown_escape(x) && !EA.has_arg_escape(x)) ||
            return ("split", x)
        (!EA.has_return_escape(x, pc) || EA.has_return_escape(x)) || return ("retpc⇒ret", x, pc)
        (!EA.has_thrown_escape(x, pc) || EA.has_thrown_escape(x)) || return ("thrpc⇒thr", x, pc)
        true
    end
    check("query values on constructors") do
        p = rand(rng, -1:6)
        R = EA.ReturnEscape(p); T = EA.ThrownEscape(p)
        vals = [
            EA.has_no_escape.((EA.NoEscape(), EA.⊥, EA.ArgEscape(), R, EA.AllReturnEscape(), T, EA.⊤)) ==
                (true, true, false, false, false, false, false),
            EA.has_arg_escape.((EA.NoEscape(), EA.⊥, EA.ArgEscape(), R, EA.AllReturnEscape(), T, EA.⊤)) ==
                (false, false, true, p == 0, true, false, true),
            EA.has_return_escape.((EA.NoEscape(), EA.⊥, EA.ArgEscape(), R, EA.AllReturnEscape(), T, EA.⊤)) ==
                (false, false, false, true, true, false, true),
            EA.has_return_escape(R, pc) == (p == -1 || p == pc),
            EA.has_return_escape(EA.AllReturnEscape(), pc), EA.has_return_escape(EA.⊤, pc),
            !EA.has_return_escape(EA.ArgEscape(), pc), !EA.has_return_escape(T, pc),
            EA.has_thrown_escape.((EA.NoEscape(), EA.⊥, EA.ArgEscape(), R, EA.AllReturnEscape(), T, EA.⊤)) ==
                (false, false, false, false, false, true, true),
            EA.has_thrown_escape(T, pc) == (p == -1 || p == pc), EA.has_thrown_escape(EA.⊤, pc),
            !EA.has_thrown_escape(R, pc), !EA.has_thrown_escape(EA.AllReturnEscape(), pc),
        ]
        all(vals) ? true : (p, pc, findall(!, vals))
    end
    check("push! into a non-constant Liveness") do
        isconstset(x.Liveness) && return nothing
        w = EA.EscapeInfo(x; Liveness=copy(x.Liveness))
        before = EA.has_arg_escape(w)
        push!(w.Liveness, pc)
        EA.has_arg_escape(w) == (before || pc == 0) || return ("arg", x, pc)
        EA.has_return_escape(w, pc) == EA.has_return_escape(w) || return ("ret", x, pc)
        true
    end
    check("ignore_argescape exact, x.Liveness unchanged") do
        before = copy(x.Liveness)
        r = EA.ignore_argescape(x)
        x.Liveness == before || return ("mutated", x)
        r.Liveness === x.Liveness && return ("shared", x)
        Set(r.Liveness) == setdiff(Set(x.Liveness), Set([0])) || return ("set", x)
        (r.Analyzed === x.Analyzed && r.ReturnEscape === x.ReturnEscape &&
         r.ThrownEscape === x.ThrownEscape && r.AliasInfo === x.AliasInfo) ? true : ("fields", x)
    end
    check("ignore_aliasinfo merge identity") do
        r = EA.ignore_aliasinfo(x)
        a = z.AliasInfo
        (EA.merge_alias_info(r.AliasInfo, a) === a && EA.merge_alias_info(a, r.AliasInfo) === a &&
         r.Liveness === x.Liveness && r.ThrownEscape === x.ThrownEscape) ? true : (x, a)
    end
    check("ignore_liveness empty") do
        r = EA.ignore_liveness(x)
        (isempty(r.Liveness) && r.AliasInfo === x.AliasInfo && r.ThrownEscape === x.ThrownEscape) ? true : x
    end
    check("from_interprocedural exact") do
        p = rand(rng, 1:6)
        a = EA.ArgEscapeInfo(x)
        r = EA.from_interprocedural(a, p)
        x === EA.⊤ && return r === EA.⊤ ? true : x
        (r.Analyzed && !r.ReturnEscape && r.AliasInfo === true && Set(r.Liveness) == Set([p]) &&
         Set(r.ThrownEscape) == (EA.has_thrown_escape(x) ? Set([p]) : Set{Int}()) &&
         !isconstset(r.Liveness)) ? true : (x, p, r)
    end
    check("merge_to_unindexable exact") do
        info = rand_ainfo(rng); infos = EA.AInfo[rand_ainfo(rng) for _ in 1:rand(rng, 0:3)]
        expect = reduce(union, (aset(s) for s in infos); init=aset(info))
        r = EA.merge_to_unindexable(copy(info), infos)
        aset(r) == expect ? true : (info, infos, r)
    end
end

function main_props(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    for _ in 1:n
        props(rng)
    end
    println("VERSION ", VERSION, " ", Base.GIT_VERSION_INFO.commit)
    for (name, st) in sort(collect(STATS))
        println(rpad(name, 44), " checked=", st[1], " violated=", st[2], " threw=", st[3])
        for ex in get(EXAMPLES, name, String[])
            println("    ", first(ex, 700))
        end
    end
end

main_props()
