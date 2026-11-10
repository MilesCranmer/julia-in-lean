# Smoke tests of the properties stated in JuliaLean/Proofs/Compiler/src/typelimits.lean, run on
# the pinned Julia before they are proved or refuted. Reuses the generators of typelimits.jl
# (everything but its final `exit(main())`).
#
#     $JULIA \
#         difftest/compiler/typelimits_props.jl --cases 5000 --seed 1
#
# Prints, per property, the number of cases checked, violated and skipped (an exception in one of
# the calls), and the first few counterexamples.
#
# Runs (2026-11-09, pinned Julia 1.15.0-DEV.184 f755f49a9e): seed 1 with 300 rounds, seed 2 with
# 1500 rounds (the validity filters were added before the seed-2 run). Violations found:
#   * tmerge idempotence on typeinf_lattice: Conditionals with isdefined=true (filed,
#     typelimits-tmerge-conditional-idempotent).
#   * tmerge upper bound: two LimitedAccuracy with equal types (filed,
#     typelimits-tmerge-limited-upper-bound); PartialTypeVar against a union containing TypeVar
#     and Const(Bool) against a Conditional (both through ⊑ in typelattice.jl, not filed here);
#     Union{} ⋢ PartialStruct on optimizer_lattice (⊑, typelattice.jl, not filed here); invalid
#     PartialStructs built by the generator (fields not ⊑ their declared types; filtered out).
#   * associativity (all lattices) and limit_type_size idempotence: leads in compiler/PERF_LEADS.md.
#   * tname_intersect misses shared ancestors of siblings: lead.
#   * tmerge_types_slow(a, Union{}) is Any: not reachable, tmerge's fast path takes Union{} first.
# Seed 3 with 1500 rounds (2026-11-09, same binary) added the checks behind the branch-by-branch
# statements (typelimits/Spec.lean, Layers.lean, Branches.lean); none was violated:
# tmerge_fast_path exact on all three lattices (1018-1067 each), union_count_abstract counts
# non-dispatch members (1500), issimpleenoughtype exact (1500), is_derived_type Union branch
# (1378), limit_type_size exact (1500), tname_intersect exact (1404), tmerge(ConstsLattice) of
# two different Consts merges their widened types (1470).
# No violations: JLTypeLattice upper bound and commutativity, tmerge_types_slow and tuplemerge
# upper bounds, tuple_tail_elem upper bound, limit_type_size and _limit_type_size upper bounds,
# Union{} identity on the three default lattices, is_derived_type reflexivity, type_more_complex
# irreflexivity, union_count_abstract ≤ unionlen, issimpleenoughtype ⇒ unionlen ≤ 3,
# issimplertype reflexivity, typeinf = JLTypeLattice on types, valid PartialStruct merges.

let src = read(joinpath(@__DIR__, "typelimits.jl"), String)
    src = replace(src, r"\nexit\(main\(\)\)\s*$" => "\n")
    include_string(Main, src, joinpath(@__DIR__, "typelimits.jl"))
end

const ⊑ = CC.:⊑
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

typesize(@nospecialize t) = length(sprint(show, t))

# Elements inference could produce: PartialStruct fields below their declared field types.
function valid(@nospecialize x)
    x isa CC.LimitedAccuracy && return valid(x.typ)
    x isa CC.Conditional && return valid(x.thentype) && valid(x.elsetype)
    x isa Core.InterConditional && return valid(x.thentype) && valid(x.elsetype)
    x isa CC.MustAlias && return valid(x.vartyp) && valid(x.fldtyp)
    x isa Core.InterMustAlias && return valid(x.vartyp) && valid(x.fldtyp)
    x isa Core.PartialTask && return valid(x.fetch_type)
    x isa Core.PartialOpaque && return valid(x.env)
    if x isa Core.PartialStruct
        for (i, f) in enumerate(x.fields)
            Base.isvarargtype(f) && continue
            valid(f) || return false
            CC.:⊑(CC.fallback_lattice, f, fieldtype(x.typ, i)) || return false
        end
    end
    return true
end
special(@nospecialize x) = occursin("PartialTypeVar", sprint(show, x)) || occursin("LimitedAccuracy", sprint(show, x))

function props(g::Gen)
    rng = g.rng
    for (lname, L) in LATTICES
        a = rand(rng) < 0.3 ? partial_struct(g, 2) : rand_elt(g)
        b = related(g, a); c = related(g, b)
        rand(rng) < 0.5 && ((a, b) = (b, a))
        check("$lname tmerge upper bound") do
            r = CC.tmerge(L, a, b)
            (⊑(L, a, r) && ⊑(L, b, r)) ? true : (a, b, r)
        end
        check("$lname tmerge upper bound (valid, no PartialTypeVar/LimitedAccuracy)") do
            (valid(a) && valid(b)) || return nothing
            (special(a) || special(b)) && return nothing
            r = CC.tmerge(L, a, b)
            (⊑(L, a, r) && ⊑(L, b, r)) ? true : (a, b, r)
        end
        check("$lname tmerge idempotent (valid, no Conditional)") do
            valid(a) || return nothing
            occursin("Conditional", sprint(show, a)) && return nothing
            r = CC.tmerge(L, a, a)
            ⊑(L, r, a) ? true : (a, r)
        end
        check("$lname tmerge Union{} identity") do
            (CC.tmerge(L, Union{}, a) === a && CC.tmerge(L, a, Union{}) === a) ? true : (a,)
        end
        check("$lname tmerge idempotent") do
            r = CC.tmerge(L, a, a)
            ⊑(L, r, a) ? true : (a, r)
        end
        check("$lname tmerge commutative (lattice-equal)") do
            CC.is_lattice_equal(L, CC.tmerge(L, a, b), CC.tmerge(L, b, a)) ? true : (a, b)
        end
        check("$lname tmerge associative (lattice-equal)") do
            CC.is_lattice_equal(L, CC.tmerge(L, CC.tmerge(L, a, b), c),
                CC.tmerge(L, a, CC.tmerge(L, b, c))) ? true : (a, b, c)
        end
        check("$lname tmerge_fast_path sound") do
            r = CC.tmerge_fast_path(L, a, b)
            r === nothing && return nothing
            ((r === a || r === b) && ⊑(L, a, r) && ⊑(L, b, r)) ? true : (a, b, r)
        end
        check("$lname tmerge_fast_path exact") do
            (a === Union{} || b === Union{}) && return nothing
            sa = ⊑(L, a, b); sb = ⊑(L, b, a)
            e = a === b ? a : (sa && CC.issimplertype(L, b, a)) ? b : (sa && sb) ? a :
                (sb && CC.issimplertype(L, a, b)) ? a : nothing
            CC.tmerge_fast_path(L, a, b) === e ? true : (a, b, e)
        end
        check("$lname issimplertype reflexive") do
            (a isa CC.LimitedAccuracy) && return nothing
            CC.issimplertype(L, a, a) ? true : (a,)
        end
    end
    # JLTypeLattice and the type-level helpers
    a = randtype(rng); b = rand(rng) < 0.5 ? randtype(rng) : deeper(rng, a); c = randtype(rng)
    check("jltype tmerge upper bound") do
        r = CC.tmerge(JLT, a, b)
        (a <: r && b <: r) ? true : (a, b, r)
    end
    check("jltype tmerge commutative") do
        CC.tmerge(JLT, a, b) == CC.tmerge(JLT, b, a) ? true : (a, b)
    end
    check("jltype tmerge associative") do
        CC.tmerge(JLT, CC.tmerge(JLT, a, b), c) == CC.tmerge(JLT, a, CC.tmerge(JLT, b, c)) ? true : (a, b, c)
    end
    check("typeinf = jltype on types") do
        CC.tmerge(LATTICES[1][2], a, b) === CC.tmerge(JLT, a, b) ? true : (a, b)
    end
    check("tmerge_types_slow upper bound") do
        r = CC.tmerge_types_slow(a, b)
        (a <: r && b <: r) ? true : (a, b, r)
    end
    check("tmerge_types_slow result simple enough") do
        r = CC.tmerge_types_slow(a, b)
        CC.issimpleenoughtype(r) ? true : (a, b, r)
    end
    check("tmerge_types_slow simple union kept") do
        u = Union{a, b}
        CC.issimpleenoughtype(u) || return nothing
        (a isa DataType || a isa UnionAll || a isa Union) || return nothing
        CC.tmerge_types_slow(a, b) == u ? true : (a, b)
    end
    ta = (t = randtype(rng, 3); t isa DataType && t.name === Tuple.name ? t :
          (try Tuple{Any[randtype(rng, 2) for _ in 1:rand(rng, 0:4)]...} catch; Tuple{} end))
    tb = rand(rng) < 0.3 ? deeper(rng, ta) : randtype(rng, 3)
    check("tuplemerge upper bound") do
        tb isa DataType && tb.name === Tuple.name || return nothing
        r = CC.tuplemerge(ta, tb)
        (ta <: r && tb <: r) ? true : (ta, tb, r)
    end
    check("tuplemerge commutative") do
        tb isa DataType && tb.name === Tuple.name || return nothing
        CC.tuplemerge(ta, tb) == CC.tuplemerge(tb, ta) ? true : (ta, tb)
    end
    ct = Any[randtype(rng, 2) for _ in 1:rand(rng, 1:4)]
    rand(rng) < 0.3 && (ct[end] = Vararg{ct[end]})
    check("tuple_tail_elem upper bound") do
        v = CC.tuple_tail_elem(CC.fallback_lattice, Union{}, ct)
        T = Base.unwrapva(v)
        all(x -> CC.unwraptv(Base.unwrapva(x)) <: T, ct) ? true : (ct, v)
    end
    # type-size limits, on the shapes recursion limiting compares
    cc = randtype(rng, 3)
    t = rand(rng) < 0.8 ? deeper(rng, rand(rng) < 0.5 ? cc : deeper(rng, cc)) : randtype(rng, 4)
    src = rand(rng) < 0.5 ? rand(rng, SOURCES_POOL) : randtype(rng, 2)
    d = rand(rng, 0:3); l = rand(rng, 0:3)
    check("limit_type_size upper bound") do
        r = CC.limit_type_size(t, cc, src, d, l)
        t <: r ? true : (t, cc, src, d, l, r)
    end
    check("limit_type_size result not more complex") do
        r = CC.limit_type_size(t, cc, src, d, l)
        r === t && return nothing
        srcs = Core.svec(Base.unwrap_unionall(cc), Base.unwrap_unionall(src))
        srcs[1] === srcs[2] && (srcs = Core.svec(srcs[1]))
        !CC.type_more_complex(r, cc, srcs, 1, d, l) ? true : (t, cc, src, d, l, r)
    end
    check("limit_type_size exact") do
        srcs = Core.svec(Base.unwrap_unionall(cc), Base.unwrap_unionall(src))
        srcs[1] === srcs[2] && (srcs = Core.svec(srcs[1]))
        e = if !CC.type_more_complex(t, cc, srcs, 1, d, l)
            t
        else
            r = CC._limit_type_size(t, cc, srcs, 1, l)
            t <: r ? r : (r2 = CC._limit_type_size(t, Any, srcs, 1, l); t <: r2 ? r2 : Any)
        end
        CC.limit_type_size(t, cc, src, d, l) === e ? true : (t, cc, src, d, l)
    end
    check("limit_type_size idempotent") do
        r = CC.limit_type_size(t, cc, src, d, l)
        CC.limit_type_size(r, cc, src, d, l) == r ? true : (t, cc, src, d, l, r)
    end
    ss = Core.svec(Any[Base.unwrap_unionall(rand(rng) < 0.5 ? rand(rng, SOURCES_POOL) : randtype(rng, 2)) for _ in 1:rand(rng, 1:2)]...)
    check("_limit_type_size upper bound") do
        r = CC._limit_type_size(t, cc, ss, 1, l)
        t <: r ? true : (t, cc, ss, l, r)
    end
    check("type_more_complex irreflexive") do
        !CC.type_more_complex(t, t, ss, rand(rng, 1:3), rand(rng, 0:3), l) ? true : (t,)
    end
    check("is_derived_type reflexive") do
        Base.has_free_typevars(t) && return nothing
        md = rand(rng, -1:3)
        CC.is_derived_type(t, t, md) == (md <= 1) ? true : (t, md)
    end
    u = randtype(rng, 4)
    check("union_count_abstract <= unionlen") do
        CC.union_count_abstract(u) <= Base.unionlen(u) ? true : (u,)
    end
    check("union_count_abstract counts non-dispatch members") do
        CC.union_count_abstract(u) == count(x -> !CC.isdispatchelem(x), Base.uniontypes(u)) ? true : (u,)
    end
    check("issimpleenoughtype exact") do
        ut = Base.unwrap_unionall(u)
        e = (ut isa DataType && ut.name.wrapper == u) ||
            (max(Base.unionlen(u), CC.union_count_abstract(u) + 1) <= CC.MAX_TYPEUNION_LENGTH &&
             CC.unioncomplexity(u) <= CC.MAX_TYPEUNION_COMPLEXITY)
        CC.issimpleenoughtype(u) == e ? true : (u,)
    end
    check("is_derived_type Union branch") do
        cu = Union{randtype(rng, 2), randtype(rng, 2)}
        cu isa Union || return nothing
        (Base.has_free_typevars(t) || Base.has_free_typevars(cu) || t === cu) && return nothing
        md = rand(rng, -1:3)
        CC.is_derived_type(t, cu, md) == (CC.is_derived_type(t, cu.a, md) || CC.is_derived_type(t, cu.b, md)) ?
            true : (t, cu, md)
    end
    check("unioncomplexity >= unionlen - 1") do
        CC.unioncomplexity(u) >= Base.unionlen(u) - 1 ? true : (u,)
    end
    check("issimpleenoughtype bounds unionlen") do
        CC.issimpleenoughtype(u) || return nothing
        ut = Base.unwrap_unionall(u)
        (ut isa DataType && ut.name.wrapper == u) && return nothing
        Base.unionlen(u) <= CC.MAX_TYPEUNION_LENGTH ? true : (u,)
    end
    # tname_intersect gives a common ancestor
    A = rand(rng, (Any, Integer, Int, Signed, Real, Number, AbsA, CA, WA, WB, AbsB, Some, Tuple,
                   Float64, AbstractArray, Vector, AbstractVector, DenseArray))
    B = rand(rng, (Any, Integer, Int, Signed, Real, Number, AbsA, CA, WA, WB, AbsB, Some, Tuple,
                   Float64, AbstractArray, Vector, AbstractVector, DenseArray))
    check("tname_intersect common ancestor") do
        an = Base.unwrap_unionall(A).name; bn = Base.unwrap_unionall(B).name
        r = CC.tname_intersect(an, bn)
        r === nothing && return nothing
        anc(x) = (x = Base.unwrap_unionall(x); ns = Any[x.name]; while x !== Any; x = supertype(x); push!(ns, x.name); end; ns)
        (r in anc(A.name.wrapper) && r in anc(B.name.wrapper)) ? true : (A, B, r)
    end
    check("tname_intersect finds shared ancestor") do
        an = Base.unwrap_unionall(A).name; bn = Base.unwrap_unionall(B).name
        anc(x) = (x = Base.unwrap_unionall(x); ns = Any[x.name]; while x !== Any; x = supertype(x); push!(ns, x.name); end; ns)
        common = filter(n -> n in anc(B.name.wrapper) && n !== Any.name, anc(A.name.wrapper))
        isempty(common) && return nothing
        (isabstracttype(A) || isabstracttype(B)) || return nothing
        CC.tname_intersect(an, bn) !== nothing ? true : (A, B, common)
    end
    check("tname_intersect exact") do
        A === B && return nothing
        an = Base.unwrap_unionall(A).name; bn = Base.unwrap_unionall(B).name
        an === bn && return nothing
        anc(x) = (x = Base.unwrap_unionall(x); ns = Any[x.name]; while x !== Any; x = supertype(x); push!(ns, x.name); end; ns)
        e = !(isabstracttype(an.wrapper) || isabstracttype(bn.wrapper)) ? nothing :
            an === Any.name ? an : an in anc(bn.wrapper) ? an : bn in anc(an.wrapper) ? bn : nothing
        CC.tname_intersect(an, bn) === e ? true : (A, B, e)
    end
    check("tmerge(ConstsLattice) on two different Consts merges their widened types") do
        x = rand(rng, VALUES); y = rand(rng, VALUES)
        x === y && return nothing
        CC.tmerge(CC.ConstsLattice(), Core.Const(x), Core.Const(y)) ==
            CC.tmerge(JLT, CC.widenconst(Core.Const(x)), CC.widenconst(Core.Const(y))) ? true : (x, y)
    end
    # widening along an ascending chain reaches a fixed point
    check("jltype widening chain converges in 30 steps") do
        x = randtype(rng, 2)
        for k in 1:30
            y = CC.tmerge(JLT, x, deeper(rng, x))
            y <: x && return true
            x = y
        end
        return (x, typesize(x))
    end
    check("typeinf partialstruct tmerge upper bound") do
        T = rand(rng, PS_TYPES)
        mk1() = begin
            vs = filter(v -> v isa T && !ismutable(v), VALUES)
            (!isempty(vs) && rand(rng) < 0.4) ? Core.Const(rand(rng, vs)) : partial_struct(g, 2, T)
        end
        p = mk1(); q = mk1()
        (valid(p) && valid(q)) || return nothing
        r = CC.tmerge_partial_struct(PARTIALS, p, q)
        r === nothing && return nothing
        (⊑(PARTIALS, p, r) && ⊑(PARTIALS, q, r)) ? true : (p, q, r)
    end
end

function main_props(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    g = Gen(Random.Xoshiro(seed))
    for k in 1:n
        props(g)
    end
    for (name, st) in sort(collect(STATS))
        println(rpad(name, 52), " checked=", st[1], " violated=", st[2], " threw=", st[3])
        for ex in get(EXAMPLES, name, String[])
            println("    ", first(ex, 700))
        end
    end
end

main_props()
