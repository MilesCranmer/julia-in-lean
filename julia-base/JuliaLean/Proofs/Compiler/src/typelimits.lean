import JuliaLean.Registry.Types
import JuliaLean.Proofs.Compiler.src.typelimits.Branches
import JuliaLean.Proofs.Compiler.src.typelimits.Laws

/-!
Properties of `Compiler/src/typelimits.jl` (`tmerge`, widening and complexity limits).

The statements are in `typelimits/`:
* `Bottom`: `Union{}` is the identity of `tmerge`, layer by layer and on the default lattices.
* `Laws`: the upper-bound and idempotence laws of `tmerge`, with the two refutations.
* `FastPath`: `tmerge_fast_path` only answers with an argument the other is `⊑`.
* `Small`: `tname_intersect`, `union_causes`, `union_count_abstract`, `issimpleenoughtype`,
  `n_initialized`.
* `Limits`: `limit_type_size`, `is_derived_type`, `is_derived_type_from_any`,
  `type_more_complex`.
* `Simpler`: `issimplertype` and `tmerge(::ConstsLattice)`.
* `Spec`: exact answers of `union_count_abstract`, `union_causes`, `issimpleenoughtype` and
  `tmerge_fast_path`.
* `Layers`: what each `tmerge` layer returns past `Union{}`.
* `Branches`: branch-by-branch answers of `limit_type_size`, `tname_intersect`,
  `issimplertype`, `is_derived_type` and `type_more_complex`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Registry

private def F : String := "Compiler/src/typelimits.jl"

/-- Registry entries of `Compiler/src/typelimits.jl`. -/
def entries : List Entry := [
  { id := "typelimits-tmerge-bottom-partials", juliaFile := F
    juliaFns := ["tmerge(::PartialsLattice, typea, typeb)", "tmerge_fast_path"]
    statement := "On PartialsLattice, tmerge(Union{}, x) and tmerge(x, Union{}) return x itself, for every lattice element x."
    source := "invariant: Union{} is the least element, so it is the identity of the join (Compiler/src/abstractlattice.jl:115-122)"
    status := .proven, prop := ``TmergeBottomPartials, thm := some ``tmergeBottomPartials_proven },
  { id := "typelimits-tmerge-bottom-conditionals", juliaFile := F
    juliaFns := ["tmerge(::ConditionalsLattice, typea, typeb)"]
    statement := "On ConditionalsLattice, tmerge with Union{} on either side returns a Conditional argument itself and passes every other argument and Union{} to the parent layer unchanged."
    source := "invariant: Union{} is the identity of the join; Compiler/src/typelimits.jl:539-546"
    status := .proven, prop := ``TmergeBottomConditionals, thm := some ``tmergeBottomConditionals_proven },
  { id := "typelimits-tmerge-bottom-interconditionals", juliaFile := F
    juliaFns := ["tmerge(::InterConditionalsLattice, typea, typeb)"]
    statement := "On InterConditionalsLattice, tmerge with Union{} on either side returns an InterConditional argument itself and passes every other argument and Union{} to the parent layer unchanged."
    source := "invariant: Union{} is the identity of the join; Compiler/src/typelimits.jl:579-586"
    status := .proven, prop := ``TmergeBottomInterConditionals, thm := some ``tmergeBottomInterConditionals_proven },
  { id := "typelimits-tmerge-bottom-mustaliases", juliaFile := F
    juliaFns := ["tmerge(::AnyMustAliasesLattice, typea, typeb)"]
    statement := "On MustAliasesLattice and InterMustAliasesLattice, tmerge with Union{} on either side returns an alias argument of the layer itself and passes every other argument and Union{} to the parent layer unchanged."
    source := "invariant: Union{} is the identity of the join; Compiler/src/typelimits.jl:589-607"
    status := .proven, prop := ``TmergeBottomMustAliases, thm := some ``tmergeBottomMustAliases_proven },
  { id := "typelimits-tmerge-bottom-inference", juliaFile := F
    juliaFns := ["tmerge(::InferenceLattice, typea, typeb)", "tmerge_limited"]
    statement := "On InferenceLattice, tmerge with Union{} on either side returns a LimitedAccuracy argument itself (through tmerge_limited) and passes every other argument and Union{} to the parent layer unchanged."
    source := "invariant: Union{} is the identity of the join; Compiler/src/typelimits.jl:450-452,501-507"
    status := .proven, prop := ``TmergeBottomInference, thm := some ``tmergeBottomInference_proven },
  { id := "typelimits-tmerge-bottom-jltype", juliaFile := F
    juliaFns := ["tmerge(::JLTypeLattice, typea::AnyType, typeb::AnyType)"]
    statement := "On JLTypeLattice, tmerge(Union{}, T) and tmerge(T, Union{}) return T for every type T, failing only where isconcretetype(T) fails."
    source := "invariant: Union{} is the identity of the join; Compiler/src/typelimits.jl:775-789"
    status := .proven, prop := ``TmergeBottomJLType, thm := some ``tmergeBottomJLType_proven },
  { id := "typelimits-tmerge-bottom-default", juliaFile := F
    juliaFns := ["tmerge(::InferenceLattice, typea, typeb)", "tmerge(::AnyMustAliasesLattice, typea, typeb)", "tmerge(::ConditionalsLattice, typea, typeb)", "tmerge(::InterConditionalsLattice, typea, typeb)", "tmerge(::PartialsLattice, typea, typeb)"]
    statement := "On typeinf_lattice, ipo_lattice and optimizer_lattice, tmerge(Union{}, x) and tmerge(x, Union{}) return x itself for every lattice element x."
    source := "invariant: Union{} is the identity of the join (Compiler/src/abstractlattice.jl:115-122); lattices from Compiler/src/types.jl:649-651"
    status := .proven, prop := ``TmergeBottomDefault, thm := some ``tmergeBottomDefault_proven },
  { id := "typelimits-tmerge-conditional-idempotent", juliaFile := F
    juliaFns := ["tmerge(::ConditionalsLattice, typea, typeb)"]
    statement := "On typeinf_lattice, tmerge(a, a) ⊑ a for every lattice element a."
    source := "lattice law inference relies on: tmerge(a, a) ⊑ a (compiler/PLAYBOOK.md); tmerge is a lattice join (Compiler/src/abstractlattice.jl:115-122)"
    status := .refuted, prop := ``TmergeIdempotentTypeinf, thm := some ``tmergeIdempotentTypeinf_refuted
    issue := "none found (queries: tmerge Conditional isdefined; isdefined Conditional merge; @isdefined UndefVarError effects nothrow phi; Conditional isdefined tmerge; isdefined conditional lost; PRs: isdefined Conditional, Conditional isdefined, isdefined refinement slot, tmerge conditional); related #55545, #62212"
    notes := "Counterexample Conditional(1, 0, Int, Int; isdefined=true), the element `@isdefined x` gives: tmerge returns Bool. With different then/else types the rebuilt Conditional drops isdefined. Visible on master: a merge of two `@isdefined(x)` results makes inference keep an UndefVarError path (repro/typelimits-tmerge-conditional-idempotent.jl); 1.13.3 shows the same tmerge result but infers the reproducer as nothrow." },
  { id := "typelimits-tmerge-limited-upper-bound", juliaFile := F
    juliaFns := ["tmerge_limited(::InferenceLattice, typea, typeb)", "merge_causes(causesa, causesb)"]
    statement := "On typeinf_lattice, tmerge of two LimitedAccuracy elements is ⊒ both arguments."
    source := "lattice law: tmerge is an upper bound (Compiler/src/abstractlattice.jl:115-122), with ⊑ on LimitedAccuracy from Compiler/src/typelattice.jl:401-418"
    status := .refuted, prop := ``TmergeUpperBoundLimited, thm := some ``tmergeUpperBoundLimited_refuted
    issue := "none found (queries: merge_causes; LimitedAccuracy causes tmerge; tmerge_limited; PRs: LimitedAccuracy, merge_causes)"
    notes := "LimitedAccuracy(Int, {s1}) and LimitedAccuracy(Int, {s2}): merge_causes returns the union {s1, s2}, and ⊑ needs the result's causes to be a subset of each argument's. No user-visible effect found (P2)." },
  { id := "typelimits-tmerge-upper-bound", juliaFile := F
    juliaFns := ["tmerge(::InferenceLattice, typea, typeb)", "tmerge(::ConstsLattice, typea, typeb)", "tmerge(::ConditionalsLattice, typea, typeb)"]
    statement := "On typeinf_lattice, tmerge(a, b) is ⊒ both arguments."
    source := "lattice law: tmerge is an upper bound (Compiler/src/abstractlattice.jl:115-122)"
    status := .todo, prop := ``TmergeUpperBoundTypeinf, thm := none
    notes := "False on the pinned Julia beyond the LimitedAccuracy entry, both times through ⊑ (Compiler/src/typelattice.jl, not this file): tmerge(PartialTypeVar(T), Const(1)) = Union{Int, TypeVar}, and ⊑(::ConstsLattice, ::PartialTypeVar, b) is b === TypeVar || a === b (typelattice.jl:561-562), already filed as compiler-tl-sqsub-widenconst-upper (no result of tmerge can be ⊒ both PartialTypeVar and Const(1), so this is that bug, not a separate tmerge bug); tmerge(Const(true), Conditional(s, X, Y)) = Conditional(s, Any, Y), and Const(true) ⊑ Conditional needs elsetype === Union{} (typelattice.jl:434-442). The Lean refutation needs jl_type_union and the JLTypeLattice fast path, which reach jl_egal and Std.Range loops; both are defined by well-founded recursion and do not reduce. Not filed." },
  { id := "typelimits-tmerge-upper-bound-jltype", juliaFile := F
    juliaFns := ["tmerge(::JLTypeLattice, typea::AnyType, typeb::AnyType)", "tmerge_types_slow", "tuplemerge"]
    statement := "On JLTypeLattice, tmerge(a, b) is a supertype of both types."
    source := "lattice law: tmerge is an upper bound (Compiler/src/abstractlattice.jl:115-122)"
    status := .todo, prop := ``TmergeUpperBoundJLType, thm := none
    notes := "Holds on 3000 smoke-test cases on the pinned Julia (difftest/compiler/typelimits_props.jl, seeds 1-2). Unproven: needs the union, tuple and wrapper laws of the subtype model." },
  { id := "typelimits-tmerge-fast-path-sound", juliaFile := F
    juliaFns := ["tmerge_fast_path(lattice, typea, typeb)"]
    statement := "tmerge_fast_path answers Union{}'s other argument directly, and otherwise only answers with an argument that the other argument is egal to or ⊑."
    source := "Compiler/src/typelimits.jl:413-425 (fast paths of the join)"
    status := .proven, prop := ``TmergeFastPathSound, thm := some ``tmergeFastPathSound_proven },
  { id := "typelimits-union-causes-superset", juliaFile := F
    juliaFns := ["union_causes(causesa, causesb)"]
    statement := "union_causes(a, b) contains every cause of a and of b."
    source := "Compiler/src/typelimits.jl:427-435 (union of IdSets)"
    status := .proven, prop := ``UnionCausesSuperset, thm := some ``unionCausesSuperset_proven },
  { id := "typelimits-tname-intersect-arg", juliaFile := F
    juliaFns := ["tname_intersect(aname, bname)"]
    statement := "tname_intersect(a, b) answers nothing or one of its arguments, never a third (common ancestor) name; it answers a for (a, a) and Any for (Any, b)."
    source := "Compiler/src/typelimits.jl:791-816"
    status := .proven, prop := ``TnameIntersectArg, thm := some ``tnameIntersectArg_proven
    notes := "Shows the lead in compiler/PERF_LEADS.md: siblings such as Signed and AbstractFloat are never joined at Real." },
  { id := "typelimits-union-count-abstract", juliaFile := F
    juliaFns := ["union_count_abstract(x::Union)", "union_count_abstract(x)"]
    statement := "union_count_abstract(t) is at most unionlen(t), and equals it when no member of the union is a dispatch element."
    source := "Compiler/src/typelimits.jl:315-316, used by issimpleenoughtype (318-323)"
    status := .proven, prop := ``UnionCountAbstractSpec, thm := some ``unionCountAbstractSpec_proven },
  { id := "typelimits-issimpleenoughtype-bound", juliaFile := F
    juliaFns := ["issimpleenoughtype(t)"]
    statement := "A type issimpleenoughtype accepts is its type name's wrapper, or has at most 3 union members, at most 2 of them non-dispatch, and union complexity at most 3."
    source := "Compiler/src/typelimits.jl:7-8,318-323"
    status := .proven, prop := ``IssimpleenoughtypeBound, thm := some ``issimpleenoughtypeBound_proven },
  { id := "typelimits-issimpleenoughtype-complete", juliaFile := F
    juliaFns := ["issimpleenoughtype(t)"]
    statement := "Every type with at most 3 union members, at most 2 of them non-dispatch, and union complexity at most 3 is simple enough."
    source := "Compiler/src/typelimits.jl:7-8,318-323"
    status := .proven, prop := ``IssimpleenoughtypeComplete, thm := some ``issimpleenoughtypeComplete_proven },
  { id := "typelimits-n-initialized-partialstruct", juliaFile := F
    juliaFns := ["n_initialized(pstruct::PartialStruct)"]
    statement := "n_initialized of a PartialStruct is the number of leading fields whose undefs entry is false."
    source := "Compiler/src/typelimits.jl:334-338"
    status := .proven, prop := ``NInitializedPartialStructSpec, thm := some ``nInitializedPartialStructSpec_proven },
  { id := "typelimits-n-initialized-const", juliaFile := F
    juliaFns := ["n_initialized(t::Const)"]
    statement := "n_initialized of a Const is the number of leading defined fields of its value, at most nfields."
    source := "Compiler/src/typelimits.jl:330-333"
    status := .proven, prop := ``NInitializedConstSpec, thm := some ``nInitializedConstSpec_proven },
  { id := "typelimits-limit-type-size-upper", juliaFile := F
    juliaFns := ["limit_type_size(t, compare, source, allowed_tupledepth, allowed_tuplelen)"]
    statement := "limit_type_size(t, ...) is a supertype of t, assuming subtyping is reflexive, has Any on top and does not depend on the fresh-variable counter."
    source := "Compiler/src/typelimits.jl:14-33 (\"no new values may be introduced\", the t <: r checks)"
    status := .proven, prop := ``LimitTypeSizeUpper, thm := some ``limitTypeSizeUpper_proven },
  { id := "typelimits-limit-type-size-self", juliaFile := F
    juliaFns := ["limit_type_size(t, compare, source, allowed_tupledepth, allowed_tuplelen)", "type_more_complex"]
    statement := "limit_type_size(t, t, source, ...) returns t, assuming === is reflexive."
    source := "Compiler/src/typelimits.jl:14-33,228-237"
    status := .proven, prop := ``LimitTypeSizeSelf, thm := some ``limitTypeSizeSelf_proven },
  { id := "typelimits-limit-type-size-inner-upper", juliaFile := F
    juliaFns := ["_limit_type_size(t, c, sources, depth, allowed_tuplelen)", "__limit_type_size(t, c, sources, depth, allowed_tuplelen)"]
    statement := "_limit_type_size(t, c, ...) is a supertype of t."
    source := "Compiler/src/typelimits.jl:86-87 (\"a type of greater size\"); the caller re-checks it (lines 22-28, #36407)"
    status := .todo, prop := ``LimitTypeSizeInnerUpper, thm := none
    notes := "Held on 1800 smoke-test cases on the pinned Julia; the source comment says it can fail for a type variable in invariant and covariant positions. Unproven: needs subtyping of wrappers, Vararg and Type{<:Q}." },
  { id := "typelimits-is-derived-type-base", juliaFile := F
    juliaFns := ["is_derived_type(t, c, mindepth)"]
    statement := "is_derived_type answers false when t or c has free type variables, and is_derived_type(t, t, d) is d ≤ 1 for t without free type variables, assuming === is reflexive."
    source := "Compiler/src/typelimits.jl:37-46"
    status := .proven, prop := ``IsDerivedTypeBase, thm := some ``isDerivedTypeBase_proven },
  { id := "typelimits-is-derived-type-from-any", juliaFile := F
    juliaFns := ["is_derived_type_from_any(t, sources, mindepth)"]
    statement := "is_derived_type_from_any(t, sources, d) is true exactly when is_derived_type(t, s, d) is true for some source s."
    source := "Compiler/src/typelimits.jl:79-84"
    status := .proven, prop := ``IsDerivedTypeFromAnySpec, thm := some ``isDerivedTypeFromAnySpec_proven },
  { id := "typelimits-type-more-complex-trivial", juliaFile := F
    juliaFns := ["type_more_complex(t, c, sources, depth, tupledepth, allowed_tuplelen)"]
    statement := "type_more_complex(t, c, ...) is false when t === c, t === Union{}, or t is a DataType without parameters, assuming === is reflexive."
    source := "Compiler/src/typelimits.jl:228-237"
    status := .proven, prop := ``TypeMoreComplexTrivial, thm := some ``typeMoreComplexTrivial_proven },
  { id := "typelimits-type-more-complex-unionall", juliaFile := F
    juliaFns := ["type_more_complex(t, c, sources, depth, tupledepth, allowed_tuplelen)"]
    statement := "With no sources and tuple depth 0, a non-trivial type that is not a UnionAll is more complex than a UnionAll comparison."
    source := "Compiler/src/typelimits.jl:242-246 (allow wrapping type with fewer UnionAlls than comparison only if in a covariant context)"
    status := .proven, prop := ``TypeMoreComplexUnionAll, thm := some ``typeMoreComplexUnionAll_proven },
  { id := "typelimits-issimplertype", juliaFile := F
    juliaFns := ["issimplertype(𝕃, typea, typeb)"]
    statement := "Every non-limited element is simpler than itself; a native type is simpler than b exactly when it is egal to b or simple enough; a PartialStruct is simpler than b only when b is egal to it, a Const or a PartialStruct."
    source := "Compiler/src/typelimits.jl:340-411"
    status := .proven, prop := ``IssimplertypeSpec, thm := some ``issimplertypeSpec_proven },
  { id := "typelimits-tmerge-consts", juliaFile := F
    juliaFns := ["tmerge(::ConstsLattice, typea, typeb)"]
    statement := "On ConstsLattice, a Const or PartialTypeVar merged with itself is returned unchanged, and elements that are neither are merged by JLTypeLattice unchanged."
    source := "Compiler/src/typelimits.jl:763-773"
    status := .proven, prop := ``TmergeConstsSpec, thm := some ``tmergeConstsSpec_proven },
  { id := "typelimits-union-count-abstract-exact", juliaFile := F
    juliaFns := ["union_count_abstract(x::Union)", "union_count_abstract(x)"]
    statement := "union_count_abstract(t) is the number of members of t that are not dispatch elements; for a non-Union x it is 0 when isdispatchelem(x) and 1 otherwise."
    source := "Compiler/src/typelimits.jl:315-316"
    status := .proven, prop := ``UnionCountAbstractExact, thm := some ``unionCountAbstractExact_proven },
  { id := "typelimits-union-causes-exact", juliaFile := F
    juliaFns := ["union_causes(causesa, causesb)"]
    statement := "union_causes(a, b) returns b itself when a ⊆ b, else a itself when b ⊆ a, else a fresh set; its members are exactly those of a and b."
    source := "Compiler/src/typelimits.jl:427-435"
    status := .proven, prop := ``UnionCausesExact, thm := some ``unionCausesExact_proven },
  { id := "typelimits-issimpleenoughtype-exact", juliaFile := F
    juliaFns := ["issimpleenoughtype(t)"]
    statement := "issimpleenoughtype(t) is true when unwrap_unionall(t) is a DataType whose wrapper == t, and otherwise is max(unionlen(t), union_count_abstract(t) + 1) ≤ 3 && unioncomplexity(t) ≤ 3."
    source := "Compiler/src/typelimits.jl:318-323"
    status := .proven, prop := ``IssimpleenoughtypeExact, thm := some ``issimpleenoughtypeExact_proven },
  { id := "typelimits-tmerge-fast-path-exact", juliaFile := F
    juliaFns := ["tmerge_fast_path(lattice, typea, typeb)"]
    statement := "For a, b not Union{}, tmerge_fast_path answers a when a === b, else b when a ⊑ b and issimplertype(b, a), else a when a ⊑ b and b ⊑ a, else a when b ⊑ a and issimplertype(a, b), else nothing."
    source := "Compiler/src/typelimits.jl:413-425"
    status := .proven, prop := ``TmergeFastPathExact, thm := some ``tmergeFastPathExact_proven },
  { id := "typelimits-tmerge-inference-dispatch", juliaFile := F
    juliaFns := ["tmerge(::InferenceLattice, typea, typeb)", "tmerge_limited"]
    statement := "On InferenceLattice, two non-LimitedAccuracy elements are handed to the layer below unchanged; LimitedAccuracy(T, causes) merged with an incomparable non-Union{} b gives LimitedAccuracy(tmerge(T, b), causes)."
    source := "Compiler/src/typelimits.jl:450-507"
    status := .proven, prop := ``TmergeInferenceDispatch, thm := some ``tmergeInferenceDispatch_proven },
  { id := "typelimits-tmerge-interconditionals", juliaFile := F
    juliaFns := ["tmerge(::InterConditionalsLattice, typea, typeb)"]
    statement := "On InterConditionalsLattice, same-slot InterConditionals merge then and else types below and give InterConditional(slot, then, else) when they differ; different slots give Const(v) for a common known Bool v, else Bool; an InterConditional against a non-InterConditional, non-Const, non-Union{} element is widened and handed down; two non-InterConditionals are handed down unchanged."
    source := "Compiler/src/typelimits.jl:549-587"
    status := .proven, prop := ``TmergeInterConditionalsSpec, thm := some ``tmergeInterConditionalsSpec_proven },
  { id := "typelimits-tmerge-mustaliases", juliaFile := F
    juliaFns := ["tmerge(::AnyMustAliasesLattice, typea, typeb)"]
    statement := "On MustAliasesLattice, two same-alias MustAliases whose vartyps widen to === types keep the alias with vartyp and fldtyp merged below (update_mustalias); a MustAlias against a non-alias, non-Union{} element is widened to its fldtyp and handed down; non-aliases are handed down unchanged. The same for InterMustAlias."
    source := "Compiler/src/typelimits.jl:589-607"
    status := .proven, prop := ``TmergeMustAliasesSpec, thm := some ``tmergeMustAliasesSpec_proven },
  { id := "typelimits-tmerge-partials", juliaFile := F
    juliaFns := ["tmerge(::PartialsLattice, typea, typeb)"]
    statement := "On PartialsLattice, past the fast path: PartialStruct/Const pairs that are not === give tmerge_partial_struct's answer; same-type PartialOpaques give PartialOpaque(typ, tmerge(envs), parent, source) when source and parent are the same, else the type; PartialTasks give PartialTask(tmerge(fetch types)) or Task when that is Any; other pairs are handed down unchanged."
    source := "Compiler/src/typelimits.jl:702-761"
    status := .proven, prop := ``TmergePartialsSpec, thm := some ``tmergePartialsSpec_proven },
  { id := "typelimits-tmerge-consts-dispatch", juliaFile := F
    juliaFns := ["tmerge(::ConstsLattice, typea, typeb)"]
    statement := "On ConstsLattice, unless both are Const/PartialTypeVar and ===, each Const or PartialTypeVar is widened to its type and the pair is merged by JLTypeLattice; other arguments are passed on unchanged."
    source := "Compiler/src/typelimits.jl:763-773"
    status := .proven, prop := ``TmergeConstsDispatch, thm := some ``tmergeConstsDispatch_proven },
  { id := "typelimits-tmerge-jltype-exact", juliaFile := F
    juliaFns := ["tmerge(::JLTypeLattice, typea::AnyType, typeb::AnyType)"]
    statement := "On JLTypeLattice, two equal concrete types give a; otherwise, when each is concrete or a Type{T}, Union{a, b}; otherwise the tmerge_fast_path answer when there is one, else tmerge_types_slow(a, b)."
    source := "Compiler/src/typelimits.jl:775-789"
    status := .proven, prop := ``TmergeJLTypeExact, thm := some ``tmergeJLTypeExact_proven },
  { id := "typelimits-limit-type-size-exact", juliaFile := F
    juliaFns := ["limit_type_size(t, compare, source, allowed_tupledepth, allowed_tuplelen)"]
    statement := "limit_type_size(t, ...) is t when type_more_complex is false; otherwise r = _limit_type_size(t, compare, ...) when t <: r, else r' = _limit_type_size(t, Any, ...) when t <: r', else Any."
    source := "Compiler/src/typelimits.jl:17-33"
    status := .proven, prop := ``LimitTypeSizeExact, thm := some ``limitTypeSizeExact_proven },
  { id := "typelimits-tname-intersect-exact", juliaFile := F
    juliaFns := ["tname_intersect(aname, bname)"]
    statement := "For two different names, tname_intersect is nothing when neither wrapper is abstract; a when the walk up from b meets a; otherwise b when a's ancestor at b's height has name b, else nothing."
    source := "Compiler/src/typelimits.jl:791-816"
    status := .proven, prop := ``TnameIntersectExact, thm := some ``tnameIntersectExact_proven },
  { id := "typelimits-issimplertype-branches", juliaFile := F
    juliaFns := ["issimplertype(𝕃, typea, typeb)"]
    statement := "issimplertype on Conditional, InterConditional, MustAlias, InterMustAlias, PartialOpaque and PartialTask, branch by branch: same-slot (alias) pairs compare their component types recursively (and issubalias for aliases), a Conditional is simpler than a Const, PartialOpaque is never simpler, and other pairings are false."
    source := "Compiler/src/typelimits.jl:356-404"
    status := .proven, prop := ``IssimplertypeBranches, thm := some ``issimplertypeBranches_proven },
  { id := "typelimits-issimplertype-partialstruct", juliaFile := F
    juliaFns := ["issimplertype(𝕃, typea, typeb)"]
    statement := "A PartialStruct a (not === b, widened type simpler, b a Const or PartialStruct with at least as many initialized fields) is simpler than b exactly when every field is lattice-equal to its declared field type, to its type name's wrapper, or to getfield_tfunc(b, i)."
    source := "Compiler/src/typelimits.jl:345-355"
    status := .proven, prop := ``IssimplertypePartialStruct, thm := some ``issimplertypePartialStruct_proven },
  { id := "typelimits-is-derived-type-branches", juliaFile := F
    juliaFns := ["is_derived_type(t, c, mindepth)"]
    statement := "is_derived_type(t, c, d) without free typevars: d ≤ 1 when t === c; otherwise, with Varargs unwrapped, found in either Union member, in a UnionAll's bound or body, in a Type{T}'s T, for another DataType as a strict supertype (t a DataType) or in a parameter at d - 1, and false for anything else."
    source := "Compiler/src/typelimits.jl:37-77"
    status := .proven, prop := ``IsDerivedTypeBranches, thm := some ``isDerivedTypeBranches_proven },
  { id := "typelimits-type-more-complex-branches", juliaFile := F
    juliaFns := ["type_more_complex(t, c, sources, depth, tupledepth, allowed_tuplelen)"]
    statement := "type_more_complex past its trivial cases, branch by branch: the TypeVar, Union, Int, Type{T} and DataType rules, including the parameter-by-parameter loop (true exactly when some tP[i] is more complex than cP[i + ntail]) and true for a DataType against a non-DataType."
    source := "Compiler/src/typelimits.jl:228-313"
    status := .proven, prop := ``TypeMoreComplexBranches, thm := some ``typeMoreComplexBranches_proven },
  { id := "typelimits-tuplemerge-upper", juliaFile := F
    juliaFns := ["tuplemerge(a::DataType, b::DataType)"]
    statement := "tuplemerge(a, b) is a supertype of both tuple types."
    source := "Compiler/src/typelimits.jl:942-1022 (the inverse of switchtupleunion, used as a join)"
    status := .todo, prop := ``TuplemergeUpper, thm := none
    notes := "Held on 576 smoke-test cases on the pinned Julia. Unproven, and a concrete Lean check is blocked: the model's for-loops over Std.Range and jl_egal do not reduce." },
  { id := "typelimits-tmerge-types-slow-upper", juliaFile := F
    juliaFns := ["tmerge_types_slow(typea::AnyType, typeb::AnyType)"]
    statement := "tmerge_types_slow(a, b) is a supertype of both types."
    source := "Compiler/src/typelimits.jl:818-940"
    status := .todo, prop := ``TmergeTypesSlowUpper, thm := none
    notes := "Held on 1800 smoke-test cases on the pinned Julia. Unproven; the same reduction limits as tuplemerge." },
  { id := "typelimits-tmerge-partial-struct-upper", juliaFile := F
    juliaFns := ["tmerge_partial_struct(𝕃::PartialsLattice, typea, typeb)"]
    statement := "tmerge_partial_struct, when it returns a PartialStruct, returns an upper bound of both arguments."
    source := "Compiler/src/typelimits.jl:609-700"
    status := .todo, prop := ``TmergePartialStructUpper, thm := none
    notes := "Held on 184 smoke-test cases with valid PartialStruct inputs (fields ⊑ declared field types) on the pinned Julia; invalid inputs the generator builds break it. Unproven." }
]

end JuliaLean.Proofs.Compiler.src.typelimits
