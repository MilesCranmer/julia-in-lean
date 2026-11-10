import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.cicache

/-!
Properties of `Compiler/src/cicache.jl`: the `WorldRange` laws and the `InternalCodeCache` view.
The model is `JuliaLean/Compiler/src/cicache.lean`.
-/

namespace JuliaLean.Proofs.Compiler.src.cicache

open JuliaLean.Registry JuliaLean.Compiler.CICache

/-! ## Constructors and accessors -/

/-- `WorldRange()` contains every `UInt` world, `WorldRange(w)` exactly `w`, and
`WorldRange(start:stop)` exactly the worlds of the `UnitRange`; `first`/`min_world` and
`last`/`max_world` read the two fields. -/
def WorldRangeCtors : Prop :=
  (∀ w, w ≤ typemaxUInt → WorldRange.all.contains w = true) ∧
  (∀ w v, (WorldRange.single w).contains v = true ↔ v = w) ∧
  (∀ start stop w, (WorldRange.ofUnitRange start stop).contains w = true ↔ start ≤ w ∧ w ≤ stop) ∧
  (∀ wr : WorldRange, wr.first = wr.minWorld ∧ wr.last = wr.maxWorld)

private theorem contains_iff (r : WorldRange) (w : Nat) :
    r.contains w = true ↔ r.minWorld ≤ w ∧ w ≤ r.maxWorld := by
  simp [WorldRange.contains]

theorem worldRangeCtors_proven : WorldRangeCtors := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    simp [WorldRange.all, WorldRange.contains, hw]
  · intro w v
    rw [contains_iff]; simp only [WorldRange.single]
    constructor <;> intro h <;> omega
  · intro start stop w
    rw [contains_iff]; simp only [WorldRange.ofUnitRange]
    split <;> constructor <;> intro h <;> omega
  · intro wr; exact ⟨rfl, rfl⟩

/-! ## `intersect` -/

/-- `intersect(a, b)` is the meet: it succeeds exactly when the two ranges share a world, the
result contains a world iff both arguments do, and it does not depend on the argument order.
When they share no world it throws the `AssertionError` of its `@assert`. -/
def IntersectMeet : Prop :=
  ∀ a b : WorldRange,
    (∀ r, intersect a b = .ok r → ∀ w, r.contains w = (a.contains w && b.contains w)) ∧
    ((∃ r, intersect a b = .ok r) ↔ ∃ w, a.contains w = true ∧ b.contains w = true) ∧
    ((¬ ∃ w, a.contains w = true ∧ b.contains w = true) →
      intersect a b = .error "julia:AssertionError: ret.min_world <= ret.max_world") ∧
    intersect a b = intersect b a

private theorem intersect_eq (a b : WorldRange) : intersect a b =
    if max a.minWorld b.minWorld ≤ min a.maxWorld b.maxWorld then
      .ok ⟨max a.minWorld b.minWorld, min a.maxWorld b.maxWorld⟩
    else .error "julia:AssertionError: ret.min_world <= ret.max_world" := by
  unfold intersect assertionError
  by_cases h : max a.minWorld b.minWorld ≤ min a.maxWorld b.maxWorld
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]; rfl
  · simp only [h, decide_false, Bool.not_false, if_false, if_true]; rfl

theorem intersectMeet_proven : IntersectMeet := by
  intro a b
  have hok : ∀ r, intersect a b = .ok r ↔
      (max a.minWorld b.minWorld ≤ min a.maxWorld b.maxWorld ∧
        r = ⟨max a.minWorld b.minWorld, min a.maxWorld b.maxWorld⟩) := by
    intro r
    rw [intersect_eq]
    by_cases h : max a.minWorld b.minWorld ≤ min a.maxWorld b.maxWorld
    · rw [if_pos h]
      constructor
      · intro e; cases e; exact ⟨h, rfl⟩
      · rintro ⟨_, rfl⟩; rfl
    · rw [if_neg h]
      constructor
      · intro e; cases e
      · rintro ⟨h', _⟩; exact absurd h' h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr w
    obtain ⟨_, rfl⟩ := (hok r).1 hr
    apply Bool.eq_iff_iff.2
    rw [Bool.and_eq_true, contains_iff, contains_iff, contains_iff]
    simp only
    omega
  · constructor
    · rintro ⟨r, hr⟩
      obtain ⟨h, _⟩ := (hok r).1 hr
      refine ⟨max a.minWorld b.minWorld, ?_, ?_⟩ <;> rw [contains_iff] <;> omega
    · rintro ⟨w, ha, hb⟩
      rw [contains_iff] at ha hb
      exact ⟨_, (hok _).2 ⟨by omega, rfl⟩⟩
  · intro hn
    rw [intersect_eq]
    have : ¬ (max a.minWorld b.minWorld ≤ min a.maxWorld b.maxWorld) := by
      intro h
      apply hn
      refine ⟨max a.minWorld b.minWorld, ?_, ?_⟩ <;> rw [contains_iff] <;> omega
    rw [if_neg this]
  · rw [intersect_eq, intersect_eq, Nat.max_comm a.minWorld, Nat.min_comm a.maxWorld]

/-! ## `union` -/

/-- `union(a, b)` of two ranges that overlap or touch is their hull: it does not throw, and the
result contains every world of `a` and of `b`. -/
def UnionHull : Prop :=
  ∀ a b : WorldRange, a.minWorld ≤ a.maxWorld → b.minWorld ≤ b.maxWorld →
    a.maxWorld ≤ typemaxUInt → b.maxWorld ≤ typemaxUInt →
    -- overlapping or adjacent
    (a.minWorld ≤ b.maxWorld + 1 ∧ b.minWorld ≤ a.maxWorld + 1) →
    ∃ r, union a b = .ok r ∧ ∀ w, (a.contains w = true ∨ b.contains w = true) → r.contains w = true

/-- Counterexample: `union(WorldRange(1, 10), WorldRange(2, 5))` is `WorldRange(1, 5)`, which
misses world 7 of the first range. (`union_self_zero_throws` is the second one.) -/
theorem unionHull_refuted : ¬ UnionHull := by
  intro h
  obtain ⟨r, hr, hc⟩ := h ⟨1, 10⟩ ⟨2, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have e : union ⟨1, 10⟩ ⟨2, 5⟩ = .ok ⟨1, 5⟩ := rfl
  rw [e] at hr
  cases hr
  exact absurd (hc 7 (Or.inl (by decide))) (by decide)

/-- `union(WorldRange(0, 5), WorldRange(0, 5))` throws the `AssertionError`: `b.min_world - 1`
wraps to `typemax(UInt)`. -/
theorem union_self_zero_throws :
    union ⟨0, 5⟩ ⟨0, 5⟩ = .error "julia:AssertionError: a.max_world >= b.min_world - 1" := rfl

private theorem union_eq (a b : WorldRange) (h : ¬ b.minWorld < a.minWorld)
    (hp : a.maxWorld ≥ uintPred b.minWorld) : union a b = .ok ⟨a.minWorld, b.maxWorld⟩ := by
  unfold union assertionError
  simp only [h, if_false, hp, decide_true, Bool.not_true, Bool.false_eq_true]; rfl

/-- The scope where `union` is right: for two ranges ordered by their start, not nested,
overlapping or touching, and with the later one not starting at world 0, `union(a, b)` (in
either argument order) is the hull `[a.min_world, b.max_world]`. -/
def UnionOrdered : Prop :=
  ∀ a b : WorldRange, 1 ≤ b.minWorld → a.minWorld < b.minWorld → b.minWorld ≤ a.maxWorld + 1 →
    a.maxWorld ≤ b.maxWorld →
    union a b = .ok ⟨a.minWorld, b.maxWorld⟩ ∧ union b a = .ok ⟨a.minWorld, b.maxWorld⟩

theorem unionOrdered_proven : UnionOrdered := by
  intro a b h1 h2 h3 _
  have hp : a.maxWorld ≥ uintPred b.minWorld := by
    simp only [uintPred]; split <;> omega
  constructor
  · exact union_eq a b (by omega) hp
  · unfold union assertionError
    simp only [h2, if_true, hp, decide_true, Bool.not_true, Bool.false_eq_true, if_false]; rfl

/-- The one call of `union` on world ranges, in `binding_access_range`
(`Compiler/src/abstractinterpretation.jl:4258-4279`), merges the range `total` found so far with
the range `this` of the partition found at `lookup_world = min_world(total) - 1`, when both give
the same access key. `this` contains that world and lies before `total` (the partitions along the
walk at an earlier world end before the partition that starts `total`), so the two ranges touch:
`this.max_world + 1 == total.min_world`. On every such pair `union(total, this)` does not throw
and returns exactly the worlds of the two ranges. -/
def UnionCallSite : Prop :=
  ∀ total this : WorldRange, this.minWorld ≤ this.maxWorld → this.maxWorld + 1 = total.minWorld →
    total.minWorld ≤ total.maxWorld →
    ∃ r, union total this = .ok r ∧ r = ⟨this.minWorld, total.maxWorld⟩ ∧
      ∀ w, r.contains w = true ↔ (this.contains w = true ∨ total.contains w = true)

theorem unionCallSite_proven : UnionCallSite := by
  intro total this h1 h2 h3
  have hp : this.maxWorld ≥ uintPred total.minWorld := by
    simp only [uintPred]; split <;> omega
  have hlt : this.minWorld < total.minWorld := by omega
  refine ⟨⟨this.minWorld, total.maxWorld⟩, ?_, rfl, ?_⟩
  · unfold union assertionError
    simp only [hlt, if_true, hp, decide_true, Bool.not_true, Bool.false_eq_true, if_false]; rfl
  · intro w
    simp only [contains_iff]
    omega

/-! ## `InternalCodeCache` -/

/-- An entry of the cache chain answers the query `[lo, hi]` for `owner`. -/
def Covers (owner lo hi : Nat) (e : CacheEntry) : Prop :=
  e.minWorld ≤ lo ∧ hi ≤ e.maxWorld ∧ e.owner = owner ∧ e.hasInferred = true

/-- `jl_rettype_inferred` returns the first entry of the chain whose world range contains the
query range, whose owner is the cache's owner and whose `inferred` is set, and `nothing` when no
entry qualifies. So `get(wvc, mi, default)` never returns code inferred for another owner, or
code whose validity does not cover all of `wvc.worlds`; `haskey` agrees with `get`; and
`getindex` returns what `get` finds, throwing `KeyError` otherwise. -/
def CacheViewSound : Prop :=
  ∀ (wvc : InternalCodeCache) (chain : List CacheEntry) (c : Nat),
    (wvc.get chain = some c ↔ ∃ pre e post, chain = pre ++ e :: post ∧ e.ci = c ∧
      Covers wvc.owner wvc.worlds.first wvc.worlds.last e ∧
      ∀ x ∈ pre, ¬ Covers wvc.owner wvc.worlds.first wvc.worlds.last x) ∧
    (wvc.get chain = none ↔ ∀ x ∈ chain, ¬ Covers wvc.owner wvc.worlds.first wvc.worlds.last x) ∧
    wvc.haskey chain = (wvc.get chain).isSome ∧
    (wvc.getindex chain = .ok c ↔ wvc.get chain = some c) ∧
    (wvc.get chain = none → wvc.getindex chain = .error "julia:KeyError: mi")

private theorem covers_iff (owner lo hi : Nat) (e : CacheEntry) :
    (e.minWorld ≤ lo && hi ≤ e.maxWorld && e.owner == owner && e.hasInferred) = true ↔
      Covers owner lo hi e := by
  simp [Covers, and_assoc]

private theorem rti_some (owner lo hi : Nat) :
    ∀ (chain : List CacheEntry) (c : Nat),
      jlRettypeInferred owner chain lo hi = some c ↔ ∃ pre e post, chain = pre ++ e :: post ∧
        e.ci = c ∧ Covers owner lo hi e ∧ ∀ x ∈ pre, ¬ Covers owner lo hi x
  | [], c => by simp [jlRettypeInferred]
  | e :: rest, c => by
    simp only [jlRettypeInferred]
    by_cases h : (e.minWorld ≤ lo && hi ≤ e.maxWorld && e.owner == owner && e.hasInferred) = true
    · rw [if_pos h]
      have hc := (covers_iff owner lo hi e).1 h
      constructor
      · intro hs; cases hs
        exact ⟨[], e, rest, rfl, rfl, hc, by simp⟩
      · rintro ⟨pre, e', post, hch, he', hc', hpre⟩
        cases pre with
        | nil => cases hch; simp [he']
        | cons p pre =>
          cases hch
          exact absurd hc (hpre _ (by simp))
    · rw [if_neg h]
      have hc : ¬ Covers owner lo hi e := fun hc => h ((covers_iff owner lo hi e).2 hc)
      rw [rti_some owner lo hi rest c]
      constructor
      · rintro ⟨pre, e', post, hch, he', hc', hpre⟩
        refine ⟨e :: pre, e', post, by simp [hch], he', hc', ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc
        · exact hpre x hx
      · rintro ⟨pre, e', post, hch, he', hc', hpre⟩
        cases pre with
        | nil => cases hch; exact absurd hc' hc
        | cons p pre =>
          cases hch
          exact ⟨pre, e', post, rfl, he', hc', fun x hx => hpre x (by simp [hx])⟩

private theorem rti_none (owner lo hi : Nat) :
    ∀ (chain : List CacheEntry),
      jlRettypeInferred owner chain lo hi = none ↔ ∀ x ∈ chain, ¬ Covers owner lo hi x
  | [] => by simp [jlRettypeInferred]
  | e :: rest => by
    simp only [jlRettypeInferred]
    by_cases h : (e.minWorld ≤ lo && hi ≤ e.maxWorld && e.owner == owner && e.hasInferred) = true
    · rw [if_pos h]
      simp only [reduceCtorEq, false_iff]
      intro hall
      exact hall e (by simp) ((covers_iff owner lo hi e).1 h)
    · rw [if_neg h, rti_none owner lo hi rest]
      have hc : ¬ Covers owner lo hi e := fun hc => h ((covers_iff owner lo hi e).2 hc)
      constructor
      · intro hr x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc
        · exact hr x hx
      · intro hr x hx; exact hr x (by simp [hx])

theorem cacheViewSound_proven : CacheViewSound := by
  intro wvc chain c
  refine ⟨rti_some _ _ _ chain c, rti_none _ _ _ chain, rfl, ?_, ?_⟩
  · simp only [InternalCodeCache.getindex]
    split
    · rename_i c' h'
      rw [h']
      constructor
      · intro e; cases e; rfl
      · intro e; cases e; rfl
    · rename_i h'
      rw [h']
      constructor
      · intro e; cases e
      · intro e; cases e
  · intro h
    simp only [InternalCodeCache.getindex, h]
    rfl

/-- `InternalCodeCache(owner, args...)` is the view of `owner` over `WorldRange(args...)`: its
lookups ask `jl_rettype_inferred` for exactly `[typemin, typemax]` with no arguments, `[w, w]`
for one world, the `UnitRange`'s worlds for a range, and `[a, b]` for the two fields. -/
def CacheArgsCtor : Prop :=
  ∀ (owner : Nat) (chain : List CacheEntry),
    (InternalCodeCache.ofArgs owner .none).get chain = jlRettypeInferred owner chain 0 typemaxUInt ∧
    (∀ w, (InternalCodeCache.ofArgs owner (.single w)).get chain = jlRettypeInferred owner chain w w) ∧
    (∀ a b, a ≤ b → (InternalCodeCache.ofArgs owner (.unitRange a b)).get chain =
      jlRettypeInferred owner chain a b) ∧
    (∀ a b, (InternalCodeCache.ofArgs owner (.fields a b)).get chain = jlRettypeInferred owner chain a b) ∧
    (∀ args, (InternalCodeCache.ofArgs owner args).owner = owner)

theorem cacheArgsCtor_proven : CacheArgsCtor := by
  intro owner chain
  refine ⟨rfl, fun _ => rfl, ?_, fun _ _ => rfl, fun _ => rfl⟩
  intro a b h
  simp [InternalCodeCache.ofArgs, InternalCodeCache.get, WorldRange.ofArgs, WorldRange.ofUnitRange,
    WorldRange.first, WorldRange.last, h]

/-- `setindex!(cache, ci, mi)` throws the `AssertionError` of `@assert ci.owner === cache.owner`
exactly when the owners differ. Otherwise it pushes `ci` to the newly inferred list exactly when
`mi.def` is a `Method`, and inserts `ci` into `mi`'s cache chain: afterwards `ci` is in the chain,
every other entry is still there, and so every view of the cache's owner over worlds inside
`ci`'s range finds code (`ci`, or an entry before it that also qualifies) when `ci` has
`inferred`. The chain entries of `ci`, if any, are snapshots of the same object (`e`). -/
def SetindexInserts : Prop :=
  ∀ (cache : InternalCodeCache) (e : CacheEntry) (isMethod : Bool) (chain : List CacheEntry),
    (e.owner ≠ cache.owner →
      cache.setindex e isMethod chain = .error "julia:AssertionError: ci.owner === cache.owner") ∧
    (e.owner = cache.owner → (∀ x ∈ chain, x.ci = e.ci → x = e) →
      ∃ chain', cache.setindex e isMethod chain = .ok (isMethod, chain') ∧ e ∈ chain' ∧
        (∀ x ∈ chain, x.ci ≠ e.ci → x ∈ chain') ∧
        ∀ wvc : InternalCodeCache, wvc.owner = cache.owner → e.hasInferred = true →
          e.minWorld ≤ wvc.worlds.first → wvc.worlds.last ≤ e.maxWorld →
          wvc.haskey chain' = true)

private theorem insert_mem (chain : List CacheEntry) (e : CacheEntry) (stop : CacheEntry → Bool)
    (hs : ∀ x ∈ chain, x.ci = e.ci → x = e) :
    e ∈ cacheInsertAt chain e stop ∧ ∀ x ∈ chain, x.ci ≠ e.ci → x ∈ cacheInsertAt chain e stop := by
  unfold cacheInsertAt
  have hsplit := List.takeWhile_append_dropWhile (p := fun o => !stop o) (l := chain)
  split
  · rename_i o post hd
    rw [hd] at hsplit
    have ho : o ∈ chain := by rw [← hsplit]; simp
    by_cases hoe : o.ci = e.ci
    · simp only [hoe, beq_self_eq_true, if_true]
      exact ⟨by rw [← hs o ho hoe]; exact ho, fun x hx _ => hx⟩
    · have : (o.ci == e.ci) = false := by simpa using hoe
      simp only [this, Bool.false_eq_true, if_false]
      refine ⟨by simp, ?_⟩
      intro x hx hxe
      rw [← hsplit] at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · simp [hx]
      · simp only [List.mem_append, List.mem_cons, List.mem_filter]
        right; right
        exact ⟨by simpa using hx, by simpa using hxe⟩
  · exact ⟨by simp, fun x hx _ => by simp [hx]⟩

theorem setindexInserts_proven : SetindexInserts := by
  intro cache e b chain
  constructor
  · intro h
    simp [InternalCodeCache.setindex, assertionError, h]; rfl
  · intro h hs
    obtain ⟨hmem, hkeep⟩ := insert_mem chain e _ hs
    refine ⟨jlMiCacheInsert chain e, ?_, hmem, hkeep, ?_⟩
    · simp [InternalCodeCache.setindex, h]; rfl
    · intro wvc hwo hinf hlo hhi
      have hcov : Covers wvc.owner wvc.worlds.first wvc.worlds.last e :=
        ⟨hlo, hhi, by rw [hwo]; exact h, hinf⟩
      simp only [InternalCodeCache.haskey]
      cases hg : jlRettypeInferred wvc.owner (jlMiCacheInsert chain e) wvc.worlds.first wvc.worlds.last with
      | some _ => rfl
      | none => exact absurd hcov ((rti_none _ _ _ _).1 hg e hmem)

def entries : List Entry := [
  { id := "compiler-cicache-worldrange-ctors", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["WorldRange()", "WorldRange(w::UInt)", "WorldRange(r::UnitRange)", "first(wr::WorldRange)", "last(wr::WorldRange)", "in(world::UInt, wr::WorldRange)", "min_world(wr::WorldRange)", "max_world(wr::WorldRange)"],
    statement := "WorldRange() contains every UInt world, WorldRange(w) exactly w, WorldRange(start:stop) exactly the worlds of the UnitRange; first/min_world and last/max_world read min_world and max_world.",
    source := "Compiler/src/cicache.jl:7-14 (what the constructors and accessors are for)",
    status := .proven, prop := ``WorldRangeCtors, thm := some ``worldRangeCtors_proven },
  { id := "compiler-cicache-intersect-meet", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["intersect(a::WorldRange, b::WorldRange)"],
    statement := "intersect(a, b) succeeds exactly when a and b share a world, contains a world iff both arguments do, is symmetric, and otherwise throws the AssertionError of its @assert.",
    source := "invariant: inference narrows valid_worlds with intersect (Compiler/src/inferencestate.jl:1334, abstractinterpretation.jl:415)",
    status := .proven, prop := ``IntersectMeet, thm := some ``intersectMeet_proven },
  { id := "compiler-cicache-union-hull", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["union(a::WorldRange, b::WorldRange)"],
    statement := "union(a, b) of two nonempty ranges that overlap or touch does not throw and contains every world of a and of b.",
    source := "the name, and the @assert (Compiler/src/cicache.jl:22-28), which rules out only a gap",
    status := .refuted, prop := ``UnionHull, thm := some ``unionHull_refuted,
    issue := "none found (queries: WorldRange union, cicache union, WorldRange intersect union; issues and prs)",
    notes := "union(WorldRange(1,10), WorldRange(2,5)) == WorldRange(1,5): a range nested in the other cuts it off. union(WorldRange(0,5), WorldRange(0,5)) throws AssertionError, since b.min_world - 1 wraps (union_self_zero_throws). Latent: the one caller, binding_access_range (Compiler/src/abstractinterpretation.jl:4269), only passes touching ranges, where union is right (compiler-cicache-union-ordered). Same on nightly 290d5bb5f5." },
  { id := "compiler-cicache-union-ordered", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["union(a::WorldRange, b::WorldRange)"],
    statement := "At its one call, in binding_access_range, union(total, this) gets a range this with this.max_world + 1 == total.min_world (the partition range at the world just before total); on every such pair it does not throw and returns exactly the worlds of both ranges, WorldRange(this.min_world, total.max_world).",
    source := "the call at Compiler/src/abstractinterpretation.jl:4258-4279 (union(total_validity, this_partition_validity) with lookup_world = total_min - 1)",
    status := .proven, prop := ``UnionCallSite, thm := some ``unionCallSite_proven,
    notes := "The touching shape is read from the source: this_partition_validity contains lookup_world = min_world(total_validity) - 1, and the walk at that world ends before the partition that starts total_validity. UnionOrdered (proven, no entry) is the same law for any ordered, non-nested, touching or overlapping pair." },
  { id := "compiler-cicache-view-sound", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["haskey(wvc::InternalCodeCache, mi::MethodInstance)", "get(wvc::InternalCodeCache, mi::MethodInstance, default)", "getindex(wvc::InternalCodeCache, mi::MethodInstance)"],
    statement := "get(wvc, mi, default) returns the first code instance of mi's cache chain whose owner is wvc.owner, whose inferred field is set and whose world range contains all of wvc.worlds, and the default when there is none; haskey agrees with get; getindex returns what get finds and throws KeyError otherwise.",
    source := "docstring Compiler/src/cicache.jl:30-36 (a cache stratified by world age ranges) and jl_rettype_inferred (src/gf.c:4272-4292)",
    status := .proven, prop := ``CacheViewSound, thm := some ``cacheViewSound_proven },
  { id := "compiler-cicache-args-ctor", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["InternalCodeCache(@nospecialize(owner), args...)"],
    statement := "InternalCodeCache(owner, args...) is the view of owner over WorldRange(args...): its lookups ask jl_rettype_inferred for [typemin, typemax] with no arguments, [w, w] for one world, the worlds of a UnitRange, and [a, b] for the two fields.",
    source := "Compiler/src/cicache.jl:41 (new(owner, WorldRange(args...)))",
    status := .proven, prop := ``CacheArgsCtor, thm := some ``cacheArgsCtor_proven },
  { id := "compiler-cicache-setindex-owner", juliaFile := "Compiler/src/cicache.jl",
    juliaFns := ["setindex!(cache::InternalCodeCache, ci::CodeInstance, mi::MethodInstance)"],
    statement := "setindex!(cache, ci, mi) throws an AssertionError exactly when ci.owner !== cache.owner; otherwise it pushes ci to the newly inferred list exactly when mi.def is a Method and inserts ci into mi's cache chain, keeping every other entry, so that afterwards every view of the cache's owner over worlds inside ci's range finds code when ci has inferred.",
    source := "Compiler/src/cicache.jl:44-52 (@assert ci.owner === cache.owner, then jl_mi_cache_insert, src/gf.c:803-857)",
    status := .proven, prop := ``SetindexInserts, thm := some ``setindexInserts_proven,
    notes := "The position jl_mi_cache_insert picks is modelled (jlMiCacheInsert) and difftested (r.iccSet); the statement only needs that ci ends up in the chain and nothing else drops out." }
]

end JuliaLean.Proofs.Compiler.src.cicache
