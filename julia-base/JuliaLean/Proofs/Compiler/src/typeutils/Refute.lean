import JuliaLean.Proofs.Compiler.src.typeutils.Split

/-!
Counterexamples on a concrete universe, checked by kernel evaluation of the model
(`decide +kernel`) and reproduced on the pinned Julia (`repro/compiler-unionsplit-*.jl`).

The universe has `abstract type AR end`, `abstract type R{T} <: AR end`, `abstract type X end`,
`struct X1 <: X end`, `struct X2 <: X end`, `struct Y end`, `Nothing` and
`mutable struct M end`.

Each subtype check is stated against a raw `Union` node (`Val.union`) rather than a normalized
`Union{...}`: subtyping treats both alike, and building the normalized union would call the C
model's union sorting, whose string comparisons the kernel cannot evaluate.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

set_option maxHeartbeats 0

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

def usTvT : Val := .typevar 7 "T" .bottom anyType
def usAR : Val := .datatype "Main.AR" []
def usRName : String := "Main.R"
def usX : Val := .datatype "Main.X" []
def usX1 : Val := .datatype "Main.X1" []
def usX2 : Val := .datatype "Main.X2" []
def usY : Val := .datatype "Main.Y" []

/-- `mutable struct M end`. -/
def usMName : TypeName :=
  { name := "Main.M", abstract := false, mutable := true, wrapper := .datatype "Main.M" [],
    super := some anyType }

/-- The universe of the counterexamples. -/
def usE : CEnv where
  types := { names := [
    { name := "Core.Any", abstract := true, mutable := false, wrapper := anyType, super := none },
    { name := "Core.Tuple", abstract := false, mutable := false,
      wrapper := .datatype "Core.Tuple" [.vararg (some anyType) none], super := some anyType },
    { name := "Main.AR", abstract := true, mutable := false, wrapper := usAR, super := some anyType },
    { name := usRName, abstract := true, mutable := false,
      wrapper := .unionall 3 "T" .bottom anyType (.datatype usRName [.typevar 3 "T" .bottom anyType]),
      super := some usAR },
    { name := "Main.X", abstract := true, mutable := false, wrapper := usX, super := some anyType },
    { name := "Main.X1", abstract := false, mutable := false, wrapper := usX1, super := some usX },
    { name := "Main.X2", abstract := false, mutable := false, wrapper := usX2, super := some usX },
    { name := "Main.Y", abstract := false, mutable := false, wrapper := usY, super := some anyType },
    { name := "Core.Nothing", abstract := false, mutable := false,
      wrapper := .datatype "Core.Nothing" [], super := some anyType },
    usMName ], layouts := [] }

/-! ## `typesubtract` loses values of a `UnionAll` over a `Union` -/

/-- `typesubtract(a, b, max_union_splitting)` returns "an upper-bound on type `a` with type `b`
removed ... such that `return <: a` && `Union{return, b} == Union{a, b}`"
(`Compiler/src/typeutils.jl:114-116`). Its first consequence: `a <: Union{return, b}`. -/
def TypesubtractCoversA : Prop :=
  ∀ n₁ n₂ E a b m s r s₁, (typesubtract n₁ E a b m).run s = .ok (r, s₁) →
    Returns (issub n₂ E a (.union r b)) (· = true)

/-- `Union{Tuple{T,T}, R{T}} where T`. -/
def usA : Val :=
  .unionall 7 "T" .bottom anyType (.union (.datatype usRName [usTvT]) (.datatype tupleName [usTvT, usTvT]))

/-- `typesubtract(A, AR, 4)` is `Tuple{T,T} where T`, and `A ⋢ Union{Tuple{T,T} where T, AR}`.
The `Union` branch (`Compiler/src/typeutils.jl:122-126`) rewraps each member in its own `UnionAll`;
alone, `Tuple{T,T} where T` is diagonal, but in `A` the variable also occurs in `R{T}`, so `A`
contains `Tuple{Int8, Int}`, which the result drops. -/
theorem typesubtract_cex :
    (match (typesubtract 25 usE usA usAR 4).run 100 with
      | .ok (r, _) => (match (issub 25 usE usA (.union r usAR)).run 100 with
        | .ok (false, _) => true | _ => false)
      | _ => false) = true := by decide +kernel

theorem typesubtractCoversA_refuted : ¬ TypesubtractCoversA := by
  intro h
  have hb := typesubtract_cex
  split at hb
  · rename_i r s₁ heq
    split at hb
    · rename_i s₂ heq2
      exact Bool.false_ne_true (h 25 25 usE usA usAR 4 100 r s₁ heq 100 false s₂ heq2)
    · cases hb
  · cases hb

/-! ## `switchtupleunion(ty)` on a `UnionAll` -/

/-- `switchtupleunion(ty)` returns tuples "such that `Union{return...} == ty`"
(`Compiler/src/typeutils.jl:318-320`); its first half is `ty <: Union{return...}`. Stated for every
`ty` the method accepts (`unwrap_unionall(ty)::DataType`). -/
def SwitchtupleunionCovers : Prop :=
  ∀ n₁ n₂ E (ty : Val) name ps rs s s₁, ty.unwrapUnionall = .datatype name ps →
    (switchtupleunion n₁ E ty).run s = .ok (rs, s₁) →
    Returns (issub n₂ E ty (rs.foldr .union .bottom)) (· = true)

/-- `Tuple{Union{T, R{T}}, T} where T`. -/
def usB : Val := .unionall 7 "T" .bottom anyType
  (.datatype tupleName [.union (.datatype usRName [usTvT]) usTvT, usTvT])

/-- `switchtupleunion(B)` is `[Tuple{R{T},T} where T, Tuple{T,T} where T]`, and `B` is not below
their union: the rewrap of each split tuple (`Compiler/src/typeutils.jl:338-339`) makes `T`
diagonal in `Tuple{T,T} where T`, while in `B` it also occurs in `R{T}`. -/
theorem switchtupleunion_cex :
    (match (switchtupleunion 25 usE usB).run 100 with
      | .ok (rs, _) => (match (issub 25 usE usB (rs.foldr .union .bottom)).run 100 with
        | .ok (false, _) => true | _ => false)
      | _ => false) = true := by decide +kernel

theorem switchtupleunionCovers_refuted : ¬ SwitchtupleunionCovers := by
  intro h
  have hb := switchtupleunion_cex
  split at hb
  · rename_i rs s₁ heq
    split at hb
    · rename_i s₂ heq2
      exact Bool.false_ne_true (h 25 25 usE usB tupleName _ rs 100 s₁ rfl heq 100 false s₂ heq2)
    · cases hb
  · cases hb

/-! ## The split decision is not monotone in the argument types -/

/-- A split allowed for wider argument types is allowed for narrower ones: if
`is_union_split_eligible(𝕃, a, m)` holds and each argument of `a'` is a subtype of the matching
argument of `a`, the cost of `a'` is within `m`. Subtyping of an argument is stated member by
member (`Union{A, B} <: T` exactly when `A <: T` and `B <: T`). -/
def UnionsplitEligibleSubtypeMonotone : Prop :=
  ∀ n E L (a a' : List Val) (m : Int),
    ListRel (fun t' t => ∀ u ∈ uniontypes t', ∃ s s', (issub n E u t).run s = .ok (true, s')) a' a →
    ∀ s s₁ s' c' s₁', (isUnionSplitEligible n E L (a.map .ty) m none).run s = .ok (true, s₁) →
      (unionsplitcost n E L (a'.map .ty) true none).run s' = .ok (c', s₁') → c' ≤ m

/-- `Union{X, Y}` and `Union{X1, X2, Y}`. -/
def usXY : Val := .union usX usY
def usX12Y : Val := .union (.union usX1 usX2) usY

theorem usX1_sub_usXY :
    (match (issub 25 usE usX1 usXY).run 100 with | .ok (true, _) => true | _ => false) = true := by
  decide +kernel
theorem usX2_sub_usXY :
    (match (issub 25 usE usX2 usXY).run 100 with | .ok (true, _) => true | _ => false) = true := by
  decide +kernel
theorem usY_sub_usXY :
    (match (issub 25 usE usY usXY).run 100 with | .ok (true, _) => true | _ => false) = true := by
  decide +kernel

theorem ok_of_match_true {m : CM Bool} {s : Nat}
    (h : (match m.run s with | .ok (true, _) => true | _ => false) = true) :
    ∃ s', m.run s = .ok (true, s') := by
  split at h
  · rename_i s' heq; exact ⟨s', heq⟩
  · cases h

/-- `[Union{X,Y}, Union{X,Y}]` costs 4, so `is_union_split_eligible` allows it with the default
`max_union_splitting = 4`; the narrower `[Union{X1,X2,Y}, Union{X1,X2,Y}]` costs 6. -/
theorem unionsplit_subtype_cex :
    (match (isUnionSplitEligible 25 usE typeinfLattice [.ty usXY, .ty usXY] 4).run 100 with
      | .ok (true, _) => (match (unionsplitcost 25 usE typeinfLattice [.ty usX12Y, .ty usX12Y] true).run 100 with
        | .ok (c', _) => c' == 6 | _ => false)
      | _ => false) = true := by decide +kernel

theorem unionsplitEligibleSubtypeMonotone_refuted : ¬ UnionsplitEligibleSubtypeMonotone := by
  intro h
  have hmem : ∀ u ∈ uniontypes usX12Y, ∃ s s', (issub 25 usE u usXY).run s = .ok (true, s') := by
    intro u hu
    have he : uniontypes usX12Y = [usX1, usX2, usY] := rfl
    rw [he] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · obtain ⟨s', h'⟩ := ok_of_match_true usX1_sub_usXY; exact ⟨_, _, h'⟩
    · obtain ⟨s', h'⟩ := ok_of_match_true usX2_sub_usXY; exact ⟨_, _, h'⟩
    · obtain ⟨s', h'⟩ := ok_of_match_true usY_sub_usXY; exact ⟨_, _, h'⟩
  have hrel : ListRel (fun t' t => ∀ u ∈ uniontypes t', ∃ s s', (issub 25 usE u t).run s = .ok (true, s'))
      [usX12Y, usX12Y] [usXY, usXY] := .cons hmem (.cons hmem .nil)
  have hb := unionsplit_subtype_cex
  split at hb
  · rename_i s₁ heq
    split at hb
    · rename_i c' s₂ heq2
      have := h 25 usE typeinfLattice [usXY, usXY] [usX12Y, usX12Y] 4 hrel 100 s₁ 100 c' s₂ heq heq2
      simp only [beq_iff_eq] at hb
      omega
    · cases hb
  · cases hb

/-! ## The number of split signatures exceeds `max_union_splitting` -/

/-- `max_union_splitting` "specifies the maximum number of union-tuples to swap or expand before
computing the set of matching methods" (`Compiler/src/types.jl:295-297`): when
`is_union_split_eligible(𝕃, argtypes, m)` holds, `switchtupleunion(𝕃, argtypes)` returns at most
`m` signatures. -/
def SplitCountWithinLimit : Prop :=
  ∀ n E L argtypes (m : Int) s s₁ rs s₂ s₃,
    (isUnionSplitEligible n E L argtypes m none).run s = .ok (true, s₁) →
    (switchtupleunionL n E L argtypes none).run s₂ = .ok (rs, s₃) → (rs.length : Int) ≤ m

/-- `[Union{X1,X2,Y}, Union{X,Y}]` costs 4 (`2 * 3 * 2 / 3`), so it is eligible with `m = 4`, but it
splits into 6 signatures. -/
theorem split_count_cex :
    (match (isUnionSplitEligible 25 usE typeinfLattice [.ty usX12Y, .ty usXY] 4).run 100 with
      | .ok (true, _) => (match (switchtupleunionL 25 usE typeinfLattice [.ty usX12Y, .ty usXY]).run 100 with
        | .ok (rs, _) => rs.length == 6 | _ => false)
      | _ => false) = true := by decide +kernel

theorem splitCountWithinLimit_refuted : ¬ SplitCountWithinLimit := by
  intro h
  have hb := split_count_cex
  split at hb
  · rename_i s₁ heq
    split at hb
    · rename_i rs s₂ heq2
      have := h 25 usE typeinfLattice _ 4 100 s₁ rs 100 s₂ heq heq2
      simp only [beq_iff_eq] at hb
      omega
    · cases hb
  · cases hb

/-! ## `is_immutable_type` treats a `TypeVar` member as immutable -/

/-- `is_immutable_argtype(argtype)` "returns `true` if the `argtype` object is known to be
immutable" (`Compiler/src/typeutils.jl:452-461`): if `is_immutable_type(T)` holds, no mutable
struct type is a subtype of `T`. -/
def IsImmutableTypeSound : Prop :=
  ∀ n E (T : Val) (name : String) s s', (isImmutableType E T).run s = .ok (true, s') →
    (∃ tn ∈ E.types.names, tn.name = name ∧ tn.mutable = true ∧ tn.abstract = false) →
    Returns (issub n E (.datatype name []) T) (· = false)

/-- `Union{Nothing, T} where T`, which is `== Any`. -/
def usNothingT : Val :=
  .unionall 7 "T" .bottom anyType (.union (.datatype "Core.Nothing" []) usTvT)

/-- `is_immutable_type(Union{Nothing, T} where T)` is `true`, and the mutable `M` is a subtype of
it: `_is_immutable_type` (`Compiler/src/typeutils.jl:463-469`) finds the bare `TypeVar` member
neither `Type{...}`, nor abstract, nor a mutable `DataType`. -/
theorem immutable_cex :
    (match (isImmutableType usE usNothingT).run 100 with
      | .ok (true, _) => (match (issub 25 usE (.datatype "Main.M" []) usNothingT).run 100 with
        | .ok (true, _) => true | _ => false)
      | _ => false) = true := by decide +kernel

theorem isImmutableTypeSound_refuted : ¬ IsImmutableTypeSound := by
  intro h
  have hb := immutable_cex
  split at hb
  · rename_i s₁ heq
    split at hb
    · rename_i s₂ heq2
      have := h 25 usE usNothingT "Main.M" 100 s₁ heq ⟨usMName, by simp [usE], rfl, rfl, rfl⟩ 100 true s₂ heq2
      cases this
    · cases hb
  · cases hb

end JuliaLean.Proofs.Compiler.src.typeutils
