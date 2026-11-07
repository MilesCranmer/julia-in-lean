import JuliaLean.Proofs.base.dict.Props
import JuliaLean.base.set
import JuliaLean.base.abstractset

namespace JuliaLean.Dicts

/-! ## Set -/

/-- Membership in a reference set. -/
def rmem {K : Type} (o : KeyOps K) (m : RMap K Unit) (x : K) : Bool := (rfind o m x).isSome

/-- The generic key type: `max_values(K) = typemax(Int)`. -/
def GenericMax {K : Type} (o : KeyOps K) : Prop := o.maxValues = JInt.typemax .i64

/-- `setdiff!(s, t)` (both branches of `base/set.jl:187-198`): membership is `x ∈ s && x ∉ t`. -/
def SetSetdiffAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', setdiffBang filterLoop o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => !rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && !rmem o mt x)

/-- Conversions consistent with `hash`/`isequal` (`base/hashing.jl:12-16`), and
`convert(K, x) === x` for `x isa K`. -/
structure ConvLawful {Q K : Type} (o : KeyOps K) (c : Conv Q K) : Prop where
  hash_eq : ∀ q k, c.iseq q k = true → c.hash q = o.hash k
  iseq_eq : ∀ q k k', c.iseq q k = true → o.eq k k' = true → c.iseq q k' = true
  isa_convert : ∀ q k, c.isa q = some k → c.convert q = .ok k ∧ c.iseq q k = true
  /-- The iterator interface requires yielded values to inhabit its declared element type. -/
  subtype_isa : c.eltypeSubtype = true → ∀ q, ∃ k, c.isa q = some k

/-- `in!(x, s)` is `in(x, s) ? true : (push!(s, x); false)` (docstring `base/set.jl:94-100`). -/
def InBangEquiv : Prop :=
  ∀ (K Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → GenericMax o →
  ∀ (s : SetT K) ms, Reach o s ms → ∀ x : Q,
    SameOutcome (inBang o c s x)
      (do if ← inConv c s x then pure (true, s) else do
            let s ← pushConv o c s x
            pure (false, s) : DR (Bool × SetT K))
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ ∀ y, setIn o r₁.2 y = setIn o r₂.2 y)

end JuliaLean.Dicts
