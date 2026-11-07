import JuliaLean.Proofs.base.set.Claims
import JuliaLean.base.abstractset

namespace JuliaLean.Dicts

/-- `union!(s, t)`: membership is `x ∈ s || x ∈ t`, and `s` agrees with the reference union. -/
def SetUnionAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', unionSet unionBang o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x || rmem o mt x)

/-- `intersect!(s, t)`: membership is `x ∈ s && x ∈ t`. -/
def SetIntersectAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', intersectBang o s t = .ok s' ∧
      Agrees o s' (ms.filter fun e => rmem o mt e.1) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x && rmem o mt x)

/-- `symdiff!(s, t)`: membership is `x ∈ s` xor `x ∈ t`. -/
def SetSymdiffAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    ∃ s', symdiffBang o s t = .ok s' ∧
      Agrees o s' (mt.foldl (fun m e => if rmem o m e.1 then rdel o m e.1 else rset o m e.1 ()) ms) ∧
      ∀ x, setIn o s' x = .ok (rmem o ms x != rmem o mt x)

/-- `issubset(s, t)` and `s == t` decide inclusion and equality of the member sets. -/
def SetCompareAgrees : Prop :=
  ∀ (K : Type) (o : KeyOps K), o.Lawful → GenericMax o →
  ∀ (s t : SetT K) ms mt, Reach o s ms → Reach o t mt →
    issubsetSet o s t = .ok (ms.all fun e => rmem o mt e.1) ∧
    setEq o s t = .ok (ms.all (fun e => rmem o mt e.1) && mt.all (fun e => rmem o ms e.1))

/-- `union!(s, itr)` (and `Set{T}(itr)`) has the outcome of pushing every element
of `itr` in turn: the same exception, or the same members. -/
def UnionPushEquiv : Prop :=
  ∀ (K Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → MaxValuesOK o →
  ∀ (s : SetT K) ms, Reach o s ms → ∀ itr : List Q, itr.length ≤ 2 ^ 30 →
    SameOutcome (unionBang o c s itr) (itr.foldlM (pushConv o c) s)
      (fun s₁ s₂ => ∀ y, setIn o s₁ y = setIn o s₂ y)

/-- `issubset(a, b)` for vectors "determine[s] whether every element of `a` is
also in `b`, using `in`" (`base/abstractset.jl:315`), and `in` on a vector uses `==`. -/
def IssubsetVecUsesIn : Prop :=
  ∀ (E : Type) (o : KeyOps E) (eqeq : E → E → Bool), o.Lawful → GenericMax o →
  (∀ a b, eqeq a b = eqeq b a) →
  ∀ a b : List E, issubsetVec o eqeq a b = .ok (a.all fun x => b.any fun y => eqeq y x)

end JuliaLean.Dicts
