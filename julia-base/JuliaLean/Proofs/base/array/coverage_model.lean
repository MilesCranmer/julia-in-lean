import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def WrapMemoryIntegerSpec : Prop :=
  ∀ (kind : IntegerKind) (length capacity : Nat), length ≤ capacity →
    wrapMemory kind length capacity = .ok length

theorem wrapMemoryIntegerSpec_refuted : ¬ WrapMemoryIntegerSpec := by
  intro h
  have bad := h .other 2 3 (by decide)
  simp [wrapMemory] at bad



def membershipIndex (a b : List FloatKey) : List (Option Nat) :=
  a.map fun value => firstIndexBy memberEq value b 1

def IndexinMembershipSpec : Prop :=
  ∀ (a b : List FloatKey), indexinModel a b = membershipIndex a b

theorem indexinMembershipSpec_refuted : ¬ IndexinMembershipSpec := by
  intro h
  have bad := h [.negZero] [.posZero]
  simp [indexinModel, membershipIndex, firstIndexBy, keyEqual, memberEq] at bad

end JuliaLean.ArrayCov
