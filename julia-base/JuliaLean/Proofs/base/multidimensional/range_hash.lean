import JuliaLean.base.multidimensional
import JuliaLean.Registry.Types

namespace JuliaLean.Ranges

open JuliaLean.Registry



/-- The numeric and singleton-tuple hash contracts, `base/hashing.jl:12-16`.
These are explicit theorem hypotheses, including cross-type integer equality. -/
def RangeHashCallbacks.RespectsValues (c : RangeHashCallbacks) : Prop :=
  (∀ x y h, x.val = y.val → c.scalar x h = c.scalar y h) ∧
  (∀ x y h, x.val = y.val → c.tuple1 x h = c.tuple1 y h)


private theorem rangeHashOne_val (ty : NType) : (Num.one ty).val = 1 := by
  cases ty with
  | bool => decide
  | bit t => cases t <;> decide

private theorem rangeHashChain_values (c : RangeHashCallbacks) (hc : c.RespectsValues)
    (xs ys : List Num) (hv : xs.map Num.val = ys.map Num.val) (h : RangeHashWord) :
    rangeHashChain c xs h = rangeHashChain c ys h := by
  induction xs generalizing ys h with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hv
  | cons x xs ih =>
      cases ys with
      | nil => simp at hv
      | cons y ys =>
          have hv' : x.val = y.val ∧ xs.map Num.val = ys.map Num.val := by simpa using hv
          simp only [rangeHashChain, List.foldl_cons]
          rw [hc.1 x y h hv'.1]
          exact ih ys hv'.2 (c.scalar y h)

/-- Inputs arise from keyword or StepRangeLen constructors, rather than arbitrary records. -/
def RangeHashConstructed (r : ResultRng) : Prop :=
  (∃ a s b n, rangeKw a s b n = some (.ok r)) ∨
  (∃ ty ref stride len offset, countedRange ty ref stride len offset = .ok r)

/-- Equal integer range contents and equal axes have equal hashes in the direct
branch, regardless of element or length storage types. Preconditions spell out
semantic array equality using complete actual iterate traces; both ranges must
come from constructors, and their machine lengths must select len < 8.
No equality assumption is made about hashes or about the stored range records. -/
def ShortEqualRangeHashConsistency : Prop :=
  ∀ (c : RangeHashCallbacks), c.RespectsValues →
  ∀ (r s : ResultRng) (nr ns : Num) (xs ys : List Num) (seed : RangeHashWord),
    RangeHashConstructed r → RangeHashConstructed s →
    resultLength r = .ok nr → resultLength s = .ok ns → nr.val = ns.val → nr.val < 8 →
    RangeHashTrace r none (.ok xs) → RangeHashTrace s none (.ok ys) →
    xs.map Num.val = ys.map Num.val →
    ∃ h, RangeHash c r seed (.ok h) ∧ RangeHash c s seed (.ok h)

theorem shortEqualRangeHashConsistency_proven : ShortEqualRangeHashConsistency := by
  intro c hc r s nr ns xs ys seed _ _ hr hs hn hsmall hx hy hvalues
  let initial := rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)
  have hshape : rangeHashShape c nr initial = rangeHashShape c ns initial := by
    unfold rangeHashShape
    rw [hc.2 (Num.one nr.ty) (Num.one ns.ty) initial
      ((rangeHashOne_val nr.ty).trans (rangeHashOne_val ns.ty).symm)]
    exact hc.2 nr ns _ hn
  refine ⟨rangeHashChain c xs (rangeHashShape c nr initial), ?_, ?_⟩
  · exact RangeHash.short hr hsmall hx
  · have heq : rangeHashChain c xs (rangeHashShape c nr initial) =
        rangeHashChain c ys (rangeHashShape c ns initial) := by
      rw [hshape]
      exact rangeHashChain_values c hc xs ys hvalues _
    rw [heq]
    exact RangeHash.short hs (by omega) hy

/-- `base/hashing.jl:55`: subtracting a key and folding retain UInt64 wrapping. -/
def RangeHashMixExact : Prop :=
  ∀ (x h : RangeHashWord), (rangeHashMixLinear x h).val =
    wrapInt .u64 (wrapInt .u64 (3 * h.val) - x.val)

theorem rangeHashMixExact_proven : RangeHashMixExact := by
  intro x h
  rfl

def hashEntries : List Entry := []

end JuliaLean.Ranges
