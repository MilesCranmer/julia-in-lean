import JuliaLean.BitSetsCov.BitSetIterProof

/-!
# `filter!(f, ::BitSet)` preserves the representation invariant

The source loop in `base/abstractset.jl:633-641`, reached by
`base/bitset.jl:328`, either keeps the current state or calls `_setint!` with
`false`. The latter preserves the `BitSet` invariant.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem filterLoop_wf (f : JInt64 → Bool) :
    ∀ (fuel : Nat) (s : BitSetS) (st : U64 × Nat), WF s → WF (filterLoop f fuel s st)
  | 0, _, _, hs => hs
  | fuel + 1, s, st, hs => by
      simp only [filterLoop]
      split
      · exact hs
      · rename_i x w i hit
        split
        · exact filterLoop_wf f fuel (deleteInt s x) (w, i) (wf_setint hs x false)
        · exact filterLoop_wf f fuel s (w, i) hs

end BS

theorem bitSetFilterSpec : BitSetFilterSpec := by
  intro f s hs
  exact BS.filterLoop_wf f _ s (0, 0) hs

end JuliaLean.BitSetsCov
