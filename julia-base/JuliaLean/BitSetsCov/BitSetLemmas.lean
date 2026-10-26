import JuliaLean.BitSetsCov.BitSet

/-!
# Basic lemmas for the `BitSet` model

`BS.mem s x` reads the bit of `x` through `G`; under the type invariant `WF`
every integer outside `typemin(Int):typemax(Int)` is absent, and `_setint!`
keeps `WF` and changes membership only at its argument.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem noOffset_val : noOffset = -1152921504606846976 := noOffset_eq

theorem mem_contains (s : BitSetS) (m : JInt64) : s.contains m = mem s m.val := contains_eq s m

theorem wf_new : WF new := by
  constructor
  · intro _; rfl
  · intro h; exact absurd rfl h

theorem mem_new (x : Int) : mem new x = false := G_nil _ _ _

theorem wf_bounds {s : BitSetS} (h : WF s) (ho : s.offset ≠ noOffset) :
    -(2 ^ 57) ≤ s.offset ∧ s.offset + s.bits.length ≤ 2 ^ 57 := h.2 ho

theorem mem_out {s : BitSetS} (h : WF s) {x : Int} (hx : ¬ inIntRange x) : mem s x = false := by
  unfold mem
  by_cases ho : s.offset = noOffset
  · rw [h.1 ho]; exact G_nil _ _ _
  · have hb := h.2 ho
    unfold inIntRange at hx
    apply G_out
    omega

theorem length_unsafeBitsetAt (bc : List U64) (x : Bool) (i1 i2 : Nat) :
    (unsafeBitsetAt bc x i1 i2).length = bc.length := by
  simp [unsafeBitsetAt, cset]

theorem length_growend0 (b : List U64) (k : Nat) : (BitSetS.growend0 b k).length = b.length + k := by
  simp [BitSetS.growend0]

theorem length_growbeg0 (b : List U64) (k : Nat) : (BitSetS.growbeg0 b k).length = k + b.length := by
  simp [BitSetS.growbeg0]

theorem jint64_bounds' (n : JInt64) : -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 :=
  jint64_bounds n

/-- `_setint!` keeps the type invariant. -/
theorem wf_setint {s : BitSetS} (h : WF s) (n : JInt64) (b : Bool) : WF (s.setint n b) := by
  obtain ⟨bits, off⟩ := s
  have hn := jint64_bounds n
  have hoff := noOffset_eq
  have hinv : Inv ⟨bits, off⟩ := h.1
  have hI := (setint_spec bits off hinv n b).1
  refine ⟨hI, ?_⟩
  by_cases h1 : n.val / 64 - off ≥ (bits.length : Int)
  · cases b
    · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by simp [BitSetS.setint, h1]
      rw [hr]; exact h.2
    · by_cases h2 : off = noOffset
      · have hb : bits = [] := h.1 h2
        subst hb
        have hr : BitSetS.setint ⟨[], off⟩ n true =
            ⟨unsafeBitsetAt (BitSetS.growend0 [] 1) true 1 (n.val % 64).toNat, n.val / 64⟩ := by
          subst h2
          have hle : noOffset ≤ n.val / 64 := by rw [noOffset_eq]; omega
          simp [BitSetS.setint, hle]
        rw [hr]
        intro _
        simp only [length_unsafeBitsetAt, length_growend0]
        simp
        omega
      · have hr : BitSetS.setint ⟨bits, off⟩ n true =
            ⟨unsafeBitsetAt (BitSetS.growend0 bits (n.val / 64 - off - bits.length + 1).toNat) true
              (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
          simp [BitSetS.setint, h1, h2]
        rw [hr]
        intro _
        have hb := h.2 h2
        simp only [length_unsafeBitsetAt, length_growend0]
        simp only at hb
        omega
  · by_cases h3 : n.val / 64 - off < 0
    · cases b
      · have hr : BitSetS.setint ⟨bits, off⟩ n false = ⟨bits, off⟩ := by
          simp [BitSetS.setint, h1, h3]
        rw [hr]; exact h.2
      · have hr : BitSetS.setint ⟨bits, off⟩ n true =
            ⟨unsafeBitsetAt (BitSetS.growbeg0 bits (-(n.val / 64 - off)).toNat) true 1
              (n.val % 64).toNat, off + (n.val / 64 - off)⟩ := by
          simp [BitSetS.setint, h1, h3]
        rw [hr]
        intro _
        have h2 : off ≠ noOffset := by
          intro he
          have hb : bits = [] := h.1 he
          subst hb
          simp at h1
          omega
        have hb := h.2 h2
        simp only [length_unsafeBitsetAt, length_growbeg0]
        simp only at hb
        omega
    · have hr : BitSetS.setint ⟨bits, off⟩ n b =
          ⟨unsafeBitsetAt bits b (n.val / 64 - off + 1).toNat (n.val % 64).toNat, off⟩ := by
        simp [BitSetS.setint, h1, h3]
      rw [hr]
      intro h2
      have hb := h.2 h2
      simp only [length_unsafeBitsetAt]
      exact hb

/-- `_setint!(s, n, b)` sets the membership of `n` to `b` and leaves every other integer. -/
theorem mem_setint {s : BitSetS} (h : WF s) (n : JInt64) (b : Bool) (x : Int) :
    mem (s.setint n b) x = if x = n.val then b else mem s x := by
  by_cases hx : inIntRange x
  · have hx' := (inIntRange_iff x).mp hx
    obtain ⟨bits, off⟩ := s
    have hspec := (setint_spec bits off h.1 n b).2 ⟨x, hx'⟩
    rw [mem_contains, mem_contains] at hspec
    rw [hspec]
    by_cases hxn : x = n.val
    · rw [if_pos (Subtype.ext hxn), if_pos hxn]
    · rw [if_neg (fun he => hxn (congrArg Subtype.val he)), if_neg hxn]
  · have hn := jint64_bounds n
    have hxn : x ≠ n.val := by
      intro he; subst he; exact hx (by unfold inIntRange; omega)
    rw [mem_out (wf_setint h n b) hx, if_neg hxn, mem_out h hx]

end BS

end JuliaLean.BitSetsCov
