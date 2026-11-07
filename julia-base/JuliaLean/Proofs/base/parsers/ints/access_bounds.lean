import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## Integer parser access envelope -/

inductive ParseWord where
  | small
  | bits64
  | bits128
  | generic
  deriving DecidableEq, Repr

def parserStart (bytes : List UInt8) (signed : Bool) : Nat :=
  if signed && (bytes.head? == some 0x2d || bytes.head? == some 0x2b) then 2 else 1

def parserFastLimit (word : ParseWord) (base start last : Nat) : Nat :=
  match word, base with
  | .bits64, 10 => min last (start + 18)
  | .bits128, 10 => min last (start + 37)
  | .bits64, 16 => min last (start + 15)
  | .bits128, 16 => min last (start + 31)
  | _, _ => start - 1

def fastBlockStarts (start limit : Nat) : List Nat :=
  (List.range ((limit + 1 - start) / 8)).map fun block => start + 8 * block

def load8Accesses (start : Nat) : List Int := span start 8

/-- Exact safety envelope of `parsevalue` and `parseint` (`base/parsers/ints.jl:84-189`).
The sign read is at one. Fast blocks start at `i, i+8, ...` while eight bytes fit below the
computed `k`; all scalar and overflow scans are subsets of `start:last`. Invalid digits and
overflow only stop early, so the envelope contains every executed access. -/
def parsevalueAccesses
    (bytes : List UInt8) (signed : Bool) (word : ParseWord) (base : Nat) : List Int :=
  let first := parserStart bytes signed
  let last := bytes.length
  let limit := parserFastLimit word base first last
  let signRead := if signed && 0 < last then [1] else []
  signRead ++
    (fastBlockStarts first limit).flatMap load8Accesses ++
    (if first ≤ last then span first (last + 1 - first) else [])

def ParserAccessesInBounds : Prop :=
  ∀ bytes signed word base i, i ∈ parsevalueAccesses bytes signed word base →
    inBounds bytes.length i

theorem parserAccessesInBounds_proven : ParserAccessesInBounds := by
  intro bytes signed word base i hi
  unfold parsevalueAccesses at hi
  rw [List.mem_append] at hi
  rcases hi with hprefix | hscalar
  · rw [List.mem_append] at hprefix
    rcases hprefix with hsign | hfast
    · split at hsign <;> simp_all [inBounds] <;> omega
    · rw [List.mem_flatMap] at hfast
      obtain ⟨blockStart, hbs, hib⟩ := hfast
      unfold fastBlockStarts at hbs
      rw [List.mem_map] at hbs
      obtain ⟨block, hblock, rfl⟩ := hbs
      obtain ⟨lane, hlane, rfl⟩ := mem_span hib
      have hb := List.mem_range.mp hblock
      have hs : 1 ≤ parserStart bytes signed := by
        unfold parserStart
        split <;> omega
      by_cases h10 : base = 10
      · subst base
        cases word <;> simp [parserFastLimit] at hb <;> simp [inBounds] <;> omega
      · by_cases h16 : base = 16
        · subst base
          cases word <;> simp [parserFastLimit] at hb <;> simp [inBounds] <;> omega
        · cases word <;> simp [parserFastLimit, h10, h16] at hb <;> exfalso <;> omega
  · by_cases hfirst : parserStart bytes signed ≤ bytes.length
    · simp only [if_pos hfirst] at hscalar
      obtain ⟨k, hk, rfl⟩ := mem_span hscalar
      have hs : 1 ≤ parserStart bytes signed := by
        unfold parserStart
        split <;> omega
      have hik : parserStart bytes signed + k ≤ bytes.length := by omega
      unfold inBounds
      constructor
      · exact_mod_cast (show 1 ≤ parserStart bytes signed + k by omega)
      · exact_mod_cast hik
    · simp [hfirst] at hscalar
end JuliaLean.MemSafety.G6
end
