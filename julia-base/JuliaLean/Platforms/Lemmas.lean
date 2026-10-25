import JuliaLean.Platforms.Props

/-!
# Basic lemmas for the `Platforms` proofs and refutations
-/

namespace JuliaLean.Platforms

open JuliaLean

theorem mem_nonos {x : Char} (h : isNono x = true) : x ∈ nonos := by
  unfold isNono List.contains at h
  exact List.mem_of_elem_eq_true h

theorem nono_fixed {c : Char} (h : isNono c = true) : c.toNat < 128 ∧ asciiLower c = c := by
  have hm := mem_nonos h
  simp only [nonos, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide +kernel

theorem upperLower_not_nono : ∀ e ∈ upperLower, isNono e.2 = false := by decide +kernel

theorem asciiLower_spec : LcSpec asciiLower := by
  refine ⟨fun _ _ => rfl, fun c h => ?_⟩
  unfold asciiLower at h ⊢
  cases hf : upperLower.find? (·.1 == c) with
  | none => rfl
  | some e =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    rw [upperLower_not_nono e (List.mem_of_find?_eq_some hf)] at h
    cases h

/-- Under `LcSpec`, `lc` fixes the characters of `nonos` and maps no other
character onto one of them. -/
theorem isNono_lc {lc : Char → Char} (hlc : LcSpec lc) (c : Char) : isNono (lc c) = isNono c := by
  cases h : isNono c
  · cases h' : isNono (lc c)
    · rfl
    · rw [hlc.2 c h'] at h'
      rw [h'] at h
      cases h
  · have ⟨hlt, hfix⟩ := nono_fixed h
    rw [hlc.1 c hlt, hfix, h]

/-- Key order `keys(a) ∪ keys(b)` with `a`'s keys first. -/
def unionOrder (a b : Platform) : List Str := keys a.tags ++ keysNotIn (keys b.tags) (keys a.tags)

theorem haskey_iff {V : Type} (d : Dict V) (k : Str) : haskey d k = true ↔ k ∈ keys d := by
  simp [haskey, dget, keys, List.find?_isSome, List.mem_map]

theorem unionOrder_ok (a b : Platform) (h : (unionOrder a b).Nodup) : IsUnionOrder (unionOrder a b) a b := by
  refine ⟨h, fun k => ?_⟩
  simp only [unionOrder, keysNotIn, List.mem_append, List.mem_filter, haskey_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases ha : k ∈ keys a.tags
      · exact Or.inl ha
      · exact Or.inr ⟨h, by simpa using ha⟩

end JuliaLean.Platforms
