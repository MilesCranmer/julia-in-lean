import JuliaLean.base.strings.string

namespace JuliaLean.Transcode

/-- Strings are immutable (`base/strings/string.jl:85`): once `String(v)` has
returned a String, no later operation changes its bytes. -/
def StringVectorImmutable : Prop :=
  ∀ (p q : List Op) (i : Nat) (c : List UInt8), i ∈ (Heap.empty.run p).visible →
    (Heap.empty.run p).content i = some c → (Heap.empty.run (p ++ q)).content i = some c

/-- `v = StringVector(3); v .= "abc"; b = reshape(v, 1, 3); s = String(v)`. -/
def aliasProg : List Op :=
  [.stringVector 3, .setindex 0 1 0x61, .setindex 0 2 0x62, .setindex 0 3 0x63, .share 0, .string 0]

theorem stringVectorImmutable_refuted : ¬ StringVectorImmutable := by
  intro h
  -- `b[1] = UInt8('A')` changes `s` from "abc" to "Abc".
  have := h aliasProg [.setindex 1 1 0x41] 0 [0x61, 0x62, 0x63] (by decide) (by decide)
  revert this; decide

/-- `w = vec(reshape(v, 1, 3)); s1 = String(v); resize!(w, 1); s2 = String(w)` truncates `s1`. -/
theorem stringVector_truncate :
    (Heap.empty.run (aliasProg ++ [.shrink 1 1, .string 1])).content 0 = some [0x61] := by decide
end JuliaLean.Transcode
