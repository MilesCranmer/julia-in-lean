import JuliaLean.ParsePrint.IntParse
import JuliaLean.ParsePrint.IntPrint
import JuliaLean.ParsePrint.IntRoundtrip1

/-! Exhaustive 8-bit roundtrip checks, continued. -/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

theorem rt_u8_16 : ∀ k : Fin 256, rtOK .u8 k 16 = true := by decide +kernel
theorem rt_i8_16 : ∀ k : Fin 256, rtOK .i8 k 16 = true := by decide +kernel
theorem rt_u8_36 : ∀ k : Fin 256, rtOK .u8 k 36 = true := by decide +kernel
theorem rt_i8_36 : ∀ k : Fin 256, rtOK .i8 k 36 = true := by decide +kernel
theorem rt_u8_37 : ∀ k : Fin 256, rtOK .u8 k 37 = true := by decide +kernel
theorem rt_i8_37 : ∀ k : Fin 256, rtOK .i8 k 37 = true := by decide +kernel
theorem rt_u8_62 : ∀ k : Fin 256, rtOK .u8 k 62 = true := by decide +kernel
theorem rt_i8_62 : ∀ k : Fin 256, rtOK .i8 k 62 = true := by decide +kernel

/-- The bases of the exhaustive checks: every specialised writer of `string`
(bases 2, 8, 10, 16) and the generic `_base` writer with both digit tables
(3, 7, 36 with `base36digits`; 37, 62 with `base62digits`). -/
def roundtripBases : List Int := [2, 3, 7, 8, 10, 16, 36, 37, 62]

/-- `parse(T, string(n; base=b); base=b) == n` (`base/parse.jl:250`,
`base/intfuncs.jl:1101`) for the 8-bit integer types and the bases above. -/
def RoundtripInt8 : Prop := ∀ (t : IntTy) (n : JInt t) (b : Int), t.bits = 8 → b ∈ roundtripBases →
  ∃ s, IntPrint.string n (JInt.lit .i64 b) = .ok s ∧ parse t (bytesOf s) (some b) = .ok n

theorem lit_of_bits8 (t : IntTy) (ht : t.bits = 8) (n : JInt t) :
    ∃ k : Fin 256, JInt.lit t k = n := by
  have hp := n.property
  cases t <;> simp only [IntTy.bits] at ht <;>
    first | omega | skip
  all_goals
    refine ⟨⟨(n.val % 256).toNat, by omega⟩, Subtype.ext ?_⟩
    simp only [JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hp ⊢
    simp at hp ⊢
    omega

theorem rtOK_sound (t : IntTy) (k : Nat) (b : Int) (h : rtOK t k b = true) :
    ∃ s, IntPrint.string (JInt.lit t k) (JInt.lit .i64 b) = .ok s ∧
      parse t (bytesOf s) (some b) = .ok (JInt.lit t k) := by
  unfold rtOK at h
  cases hs : IntPrint.string (JInt.lit t k) (JInt.lit .i64 b) 1 with
  | error e => simp only [hs] at h; cases h
  | ok s =>
    simp only [hs] at h
    cases hp : parse t (bytesOf s) (some b) with
    | error e => simp only [hp] at h; cases h
    | ok v =>
      simp only [hp] at h
      refine ⟨s, rfl, ?_⟩
      have : v.val = (JInt.lit t k).val := by simpa using h
      rw [hp, Subtype.ext this]

theorem roundtripInt8 : RoundtripInt8 := by
  intro t n b ht hb
  obtain ⟨k, rfl⟩ := lit_of_bits8 t ht n
  apply rtOK_sound
  have h8 : t = .u8 ∨ t = .i8 := by cases t <;> simp_all [IntTy.bits]
  simp only [roundtripBases, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases h8 with rfl | rfl
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt_u8_2 k
    · exact rt_u8_3 k
    · exact rt_u8_7 k
    · exact rt_u8_8 k
    · exact rt_u8_10 k
    · exact rt_u8_16 k
    · exact rt_u8_36 k
    · exact rt_u8_37 k
    · exact rt_u8_62 k
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt_i8_2 k
    · exact rt_i8_3 k
    · exact rt_i8_7 k
    · exact rt_i8_8 k
    · exact rt_i8_10 k
    · exact rt_i8_16 k
    · exact rt_i8_36 k
    · exact rt_i8_37 k
    · exact rt_i8_62 k

end JuliaLean.ParsePrint.IntParse
