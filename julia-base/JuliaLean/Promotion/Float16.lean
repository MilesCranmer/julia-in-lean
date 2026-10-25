import JuliaLean.Promotion.F16.Chunk0
import JuliaLean.Promotion.F16.Chunk1
import JuliaLean.Promotion.F16.Chunk2
import JuliaLean.Promotion.F16.Chunk3
import JuliaLean.Promotion.F16.Chunk4
import JuliaLean.Promotion.F16.Chunk5
import JuliaLean.Promotion.F16.Chunk6
import JuliaLean.Promotion.F16.Chunk7
import JuliaLean.Promotion.F16.Chunk8
import JuliaLean.Promotion.F16.Chunk9
import JuliaLean.Promotion.F16.Chunk10
import JuliaLean.Promotion.F16.Chunk11
import JuliaLean.Promotion.F16.Chunk12
import JuliaLean.Promotion.F16.Chunk13
import JuliaLean.Promotion.F16.Chunk14
import JuliaLean.Promotion.F16.Chunk15

/-!
Exhaustive properties of `Float16` conversion to every `BitInteger` type and of `Float16`
hashing, over all 65,536 bit patterns.
-/

namespace JuliaLean.Promotion.F16

open JuliaLean.Promotion

theorem all_chunks : ∀ k, k < 128 → chunkOk k = true
  | 0, _ => chunk0 | 1, _ => chunk1 | 2, _ => chunk2 | 3, _ => chunk3
  | 4, _ => chunk4 | 5, _ => chunk5 | 6, _ => chunk6 | 7, _ => chunk7
  | 8, _ => chunk8 | 9, _ => chunk9 | 10, _ => chunk10 | 11, _ => chunk11
  | 12, _ => chunk12 | 13, _ => chunk13 | 14, _ => chunk14 | 15, _ => chunk15
  | 16, _ => chunk16 | 17, _ => chunk17 | 18, _ => chunk18 | 19, _ => chunk19
  | 20, _ => chunk20 | 21, _ => chunk21 | 22, _ => chunk22 | 23, _ => chunk23
  | 24, _ => chunk24 | 25, _ => chunk25 | 26, _ => chunk26 | 27, _ => chunk27
  | 28, _ => chunk28 | 29, _ => chunk29 | 30, _ => chunk30 | 31, _ => chunk31
  | 32, _ => chunk32 | 33, _ => chunk33 | 34, _ => chunk34 | 35, _ => chunk35
  | 36, _ => chunk36 | 37, _ => chunk37 | 38, _ => chunk38 | 39, _ => chunk39
  | 40, _ => chunk40 | 41, _ => chunk41 | 42, _ => chunk42 | 43, _ => chunk43
  | 44, _ => chunk44 | 45, _ => chunk45 | 46, _ => chunk46 | 47, _ => chunk47
  | 48, _ => chunk48 | 49, _ => chunk49 | 50, _ => chunk50 | 51, _ => chunk51
  | 52, _ => chunk52 | 53, _ => chunk53 | 54, _ => chunk54 | 55, _ => chunk55
  | 56, _ => chunk56 | 57, _ => chunk57 | 58, _ => chunk58 | 59, _ => chunk59
  | 60, _ => chunk60 | 61, _ => chunk61 | 62, _ => chunk62 | 63, _ => chunk63
  | 64, _ => chunk64 | 65, _ => chunk65 | 66, _ => chunk66 | 67, _ => chunk67
  | 68, _ => chunk68 | 69, _ => chunk69 | 70, _ => chunk70 | 71, _ => chunk71
  | 72, _ => chunk72 | 73, _ => chunk73 | 74, _ => chunk74 | 75, _ => chunk75
  | 76, _ => chunk76 | 77, _ => chunk77 | 78, _ => chunk78 | 79, _ => chunk79
  | 80, _ => chunk80 | 81, _ => chunk81 | 82, _ => chunk82 | 83, _ => chunk83
  | 84, _ => chunk84 | 85, _ => chunk85 | 86, _ => chunk86 | 87, _ => chunk87
  | 88, _ => chunk88 | 89, _ => chunk89 | 90, _ => chunk90 | 91, _ => chunk91
  | 92, _ => chunk92 | 93, _ => chunk93 | 94, _ => chunk94 | 95, _ => chunk95
  | 96, _ => chunk96 | 97, _ => chunk97 | 98, _ => chunk98 | 99, _ => chunk99
  | 100, _ => chunk100 | 101, _ => chunk101 | 102, _ => chunk102 | 103, _ => chunk103
  | 104, _ => chunk104 | 105, _ => chunk105 | 106, _ => chunk106 | 107, _ => chunk107
  | 108, _ => chunk108 | 109, _ => chunk109 | 110, _ => chunk110 | 111, _ => chunk111
  | 112, _ => chunk112 | 113, _ => chunk113 | 114, _ => chunk114 | 115, _ => chunk115
  | 116, _ => chunk116 | 117, _ => chunk117 | 118, _ => chunk118 | 119, _ => chunk119
  | 120, _ => chunk120 | 121, _ => chunk121 | 122, _ => chunk122 | 123, _ => chunk123
  | 124, _ => chunk124 | 125, _ => chunk125 | 126, _ => chunk126 | 127, _ => chunk127
  | _ + 128, h => absurd h (by omega)

theorem valueOk_all (x : FV .f16) : valueOk x = true := by
  obtain ⟨⟨n, hn⟩⟩ := x
  have hw : (2 : Nat) ^ (FTy.fmt .f16).width = 65536 := rfl
  have hn' : n < 65536 := hw ▸ hn
  have hx : (Fl.ofBits (n / 512 * 512 + n % 512) : FV .f16) = ⟨⟨n, hn⟩⟩ := by
    have e : n / 512 * 512 + n % 512 = n := by omega
    simp only [Fl.ofBits, e, hw, Nat.mod_eq_of_lt hn']
  rw [← hx]
  exact of_chunk (all_chunks _ (by omega)) _ (Nat.mod_lt _ (by decide))

/-- `Ti(x::Float16)` returns the exact value when `x` is an integer representable in `Ti`
and throws `InexactError` otherwise, for every `BitInteger` type `Ti`. -/
def Float16ToIntExact : Prop := ∀ (t : IntTy) (x : FV .f16), toIntOk t x = true

/-- `trunc(Ti, x::Float16)` returns the truncated value when it is representable in `Ti`
and throws `InexactError` otherwise. -/
def Float16TruncExact : Prop := ∀ (t : IntTy) (x : FV .f16), truncOk t x = true

/-- `hash(x::Float16) == hash(Float64(x))`, and `hash(x) == hash(Int64(x))` whenever
`isequal(x, Int64(x))`. -/
def Float16HashConsistent : Prop := ∀ x : FV .f16, hashOk x = true

theorem float16ToIntExact_proven : Float16ToIntExact := by
  intro t x
  have h := valueOk_all x
  simp only [valueOk, Bool.and_eq_true, List.all_eq_true] at h
  exact (h.1 t (mem_allInts t)).1

theorem float16TruncExact_proven : Float16TruncExact := by
  intro t x
  have h := valueOk_all x
  simp only [valueOk, Bool.and_eq_true, List.all_eq_true] at h
  exact (h.1 t (mem_allInts t)).2

theorem float16HashConsistent_proven : Float16HashConsistent := by
  intro x
  have h := valueOk_all x
  simp only [valueOk, Bool.and_eq_true] at h
  exact h.2

end JuliaLean.Promotion.F16
