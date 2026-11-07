import JuliaLean.Registry.Types
import JuliaLean.base.secretbuffer

/-!
Public-contract statement round 1. Full contracts and exact model blockers are
recorded in the adjacent TSV. Frozen inputs are not changed. No proposed repair
is imported here.
-/

namespace JuliaLean.Proofs.base.secretbuffer

open JuliaLean JuliaLean.base.secretbuffer

/-- Representation bounds for a valid buffer cursor; the size cap excludes Int wraparound
in length/index arithmetic, not a bound chosen to hide a reachable small-input failure. -/
def ValidCursor {M : Type} (s : SecretBuffer M) : Prop :=
  0 ≤ s.size.val ∧ s.size.val < (2 : Int)^62 ∧
  1 ≤ s.ptr.val ∧ s.ptr.val ≤ s.size.val + 1

/-- The exact existing Int64 callee composition used by seekend; no new model body. -/
def seekAtInt64 {M : Type} (s : SecretBuffer M) (n : I64) :
    Except IOErr (SecretBuffer M) :=
  seekSecretBuffer
    (fun value : I64 => .ok (JuliaLean.base.int.add_int value (JInt.lit .i64 1)))
    (fun (left right : I64) => .ok (JuliaLean.base.int.jmin left right))
    (fun (left right : I64) => .ok (JuliaLean.base.int.jmax left right))
    (fun value : I64 => (JuliaLean.base.int.convert .i64 value).mapError JuliaLean.base.iobuffer.IOErr.jl)
    s n

end JuliaLean.Proofs.base.secretbuffer

namespace JuliaLean.Proofs.base.secretbuffer.Round1

open JuliaLean.Proofs.base.secretbuffer
open JuliaLean JuliaLean.base.secretbuffer

/-- The current position and unread byte count partition the buffer's logical contents.
Julia source: base/secretbuffer.jl:175-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/io.jl:130-142; base/iostream.jl:223-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CursorAccounting : Prop :=
  ∀ {M : Type} (s : SecretBuffer M), ValidCursor s →
    0 ≤ (positionSecretBuffer s).val ∧
    0 ≤ (bytesavailableSecretBuffer s).val ∧
    (positionSecretBuffer s).val + (bytesavailableSecretBuffer s).val = s.size.val

/-- For a valid finite buffer, EOF holds exactly when no unread byte remains.
Julia source: base/secretbuffer.jl:175-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/io.jl:130-142,209-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EOFMatchesAvailability : Prop :=
  ∀ {M : Type} (s : SecretBuffer M), ValidCursor s →
    (eofSecretBuffer s = true ↔ (bytesavailableSecretBuffer s).val = 0)

/-- A valid buffer has no contents exactly when it is both at its beginning and at EOF.
Julia source: base/secretbuffer.jl:175-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/essentials.jl:1213-1234; base/io.jl:209-230; base/iostream.jl:223-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EmptyAtBeginningAndEnd : Prop :=
  ∀ {M : Type} (s : SecretBuffer M), ValidCursor s →
    (isemptySecretBuffer s = true ↔
      (positionSecretBuffer s).val = 0 ∧ eofSecretBuffer s = true)

/-- Seeking to the end yields no unread bytes and preserves the logical contents.
Julia source: base/secretbuffer.jl:171-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/iostream.jl:188-195; base/io.jl:130-142,209-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SeekEndCorrect : Prop :=
  ∀ {M : Type} (s : SecretBuffer M), ValidCursor s →
    ∃ result,
      seekendSecretBuffer seekAtInt64 s = .ok result ∧
      result.data = s.data ∧ result.size = s.size ∧
      (positionSecretBuffer result).val = s.size.val ∧
      eofSecretBuffer result = true ∧
      (bytesavailableSecretBuffer result).val = 0

end JuliaLean.Proofs.base.secretbuffer.Round1

namespace JuliaLean.Proofs.base.secretbuffer

open JuliaLean.Registry

end JuliaLean.Proofs.base.secretbuffer

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.C JuliaLean.base.secretbuffer
open JuliaLean.Proofs.base.secretbuffer

-- These arithmetic lemmas use only the original model imports.
theorem secretWrapCongr {a b : Int}
    (h : a % 18446744073709551616 = b % 18446744073709551616) :
    wrapInt .i64 a = wrapInt .i64 b := by
  change (a + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 =
    (b + 9223372036854775808) % 18446744073709551616 - 9223372036854775808
  omega

theorem secretToJIntOfInt (z : Int) :
    (toJInt .i64 (BitVec.ofInt 64 z)).val = wrapInt .i64 z := by
  change wrapInt .i64 (BitVec.ofInt 64 z).toInt = wrapInt .i64 z
  rw [BitVec.toInt_ofInt]
  apply secretWrapCongr
  exact Int.bmod_emod

theorem secretAddVal (x y : I64) :
    (JuliaLean.base.int.add_int x y).val = wrapInt .i64 (x.val + y.val) := by
  simp only [JuliaLean.base.int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add]
  exact secretToJIntOfInt _

theorem secretSubVal (x y : I64) :
    (JuliaLean.base.int.sub_int x y).val = wrapInt .i64 (x.val - y.val) := by
  simp only [JuliaLean.base.int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    Int.sub_eq_add_neg]
  exact secretToJIntOfInt _

theorem secretOneVal : (JInt.lit .i64 1).val = 1 := rfl

theorem secretWrapOfBounds {x : Int}
    (hlo : -9223372036854775808 ≤ x) (hhi : x ≤ 9223372036854775807) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x ⟨hlo, hhi⟩

theorem secretPositionValue {M : Type} (s : SecretBuffer M) (hs : ValidCursor s) :
    (positionSecretBuffer s).val = s.ptr.val - 1 := by
  rcases hs with ⟨hs0, hsmax, hp0, hpmax⟩
  change s.size.val < 4611686018427387904 at hsmax
  rw [positionSecretBuffer, secretSubVal, secretOneVal]
  exact secretWrapOfBounds (by omega) (by omega)

theorem secretAvailableValue {M : Type} (s : SecretBuffer M) (hs : ValidCursor s) :
    (bytesavailableSecretBuffer s).val = s.size.val - s.ptr.val + 1 := by
  rcases hs with ⟨hs0, hsmax, hp0, hpmax⟩
  change s.size.val < 4611686018427387904 at hsmax
  rw [bytesavailableSecretBuffer, secretAddVal, secretSubVal, secretOneVal,
    secretWrapOfBounds (x := s.size.val - s.ptr.val) (by omega) (by omega)]
  exact secretWrapOfBounds (by omega) (by omega)

/-- secretbuffer-cursor-accounting. -/
theorem SecretbufferCursorAccounting_proven : JuliaLean.Proofs.base.secretbuffer.Round1.CursorAccounting := by
  intro M s hs
  rw [secretPositionValue s hs, secretAvailableValue s hs]
  rcases hs with ⟨hs0, hsmax, hp0, hpmax⟩
  omega

/-- iocov-secret-eof-v2. -/
theorem IocovSecretEofV2_proven : JuliaLean.Proofs.base.secretbuffer.Round1.EOFMatchesAvailability := by
  intro M s hs
  rw [secretAvailableValue s hs]
  simp only [eofSecretBuffer, decide_eq_true_eq]
  rcases hs with ⟨hs0, hsmax, hp0, hpmax⟩
  omega

/-- iocov-secret-isempty-v2. -/
theorem IocovSecretIsemptyV2_proven : JuliaLean.Proofs.base.secretbuffer.Round1.EmptyAtBeginningAndEnd := by
  intro M s hs
  rw [secretPositionValue s hs]
  simp only [isemptySecretBuffer, beq_iff_eq, eofSecretBuffer, decide_eq_true_eq]
  rcases hs with ⟨hs0, hsmax, hp0, hpmax⟩
  omega

theorem secretFromInt (x : I64) : (fromJInt x).toInt = x.val := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · exact x.property.1
  · have hx := x.property.2
    change x.val ≤ 9223372036854775807 at hx
    change x.val < 9223372036854775808
    omega

theorem secretWiden (x : I64) : JuliaLean.base.int.widenTo .i64 x = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 x.val x.property

theorem secretLtSame (x y : I64) :
    JuliaLean.base.int.ltSame x y = decide (x.val < y.val) := by
  change decide ((fromJInt x).toInt < (fromJInt y).toInt) = _
  rw [secretFromInt, secretFromInt]

theorem secretLt (x y : I64) :
    JuliaLean.base.int.lt x y = decide (x.val < y.val) := by
  change JuliaLean.base.int.ltSame (JuliaLean.base.int.widenTo .i64 x)
    (JuliaLean.base.int.widenTo .i64 y) = _
  rw [secretWiden, secretWiden, secretLtSame]

theorem secretMin (x y : I64) :
    JuliaLean.base.int.jmin x y = if y.val < x.val then y else x := by
  change JuliaLean.base.int.ifelse
    (JuliaLean.base.int.ltSame (JuliaLean.base.int.widenTo .i64 y)
      (JuliaLean.base.int.widenTo .i64 x))
    (JuliaLean.base.int.widenTo .i64 y) (JuliaLean.base.int.widenTo .i64 x) = _
  rw [secretWiden, secretWiden, secretLtSame]
  simp only [JuliaLean.base.int.ifelse, decide_eq_true_eq]

theorem secretMax (x y : I64) :
    JuliaLean.base.int.jmax x y = if y.val < x.val then x else y := by
  change JuliaLean.base.int.ifelse (JuliaLean.base.int.lt y x) x y = _
  rw [secretLt]
  simp only [JuliaLean.base.int.ifelse, decide_eq_true_eq]

theorem secretConvert (x : I64) : JuliaLean.base.int.convert .i64 x = .ok x := by
  unfold JuliaLean.base.int.convert JInt.convert
  rw [dite_eq_left x.property]

/-- iocov-secret-seekend-v2. -/
theorem IocovSecretSeekendV2_proven : JuliaLean.Proofs.base.secretbuffer.Round1.SeekEndCorrect := by
  intro M s hs
  obtain ⟨hs0, hsmax, hp0, hpmax⟩ := hs
  change s.size.val < 4611686018427387904 at hsmax
  let p := JuliaLean.base.int.add_int s.size (JInt.lit .i64 1)
  let result : SecretBuffer M := { s with ptr := p }
  have hp : p.val = s.size.val + 1 := by
    dsimp only [p]
    rw [secretAddVal, secretOneVal]
    exact secretWrapOfBounds (by omega) (by omega)
  have hp2 : (JuliaLean.base.int.add_int p (JInt.lit .i64 1)).val = s.size.val + 2 := by
    rw [secretAddVal, secretOneVal, hp,
      secretWrapOfBounds (x := s.size.val + 1 + 1) (by omega) (by omega)]
    omega
  have hmin : JuliaLean.base.int.jmin
      (JuliaLean.base.int.add_int p (JInt.lit .i64 1)) p = p := by
    rw [secretMin, ite_eq_left (show p.val <
      (JuliaLean.base.int.add_int p (JInt.lit .i64 1)).val by rw [hp, hp2]; omega)]
  have hmax : JuliaLean.base.int.jmax p (JInt.lit .i64 1) = p := by
    rw [secretMax]
    split
    · rfl
    · apply Subtype.ext
      rw [secretOneVal, hp]
      rename_i h
      rw [secretOneVal, hp] at h
      omega
  have hr : ValidCursor result := by
    change 0 ≤ s.size.val ∧ s.size.val < (2 : Int)^62 ∧
      1 ≤ p.val ∧ p.val ≤ s.size.val + 1
    rw [hp]
    exact ⟨hs0, hsmax, by omega, by omega⟩
  refine ⟨result, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [seekendSecretBuffer, seekAtInt64, seekSecretBuffer,
      bind, Except.bind, pure, Except.pure]
    dsimp only [p] at hmin hmax
    rw [hmin, hmax, secretConvert]
    rfl
  · rw [secretPositionValue result hr]
    change p.val - 1 = s.size.val
    omega
  · change decide (p.val > s.size.val) = true
    exact decide_eq_true (by omega)
  · rw [secretAvailableValue result hr]
    change s.size.val - p.val + 1 = 0
    omega

end JuliaLean.ChatGPT.Batch4.Group14

namespace JuliaLean.Proofs.base.secretbuffer

open JuliaLean.Registry

def entries : List Entry := [
  { id := "secretbuffer-cursor-accounting", juliaFile := "base/secretbuffer.jl",
    juliaFns := ["position", "bytesavailable"],
    statement := "Position and unread byte count are nonnegative and sum to logical size for every valid buffer cursor.",
    source := "base/secretbuffer.jl:175-176; base/io.jl:130-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.secretbuffer.Round1.CursorAccounting, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SecretbufferCursorAccounting_proven },
  { id := "iocov-secret-eof-v2", juliaFile := "base/secretbuffer.jl",
    juliaFns := ["eof", "bytesavailable"],
    statement := "A valid finite secret buffer is at EOF exactly when no unread bytes remain.",
    source := "base/secretbuffer.jl:175-177; base/io.jl:209-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.secretbuffer.Round1.EOFMatchesAvailability, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.IocovSecretEofV2_proven },
  { id := "iocov-secret-isempty-v2", juliaFile := "base/secretbuffer.jl",
    juliaFns := ["isempty", "position", "eof"],
    statement := "A valid secret buffer is empty exactly when it is at both its beginning and EOF.",
    source := "base/secretbuffer.jl:175-178; base/essentials.jl:1213-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.secretbuffer.Round1.EmptyAtBeginningAndEnd, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.IocovSecretIsemptyV2_proven },
  { id := "iocov-secret-seekend-v2", juliaFile := "base/secretbuffer.jl",
    juliaFns := ["seekend", "seek", "position", "eof", "bytesavailable"],
    statement := "Seeking a valid secret buffer to its end preserves contents and size, sets position to size, and leaves no unread bytes.",
    source := "base/secretbuffer.jl:171-177; base/iostream.jl:188-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.secretbuffer.Round1.SeekEndCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.IocovSecretSeekendV2_proven }
]

end JuliaLean.Proofs.base.secretbuffer
