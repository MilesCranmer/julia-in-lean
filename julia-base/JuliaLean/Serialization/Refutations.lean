import JuliaLean.Serialization.Props

/-!
Counterexamples, checked by evaluating the model.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-- Whether a decode ended in `EOFError`. -/
def isEofErr : Except SErr (Obj × Bytes) → Bool
  | .error .eof => true
  | _ => false

/-- `'\xc0'` (the `Char` of the string `"\xc0"`) followed by `Int32(1)`: `read(io, Char)`
takes the tag byte `0xbf` of `Int32(1)` as a continuation byte, and the tuple's
second element then hits the end of the stream. -/
theorem charPair_eof :
    isEofErr (deserialize (serialize (.tup [.char 0xc0000000, .int .i32 1]))) = true := by
  decide +kernel

/-- With a further value in the stream the result is silently wrong:
`serialize(io, ('\xc0', Int32(1))); serialize(io, 42)` reads back `('\xc0\xbf', 42)` and
leaves nothing for the second `deserialize`, as Julia does (`repro/serialization-char-malformed.jl`). -/
theorem charPair_misread :
    (match deserialize (serialize (.tup [.char 0xc0000000, .int .i32 1]) ++ serialize (.int .i64 42)) with
      | .ok (.v y, []) => y == .tup [.char 0xc0bf0000, .int .i64 42]
      | _ => false) = true := by
  decide +kernel

theorem charRoundTrip_refuted : ¬ CharRoundTrip := by
  intro h
  have hc := h 0xc0000000 (by decide) 1
    (by simp [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])
  have he := charPair_eof
  rw [hc] at he
  exact absurd he (by decide)

/-- A user `primitive type Bits32 32 end`: `write(io, x)` has no method. -/
theorem primitiveRoundTrip_refuted : ¬ PrimitiveRoundTrip := by
  intro h
  have := h (.user [66, 105, 116, 115, 51, 50] 4) 0x01020304 (by decide)
  simp [primRoundTrip, writePrim, bind, Except.bind] at this

end JuliaLean.Serialization
