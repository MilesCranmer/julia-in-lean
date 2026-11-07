import JuliaLean.base.flfrontend

namespace JuliaLean.MiscCov.FlFrontend

/-- `fl_parse` rejects another edition with `ErrorException`; otherwise it passes the
byte length `sizeof(text)` of a `String` (and the given length of a `SimpleVector`);
the `AbstractString` method is the `String` method on the converted text; `fl_lower`
passes its arguments, with defaults `"none"`, `0`, `typemax(Csize_t)`, `false`. -/
def Contract : Prop :=
  ∀ (ve e fname : String) (bytes : List Nat) (len : Nat) (lineno offset : Int),
    (e ≠ ve → ∀ text, flParse ve text fname lineno offset e =
      .error (.errorException "Edition not supported by flisp parser")) ∧
    (e = ve → flParse ve (.str bytes) fname lineno offset e = .ok ⟨bytes, bytes.length, fname, lineno, offset⟩ ∧
      flParse ve (.svec bytes len) fname lineno offset e = .ok ⟨bytes, len, fname, lineno, offset⟩) ∧
    flParseAbstract ve bytes fname lineno offset e = flParse ve (.str bytes) fname lineno offset e ∧
    flLower = ⟨"none", 0, 2 ^ 64 - 1, false⟩ ∧
    (∀ w warn, flLower fname lineno w warn = ⟨fname, lineno, w, warn⟩)

theorem contract_proven : Contract := by
  intro ve e fname bytes len lineno offset
  refine ⟨?_, ?_, rfl, rfl, fun _ _ => rfl⟩
  · intro h text; simp [flParse, h]
  · intro h; subst h; simp [flParse]

end JuliaLean.MiscCov.FlFrontend
