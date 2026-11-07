import JuliaLean.base.opaque_closure

namespace JuliaLean.MiscCov.OpaqueClosure

/-- The macros build the documented `:opaque_closure` expression (no types, or the
argument and return types of `AT -> RT`, with `_` meaning unspecified) and reject any
other type syntax; `Core.OpaqueClosure` asks for return type bounds `Union{}` to
`rettype` with the defaults of `generate_opaque_closure`. -/
def Contract : Prop :=
  (∀ ex, opaque1 ex = Ex.esc (.expr "opaque_closure" [.nothing, .nothing, .nothing, .bool true, ex])) ∧
  (∀ (AT RT ex : Ex), RT.isLnn = false →
    opaque2 (.expr "->" [AT, .expr "block" [.lnn, RT]]) ex =
      .ok (Ex.esc (.expr "opaque_closure"
        [if AT.isSym "_" then .nothing else AT, if RT.isSym "_" then .nothing else RT,
         if RT.isSym "_" then .nothing else RT, .bool true, ex]))) ∧
  (∀ ty ex, (∀ AT body, ty ≠ .expr "->" [AT, body]) →
    opaque2 ty ex = .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")) ∧
  (∀ (AT ex : Ex) (xs : List Ex), (xs.filter (fun x => !x.isLnn)).length ≠ 1 →
    opaque2 (.expr "->" [AT, .expr "block" xs]) ex =
      .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")) ∧
  (∀ env rettype sig nargs isva, ofCodeInfo env rettype sig nargs isva =
    ⟨sig, "Union{}", rettype, "Base", 0, none, nargs, isva, env, true, true⟩)

theorem contract_proven : Contract := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, fun _ _ _ _ _ => rfl⟩
  · intro AT RT ex hRT
    have hl : Ex.isLnn .lnn = true := rfl
    have hf : ([Ex.lnn, RT].filter (fun x => !x.isLnn)) = [RT] := by
      simp only [List.filter, hl, hRT, Bool.not_true, Bool.not_false]
    simp only [opaque2, Ex.args?, Option.getD_some, hf, Ex.isExpr]
    cases ha : AT.isSym "_" <;> cases hr : RT.isSym "_" <;> simp [ha, hr, List.head!]
  · intro ty ex h
    unfold opaque2
    split
    · rename_i AT body; exact absurd rfl (h AT body)
    · rfl
  · intro AT ex xs h
    simp [opaque2, Ex.args?, Ex.isExpr, h]

end JuliaLean.MiscCov.OpaqueClosure
