import JuliaLean.base.osutils

namespace JuliaLean.MiscCov.Static

/-- `@static` selects exactly the branch the run-time conditional would take: for
`if c a [else b]`, `a` when `c` is true, else the `else`/`elseif` part (recursively) or
`nothing`; for `c && a`, `a` or `false`; for `c || a`, `true` or `a`; a non-`Bool`
condition is a `TypeError` and any other expression an `ArgumentError`. -/
def Contract : Prop :=
  ∀ (evalCond : Ex → M Ex) (fuel : Nat) (c a b : Ex),
    (evalCond c = .ok (.bool true) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "if" [c, a, b]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "&&" [c, a]) = .ok (Ex.esc a) ∧
      static evalCond (fuel + 1) (.expr "||" [c, a]) = .ok (.bool true)) ∧
    (evalCond c = .ok (.bool false) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .ok .nothing ∧
      ((¬ b.isExpr "elseif") → static evalCond (fuel + 1) (.expr "if" [c, a, b]) = .ok (Ex.esc b)) ∧
      (∀ bargs, static evalCond (fuel + 1) (.expr "if" [c, a, .expr "elseif" bargs]) =
        static evalCond fuel (.expr "elseif" bargs)) ∧
      static evalCond (fuel + 1) (.expr "&&" [c, a]) = .ok (.bool false) ∧
      static evalCond (fuel + 1) (.expr "||" [c, a]) = .ok (Ex.esc a)) ∧
    (∀ v, evalCond c = .ok v → (∀ x, v ≠ .bool x) →
      static evalCond (fuel + 1) (.expr "if" [c, a]) = .error .typeError) ∧
    (∀ hd args, hd ∉ ["if", "elseif", "&&", "||"] →
      static evalCond (fuel + 1) (.expr hd args) = .error (.argumentError "invalid @static macro")) ∧
    (∀ x, (∀ hd args, x ≠ .expr hd args) →
      static evalCond (fuel + 1) x = .error (.argumentError "invalid @static macro"))

theorem contract_proven : Contract := by
  intro evalCond fuel c a b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [static, h, bind, Except.bind, pure, Except.pure]
  · intro h
    refine ⟨by simp [static, h, bind, Except.bind, pure, Except.pure], ?_, ?_,
      by simp [static, h, bind, Except.bind, pure, Except.pure],
      by simp [static, h, bind, Except.bind, pure, Except.pure]⟩
    · intro hb
      cases b with
      | expr hd args =>
        by_cases he : hd = "elseif"
        · subst he; simp [Ex.isExpr] at hb
        · simp [static, h, bind, Except.bind, pure, Except.pure, he]
      | _ => simp [static, h, bind, Except.bind, pure, Except.pure]
    · intro bargs; simp [static, h, bind, Except.bind, pure, Except.pure]
  · intro v h hv
    cases v <;> simp_all [static, bind, Except.bind]
  · intro hd args hn
    simp [static, hn]
  · intro x hx
    cases x <;> simp_all [static]

end JuliaLean.MiscCov.Static
