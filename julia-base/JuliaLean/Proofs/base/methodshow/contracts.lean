import JuliaLean.base.methodshow


namespace JuliaLean.ErrorShow


def MethodDisplayModes : Prop := ∀ method : MethodView,
  showMethod method true false = methodSignature method ++ " " ++ method.location ∧
    showMethod method false false = methodSignature method ++ "\n    " ++ method.location ∧
    showMethod method false true = methodSignature method

theorem methodDisplayModes_proven : MethodDisplayModes := by
  intro method
  simp [showMethod]

end JuliaLean.ErrorShow
