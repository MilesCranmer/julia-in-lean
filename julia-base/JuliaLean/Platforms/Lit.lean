import Lean

/-! String literals as character lists for the `Platforms` model. -/

namespace JuliaLean.Platforms

/-- `s% "abc"`: the characters of a string literal as a `List Char` literal
(computed at elaboration time, so the kernel never decodes a `String`). -/
elab "s% " s:str : term => return Lean.toExpr s.getString.toList

end JuliaLean.Platforms
