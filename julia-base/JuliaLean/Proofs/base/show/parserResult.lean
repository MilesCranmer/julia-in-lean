import JuliaLean.base.expr

namespace JuliaLean.Show

/-- Result of the parser model on a source text: the parsed tree, a Julia
`ParseError`, or `unknown` when the text leaves the modelled fragment. -/
inductive PResult where
  | ok (e : JE)
  | error
  | unknown
  deriving Repr, Inhabited, DecidableEq

end JuliaLean.Show
