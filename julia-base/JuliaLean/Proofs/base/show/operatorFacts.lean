import JuliaLean.base.meta


namespace JuliaLean.Show


/-- The table entries confirmed on Julia 1.13.2 and master (module docstring). -/
def OpData.Faithful (o : OpData) : Prop :=
  o.prec "+" = 11 ∧ o.prec "-" = 11 ∧ o.prec "*" = 12 ∧ o.prec "/" = 12 ∧
  o.prec "^" = 15 ∧ o.prec "::" = 16 ∧ o.prec "=" = 1 ∧ o.prec "//" = 13 ∧
  o.prec ":" = 10 ∧ o.prec "=>" = 2 ∧ o.prec "==" = 7 ∧ o.prec "<" = 7 ∧
  o.prec "&&" = 6 ∧ o.prec "||" = 5 ∧ o.prec "." = 17 ∧ o.prec ".&&" = 6 ∧
  o.prec ".||" = 5 ∧ o.prec "'" = 0 ∧ o.prec "!" = 0 ∧ o.prec "<:" = 7 ∧
  o.prec ".+" = 11 ∧ o.prec "√" = 0 ∧ o.prec "~" = 1 ∧
  (∀ s ∈ ["+", "-", "*", "/", "^", "::", "=", "'", "!", "~", "&&", "||", ".&&", ".", "..",
      "...", "?", "$", "->", "-->", "<:", ">:", "%", "&", "|", "\\", "<<", ">>", ">>>", "==",
      "!=", "<", ">", "<=", ">=", "===", "!==", "=>", "|>", "<|", ":", "+=", ".+", ".=", "√", "∈"],
    o.isOp s = true) ∧
  (∀ s ∈ ["x", "end", "a b"], o.isOp s = false) ∧
  (∀ s ∈ ["+", "-", "!", "~", "<:", ">:", ".+", "√"], o.isUnaryOp s = true) ∧
  (∀ s ∈ ["*", "/", "^", "::", "=", "'", "&&", "||", ".&&", ".", "..", "...", "?", "$", "->",
      "-->", "%", "&", "|", "\\", "<<", ">>", ">>>", "==", "!=", "<", ">", "<=", ">=", "===",
      "!==", "=>", "|>", "<|", ":", "+=", ".=", "∈", "x", "end", "a b"],
    o.isUnaryOp s = false) ∧
  (∀ s ∈ ["=", "&&", "||", ".&&", ".", "...", "->", "+=", ".="], o.isSyntacticOp s = true) ∧
  (∀ s ∈ ["+", "-", "*", "/", "^", "::", "'", "!", "~", "..", "?", "$", "-->", "<:", ">:",
      "%", "&", "|", "\\", "<<", ">>", ">>>", "==", "!=", "<", ">", "<=", ">=", "===", "!==",
      "=>", "|>", "<|", ":", ".+", "√", "∈", "x", "end", "a b"],
    o.isSyntacticOp s = false) ∧
  (∀ s ∈ ["a", "b", "f", "k", "T", "y", "Symbol", "Core", "@cmd"],
    o.isOp s = false ∧ o.isUnaryOp s = false ∧ o.isSyntacticOp s = false ∧ o.prec s = 0) ∧
  o.isOp ".-" = true ∧ o.isUnaryOp ".-" = true ∧ o.isSyntacticOp ".-" = false ∧ o.prec ".-" = 11

end JuliaLean.Show
