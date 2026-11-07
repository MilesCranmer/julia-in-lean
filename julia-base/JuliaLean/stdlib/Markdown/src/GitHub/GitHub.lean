import JuliaLean.stdlib.Markdown.src.Common.block

namespace JuliaLean.Markdown

/-- The character loop of `github_paragraph`, `GitHub/GitHub.jl:10-26`. -/
def githubParagraphLoop (brk : M Bool) : Bytes → Nat → M Bytes
  | _, 0 => throw .outOfFuel
  | buf, fuel + 1 => do
    if ← eof then return buf
    let mut char ← readChar
    if char == C '\r' then
      if (← peekChar) == C '\n' then
        let _ ← readChar
      char := C '\n'
    if char == C '\n' then
      if ← eof then return buf
      if ← blankline then return buf
      if ← brk then return buf
      githubParagraphLoop brk (buf ++ [10]) fuel
    else
      githubParagraphLoop brk (buf ++ charBytes char) fuel

/-- `github_paragraph(stream, md)`, `GitHub/GitHub.jl:5-28`: the paragraph content. -/
def githubParagraph {α} (brk : M Bool) (inl : Bytes → Except Err α) : M α := do
  skipwhitespace
  let s ← get
  let buf ← githubParagraphLoop brk [] (s.data.length - s.pos + 1)
  liftExcept (inl buf)

end JuliaLean.Markdown
