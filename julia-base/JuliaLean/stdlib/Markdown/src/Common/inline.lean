import JuliaLean.stdlib.Markdown.src.parse.parse

/-!
# Markdown: inline readers

Models of `readuntil`, `peekprev`, `parse_inline_wrapper`
(`stdlib/Markdown/src/parse/util.jl`), `read_code_span` and `inline_code`
(`Common/inline.jl`) at master `bbfa0ce4150`.

`isword` (`parse/util.jl:194-202`) needs the Unicode punctuation and symbol
categories; `parse_inline_wrapper` takes it as the argument `isword`. It is only
called when `intraword = false` (the `_` delimiters), so the `*`, `~` and `$`
readers do not depend on it.
-/

namespace JuliaLean.Markdown

/-- `inline_code(stream, md)`, `Common/inline.jl:73-94`. -/
def inlineCode : M (Option Inline) := withstreamOpt do
  match ← readCodeSpan with
  | none => return none
  | some (n, result) =>
    let result := replaceNewlines (strip result)
    return some (if n % 2 == 1 then .code [] result else .latex result)

/-- The text that `asterisk_italic` (`Common/inline.jl:11-15`) wraps in `Italic`. -/
def asteriskItalic (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '*') 1

/-- The text that `asterisk_bold` (`Common/inline.jl:27-31`) wraps in `Bold`. -/
def asteriskBold (isword : Nat → Bool) : M (Option Bytes) := parseInlineWrapper isword (C '*') 2

end JuliaLean.Markdown
