import JuliaLean.Strings.Char

/-!
# `textwidth`, `base/strings/unicode.jl:270-298`

The column width of a valid non-ASCII character comes from the C library
call `utf8proc_charwidth`, which the model does not contain. Every
definition here takes that function as the parameter `cw`, mapping a code
point to its width; properties quantify over all `cw` (utf8proc returns 0, 1
or 2).
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings

/-- `textwidth(c::Char)`, `base/strings/unicode.jl:272-282`:
`b = bswap(u)`; `b < 0x7f && return Int(b >= 0x20)`; malformed or overlong
characters have width 1; otherwise `utf8proc_charwidth(unsafe_codepoint(c))`,
here `cw` of the code point. `codepoint` cannot fail on that branch (it
rejects exactly the malformed characters), so its error case is unreachable. -/
def textwidthChar (cw : UInt32 → Int) (c : UInt32) : Int :=
  let b := bswap32 c
  if b < 0x7f then (if b ≥ 0x20 then 1 else 0)
  else if ismalformed c || isOverlongEnc c then 1
  else
    match codepoint c with
    | .ok u => cw u
    | .error _ => 1

/-- `textwidth(s::String) = mapreduce(textwidth, +, s; init=0)`,
`base/strings/unicode.jl:297`: the sum over the characters that iterating `s`
yields (`Strings.chars`). The sum is an `Int` in Julia; with widths `0 ≤ cw ≤ 2`
and fewer than `2^62` characters it stays below `2^63`, so it never wraps. -/
def textwidth (cw : UInt32 → Int) (s : JStr) : Int :=
  (chars s).foldl (fun acc c => acc + textwidthChar cw c) 0

end JuliaLean.StringUtil
