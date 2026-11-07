import JuliaLean.base.strings.string


/-!
# Strings as UTF-8 code units

Model of `String` from `base/strings/string.jl` and the generic index
functions of `base/strings/basic.jl` (master `bbfa0ce4150`).

* A `String` is its byte sequence (`JStr.bytes`), with no validity
  requirement: overlong forms, surrogates, truncated sequences and stray
  continuation bytes are all representable, exactly as in Julia
  (`base/strings/string.jl:80-90`).
* A `Char` is its 32-bit encoded bit pattern (`base/char.jl:39-52`): the
  UTF-8 bytes of the character, left-aligned, padded with zero bytes.
  Bit patterns are Lean `UInt8`/`UInt32`, whose operators are the
  fixed-width wrapping operators Julia uses on those types.
* Indices and counts are `Int` (`JInt64`) and use the wrapping `JInt`
  operators, so overflow happens exactly where Julia overflows.
* Julia's `while` loops are written as structural recursion on an explicit
  bound on the number of remaining iterations (for example `n - i` when `i`
  increases towards `n`). Each docstring states the bound; when it reaches
  zero the loop condition is false, so the bound never truncates a run.
-/

namespace JuliaLean.Strings

/-- Complete iteration traces: `xs` lists the `(char, index)` pairs produced by
iterating `s` from state `i` until `iterate` returns `nothing`. -/
inductive IterTrace (s : JStr) : JInt64 → List (UInt32 × JInt64) → Prop where
  | done {i} : iterate s i = none → IterTrace s i []
  | step {i c j xs} : iterate s i = some (c, j) → IterTrace s j xs →
      IterTrace s i ((c, i) :: xs)

end JuliaLean.Strings
