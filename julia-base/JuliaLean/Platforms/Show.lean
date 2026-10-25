import JuliaLean.Platforms.Lemmas

/-!
# `show(io, p::Platform)` (`base/binaryplatforms.jl:198-209`)
-/

namespace JuliaLean.Platforms

open JuliaLean

/-- The keyword-argument names `show(io, p::Platform)` prints: every tag name
other than `arch` and `os`, sorted (`base/binaryplatforms.jl:206-207`). -/
def showKeys (p : Platform) : List Str :=
  (sortBy (fun a b => strLt a.1 b.1) (p.tags.filter fun kv => kv.1 != s% "arch" && kv.1 != s% "os")).map (·.1)

/-- Julia's reserved words. -/
def juliaKeywords : List Str :=
  [s% "baremodule", s% "begin", s% "break", s% "catch", s% "const", s% "continue", s% "do", s% "else",
   s% "elseif", s% "end", s% "export", s% "false", s% "finally", s% "for", s% "function", s% "global",
   s% "if", s% "import", s% "let", s% "local", s% "macro", s% "module", s% "quote", s% "return",
   s% "struct", s% "true", s% "try", s% "using", s% "while"]

/-- Sufficient conditions for a name not to be usable as a keyword argument
(`Base.isidentifier` is false): it contains `.`, starts with an ASCII digit, or
is a reserved word. -/
def NotIdentifier (k : Str) : Prop :=
  '.' ∈ k ∨ (∃ c r, k = c :: r ∧ isAsciiDigit c = true) ∨ k ∈ juliaKeywords

/-- Every name `show` prints as a keyword argument can be one, for every
platform accepted with `validate_strict = true` (so `repr(p)` is valid Julia,
as the comment "Allow us to easily serialize Platform objects" intends). -/
def ShowKeysAreNames : Prop :=
  ∀ lc, LcSpec lc → ∀ (a o : Str) (ts : List (Str × TagVal)) (p : Platform),
    platform lc a o ts true = .ok p → ∀ k ∈ showKeys p, ¬ NotIdentifier k

def dottedTagPlatform : Platform :=
  ⟨[(s% "arch", s% "x86_64"), (s% "os", s% "linux"), (s% "cuda.version", s% "11.8"), (s% "libc", s% "glibc")], []⟩

theorem dottedTag_ctor :
    platform asciiLower (s% "x86_64") (s% "linux") [(s% "cuda.version", .str (s% "11.8"))] true =
      .ok dottedTagPlatform := by decide +kernel

theorem dottedTag_showKeys : showKeys dottedTagPlatform = [s% "cuda.version", s% "libc"] := by decide +kernel

theorem showKeysAreNames_refuted : ¬ ShowKeysAreNames := by
  intro h
  have := h asciiLower asciiLower_spec _ _ _ _ dottedTag_ctor (s% "cuda.version")
    (by rw [dottedTag_showKeys]; exact List.mem_cons_self)
  exact this (Or.inl (by decide))

end JuliaLean.Platforms
