import JuliaLean.Core

namespace JuliaLean.Strings

/-- Error variants returned by Julia's `show` methods. -/
inductive ShowDictErrorKind where
  | keyError
  | keyTypeError
  | argumentError
  | undefRef
  | thrownDict
  | diverges
  | typeError
  | concurrentWrite
  | inexactError
  deriving Repr, DecidableEq

inductive ShowErrorKind where
  | errorException (message : String)
  | assertionError (message : String)
  | dict (error : ShowDictErrorKind)
  | typeError
  | stringIndexError
  | undefRefError
  deriving Repr, DecidableEq

/-- Exceptions thrown by the modelled string functions. `jl` wraps the shared
`JlError` (BoundsError, ArgumentError, ...); the others are
`StringIndexError` (`base/strings/string.jl:56`), `OutOfMemoryError`,
`InvalidCharError` and `CodePointError` (`base/char.jl:102-107`), an
`@assert` failure, and errors carried from `show` methods. -/
inductive SErr where
  | jl (e : JlError)
  | stringIndexError (i : Int)
  | outOfMemory
  | invalidChar (bits : UInt32)
  | codePointError (u : UInt32)
  | assertion
  | showError (error : ShowErrorKind)
  deriving Repr, DecidableEq, Inhabited

abbrev SJl (α : Type) := Except SErr α

abbrev boundsErr : SErr := .jl .boundsError

/-- A Julia `String`: its UTF-8 code units. Julia cannot allocate `2^62` bytes,
so every String is shorter; the bound keeps `ncodeunits(s) + 1`-style index
arithmetic exact, as it is in Julia. -/
structure JStr where
  bytes : List UInt8
  small : bytes.length < 2 ^ 62

instance : DecidableEq JStr := fun a b =>
  if h : a.bytes = b.bytes then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; cases e; exact h rfl)

instance : Repr JStr := ⟨fun s _ => repr s.bytes⟩

def JStr.empty : JStr := ⟨[], by decide⟩

/-- Integer literal of type `Int`. -/
abbrev ix (x : Int) : JInt64 := JInt.lit .i64 x

/-- `Int(b)` for a Bool, as used in `n -= isvalid(s, i)`. -/
abbrev bInt (b : Bool) : JInt64 := ix (if b then 1 else 0)

theorem slice_small (s : JStr) (a b : Nat) : ((s.bytes.drop a).take b).length < 2 ^ 62 := by
  have := s.small; simp only [List.length_take, List.length_drop]; omega

/-- The fresh String holding `len` code units of `s` starting after byte `a`
(`unsafe_copyto!` from `pointer(s, a + 1)`). -/
def JStr.slice (s : JStr) (a len : Nat) : JStr := ⟨(s.bytes.drop a).take len, slice_small s a len⟩

end JuliaLean.Strings

namespace JuliaLean.Strings

/-- `SubString{String}`, `base/strings/substring.jl:71-106`. -/
structure JSub where
  str : JStr
  offset : JInt64
  ncu : JInt64
  deriving DecidableEq, Repr

end JuliaLean.Strings
