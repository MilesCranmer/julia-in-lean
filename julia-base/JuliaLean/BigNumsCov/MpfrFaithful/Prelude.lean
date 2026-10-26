import JuliaLean.BigNumsCov.Mpfr

namespace JuliaLean.BigNumsCov.MpfrFaithful

open JuliaLean
open JuliaLean.BigNumsCov
open JuliaLean.BigNumsCov.Mpfr

abbrev BFRep := JuliaLean.BigNumsCov.Mpfr.BigFloatRep
abbrev RMode := JuliaLean.BigNumsCov.Mpfr.Mode
abbrev PMode := JuliaLean.BigNumsCov.Mpfr.PublicMode
abbrev BFField := JuliaLean.BigNumsCov.Mpfr.Field
abbrev BFFieldValue := JuliaLean.BigNumsCov.Mpfr.FieldValue
abbrev BFClass := JuliaLean.BigNumsCov.Mpfr.FloatClass
abbrev IEEEOut := JuliaLean.BigNumsCov.Mpfr.IeeeResult

/-- Observable call order together with a method result. -/
structure Run (α : Type) where
  calls : List String
  value : α
  deriving Repr, DecidableEq

def pureRun (value : α) : Run α := ⟨[], value⟩

def oneCall (name : String) (value : α) : Run α := ⟨[name], value⟩

def appendCall (run : Run α) (name : String) (value : β) : Run β :=
  ⟨run.calls ++ [name], value⟩

inductive PtrInput where
  | pointer | reference
  deriving Repr, DecidableEq

inductive TypeResult where
  | bigFloat | bigInt | rationalBigInt
  deriving Repr, DecidableEq

inductive RefConversionError where
  | errorException (message : String)
  deriving Repr, DecidableEq

end JuliaLean.BigNumsCov.MpfrFaithful
