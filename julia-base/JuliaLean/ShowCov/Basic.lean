import JuliaLean.Core

/-!
Shared vocabulary of the `ShowCov` area (`base/show.jl`, `base/strings/io.jl`,
`base/terminfo.jl`, `base/Terminals.jl`, `base/coreio.jl` at master
`bbfa0ce4150`).

Output written to an `IO` is a list of printed pieces (`Out`); the text is
their concatenation. Values whose own `show`/`print` methods live in other
files enter as the strings those methods print.
-/

namespace JuliaLean.ShowCov

/-- Julia exceptions thrown by the modelled methods. -/
inductive Err where
  | errorException (msg : String)
  | argumentError (msg : String)
  | keyError (key : String)
  | methodError (fn : String)
  | eofError
  | boundsError
  | inexactError (fn : String)
  | typeError
  deriving Repr, DecidableEq, Inhabited

/-- Julia computations that may throw. -/
abbrev R (α : Type) := Except Err α

instance instDecidableEqR {α : Type} [DecidableEq α] : DecidableEq (R α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

@[simp] theorem R.ok_bind {α β : Type} (a : α) (f : α → R β) : (Except.ok a >>= f) = f a := rfl
@[simp] theorem R.error_bind {α β : Type} (e : Err) (f : α → R β) :
    ((Except.error e : R α) >>= f) = Except.error e := rfl
@[simp] theorem R.map_ok {α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : R α)) = Except.ok (f a) := rfl
@[simp] theorem R.map_error {α β : Type} (e : Err) (f : α → β) :
    (f <$> (Except.error e : R α)) = Except.error e := rfl
@[simp] theorem R.pure_eq {α : Type} (a : α) : (pure a : R α) = Except.ok a := rfl

/-- Pieces printed to a stream, in order. -/
abbrev Out := List String

/-- The text a list of printed pieces forms. -/
def Out.text (o : Out) : String := String.join o

@[simp] theorem Out.text_nil : Out.text [] = "" := rfl
@[simp] theorem Out.text_cons (s : String) (o : Out) : Out.text (s :: o) = s ++ Out.text o := by
  simp [Out.text, String.join_cons]
@[simp] theorem Out.text_append (a b : Out) : Out.text (a ++ b) = Out.text a ++ Out.text b := by
  simp [Out.text, String.join_append]

/-- `string(n::Int)`: decimal digits with a leading `-` for negatives. -/
def intStr (n : Int) : String := toString n

end JuliaLean.ShowCov
