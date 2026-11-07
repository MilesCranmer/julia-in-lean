import JuliaLean.base.coreio

/-!
Shared vocabulary of the `ShowCov` area (`base/show.jl`, `base/strings/io.jl`,
`base/terminfo.jl`, `base/Terminals.jl`, `base/coreio.jl` at master
`bbfa0ce4150`).

Output written to an `IO` is a list of printed pieces (`Out`); the text is
their concatenation. Values whose own `show`/`print` methods live in other
files enter as the strings those methods print.
-/

namespace JuliaLean.ShowCov


@[simp] theorem R.ok_bind {α β : Type} (a : α) (f : α → R β) : (Except.ok a >>= f) = f a := rfl
@[simp] theorem R.error_bind {α β : Type} (e : Err) (f : α → R β) :
    ((Except.error e : R α) >>= f) = Except.error e := rfl
@[simp] theorem R.map_ok {α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : R α)) = Except.ok (f a) := rfl
@[simp] theorem R.map_error {α β : Type} (e : Err) (f : α → β) :
    (f <$> (Except.error e : R α)) = Except.error e := rfl
@[simp] theorem R.pure_eq {α : Type} (a : α) : (pure a : R α) = Except.ok a := rfl


@[simp] theorem Out.text_nil : Out.text [] = "" := rfl
@[simp] theorem Out.text_cons (s : String) (o : Out) : Out.text (s :: o) = s ++ Out.text o := by
  simp [Out.text, String.join_cons]
@[simp] theorem Out.text_append (a b : Out) : Out.text (a ++ b) = Out.text a ++ Out.text b := by
  simp [Out.text, String.join_append]


end JuliaLean.ShowCov
