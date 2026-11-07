import JuliaLean.base.indices

namespace JuliaLean.AbstractArraySpecs

theorem bind_ok {α β : Type} (a : α) (f : α → R β) : ((Except.ok a : R α) >>= f) = f a := rfl
theorem bind_err {α β : Type} (e : Err) (f : α → R β) : ((Except.error e : R α) >>= f) = .error e := rfl

end JuliaLean.AbstractArraySpecs
