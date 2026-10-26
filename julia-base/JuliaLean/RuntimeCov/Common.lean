import JuliaLean.Core

/-!
Shared vocabulary for the runtime, startup and reflection files of Julia Base
(`base/runtime_internals.jl`, `base/precompilation.jl`, `base/Base_compiler.jl`,
`base/initdefs.jl`, `base/sysinfo.jl`, `base/client.jl`, `base/options.jl`,
`base/cpuid.jl`, `base/osinfo.jl` at master `bbfa0ce4150`).

These functions mostly combine runtime queries (`ccall`s into libjulia or
libuv, environment variables, the file system).  Every such query is an
explicit parameter of the Lean model, so a property holds for every answer the
runtime may give.  Symbols are modelled by their names.
-/

namespace JuliaLean.RuntimeCov

/-- A Julia `Symbol`, modelled by its name. -/
abbrev Sym := String

/-- Exceptions thrown by the modelled methods, by Julia exception type. -/
inductive RtErr where
  | ioError (code : Int)
  | argumentError (msg : String)
  | boundsError
  | keyError
  | typeError
  | methodError
  | undefRefError
  | fieldError
  | inexactError
  | errorException (msg : String)
  deriving DecidableEq, Repr

/-- Result of a Julia call: a value or a thrown exception. -/
abbrev Rt (α : Type) := Except RtErr α

/-- `Base.uv_error(prefix, err)`: throws an `IOError` exactly when `err < 0`. -/
def uvError (err : Int) : Rt Unit :=
  if err < 0 then .error (.ioError err) else .ok ()

/-- `Base.UV_ENOENT` and `Base.UV_EACCES` (negated POSIX codes, libuv convention). -/
def UV_ENOENT : Int := -2
def UV_EACCES : Int := -13

theorem uvError_ok_iff (err : Int) : uvError err = .ok () ↔ 0 ≤ err := by
  unfold uvError; split <;> simp_all <;> omega

/-- `lpad(s, n)` on ASCII text: left-pad with spaces to at least `n` characters. -/
def lpad (s : String) (n : Nat) : String :=
  String.ofList (List.replicate (n - s.length) ' ') ++ s

end JuliaLean.RuntimeCov
