import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.RuntimeInternals

open JuliaLean
open JuliaLean.C

/--
Julia source: base/runtime_internals.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isprimitivetype(@nospecialize t)
    @_total_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    isa(t, DataType) || return false
    return (t.flags & 0x0080) == 0x0080
end
```
-/
def isPrimitiveType : Body := fun call args => do
  let [arg] := args | throwMethodError "isprimitivetype(t): arity"
  let t ← call "Base.unwrap_unionall" [arg]
  let .type ty@(.datatype _ _) := t | return mkBool false
  let st ← get
  let some (_, flags) := st.typeFlags.find? (fun (dt, _) => dt == ty)
    | throw (.internal s!"missing DataType.flags for {repr ty}")
  let mask : Obj := .bits uint16Type 0x0080
  let masked ← call "Base.&" [.bits uint16Type (Int.ofNat flags), mask]
  call "Base.==" [masked, mask]

def bodies : List (String × Body) :=
  [("base/runtime_internals.jl:885", isPrimitiveType)]

end JuliaLean.Pilot.Base.RuntimeInternals
