import JuliaLean.base.broadcast
import JuliaLean.base.multidimensional

namespace JuliaLean.base.broadcast.AliasExamples
open JuliaLean.BroadcastViews
/--
Julia source: base/broadcast.jl:1001-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
broadcast_unalias(::Nothing, src) = src
```
-/
def bcSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  let src := Material.m1001 (fun a b : List Nat => a == b) (fun _ src => src) dpos dpos
  let result : Except Empty (Unit × List Int) :=
    Material.copyLoop (m := StateT (List Int) (Except Empty))
      (fun (_ : Unit) p memory => .ok (memory.getD p 0 + c, memory))
      (fun (_ : Unit) p value memory => .ok ((), memory.set p value))
      () () src mem
  match result with
  | .ok (_, memory) => memory
  | .error impossible => nomatch impossible
end JuliaLean.base.broadcast.AliasExamples
