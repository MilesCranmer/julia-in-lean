import JuliaLean.Core
import JuliaLean.base.int

namespace JuliaLean.RandomSampling

open JuliaLean

/-- A request the sampling code makes of the RNG: `rand(rng, U)` for a `BitInteger`
type `U`, or `rand(rng, UInt52Raw())` (`Random.jl:64-65`, a `UInt64`). -/
inductive Req where
  | int (u : IntTy)
  | raw52

/-- The Julia type of the answer to a request. -/
def Req.Out : Req → Type
  | .int u => JInt u
  | .raw52 => JInt .u64

/-- An arbitrary RNG: a state machine answering requests. -/
structure Rng (σ : Type) where
  next : σ → (q : Req) → q.Out × σ

/-- Outcome of a call that consumes random words (see the module docstring). -/
abbrev Run (σ α : Type) := Option (Jl (α × σ))

/-- `rand(rng, LessThan(sup, Masked(mask, uniform(U))))`, `Random.jl:231-243`. -/
def lessThanMasked {σ : Type} (g : Rng σ) (u : IntTy) (sup mask : JInt u) :
    Nat → σ → Option (JInt u × σ)
  | fuel, st =>
    let p := g.next st (.int u)
    let w : JInt u := p.1
    let x := band w mask
    if x.val ≤ sup.val then some (x, p.2)
    else match fuel with
      | 0 => none
      | f + 1 => lessThanMasked g u sup mask f p.2

end JuliaLean.RandomSampling
