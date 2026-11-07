import JuliaLean.stdlib.Random.src.generation
import JuliaLean.stdlib.Random.src.normal
import JuliaLean.base.special.log
import JuliaLean.base.float

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- The `UInt8` path of `randstring(r, chars, n)`, `misc.jl:73-78`: `n` bytes, each
`chars[rand(r, 1:length(chars))]` through one `Val(Inf)` array sampler
(`generation.jl:469-473`). -/
def randstringBytes {σ : Type} (g : Rng σ) (fuel : Nat) (chars : List UInt8) (n : Nat)
    (st : σ) : Run σ (List UInt8) :=
  match ndlSampler (JInt.lit .i64 1) (JInt.lit .i64 chars.length) with
  | .error e => some (.error e)
  | .ok sp =>
    let rec go : Nat → σ → List UInt8 → Run σ (List UInt8)
      | 0, st, acc => some (.ok (acc, st))
      | k + 1, st, acc =>
        match ndlRand g sp fuel st with
        | none => none
        | some (.error e) => some (.error e)
        | some (.ok (i, st')) => go k st' (acc ++ [chars.getD (i.val.toNat - 1) 0])
    go n st []

/-! ## `randperm!`, `randcycle!`, `shuffle!` -/

/-- `a[k] = v` on a one-based array represented as a function. -/
def update (a : Nat → Int) (k : Nat) (v : Int) : Nat → Int := fun x => if x = k then v else a x

/-- The loop `for i = 2:n; j = rand(rng, 1:hi(i)); body; end` shared by `randperm!`,
`randcycle!` and `shuffle!`; `k` iterations remain and the next index is `i`. `draw h` is
`rand(rng, 1:h)` (`randIndex`); it is a parameter so that unfolding the loop never
evaluates the `Int64` literals of the range. -/
def permLoop {σ : Type} (draw : Nat → σ → Run σ JInt64) (hi : Nat → Nat)
    (body : Nat → Nat → (Nat → Int) → (Nat → Int)) :
    Nat → Nat → (Nat → Int) → σ → Run σ (Nat → Int)
  | 0, _, a, st => some (.ok (a, st))
  | k + 1, i, a, st =>
    match draw (hi i) st with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (j, st')) => permLoop draw hi body k (i + 1) (body i j.val.toNat a) st'

/-- Loop body of `randperm!`, `misc.jl:355-359`. -/
def randpermBody (i j : Nat) (a : Nat → Int) : Nat → Int :=
  if i ≠ j then update (update a i (a j)) j i else update a j i

/-- Loop body of `randcycle!` (Sattolo), `misc.jl:437-439`. -/
def randcycleBody (i j : Nat) (a : Nat → Int) : Nat → Int := update (update a i (a j)) j i

/-- Loop body of `shuffle!`, `misc.jl:240-241`: `a[i], a[j] = a[j], a[i]`. -/
def shuffleBody (i j : Nat) (a : Nat → Int) : Nat → Int := update (update a i (a j)) j (a i)

/-- The `#undef` contents of `Vector{Int}(undef, n)`; never read by the modelled code. -/
def undefArray : Nat → Int := fun _ => 0

/-- `randperm(r, n::Int) = randperm!(r, Vector{Int}(undef, n))`, `misc.jl:322,348-362`. -/
def randperm {σ : Type} (g : Rng σ) (fuel n : Nat) (st : σ) : Run σ (Nat → Int) :=
  if n = 0 then some (.ok (undefArray, st))
  else permLoop (randIndex g fuel) id randpermBody (n - 1) 2 (update undefArray 1 1) st

/-- `randcycle(r, n::Int)`, `misc.jl:398,429-442`. -/
def randcycle {σ : Type} (g : Rng σ) (fuel n : Nat) (st : σ) : Run σ (Nat → Int) :=
  if n = 0 then some (.ok (undefArray, st))
  else permLoop (randIndex g fuel) (fun i => i - 1) randcycleBody (n - 1) 2 (update undefArray 1 1) st

/-- `shuffle!(r, a)` for a length-`n` `Vector{Int}` `a`, `misc.jl:236-244`. -/
def shuffle {σ : Type} (g : Rng σ) (fuel n : Nat) (a : Nat → Int) (st : σ) : Run σ (Nat → Int) :=
  permLoop (randIndex g fuel) id shuffleBody (n - 1) 2 a st

/-- The `p > 0.15` loop of `randsubseq!`, `misc.jl:117-119`. -/
def bernoulliLoop {σ : Type} (g : Rng σ) (p : F64) : List Int → List Int → σ → Run σ (List Int)
  | [], S, st => some (.ok (S, st))
  | x :: xs, S, st =>
    let (u, st') := randFloat64 g st
    bernoulliLoop g p xs (if F64.le u p then S ++ [x] else S) st'

/-- The geometric-skip loop of `randsubseq!`, `misc.jl:129-135`; `fuel` bounds both the
loop and each `randexp` call. -/
def skipLoop {σ : Type} (g : Rng σ) (fuel : Nat) (A : List Int) (L : F64) :
    Nat → JInt64 → List Int → σ → Run σ (List Int)
  | 0, _, _, _ => none
  | k + 1, i, S, st =>
    match randexp g fuel st with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (e, st')) =>
      let s := F64.mul e L
      if intLeF64 (JInt.lit .i64 A.length - i) s then some (.ok (S, st'))
      else match F64.ceilInt .i64 s with
        | .error err => some (.error err)
        | .ok c =>
          let i' := i + c
          if 1 ≤ i'.val ∧ i'.val ≤ A.length then
            skipLoop g fuel A L k i' (S ++ [A.getD (i'.val.toNat - 1) 0]) st'
          else some (.error .boundsError)

/-- `0.15`. -/
def f015 : F64 := F64.ofBits 4594572339843380019

/-- `randsubseq(r, A, p)` for `A::Vector{Int}` and `p::Float64`, `misc.jl:107-141,166-167`. -/
def randsubseq {σ : Type} (g : Rng σ) (fuel : Nat) (A : List Int) (p : F64) (st : σ) :
    Run σ (List Int) :=
  if !(F64.le (F64.zero) p && F64.le p F64.one) then
    some (.error (.argumentError "probability not in [0,1]"))
  else if F64.eq p F64.one then some (.ok (A, st))
  else if F64.eq p F64.zero then some (.ok ([], st))
  else if F64.lt f015 p then bernoulliLoop g p A [] st
  else
    match MathFuncs.log1p (F64.neg p) with
    | .error e => some (.error e)
    | .ok l => skipLoop g fuel A (F64.div (F64.ofInt (-1)) l) fuel (JInt.lit .i64 0) [] st

end JuliaLean.RandomSampling
