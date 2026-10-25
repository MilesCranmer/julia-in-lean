import JuliaLean.Core

/-!
`unique`, `allunique` and `allequal` on `Vector{Int}`, `base/set.jl` (master
`bbfa0ce4150`). For `Int`, `isequal` is `==`, `isless` is `<`, `OrderStyle(Int)` is
`Ordered()`, and a `Set{Int}` is modelled as the list of the values inserted so far.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

/-- `unique(itr)` for an iterator with an element type, `base/set.jl:224-233`:
`!in!(x, seen) && push!(out, x)`. -/
def uniqueLoop (seen : List Int) : List Int → List Int
  | [] => []
  | x :: rest => if x ∈ seen then uniqueLoop seen rest else x :: uniqueLoop (x :: seen) rest

def unique (v : List JInt64) : List JInt64 :=
  (uniqueLoop [] (v.map (·.val))).map (JInt.wrap .i64)

/-- `_hashed_allunique(C)`, `base/set.jl:525-542`: `in!(v, seen) && return false`
over the elements (the first 1000 elements are scanned separately before a `sizehint!`,
which does not change the result). -/
def hashedLoop (seen : List Int) : List Int → Bool
  | [] => true
  | x :: rest => if x ∈ seen then false else hashedLoop (x :: seen) rest

/-- `_indexed_allunique(A)`, `base/set.jl:579-592`: compare each element with every later one. -/
def indexedAllunique : List Int → Bool
  | [] => true
  | a :: rest => if rest.any (· == a) then false else indexedAllunique rest

/-- The scan of the sorted fast path of `allunique(A::StridedArray)`,
`base/set.jl:557-567`: `compare(a2, a)` advances, `isequal` fails, anything else falls
back to the hashed method on the whole array. -/
def sortedScan (whole : List Int) (incr : Bool) (a2 : Int) : List Int → Bool
  | [] => true
  | a :: rest =>
    if (if incr then decide (a2 < a) else decide (a < a2)) then sortedScan whole incr a rest
    else if a2 = a then false
    else hashedLoop [] whole

/-- `allunique(A::StridedArray)` for `Vector{Int}`, `base/set.jl:553-577`. -/
def allunique (v : List JInt64) : Bool :=
  let w := v.map (·.val)
  if w.length < 32 then (if w.length < 2 then true else indexedAllunique w)
  else match w with
    | a1 :: a2 :: rest =>
      if a1 ≠ a2 then sortedScan w (decide (a1 < a2)) a2 rest else false
    | _ => hashedLoop [] w

/-- `allequal(itr)`, `base/set.jl:648-656`: true for length ≤ 1, else
`all(isequal(a), rest)` for the first element `a`. -/
def allequal (v : List JInt64) : Bool :=
  if v.length ≤ 1 then true
  else match v with
    | a :: rest => rest.all (fun x => x.val == a.val)
    | [] => true

/-- `unique(v)` keeps the first occurrence of each value in order; `allunique(v)` holds
exactly when no value repeats (also through the sorted fast path for 32 or more
elements); `allequal(v)` holds exactly when all values are equal. -/
def UniqueSpec : Prop :=
  ∀ (v : List JInt64),
    ((unique v).map (·.val)) = (v.map (·.val)).foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] ∧
    (allunique v = true ↔ (v.map (·.val)).Nodup) ∧
    (allequal v = true ↔ ∀ x ∈ v, ∀ y ∈ v, x.val = y.val)

end JuliaLean.ArrayOps
