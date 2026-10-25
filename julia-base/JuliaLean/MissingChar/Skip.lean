import JuliaLean.MissingChar.Basic

/-!
# `skipmissing`, `base/missing.jl:182-393`

`skipmissing(x)` of a `Vector{Union{Missing, T}}` `x`. The vector is
`List (Option α)` (`none` is `missing`); Julia's index `i` is list position
`i - 1`. Indices are `Nat`: a Julia vector has fewer than `typemax(Int)`
elements, so the `i == typemax(typeof(i))` early exits of `_mapreduce`
(`base/missing.jl:287, 328, 337`) never fire and are omitted.

`while` and `for` loops are structural recursion on an explicit bound on the
remaining iterations; each docstring states it.
-/

namespace JuliaLean.MissingChar

/-- Errors of the skipmissing functions: a shared `JlError` or `MissingException`
(`base/missing.jl:14-16`). -/
inductive SMErr where
  | jl (e : JlError)
  | missingException
  deriving Repr, DecidableEq

abbrev SMJl (α : Type) := Except SMErr α

/-- `iterate(x::Vector, i)`, `base/array.jl`: `(x[i], i+1)` while `i ≤ length(x)`.
The state is the 1-based index of the next element. -/
def vecIterate (x : List (Option α)) (i : Nat) : Option (Option α × Nat) :=
  if 1 ≤ i ∧ i ≤ x.length then some (x.getD (i - 1) none, i + 1) else none

/-- The `while ismissing(item)` loop of `iterate(itr::SkipMissing, state...)`,
`base/missing.jl:244-248`. Bound: `fuel` = elements left after `s`. -/
def smWhile (x : List (Option α)) : Nat → Option α → Nat → Option (α × Nat)
  | _, some a, s => some (a, s)
  | 0, none, _ => none
  | fuel + 1, none, s =>
    match vecIterate x s with
    | none => none
    | some (item, s') => smWhile x fuel item s'

/-- `iterate(itr::SkipMissing, state...)`, `base/missing.jl:240-250`. -/
def smIterate (x : List (Option α)) (s : Nat) : Option (α × Nat) :=
  match vecIterate x s with
  | none => none
  | some (item, s') => smWhile x (x.length + 1 - s') item s'

/-- `collect(skipmissing(x))`: the values `iterate` yields from state 1.
Bound: `fuel`, at least the number of elements left. -/
def smCollectFrom (x : List (Option α)) : Nat → Nat → List α
  | 0, _ => []
  | fuel + 1, s =>
    match smIterate x s with
    | none => []
    | some (a, s') => a :: smCollectFrom x fuel s'

def smCollect (x : List (Option α)) : List α := smCollectFrom x (x.length + 1) 1

/-- `keys(itr::SkipMissing) = Iterators.filter(i -> !ismissing(itr.x[i]), keys(itr.x))`
and `eachindex` likewise, `base/missing.jl:253-256`. -/
def smKeys (x : List (Option α)) : List Nat :=
  (List.range x.length).map (· + 1) |>.filter fun i => (x.getD (i - 1) none).isSome

/-- `x[i]` for an `Int` index: `BoundsError` outside `1:length(x)`. -/
def vecGet (x : List (Option α)) (i : Int) : SMJl (Option α) :=
  if 1 ≤ i ∧ i ≤ x.length then .ok (x.getD (i.toNat - 1) none) else .error (.jl .boundsError)

/-- `getindex(itr::SkipMissing, i::Int)`, `base/missing.jl:257-261`. -/
def smGetindex (x : List (Option α)) (i : Int) : SMJl α := do
  let v ← vecGet x i
  match v with
  | none => .error .missingException
  | some a => .ok a

/-- `getindex(itr::SkipMissing, I::AbstractVector{Int})`, `base/missing.jl:257-261`:
`v = itr.x[I]` is a vector, and `ismissing(v)` is false for a vector. -/
def smGetindexVec (x : List (Option α)) (I : List Int) : SMJl (List (Option α)) :=
  I.mapM (vecGet x)

/-- `filter(f, itr::SkipMissing{<:AbstractArray})`, `base/missing.jl:385-393`. -/
def smFilter (f : α → Bool) (x : List (Option α)) : List α :=
  x.foldl (fun y xi => match xi with
    | some a => if f a then y ++ [a] else y
    | none => y) []

/-- `findfirst(testf, A)` for non-arrays, `base/array.jl:2523-2528`:
`for (i, a) in pairs(A)`; `pairs(A) = Generator(=>, keys(A), values(A))`
(`base/abstractdict.jl:178`) zips `keys(itr)` with the iteration of `itr`. -/
def smFindfirst (f : α → Bool) (x : List (Option α)) : Option Nat :=
  ((smKeys x).zip (smCollect x)).find? (fun p => f p.2) |>.map (·.1)

/-- `IteratorSize` of an iterator. -/
inductive ISize where
  | hasLength (n : Nat)
  | sizeUnknown
  | isInfinite
  deriving DecidableEq

/-- `first(_zip_lengths_finite_equal(is))`, `base/iterators.jl:401-411`. -/
def zipLengthsFiniteEqual : List ISize → Bool × Option Nat
  | [] => (true, none)
  | .hasLength m :: rest =>
    let (b, n) := zipLengthsFiniteEqual rest
    (b && (n.isNone || n == some m), some m)
  | _ :: _ => (false, none)

/-- `findlast(testf, A)` for non-arrays, `base/array.jl:2716-2721`:
`for (i, a) in Iterators.reverse(pairs(A))`. `reverse(G::Generator)` reverses the
zipped iterators (`base/iterators.jl:157`), and `reverse(z::Zip)` throws
`ArgumentError` unless all have finite equal lengths (`:521-526`).
`IteratorSize(::Type{<:Filter}) = SizeUnknown()` (`:596`) for `keys(itr)` and
`IteratorSize(::Type{<:SkipMissing}) = SizeUnknown()` (`base/missing.jl:236`). -/
def smFindlast (f : α → Bool) (x : List (Option α)) : SMJl (Option Nat) :=
  if !(zipLengthsFiniteEqual [.sizeUnknown, .sizeUnknown]).1 then
    .error (.jl (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths"))
  else
    .ok (((smKeys x).zip (smCollect x)).reverse.find? (fun p => f p.2) |>.map (·.1))

/-! ## `mapreduce` over `skipmissing` of an array, `base/missing.jl:272-362` -/

/-- The `for outer i in i:ilast; ai = A[i]; !ismissing(ai) && break; end` scans
(`base/missing.jl:281-284, 290-293, 322-325, 331-334`): the first non-missing value
at an index in `i:ilast` and that index. Bound: `fuel` = `ilast + 1 - i`. -/
def firstNonMissing (x : List (Option α)) : Nat → Nat → Nat → Option (α × Nat)
  | 0, _, _ => none
  | fuel + 1, i, ilast =>
    if i > ilast then none
    else match x.getD (i - 1) none with
      | some a => some (a, i)
      | none => firstNonMissing x fuel (i + 1) ilast

/-- The `@simd for i = i:ilast` accumulation, `base/missing.jl:340-345`, as a
left fold (`@simd` may reassociate `op`; the statements below assume `op`
associative). Bound: `fuel` = `ilast + 1 - i`. -/
def simdLoop (f : α → β) (op : β → β → β) (x : List (Option α)) : Nat → Nat → Nat → β → β
  | 0, _, _, v => v
  | fuel + 1, i, ilast, v =>
    if i > ilast then v
    else
      let v := match x.getD (i - 1) none with
        | some a => op v (f a)
        | none => v
      simdLoop f op x fuel (i + 1) ilast v

/-- `_mapreduce_impl_skipmissing(f, op, itr, ifirst, ilast, blksize)`,
`base/missing.jl:306-362`, returning `nothing` (`none`) or `Some(v)`.
`mapreduce_first(f, op, a) = reduce_first(op, f(a)) = f(a)` for a generic `op`
(`base/reduce.jl`). -/
def mrImpl (f : α → β) (op : β → β → β) (x : List (Option α)) (blk : Nat)
    (ifirst ilast : Nat) : Option β :=
  if ifirst > ilast then none
  else if ifirst = ilast then
    match x.getD (ifirst - 1) none with
    | none => none
    | some a1 => some (f a1)
  else if ilast - ifirst < blk then
    match firstNonMissing x (ilast + 1 - ifirst) ifirst ilast with
    | none => none
    | some (a1, i) =>
      match firstNonMissing x (ilast - i) (i + 1) ilast with
      | none => some (f a1)
      | some (a2, i) => some (simdLoop f op x (ilast - i) (i + 1) ilast (op (f a1) (f a2)))
  else
    let imid := ifirst + (ilast - ifirst) / 2
    let v1 := mrImpl f op x blk ifirst imid
    let v2 := mrImpl f op x blk (imid + 1) ilast
    match v1, v2 with
    | none, none => none
    | none, v2 => v2
    | v1, none => v1
    | some a, some b => some (op a b)
termination_by ilast + 1 - ifirst

/-- `mapreduce(f, op, skipmissing(A))` for `A::Vector{Union{Missing,T}}`:
`_mapreduce(f, op, IndexLinear(), itr)`, `base/missing.jl:272-297`. `empty` is
`mapreduce_empty(f, op, eltype(itr))` (an error for a generic `op`). -/
def mrSkip (f : α → β) (op : β → β → β) (empty : Jl β) (blk : Nat)
    (x : List (Option α)) : Jl β :=
  let ilast := x.length
  match firstNonMissing x ilast 1 ilast with
  | none => empty
  | some (a1, i) =>
    match firstNonMissing x (ilast - i) (i + 1) ilast with
    | none => .ok (f a1)
    | some _ =>
      match mrImpl f op x blk 1 ilast with
      | some v => .ok v
      | none => .error (.argumentError "something(nothing)")

/-! ## Properties -/

/-- The skipmissing docstring, `base/missing.jl:185`: "Return an iterator over the
elements in `itr` skipping `missing` values"; `collect` gives the non-missing
values in order (`:190-193`). -/
def SkipMissingIterate : Prop :=
  ∀ (α : Type) (x : List (Option α)), smCollect x = x.filterMap id

/-- `base/missing.jl:186-188`: the object "can be indexed using indices of `itr`";
indices of missing values "are skipped by `keys` and `eachindex`, and a
`MissingException` is thrown when trying to use them". Scalar indexing at the
keys returns exactly the iterated values. -/
def SkipMissingKeys : Prop :=
  ∀ (α : Type) (x : List (Option α)),
    (smKeys x).mapM (fun (i : Nat) => smGetindex x (i : Int)) = .ok (smCollect x) ∧
    ∀ i : Int, 1 ≤ i → i ≤ x.length →
      (i.toNat ∈ smKeys x ↔ ∃ a, smGetindex x i = .ok a) ∧
      (i.toNat ∉ smKeys x → smGetindex x i = .error .missingException)

/-- Non-scalar indexing respects the same rule: indexing `skipmissing(x)` with a
vector of indices never returns a `missing` value (it throws instead). -/
def SkipMissingGetindexNoMissing : Prop :=
  ∀ (α : Type) (x : List (Option α)) (I : List Int) (v : List (Option α)),
    smGetindexVec x I = .ok v → ∀ e ∈ v, e.isSome

theorem skipMissingGetindexNoMissing_refuted : ¬ SkipMissingGetindexNoMissing := by
  intro h
  have := h Unit [some (), none] [2] [none] (by decide) none (by simp)
  simp at this

/-- `filter(f, skipmissing(A))` docstring, `base/missing.jl:367-368`: "a vector ...
with all missing elements and those for which `f` returns `false` removed". -/
def SkipMissingFilter : Prop :=
  ∀ (α : Type) (f : α → Bool) (x : List (Option α)), smFilter f x = (smCollect x).filter f

/-- Manual, doc/src/manual/missing.md:356-360: find functions on `skipmissing`
"return indices valid for the object returned by `skipmissing`, and are also the
indices of the matching entries in the parent array": `findfirst` returns the
first index whose value is not missing and satisfies the predicate. -/
def SkipMissingFindFirst : Prop :=
  ∀ (α : Type) (f : α → Bool) (x : List (Option α)),
    smFindfirst f x = (smKeys x).find? (fun i => match x.getD (i - 1) none with
      | some a => f a
      | none => false)

/-- The same promise for `findlast`: it returns the last index whose value is not
missing and satisfies the predicate. -/
def SkipMissingFindLast : Prop :=
  ∀ (α : Type) (f : α → Bool) (x : List (Option α)),
    smFindlast f x = .ok ((smKeys x).reverse.find? (fun i => match x.getD (i - 1) none with
      | some a => f a
      | none => false))

theorem skipMissingFindLast_refuted : ¬ SkipMissingFindLast := by
  intro h
  have := h Unit (fun _ => true) [some ()]
  simp [smFindlast, zipLengthsFiniteEqual] at this

/-- Reductions over `skipmissing` (manual, doc/src/manual/missing.md:318-326):
for an associative `op`, `mapreduce(f, op, skipmissing(x))` equals the left fold
of `op` over `f` of the non-missing values, and `mapreduce_empty` when there are
none, for every pairwise block size. -/
def SkipMissingMapreduce : Prop :=
  ∀ (α β : Type) (f : α → β) (op : β → β → β) (empty : Jl β) (blk : Nat)
    (x : List (Option α)),
    (∀ a b c, op (op a b) c = op a (op b c)) →
    mrSkip f op empty blk x = (match x.filterMap id with
      | [] => empty
      | a :: rest => .ok (rest.foldl (fun acc b => op acc (f b)) (f a)))

end JuliaLean.MissingChar
