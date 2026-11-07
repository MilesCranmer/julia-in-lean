import JuliaLean.base.missing
import JuliaLean.Proofs.base.missing.common

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
