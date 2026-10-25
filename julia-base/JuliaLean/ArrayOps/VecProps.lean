import JuliaLean.ArrayOps.Vec

/-!
Properties of the mutating `Vector` operations, stated against list
specifications, and the refutations. A fully assigned vector with contents
`a : List α` is `a.map some`.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

/-! ### Specifications -/

/-- The elements of `a` whose 1-based position is not in `S`. -/
def dropPositions {α : Type} (a : List α) (S : List Int) : List α :=
  ((a.zipIdx 1).filter fun p => decide ((p.2 : Int) ∉ S)).map Prod.fst

/-- The elements of `a` at the 1-based positions `S`, in order. -/
def atPositions {α : Type} (a : List α) (S : List Int) : List α :=
  S.filterMap fun i => a[(i - 1).toNat]?

/-- A list of indices that is strictly increasing and lies in `1:n`. -/
def SortedIn (n : Nat) (inds : List JInt64) : Prop :=
  inds.Pairwise (fun i j => i.val < j.val) ∧ ∀ i ∈ inds, 1 ≤ i.val ∧ i.val ≤ n

/-! ### Statements -/

/-- `push!`, `pushfirst!`, `pop!`, `popfirst!` on a vector act on the ends of the list;
`pop!`/`popfirst!` of an empty vector throw `ArgumentError`. -/
def DequeueSpec : Prop :=
  ∀ (α : Type) (a : List α) (x : α), a.length < 2 ^ 62 →
    push (a.map some) x = ⟨(a ++ [x]).map some, .ok ()⟩ ∧
    pushfirst (a.map some) x = ⟨(x :: a).map some, .ok ()⟩ ∧
    pop (a.map some) =
      (if a.isEmpty then ⟨[], .error (.argumentError "array must be non-empty")⟩
       else ⟨a.dropLast.map some, .ok a.getLast?⟩) ∧
    popfirst (a.map some) =
      (if a.isEmpty then ⟨[], .error (.argumentError "array must be non-empty")⟩
       else ⟨a.tail.map some, .ok a.head?⟩)

/-- `insert!(a, i, x)` for an index of any integer type: `x` ends up at index `i` for
`1 ≤ i ≤ length(a)+1`; otherwise `BoundsError` (or the `InexactError` of `Int(i)`)
and `a` is unchanged. -/
def InsertSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (a : List α) (i : JInt t) (x : α), a.length < 2 ^ 62 →
    insert (a.map some) i x =
      match toInt i with
      | .error e => ⟨a.map some, .error e⟩
      | .ok i =>
        if 1 ≤ i.val ∧ i.val ≤ a.length + 1 then
          ⟨(a.take (i.val - 1).toNat ++ x :: a.drop (i.val - 1).toNat).map some, .ok ()⟩
        else ⟨a.map some, .error .boundsError⟩

/-- `deleteat!(a, i)` for an index of any integer type removes the element at `i` when
`1 ≤ i ≤ length(a)`, and otherwise throws `BoundsError` (or the `InexactError` of
`Int(i)`) leaving `a` unchanged. -/
def DeleteatIndexSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (a : List α) (i : JInt t), a.length < 2 ^ 62 →
    deleteatIndex (a.map some) i =
      match toInt i with
      | .error e => ⟨a.map some, .error e⟩
      | .ok i =>
        if 1 ≤ i.val ∧ i.val ≤ a.length then ⟨(a.eraseIdx (i.val - 1).toNat).map some, .ok ()⟩
        else ⟨a.map some, .error .boundsError⟩

/-- `deleteat!(a, r)` for a unit range `r = lo:hi` of any integer type whose endpoints
are representable as `Int`: an empty range does nothing, a range inside `1:length(a)`
removes exactly its elements, and any other range throws `BoundsError` with `a`
unchanged. -/
def DeleteatRangeSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (a : List α) (lo hi : JInt t), a.length < 2 ^ 62 →
    lo.val ≤ hi.val + 1 → IntTy.i64.min ≤ lo.val → hi.val ≤ IntTy.i64.max →
    deleteatRange (a.map some) lo hi =
      if lo.val > hi.val then ⟨a.map some, .ok ()⟩
      else if 1 ≤ lo.val ∧ hi.val ≤ a.length then
        ⟨(a.take (lo.val - 1).toNat ++ a.drop hi.val.toNat).map some, .ok ()⟩
      else ⟨a.map some, .error .boundsError⟩

/-- The in-bounds part of `DeleteatRangeSpec`: for every empty range, and every
range `lo:hi` with `1 ≤ lo ≤ hi ≤ length(a)`, of any integer type. -/
def DeleteatRangeInBounds : Prop :=
  ∀ (α : Type) (t : IntTy) (a : List α) (lo hi : JInt t), a.length < 2 ^ 62 →
    lo.val ≤ hi.val + 1 → (lo.val > hi.val ∨ (1 ≤ lo.val ∧ hi.val ≤ a.length)) →
    deleteatRange (a.map some) lo hi =
      if lo.val > hi.val then ⟨a.map some, .ok ()⟩
      else ⟨(a.take (lo.val - 1).toNat ++ a.drop hi.val.toNat).map some, .ok ()⟩

/-- `deleteat!(a, inds)` for sorted, unique, in-bounds `inds::Vector{Int}` removes
exactly the elements at those positions. -/
def DeleteatSortedSpec : Prop :=
  ∀ (α : Type) (a : List α) (inds : List JInt64), a.length < 2 ^ 62 → SortedIn a.length inds →
    deleteatInds (a.map some) inds = ⟨(dropPositions a (inds.map (·.val))).map some, .ok ()⟩

/-- When `deleteat!(a, inds)` throws (unsorted, repeated or out-of-bounds indices),
`a` is left unchanged. -/
def DeleteatErrorUnchanged : Prop :=
  ∀ (α : Type) (a : List α) (inds : List JInt64), a.length < 2 ^ 62 →
    (∃ e, (deleteatInds (a.map some) inds).res = .error e) →
    (deleteatInds (a.map some) inds).vec = a.map some

/-- `deleteat!(a, mask)` with a `Bool` vector of the same length removes the entries
marked `true`; a mask of another length throws `BoundsError`. -/
def DeleteatMaskSpec : Prop :=
  ∀ (α : Type) (a : List α) (mask : List Bool), a.length < 2 ^ 62 →
    deleteatMask (a.map some) mask =
      if mask.length = a.length then
        ⟨((a.zip mask).filter (fun p => !p.2)).map (some ∘ Prod.fst), .ok ()⟩
      else ⟨a.map some, .error .boundsError⟩

/-- `keepat!(a, inds)` for sorted, unique, in-bounds `inds::Vector{Int}` keeps exactly
`a[inds]`. -/
def KeepatSortedSpec : Prop :=
  ∀ (α : Type) (a : List α) (inds : List JInt64), a.length < 2 ^ 62 → SortedIn a.length inds →
    keepat (a.map some) inds = ⟨(atPositions a (inds.map (·.val))).map some, .ok ()⟩

/-- `filter!(f, a)` keeps exactly the elements satisfying `f`, in order. -/
def FilterBangSpec : Prop :=
  ∀ (α : Type) (f : α → Bool) (a : List α), a.length < 2 ^ 62 → filterBang f (a.map some) = (a.filter f).map some

/-- `splice!(a, f:l, ins)` for `1 ≤ f ≤ l+1 ≤ length(a)+1` (including the empty range
`f:f-1` that inserts before `f`) returns `a[f:l]` and replaces it by `ins`. -/
def SpliceRangeSpec : Prop :=
  ∀ (α : Type) (a : List α) (f l : JInt64) (ins : List α), a.length < 2 ^ 62 → ins.length < 2 ^ 62 →
    1 ≤ f.val → f.val ≤ l.val + 1 → l.val ≤ a.length →
    spliceRange Except.ok (a.map some) f l ins =
      ⟨(a.take (f.val - 1).toNat ++ ins ++ a.drop l.val.toNat).map some,
       .ok (((a.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat).map some)⟩

/-- `resize!(a, n; first)` for `n` of any integer type: a negative `n` throws
`ArgumentError`; otherwise the length becomes `n`, keeping the first (or, with
`first=true`, the last) `min(n, length(a))` elements and adding unassigned slots
at the end (or the front). -/
def ResizeSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (a : List α) (n : JInt t) (first : Bool), a.length < 2 ^ 62 →
    resize (a.map some) n first =
      match toInt n with
      | .error e => ⟨a.map some, .error e⟩
      | .ok nl =>
        if nl.val < 0 then ⟨a.map some, .error (.argumentError "new length must be ≥ 0")⟩
        else if first then
          ⟨(List.replicate (nl.val.toNat - a.length) none ++ a.map some).drop
              (a.length - nl.val.toNat), .ok ()⟩
        else ⟨(a.map some ++ List.replicate (nl.val.toNat - a.length) none).take nl.val.toNat, .ok ()⟩

/-- `append!(a, a)` and `prepend!(a, a)` with one collection behave as if the source
were copied first. -/
def AppendSelfSpec : Prop :=
  ∀ (α : Type) (a : Vec α) (s : Src α), a.length < 2 ^ 62 →
    append a [s] = a ++ s.read a ∧ prepend a [s] = s.read a ++ a

/-- `append!(a, cs...)` and `prepend!(a, cs...)` behave as if every collection were
copied before the call: the result is `vcat(a, cs...)` (respectively `vcat(cs..., a)`)
of the original values, also when some `cs` is `a` itself. -/
def AppendManySpec : Prop :=
  ∀ (α : Type) (a : Vec α) (srcs : List (Src α)), a.length < 2 ^ 62 →
    append a srcs = a ++ srcs.flatMap (·.read a) ∧
    prepend a srcs = srcs.flatMap (·.read a) ++ a

/-! ### Refutations -/

/-- The exception of a result, if any (`Jl` has no `DecidableEq`). -/
def errOf {β : Type} : Jl β → Option JlError
  | .error e => some e
  | .ok _ => none

/-- `deleteat!([1,2,3], 1:typemax(Int))` throws the internal
`ArgumentError("_deletebeg! requires delta in 0:length(a)")`: `i + delta` wraps. -/
theorem deleteatFullRange :
    errOf (deleteatRange ([1, 2, 3].map some : Vec Int) (JInt.lit .i64 1) (JInt.typemax .i64)).res =
      some (.argumentError "_deletebeg! requires delta in 0:length(a)") := by
  decide +kernel

theorem deleteatRangeSpec_refuted : ¬ DeleteatRangeSpec := by
  intro h
  have e := h Int .i64 [1, 2, 3] (JInt.lit .i64 1) (JInt.typemax .i64)
    (by decide) (by decide) (by decide) (by decide)
  have r := congrArg (fun o => errOf o.res) e
  revert r
  decide +kernel

/-- `deleteat!([10,20,30,40], [1,3,5])` throws `BoundsError` after copying `20` over `10`. -/
theorem deleteatPartial :
    errOf (deleteatInds ([10, 20, 30, 40].map some : Vec Int)
        [JInt.lit .i64 1, JInt.lit .i64 3, JInt.lit .i64 5]).res = some .boundsError ∧
    (deleteatInds ([10, 20, 30, 40].map some : Vec Int)
        [JInt.lit .i64 1, JInt.lit .i64 3, JInt.lit .i64 5]).vec =
      [some 20, some 20, some 30, some 40] := by
  decide +kernel

theorem deleteatErrorUnchanged_refuted : ¬ DeleteatErrorUnchanged := by
  intro h
  have hr := deleteatPartial.1
  have e := h Int [10, 20, 30, 40] [JInt.lit .i64 1, JInt.lit .i64 3, JInt.lit .i64 5] (by decide)
    ⟨.boundsError, by
      revert hr
      cases (deleteatInds ([10, 20, 30, 40].map some : Vec Int)
        [JInt.lit .i64 1, JInt.lit .i64 3, JInt.lit .i64 5]).res <;> simp [errOf]⟩
  rw [deleteatPartial.2] at e
  revert e
  decide

/-- `append!(a, a, a)` for `a = [1]` gives `[1, 1, 1, 1]`. -/
theorem appendTwiceSelf :
    append [some (1 : Int)] [.self, .self] = [some 1, some 1, some 1, some 1] := by
  decide

theorem appendManySpec_refuted : ¬ AppendManySpec := by
  intro h
  have e := (h Int [some 1] [.self, .self] (by decide)).1
  rw [appendTwiceSelf] at e
  revert e
  decide

end JuliaLean.ArrayOps
