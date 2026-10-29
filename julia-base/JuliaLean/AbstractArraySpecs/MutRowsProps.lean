import JuliaLean.AbstractArraySpecs.MutRows
import JuliaLean.AbstractArraySpecs.CopyRowsProps

/-!
Spec-first properties of the `map!`, `push!`/`pushfirst!` and `circshift!` methods modelled
in `MutRows.lean`. Sources: map! docstring (base/abstractarray.jl:3562-3592: "Like map,
but stores the result in destination rather than a new collection"), the one-argument
map! docstring (lines 3598-3616), push!/pushfirst! docstrings (base/collections.jl: "Insert
one or more items in collection ... inserted at the end (in the given order)"; "Insert
one or more items at the beginning of collection"), resize! docstring (base/array.jl:
"Resize a to contain n elements. If n is smaller than the current collection length, the
first n elements will be retained.") and the circshift! docstring (lines 3737-3755).
-/

namespace JuliaLean.AbstractArraySpecs

/-- `map!(f, dest, A, B)` stores `f(A[k], B[k])` in the first
`min(length(dest), length(A), length(B))` positions of `dest` (iteration order) and leaves
the rest unchanged, for either `IndexStyle` and any axes. -/
def MapBang2Prefix : Prop :=
  ∀ {α : Type} (f : α → α → α) (dest A B : Arr α), dest.WF → A.WF → B.WF →
    let d := (List.zipWith f A.data B.data).take dest.data.length ++
      dest.data.drop (min A.data.length B.data.length)
    mapBang2 f dest A B = .ok { dest with data := d }

/-- The values `f([A₁[k], ..., Aₙ[k]])` for every position `k` that all sources have. -/
def mapNRef {α : Type} (f : List α → α) (ls : List (List α)) : List α :=
  (List.range ((ls.map List.length).min?.getD 0)).filterMap (fun k => (ls.mapM (·[k]?)).map f)

/-- `map_n!(f, dest, As)` with at least one source stores `f` of the `k`-th elements of the
sources in position `k` of `dest` for every `k` that `dest` and all sources have, and
leaves the rest of `dest` unchanged, for either `IndexStyle` and any axes. -/
def MapNPrefix : Prop :=
  ∀ {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)), dest.WF → (∀ x ∈ As, x.WF) →
    As ≠ [] →
    let r := mapNRef f (As.map (·.data))
    mapN f dest As = .ok { dest with data := r.take dest.data.length ++ dest.data.drop r.length }

/-- `map!(f, dest, As...)` with one or more sources: the `map_n!` contract above. -/
def MapBangNPrefix : Prop :=
  ∀ {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)), dest.WF → (∀ x ∈ As, x.WF) →
    As ≠ [] →
    let r := mapNRef f (As.map (·.data))
    mapBangN f dest As = .ok { dest with data := r.take dest.data.length ++ dest.data.drop r.length }

/-- `ith_all(i, as)` is the tuple of the elements at linear index `i` of each array, or
`BoundsError` when one of them has no such index. -/
def IthAllSpec : Prop :=
  ∀ {α : Type} (i : I64) (As : List (Arr α)), (∀ x ∈ As, x.WF) →
    ithAll i As = As.mapM (fun a => refGet a [i])

/-- `map!(f, A)` replaces every element of `A` by `f` of it ("Like map, but stores the
result in the same array"). -/
def MapBangInplaceSpec : Prop :=
  ∀ {α : Type} (f : α → α) (A : Arr α), A.WF → mapBangInplace f A = .ok { A with data := A.data.map f }

/-- The `resize!` contract for vectors, including retention of the first elements. -/
def ResizeKeeps {α : Type} (resize : Arr α → I64 → R (Arr α)) : Prop :=
  ∀ (a : Arr α) (n : I64), a.WF → a.axes.length = 1 → 0 ≤ n.val →
    ∃ a', resize a n = .ok a' ∧ a'.WF ∧ a'.axes.length = 1 ∧ a'.data.length = n.val.toNat ∧
      (linearAxis a').lo = (linearAxis a).lo ∧
      a'.data.take a.data.length = a.data.take n.val.toNat

/-- `push!(a, item)` for a vector: when `item` converts to the element type, the result
holds `a`'s elements followed by the converted item and keeps `a`'s first index; a failed
conversion is thrown. -/
def PushOneSpec : Prop :=
  ∀ {α β : Type} (conv : β → R α) (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (item : β),
    ResizeKeeps resize → a.WF → a.axes.length = 1 → (a.data.length : Int) < tmax →
    (∀ e, conv item = .error e → pushOne conv resize a item = .error e) ∧
    (∀ x, conv item = .ok x → ∃ r, pushOne conv resize a item = .ok r ∧ r.data = a.data ++ [x] ∧
      (linearAxis r).lo = (linearAxis a).lo)

/-- `push!(a::AbstractVector{Any}, x)`: `a`'s elements followed by `x`. -/
def PushOneAnySpec : Prop :=
  ∀ {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (x : α),
    ResizeKeeps resize → a.WF → a.axes.length = 1 → (a.data.length : Int) < tmax →
    ∃ r, pushOneAny resize a x = .ok r ∧ r.data = a.data ++ [x] ∧ (linearAxis r).lo = (linearAxis a).lo

/-- `push!(a::AbstractVector{Any}, x...)`: `a`'s elements followed by the items in the
given order. -/
def PushManyAnySpec : Prop :=
  ∀ {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (xs : List α),
    ResizeKeeps resize → a.WF → a.axes.length = 1 → (a.data.length : Int) + xs.length ≤ tmax →
    ∃ r, pushManyAny resize a xs = .ok r ∧ r.data = a.data ++ xs ∧ (linearAxis r).lo = (linearAxis a).lo

/-- The one-item `push!` contract of a collection type `C` whose elements in order are
`elems`: the item is appended. -/
def PushContract {C α : Type} (elems : C → List α) (push : C → α → R C) : Prop :=
  ∀ (A : C) (x : α), ∃ A', push A x = .ok A' ∧ elems A' = elems A ++ [x]

/-- The one-item `pushfirst!` contract of a collection type: the item is prepended. -/
def PushfirstContract {C α : Type} (elems : C → List α) (pushfirst : C → α → R C) : Prop :=
  ∀ (A : C) (x : α), ∃ A', pushfirst A x = .ok A' ∧ elems A' = x :: elems A

/-- `push!(A, a, b)` appends `a` and then `b`. -/
def Push2Spec : Prop :=
  ∀ {C α : Type} (elems : C → List α) (push : C → α → R C) (A : C) (a b : α), PushContract elems push →
    ∃ r, push2 push A a b = .ok r ∧ elems r = elems A ++ [a, b]

/-- `push!(A, a, b, c...)` appends all the items in the given order. -/
def PushVarSpec : Prop :=
  ∀ {C α : Type} (elems : C → List α) (push : C → α → R C) (A : C) (a b c : α) (cs : List α),
    PushContract elems push →
    ∃ r, pushVar push A a b c cs = .ok r ∧ elems r = elems A ++ (a :: b :: c :: cs)

/-- `pushfirst!(A, a, b)` puts `a, b` (in that order) before `A`'s elements. -/
def Pushfirst2Spec : Prop :=
  ∀ {C α : Type} (elems : C → List α) (pushfirst : C → α → R C) (A : C) (a b : α),
    PushfirstContract elems pushfirst →
    ∃ r, pushfirst2 pushfirst A a b = .ok r ∧ elems r = a :: b :: elems A

/-- `pushfirst!(A, a, b, c...)` puts all the items, in the given order, before `A`'s
elements. -/
def PushfirstVarSpec : Prop :=
  ∀ {C α : Type} (elems : C → List α) (pushfirst : C → α → R C) (A : C) (a b c : α) (cs : List α),
    PushfirstContract elems pushfirst →
    ∃ r, pushfirstVar pushfirst A a b c cs = .ok r ∧ elems r = (a :: b :: c :: cs) ++ elems A

/-- `circshift!(a, shift)` rotates the elements of the vector `a` by `shift` positions:
the element at position `k` moves to position `mod(k + shift, n)`, i.e. the last
`mod(shift, n)` elements come first (docstring example: `[1, 2, 3, 4, 5]` shifted by 2
is `[4, 5, 1, 2, 3]`), for any integer `shift` and any axis. -/
def CircshiftSpec : Prop :=
  ∀ {α : Type} (a : Arr α) (shift : Int), a.WF → a.axes.length = 1 →
    let k := a.data.length - (shift % a.data.length).toNat
    circshiftBang a shift = .ok { a with data := a.data.drop k ++ a.data.take k }

end JuliaLean.AbstractArraySpecs
