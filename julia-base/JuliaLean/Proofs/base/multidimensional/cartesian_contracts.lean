import JuliaLean.base.multidimensional
import JuliaLean.Proofs.base.range.cartesian_components

namespace JuliaLean.Multidim

/-- Column-major product of the component ranges: the elements of a `CartesianIndices`
in the order of the nested loops of its docstring (`base/multidimensional.jl:216-225`). -/
def elems : List Rng → List (List I64)
  | [] => [[]]
  | r :: rs => (elems rs).flatMap fun t => r.elems.map fun x => x :: t

/-- Iterating a `CartesianIndices` visits its elements in the order of the nested loops
of its docstring (first dimension fastest), once each, then stops: `iterate(R)` gives
the first element (or `nothing` when empty) and `iterate(R, I)` the next one. -/
def CartesianIterOrder : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) →
    iterFirst R = (elems R).head? ∧
    ∀ k : Nat, k < (elems R).length → iterNext R ((elems R).getD k []) = (elems R)[k + 1]?

/-- `Iterators.reverse(R)` for a `CartesianIndices` visits the elements in exactly the
reverse order. -/
def CartesianRevOrder : Prop :=
  ∀ R : List Rng, (∀ r ∈ R, r.WF) →
    revFirst R = (elems R).reverse.head? ∧
    ∀ k : Nat, k < (elems R).length →
      revNext R ((elems R).reverse.getD k []) = (elems R).reverse[k + 1]?

/-- `isless` on `CartesianIndex{N}` is a strict total order (reverse-lexicographic). -/
def CartesianIslessOrder : Prop :=
  ∀ a b c : List I64, a.length = b.length → b.length = c.length →
    ciLess a a = false ∧ (ciLess a b = true → ciLess b c = true → ciLess a c = true) ∧
    (ciLess a b = true ∨ a = b ∨ ciLess b a = true)

/-- `reverse(R::CartesianIndices; dims)` accepts exactly the `dims` that are distinct
dimensions in `1:ndims(R)`. -/
def ReverseDimsCheck : Prop :=
  ∀ (N : Nat) (dims : List Int),
    reverseDimsOk N dims = true ↔ (dims.Nodup ∧ ∀ d ∈ dims, 1 ≤ d ∧ d ≤ N)

/-- `diff(A; dims)` has the size of `A` with `size(A, dims)` reduced by one (not below
zero), and throws `ArgumentError` for `dims` outside `1:ndims(A)`. -/
def DiffSize : Prop :=
  ∀ (sz : List Nat) (dims : Int),
    diffSize sz dims =
      if 1 ≤ dims ∧ dims ≤ sz.length then
        .ok (sz.set (dims.toNat - 1) (sz.getD (dims.toNat - 1) 0 - 1))
      else .error .argumentError

/-- `circcopy!(dest, src)` on nonempty arrays of the same size copies `src` with each
dimension indexed modulo its length: `dest[J] == src[K]` where `K ≡ J (mod size)` lies in
the axes of `src`. -/
def CirccopyNonempty : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int),
    (∀ p ∈ axd, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    (∀ p ∈ axs, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    ∃ out, circcopy axd dest axs src = .ok out ∧
      ∀ J : List Int, inAxes axd J = true →
        out J = some (src ((J.zip axs).map fun (j, s) => s.1 + (j - s.1) % (s.2 - s.1 + 1)))

/-- `circcopy!(dest, src)` succeeds whenever `src` and `dest` have the same size. -/
def CirccopyCorrect : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int),
    (∀ p ∈ axd, p.1 - 1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    (∀ p ∈ axs, p.1 - 1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    ∃ out, circcopy axd dest axs src = .ok out

/-- `copyto!(dest, Rdest, src, Rsrc)` throws `ArgumentError` when the regions differ in size. -/
def CopytoSizeChecked : Prop :=
  ∀ (axd axs : List (Int × Int)) (dest : List Int → Option Int) (src : List Int → Int)
    (Rd Rs : List Rng),
    Rd.length = Rs.length → Rd.map (·.len) ≠ Rs.map (·.len) →
    errKind (copytoCI axd dest Rd axs src Rs) = some .argumentError

/-- `==` on `CartesianIndices` agrees with `==` on the arrays they represent: equal size and
equal elements. -/
def CartesianEqArrays : Prop :=
  ∀ R S : List Rng, R.length = S.length → (∀ r ∈ R, r.WF) → (∀ s ∈ S, s.WF) →
    ciEq R S = (R.map (·.len) == S.map (·.len) && elems R == elems S)

end JuliaLean.Multidim
