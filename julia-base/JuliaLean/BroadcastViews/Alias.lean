import JuliaLean.BroadcastViews.Shape

/-!
Aliasing detection for broadcast assignment between views of one parent array:
`Base.mightalias(::SubArray, ::SubArray)` and `_indicesmightoverlap`
(`base/multidimensional.jl:1130-1188`), `unalias` (`base/abstractarray.jl:1566`) and
`broadcast_unalias`/`preprocess` (`base/broadcast.jl:1001-1008`), master `bbfa0ce4150`.

* A parent index stored in a `SubArray` is an `Idx`: an `Int`, a unit range, a step range, an
  array of `Int`s, or an array of `CartesianIndex{n}` (which spans `n` parent dimensions).
* A view selects a list of parent positions (one `List Int` subscript tuple per element, in
  column-major order of the view); a parent array is its column-major memory `List Int`.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- An element of an index: an `Int` or a `CartesianIndex` with the given subscripts. -/
inductive Elem where
  | int (i : Int)
  | cart (is : List Int)
  deriving DecidableEq, Repr

/-- `x == y` between index elements. `CartesianIndex == Int` has no method of its own and falls
back to `===`, which is false. -/
def Elem.eqb : Elem → Elem → Bool
  | .int a, .int b => a == b
  | .cart a, .cart b => a == b
  | _, _ => false

/-- A parent index of a `SubArray`. -/
inductive Idx where
  /-- An `Int` (`Real` scalar index). -/
  | scalar (i : Int)
  /-- An `AbstractUnitRange{Int}` `lo:hi` (`UnitRange`, `OneTo`, `Slice(OneTo(n))`). -/
  | urange (lo hi : Int)
  /-- A non-unit `StepRange{Int,Int}` with `len` elements. -/
  | srange (start step : Int) (len : Nat)
  /-- A `Vector{Int}`. -/
  | ints (xs : List Int)
  /-- A `Vector{CartesianIndex{n}}` (each element has `n` subscripts). -/
  | carts (n : Nat) (xs : List (List Int))
  deriving DecidableEq, Repr

/-- The elements of an index, in order. -/
def Idx.elems : Idx → List Elem
  | .scalar i => [.int i]
  | .urange lo hi => ((List.range (hi - lo + 1).toNat).map (fun k : Nat => lo + (k : Int))).map .int
  | .srange a s n => ((List.range n).map (fun k : Nat => a + (k : Int) * s)).map .int
  | .ints xs => xs.map .int
  | .carts _ xs => xs.map .cart

/-- `x in A` for an index array `A`: `any(y -> y == x, A)` (the range methods of `in` agree on
`Int`s; a `CartesianIndex` is never `==` to a range element). -/
def inIdx (x : Elem) (A : Idx) : Bool := A.elems.any (fun y => y.eqb x)

/-- `_indicesmightoverlap(A, B)` on the parent index tuples of two views of the same parent,
`base/multidimensional.jl:1158-1188`, with Julia's method specificity:
unit range × unit range (1166), range × range (1162), `Real` × `Real` (1170), `Real` × array (1172),
array × `Real` (1174), array × array (1177), anything else `true` (1188). An index tuple that
runs out before the other throws `error("malformed subarray")` (1159-1160). -/
def indicesMightOverlap : List Idx → List Idx → R Bool
  | [], [] => .ok true
  | [], _ :: _ => .error .argumentError
  | _ :: _, [] => .error .argumentError
  | a :: as, b :: bs =>
    let next := indicesMightOverlap as bs
    match a, b with
    | .urange alo ahi, .urange blo bhi => if max alo blo ≤ min ahi bhi then next else .ok false
    | .urange _ _, .srange _ _ _ | .srange _ _ _, .urange _ _ | .srange _ _ _, .srange _ _ _ =>
      if a.elems.any (fun x => inIdx x b) then next else .ok false
    | .scalar x, .scalar y => if x = y then next else .ok false
    | .scalar x, _ => if inIdx (.int x) b then next else .ok false
    | _, .scalar y => if inIdx (.int y) a then next else .ok false
    | _, _ =>
      match a.elems, b.elems with
      | [x], _ => if inIdx x b then next else .ok false
      | _, [y] => if inIdx y a then next else .ok false
      | _, _ => .ok true

/-- The parent subscripts an index contributes per selected element. -/
def Idx.subs : Idx → List (List Int)
  | .carts _ xs => xs
  | i => i.elems.filterMap (fun | .int k => some [k] | .cart _ => none)

/-- The parent subscript tuples selected by a view's index tuple, in the view's column-major
element order (first index varies fastest). -/
def positions : List Idx → List (List Int)
  | [] => [[]]
  | i :: is => (positions is).flatMap (fun q => i.subs.map (fun p => p ++ q))

/-- Column-major linear index (0-based) of 1-based subscripts in a parent of size `dims`. -/
def linIdx : List Nat → List Int → Nat
  | n :: ns, i :: is => (i - 1).toNat + n * linIdx ns is
  | _, _ => 0

/-- `Base.mightalias(A::SubArray, B::SubArray)` for two nonempty views whose parents are the same
array, `base/multidimensional.jl:1130-1144`, as used by `unalias(dest, A)`
(`base/abstractarray.jl:1566`, 1603: empty arrays never alias). -/
def mightaliasSame (I J : List Idx) : R Bool :=
  if (positions I).isEmpty || (positions J).isEmpty then .ok false else indicesMightOverlap I J

/-- `dest .= src` for two distinct view objects `dest = view(P, I...)`, `src = view(P, J...)` of
one parent with memory `mem` and size `dims`: `materialize!` → `copyto!(dest, bc)`
(`base/broadcast.jl:1015-1031`), whose identity fast path calls `copyto!(dest, src)` and otherwise
`preprocess`es the argument; both replace `src` by a copy exactly when `mightalias(dest, src)`.
The elements are then written in order. -/
def bcAssign (dims : List Nat) (mem : List Int) (I J : List Idx) : R (List Int) := do
  let copySrc ← mightaliasSame I J
  let dpos := (positions I).map (linIdx dims)
  let spos := (positions J).map (linIdx dims)
  pure <| (dpos.zip spos).foldl
    (fun m (p : Nat × Nat) => m.set p.1 ((if copySrc then mem else m).getD p.2 0)) mem

/-- `dest .= src` computed into a fresh array first (`dest .= copy(src)`). -/
def freshAssign (dims : List Nat) (mem : List Int) (I J : List Idx) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  let spos := (positions J).map (linIdx dims)
  (dpos.zip spos).foldl (fun m (p : Nat × Nat) => m.set p.1 (mem.getD p.2 0)) mem

/-- `dest .= dest .+ c` (`dest .+= c`) for a view `dest = view(P, I...)`: `dest` is `===` the
destination, so `broadcast_unalias(dest, dest) = dest` (`base/broadcast.jl:1001`) does not copy it
and each element is read from the current memory just before its own write. -/
def bcSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  dpos.foldl (fun m p => m.set p (m.getD p 0 + c)) mem

/-- `dest .= dest .+ c` with the right-hand side computed into a fresh array first, as
`P[I...] .+= c` (which reads `P[I...]`, a copy) does. -/
def freshSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  dpos.foldl (fun m p => m.set p (mem.getD p 0 + c)) mem

end JuliaLean.BroadcastViews
