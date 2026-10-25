import JuliaLean.BitArrays.Reference
import JuliaLean.BitArrays.BitSet

/-!
# Properties of `BitVector` and `BitSet`

A valid `BitVector` holding `l` is `BV.ofList l`: `num_bit_chunks(length(l))`
chunks whose unused high bits are zero. Every valid state is of this form, so
`op (BV.ofList l) = BV.ofList l'` states at once that the operation computes the
`Vector{Bool}` result `l'` and that it keeps the chunk invariant
(`base/bitarray.jl:5-6`) that `count`, `==`, `hash`, `any` and `all` rely on.
Grown-but-uninitialised chunks are an arbitrary `dirty` value. Every `BitVector`
in memory has fewer than `2^62` elements (its chunks take `length/8` bytes), so
the properties assume `l.length < 2^62`; the model converts lengths to `Int`
with Julia's wrapping, which only matters beyond that bound.
-/

namespace JuliaLean.BitArrays

open BV

/-- Julia's `Int` index `i` as a 1-based list position (`none` when out of
`1:length(l)`). -/
def idx (l : List Bool) (i : JInt64) : Option Nat :=
  if 1 ≤ i.val ∧ i.val ≤ l.length then some (i.val.toNat - 1) else none

/-! ## Scalar indexing -/

/-- `B[i]` agrees with `v[i]` (`BoundsError` outside `1:length`), and `B[i] = x`
agrees with `v[i] = x` and keeps the invariant. -/
def ScalarIndexAgrees : Prop :=
  ∀ (l : List Bool) (i : JInt64) (x : Bool), l.length < 2 ^ 62 →
    kindOf (getindex (ofList l) i) = (match idx l i with
      | some p => .ok (l.getD p false) | none => .error .bounds) ∧
    kindOf (setindex (ofList l) x i) = (match idx l i with
      | some p => .ok (ofList (l.set p x)) | none => .error .bounds)

/-! ## Dequeue operations -/

/-- `push!`, `pop!`, `pushfirst!`, `popfirst!` agree with `Vector{Bool}`
(`ArgumentError` on empty `pop!`/`popfirst!`) and keep the invariant, whatever
the contents of newly allocated chunks. -/
def DequeAgrees : Prop :=
  ∀ (l : List Bool) (x : Bool) (dirty : U64), l.length < 2 ^ 62 →
    push (ofList l) x dirty = ofList (l ++ [x]) ∧
    pushfirst (ofList l) x dirty = ofList (x :: l) ∧
    kindOf (pop (ofList l)) = (if l = [] then .error .argument
      else .ok (ofList l.dropLast, l.getLastD false)) ∧
    kindOf (popfirst (ofList l)) = (if l = [] then .error .argument
      else .ok (ofList l.tail, l.headD false))

/-- `insert!(B, i, x)` and `deleteat!(B, i)` agree with `Vector{Bool}`
(`BoundsError` unless `1 ≤ i ≤ length+1`, resp. `length`) and keep the invariant. -/
def InsertDeleteAgrees : Prop :=
  ∀ (l : List Bool) (i : JInt64) (x : Bool) (dirty : U64), l.length < 2 ^ 62 →
    kindOf (insert (ofList l) i x dirty) =
      (if 1 ≤ i.val ∧ i.val ≤ l.length + 1 then .ok (ofList (l.insertIdx (i.val.toNat - 1) x))
       else .error .bounds) ∧
    kindOf (deleteat (ofList l) i) =
      (match idx l i with | some p => .ok (ofList (l.eraseIdx p)) | none => .error .bounds)

/-- `deleteat!(B, r)` agrees with `deleteat!(v, r)` for every `UnitRange{Int}` `r`:
the same elements are removed, the same exception type is thrown. -/
def DeleteatRangeAgrees : Prop :=
  ∀ (l : List Bool) (r : URange), l.length < 2 ^ 62 → r.first.val - 1 ≤ r.last.val →
    kindOf (deleteatRange (ofList l) r) = kindOf ((Ref.deleteatRange l r).map ofList)

/-- The same agreement for ranges that are nonempty or start inside `1:length+1`. -/
def DeleteatRangeInsideAgrees : Prop :=
  ∀ (l : List Bool) (r : URange), l.length < 2 ^ 62 → r.first.val - 1 ≤ r.last.val →
    (r.length > 0 ∨ (1 ≤ r.first.val ∧ r.first.val ≤ l.length + 1)) →
    kindOf (deleteatRange (ofList l) r) = kindOf ((Ref.deleteatRange l r).map ofList)

/-- `append!(B, items)` and `prepend!(B, items)` (including `items === B`)
compute `[B; items]` and `[items; B]` and keep the invariant. -/
def AppendPrependAgrees : Prop :=
  ∀ (l m : List Bool) (dirty : U64), l.length + m.length < 2 ^ 62 →
    append (ofList l) (some (ofList m)) dirty = ofList (l ++ m) ∧
    prepend (ofList l) (some (ofList m)) dirty = ofList (m ++ l) ∧
    append (ofList l) none dirty = ofList (l ++ l) ∧
    prepend (ofList l) none dirty = ofList (l ++ l)

/-- `resize!(B, n; first)` keeps the invariant, keeps the old elements (at the end
when `first = true`), and throws the same exception type as `resize!(v, n)`:
`ArgumentError` for `n < 0` (`base/array.jl:1575-1576`). Newly exposed elements
are unspecified, as for `Vector`. -/
def ResizeAgrees : Prop :=
  ∀ (l : List Bool) (n : JInt64) (first : Bool) (dirty : U64), l.length < 2 ^ 62 →
    match kindOf (resize (ofList l) n first dirty) with
    | .ok B => n.val ≥ 0 ∧ B = ofList B.toList ∧ B.len = n.val.toNat ∧
        (if first then B.toList.drop (B.len - min B.len l.length) = l.drop (l.length - min B.len l.length)
         else B.toList.take (min B.len l.length) = l.take (min B.len l.length))
    | .error e => n.val < 0 ∧ e = .argument

/-- The same for every `n ≥ 0`: `resize!` succeeds, keeps the invariant and the
old elements. -/
def ResizeNonnegAgrees : Prop :=
  ∀ (l : List Bool) (n : JInt64) (first : Bool) (dirty : U64), l.length < 2 ^ 62 → n.val ≥ 0 →
    match kindOf (resize (ofList l) n first dirty) with
    | .ok B => B = ofList B.toList ∧ B.len = n.val.toNat ∧
        (if first then B.toList.drop (B.len - min B.len l.length) = l.drop (l.length - min B.len l.length)
         else B.toList.take (min B.len l.length) = l.take (min B.len l.length))
    | .error _ => False

/-- `fill!(B, x)` sets every element and keeps the invariant. -/
def FillAgrees : Prop :=
  ∀ (l : List Bool) (x : Bool), l.length < 2 ^ 62 → fill (ofList l) x = ofList (List.replicate l.length x)

/-! ## Shifts and rotation -/

/-- `B << k` and `B >>> k` (`B >> k`) for every `k::Int` match the docstrings
(`base/bitarray.jl:1333-1414`): elements move `k` positions backwards (`<<`) or
forwards (`>>`), filling with `false`, and the result is a valid `BitVector`. -/
def ShiftAgrees : Prop :=
  ∀ (l : List Bool) (k : JInt64), l.length < 2 ^ 62 →
    shl (ofList l) k = ofList ((List.range l.length).map (fun (t : Nat) =>
      if 0 ≤ (t : Int) + k.val ∧ (t : Int) + k.val < l.length then l.getD ((t : Int) + k.val).toNat false else false)) ∧
    shr (ofList l) k = ofList ((List.range l.length).map (fun (t : Nat) =>
      if 0 ≤ (t : Int) - k.val ∧ (t : Int) - k.val < l.length then l.getD ((t : Int) - k.val).toNat false else false))

/-- `circshift!(B, k)` and `circshift!(dest, B, k)` agree with `Vector{Bool}`'s
`circshift!` for every `k::Int`, including empty vectors. -/
def CircshiftAgrees : Prop :=
  ∀ (l d : List Bool) (k : JInt64), l.length < 2 ^ 62 → d.length = l.length →
    kindOf (circshift (ofList l) none k) = .ok (ofList (Ref.circshift l k)) ∧
    kindOf (circshift (ofList d) (some (ofList l)) k) = .ok (ofList (Ref.circshift l k))

/-- The same agreement for nonempty vectors. -/
def CircshiftNonemptyAgrees : Prop :=
  ∀ (l d : List Bool) (k : JInt64), l.length < 2 ^ 62 → d.length = l.length → l ≠ [] →
    kindOf (circshift (ofList l) none k) = .ok (ofList (Ref.circshift l k)) ∧
    kindOf (circshift (ofList d) (some (ofList l)) k) = .ok (ofList (Ref.circshift l k))

/-- `reverse!(B)` reverses the elements and keeps the invariant. -/
def ReverseAgrees : Prop :=
  ∀ (l : List Bool), l.length < 2 ^ 62 → reverse (ofList l) = ofList l.reverse

/-- `reverse(A; dims=d)` for a `BitArray` of any size `dims` agrees with
`reverse(A; dims=d)` on `Array{Bool}`, including empty arrays, and returns a
valid `BitArray`. -/
def ReverseDimsAgrees : Prop :=
  ∀ (l : List Bool) (dims : List Nat) (d : JInt64) (dirty : U64), l.length < 2 ^ 62 →
    l.length = dimsProd dims → 1 ≤ d.val → d.val ≤ dims.length →
    kindOf (reverseDims (ofList l) dims d dirty) = .ok (ofList (Ref.reverseDims l dims d.val.toNat))

/-- The same for arrays without an empty dimension. -/
def ReverseDimsNonemptyAgrees : Prop :=
  ∀ (l : List Bool) (dims : List Nat) (d : JInt64) (dirty : U64), l.length < 2 ^ 62 →
    l.length = dimsProd dims → 1 ≤ d.val → d.val ≤ dims.length → (∀ s ∈ dims, 0 < s) →
    kindOf (reverseDims (ofList l) dims d dirty) = .ok (ofList (Ref.reverseDims l dims d.val.toNat))

/-! ## Reductions and search -/

/-- `count(B; init)` agrees with `count(v; init)` for every `BitInteger` type of
`init`: both return `init + count` (as an `Int` for small `init` types on
`Vector{Bool}`, `base/reduce.jl:17, 1097-1113`). -/
def CountAgrees : Prop :=
  ∀ (t : IntTy) (init : JInt t) (l : List Bool),
    (count (ofList l) init).val = Ref.count t init l

/-- `count(B)` (default `init = 0`), `any(B)` and `all(B)` agree with `Vector{Bool}`
for every `BitVector` that fits in memory (`length < 2^62`, so the `Int` count
does not wrap). -/
def CountAnyAllAgrees : Prop :=
  ∀ (l : List Bool), l.length < 2 ^ 62 →
    (count (ofList l) (JInt.lit .i64 0)).val = (l.filter id).length ∧
    any (ofList l) = l.any id ∧ all (ofList l) = l.all id

/-- `findnext(B, i)`, `findprev(B, i)` and their negations (`findnext(!, B, i)`,
`findprev(!, B, i)`, `base/bitarray.jl:1521-1532, 1597-1608`) agree with the
generic `findnext`/`findprev` on `Vector{Bool}`: the first (last) position at or
after (before) `i` holding `true` (`false`), `nothing` if none; `findnext` throws
`BoundsError` for `i < 1` and `findprev` for `i > length`. -/
def FindAgrees : Prop :=
  ∀ (l : List Bool) (i : JInt64) (b : Bool), l.length < 2 ^ 62 →
    let fwd : Jl (Option Nat) := if i.val < 1 then .error .boundsError
      else .ok (((List.range l.length).find? (fun (p : Nat) => decide (i.val ≤ (p : Int) + 1) && l.getD p (!b) == b)).map (· + 1))
    let bwd : Jl (Option Nat) := if i.val > l.length then .error .boundsError
      else .ok (((List.range l.length).reverse.find? (fun (p : Nat) => decide ((p : Int) + 1 ≤ i.val) && l.getD p (!b) == b)).map (· + 1))
    kindOf (if b then findnext (ofList l) i else findnextnot (ofList l) i) = kindOf fwd ∧
    kindOf (if b then findprev (ofList l) i else findprevnot (ofList l) i) = kindOf bwd

/-! ## Elementwise maps and logical indexing -/

/-- `map!(f, dest, A)` for `f ∈ {!, ~}` and `map!(g, dest, A, B)` for the
chunkwise `g` of `base/bitarray.jl:1757-1769` agree with elementwise `map!` on
`Vector{Bool}` over the first `min` lengths, leave the rest of `dest`
unchanged, and keep the invariant; `A` may be `dest` itself. -/
def MapAgrees : Prop :=
  ∀ (d a b : List Bool) (g : Bool → Bool → Bool), d.length < 2 ^ 62 → a.length ≤ d.length → b.length ≤ d.length →
    let gc : U64 → U64 → U64 := liftBits g
    bitMap1 (fun x => ~~~x) (ofList d) (some (ofList a)) =
      .ok (ofList (a.map (!·) ++ d.drop a.length)) ∧
    bitMap1 (fun x => ~~~x) (ofList d) none = .ok (ofList (d.map (!·))) ∧
    bitMap2 gc (ofList d) (ofList a) (ofList b) =
      .ok (ofList (List.zipWith g (a.take b.length) (b.take a.length) ++ d.drop (min a.length b.length)))

/-- `B[I] = X` with a logical `BitVector` mask `I` agrees with `v[I] = X` on
`Vector{Bool}`, including the state after a `DimensionMismatch` (none of `v`'s
elements is written: `setindex_shape_check` runs first). -/
def SetindexMaskAgrees : Prop :=
  ∀ (l X I : List Bool), l.length < 2 ^ 62 →
    let (B, e) := setindexMask (ofList l) X (ofList I)
    let (l', e') := Ref.setindexMask l X I
    B = ofList l' ∧ e.map excType = e'.map excType

/-! ## `vec(M)` aliasing -/

/-- Resizing `v = vec(M)` with `push!` or `pop!` leaves `M` a valid `BitArray`
(`num_bit_chunks(length(M))` chunks, unused bits zero), so `M` keeps its
elements, `M == BitArray(collect(M))` holds and reads of `M` stay in bounds. -/
def VecAliasKeepsParentValid : Prop :=
  ∀ (l : List Bool) (x : Bool) (dirty : U64), l.length < 2 ^ 62 →
    let a := Aliased.vecOf (ofList l)
    let p1 := (a.onVec (fun v => push v x dirty)).parent
    let p2 := (a.onVec (fun v => match pop v with | .ok (v', _) => v' | .error _ => v)).parent
    p1 = ofList p1.toList ∧ p2 = ofList p2.toList

/-! ## BitSet -/

/-- `n in s` after any sequence of `push!` and `delete!` agrees with `Set{Int}`
for all `Int` elements, including negative ones and `typemin`/`typemax`. -/
def BitSetPushDeleteAgrees : Prop :=
  ∀ (ops : List (Bool × JInt64)) (n : JInt64),
    (ops.foldl (fun s (o : Bool × JInt64) => if o.1 then s.push o.2 else s.delete o.2) BitSetS.empty).contains n =
      (ops.foldl (fun (S : JInt64 → Bool) (o : Bool × JInt64) =>
        fun y => if y = o.2 then o.1 else S y) (fun _ => false)) n

/-- `symdiff!(s::BitSet, itr)` agrees with `symdiff!(Set{Int}(s), itr)`, which
symmetric-differences with the set of elements of `itr`
(`base/abstractset.jl:297`, #46397): `x` is in the result exactly when it is in
exactly one of `s` and `itr`. -/
def BitSetSymdiffAgrees : Prop :=
  ∀ (xs ns : List JInt64) (y : JInt64),
    ((BitSetS.ofList xs).symdiff ns).contains y = (decide (y ∈ xs) ^^ decide (y ∈ ns))

end JuliaLean.BitArrays
