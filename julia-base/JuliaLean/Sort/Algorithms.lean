import JuliaLean.Core

/-!
The comparison-based sorting kernels of `base/sort.jl` (master `bbfa0ce4150`)
reached by `sort!`, `partialsort!` and `partialsortperm!` for orderings that
are not `UIntMappable` (any `by`/`lt`, and `Perm`), and their entry points.

Vectors are one-based `Array α`; `lt` is `lt(o, ·, ·)` for the ordering `o`.
Index reads and writes mirror Julia's `@inbounds` accesses: the model is only
claimed faithful on executions whose accesses are in bounds (every property
below holds on such executions only). `fuel` bounds recursion and is a model
artifact; the entry points supply enough for every input.
-/

namespace JuliaLean.Sort

open JuliaLean

section
variable {α : Type} [Inhabited α]

/-- `v[i]` (one-based). -/
def rd (v : Array α) (i : Int) : α := if 1 ≤ i then v.getD (i - 1).toNat default else default

/-- `v[i] = x` (one-based). -/
def wr (v : Array α) (i : Int) (x : α) : Array α :=
  if 1 ≤ i then v.modify (i - 1).toNat (fun _ => x) else v

/-- `copyto!(dest, d, src, s, n)` for `n ≥ 0`, `base/array.jl`. -/
def copyTo (dest : Array α) (d : Int) (src : Array α) (s : Int) (n : Int) : Array α :=
  (List.range n.toNat).foldl (fun w (k : Nat) => wr w (d + k) (rd src (s + k))) dest

/-- `reverse!(v, lo, hi)`, `base/array.jl` (swaps `v[lo+k]` and `v[hi-k]`). -/
def reverseRange (v : Array α) (lo hi : Int) : Array α :=
  (List.range ((hi - lo + 1) / 2).toNat).foldl
    (fun w (k : Nat) => let a := rd w (lo + k); let b := rd w (hi - k); wr (wr w (lo + k) b) (hi - k) a) v

/-- Inner loop of `InsertionSort`, `base/sort.jl:841-849`: `k = j - lo` steps remain. -/
def insertLoop (lt : α → α → Bool) (lo : Int) (x : α) : Nat → Array α → Int → Array α
  | 0, v, j => wr v j x
  | k + 1, v, j =>
    let y := rd v (j - 1)
    if !(lt x y) then wr v j x
    else insertLoop lt lo x k (wr v j y) (j - 1)

/-- `_sort!(v, InsertionSortAlg(), o, (; lo, hi))`, `base/sort.jl:835-852`. -/
def insertionSort (lt : α → α → Bool) (v : Array α) (lo hi : Int) : Array α :=
  (List.range (hi - lo).toNat).foldl
    (fun w (k : Nat) => let i := lo + 1 + k; insertLoop lt lo (rd w i) (i - lo).toNat w i) v

/-- `partition!(t, lo, hi, offset, o, v, rev, pivot_dest, pivot_index_offset)`,
`base/sort.jl:1088-1119`, with source `src` (Julia's `v`) and destination `dst`
(Julia's `t`). `pivotToSrc` says whether `pivot_dest` is the source array
(the first call site, sort.jl:1135) or the destination (sort.jl:1133).
`piv lo hi` is `mod(hash(lo), lo:hi)` (sort.jl:1092). Returns the updated
source, destination and the pivot index. -/
def partition (piv : Int → Int → Int) (lt : α → α → Bool) (src dst : Array α)
    (lo hi offset : Int) (rev pivotToSrc : Bool) (pio : Int) : Array α × Array α × Int :=
  let p := piv lo hi
  let pivot := rd src p
  -- sort.jl:1095-1101
  let r1 := (List.range (p - lo).toNat).foldl (fun (st : Array α × Int) (k : Nat) =>
      let l := lo + k
      let x := rd src l
      let fx := if rev then !(lt x pivot) else lt pivot x
      (wr st.1 ((if fx then hi else l) - st.2) x, st.2 + (if fx then 1 else 0))) (dst, offset)
  -- sort.jl:1102-1108
  let r2 := (List.range (hi - p).toNat).foldl (fun (st : Array α × Int) (k : Nat) =>
      let l := p + k
      let x := rd src (l + 1)
      let fx := if rev then lt pivot x else !(lt x pivot)
      (wr st.1 ((if fx then hi else l) - st.2) x, st.2 + (if fx then 1 else 0))) r1
  -- sort.jl:1109-1110 (the loops end with `lo == hi`)
  let j := hi - r2.2 + pio
  if pivotToSrc then (wr src j pivot, r2.1, j) else (src, wr r2.1 j pivot, j)

/-- The `lo`/`hi` targets of `ScratchQuickSort` (`missing` is `none`), sort.jl:1074-1082. -/
structure Target where
  lo : Option Int
  hi : Option Int

/-- `SMALL_THRESHOLD`, `base/sort.jl:1595`. -/
def smallThreshold : Int := 20

/-- `_sort!(v, a::ScratchQuickSort, o, kw; t, offset, swap, rev)`,
`base/sort.jl:1121-1164`, on the pair `(v, t)`; `a.next` is `InsertionSort`. -/
def scratchQuickSortLoop (piv : Int → Int → Int) (lt : α → α → Bool) (a : Target) :
    Nat → Array α → Array α → Int → Int → Int → Bool → Bool → Array α × Array α
  | 0, v, t, _, _, _, _, _ => (v, t)
  | fuel + 1, v, t, lo, hi, offset, swap, rev =>
    if lo < hi ∧ hi - lo > smallThreshold then
      -- sort.jl:1132-1137
      let r : Array α × Array α × Int :=
        if swap then
          let (s, d, j) := partition piv lt t v (lo + offset) (hi + offset) offset rev false 0
          (d, s, j)
        else partition piv lt v t lo hi (-offset) rev true (-offset)
      let v := r.1
      let t := r.2.1
      let j := r.2.2
      let swap := !swap
      if a.lo.isSome ∧ j ≤ a.lo.getD 0 then
        -- sort.jl:1140-1144: skip sorting the lower part
        let v := if swap then copyTo v lo t (lo + offset) (j - lo) else v
        let v := if rev then reverseRange v lo (j - 1) else v
        scratchQuickSortLoop piv lt a fuel v t (j + 1) hi offset swap (!rev)
      else if a.hi.isSome ∧ a.hi.getD 0 ≤ j then
        -- sort.jl:1145-1148: skip sorting the upper part
        let v := if swap then copyTo v (j + 1) t (j + 1 + offset) (hi - j) else v
        let v := if rev then v else reverseRange v (j + 1) hi
        scratchQuickSortLoop piv lt a fuel v t lo (j - 1) offset swap rev
      else if j - lo < hi - j then
        -- sort.jl:1149-1154
        let r := scratchQuickSortLoop piv lt a fuel v t lo (j - 1) offset swap rev
        scratchQuickSortLoop piv lt a fuel r.1 r.2 (j + 1) hi offset swap (!rev)
      else
        -- sort.jl:1155-1157
        let r := scratchQuickSortLoop piv lt a fuel v t (j + 1) hi offset swap (!rev)
        scratchQuickSortLoop piv lt a fuel r.1 r.2 lo (j - 1) offset swap rev
    else
      -- sort.jl:1160-1163
      if hi < lo then (v, t)
      else
        let v := if swap then copyTo v lo t (lo + offset) (hi - lo + 1) else v
        let v := if rev then reverseRange v lo hi else v
        (insertionSort lt v lo hi, t)

/-- Entry of `ScratchQuickSort` without a caller scratch vector, sort.jl:1125-1129:
`t` is a fresh vector of length `hi-lo+1` and `offset = 1-lo`. -/
def scratchQuickSort (piv : Int → Int → Int) (lt : α → α → Bool) (a : Target)
    (v : Array α) (lo hi : Int) : Array α :=
  (scratchQuickSortLoop piv lt a ((hi - lo + 2).toNat) v
    (Array.replicate (hi - lo + 1).toNat default) lo hi (1 - lo) false false).1

/-- `InitialOptimizations(next)` (sort.jl:1473-1478) for element types that are
neither `Missing`-unions, `Bool` nor IEEE floats, on a plain vector: only
`Small{10}` acts, sending `hi - lo < 10` to `InsertionSort` (sort.jl:795-802). -/
def initialOptimizations (lt : α → α → Bool) (next : Array α → Array α)
    (v : Array α) (lo hi : Int) : Array α :=
  if hi - lo < 10 then insertionSort lt v lo hi else next v

/-- `_issorted(v, lo, hi, o)`, `base/sort.jl:1445-1451`. -/
def isSortedRange (lt : α → α → Bool) (v : Array α) (lo hi : Int) : Bool :=
  (List.range (hi - lo).toNat).all fun (k : Nat) => !(lt (rd v (lo + 1 + k)) (rd v (lo + k)))

/-- `StableCheckSorted(ScratchQuickSort())`, `base/sort.jl:1368-1379`. The
reverse check uses `Lt((x, y) -> !lt(o, x, y))`. -/
def stableCheckSorted (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α)
    (lo hi : Int) : Array α :=
  if isSortedRange lt v lo hi then v
  else if isSortedRange (fun x y => !(lt x y)) v lo hi then reverseRange v lo hi
  else scratchQuickSort piv lt ⟨none, none⟩ v lo hi

/-- `sort!(v; alg=DEFAULT_STABLE or DEFAULT_UNSTABLE, order)` for an ordering
that is not `UIntMappable` (sort.jl:1580-1593, 1732-1741): the `IsUIntMappable`
test (sort.jl:774-780) takes the `StableCheckSorted(ScratchQuickSort())` branch. -/
def sortGeneric (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α) : Array α :=
  initialOptimizations lt (fun w => stableCheckSorted piv lt w 1 w.size) v 1 v.size

/-- The pivot rule `mod(hash(lo), lo:hi)` (sort.jl:1092) on 64-bit Julia, for
`1 ≤ lo ≤ hi`: `hash(x::Int64) = hash_finalizer(3 * HASH_SEED - x)` with
wrapping `UInt64` arithmetic (`base/hashing.jl:3,40,55-63,75-76`), and
`mod(i, lo:hi) = mod(i - lo, hi - lo + 1) + lo` (`base/range.jl:1549`) in `UInt64`. -/
def juliaHashInt (x : Int) : Nat :=
  let m : Nat := 2 ^ 64
  let z : Nat := (((3 * 0xbdd89aa982704029 + m * m : Nat) : Int) - x).toNat % m
  let z : Nat := z ^^^ (z >>> 32)
  let z : Nat := (z * 0x63652a4cd374b267) % m
  z ^^^ (z >>> 33)

def juliaPivot (lo hi : Int) : Int :=
  lo + (((juliaHashInt lo + 2 ^ 64 - lo.toNat) % 2 ^ 64) % (hi - lo + 1).toNat : Nat)

end

end JuliaLean.Sort
