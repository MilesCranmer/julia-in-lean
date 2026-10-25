import JuliaLean.Ranges.Counted

namespace JuliaLean.Ranges

open JuliaLean.Registry

/-- `base/hashing.jl:55-69`: UInt is UInt64 on the modelled platform. -/
abbrev RangeHashWord := JInt .u64

/-- `base/int.jl` xor intrinsic, used by `base/hashing.jl:57,59`.
The operands are nonnegative UInt64 bit patterns; Core performs the reduction. -/
def rangeHashXor (x y : RangeHashWord) : RangeHashWord :=
  JInt.wrap .u64 (Int.ofNat (Nat.xor x.val.toNat y.val.toNat))

/-- `base/hashing.jl:55`: `3 *% h -% x`, with both wrapping intermediates. -/
def rangeHashMixLinear (x h : RangeHashWord) : RangeHashWord :=
  JInt.lit .u64 3 * h - x

/-- `base/hashing.jl:56-69`: the 64-bit hash_uint finalizer. -/
def rangeHashUInt (x : RangeHashWord) : RangeHashWord :=
  let x := rangeHashXor x (JInt.wrap .u64 (Int.ofNat (x.val.toNat / 2^32)))
  let x := x * JInt.lit .u64 0x63652a4cd374b267
  rangeHashXor x (JInt.wrap .u64 (Int.ofNat (x.val.toNat / 2^33)))

/-- `base/multidimensional.jl:2084-2085,2101,2122-2123`: the two external
hash methods used by range hashing. `scalar` is hash of a scalar integer;
`tuple1` is hash of a one-element tuple of integers, used for axis endpoints.
Neither callback supplies an array hash or chooses the array algorithm. -/
structure RangeHashCallbacks where
  scalar : Num → RangeHashWord → RangeHashWord
  tuple1 : Num → RangeHashWord → RangeHashWord

/-- The numeric and singleton-tuple hash contracts, `base/hashing.jl:12-16`.
These are explicit theorem hypotheses, including cross-type integer equality. -/
def RangeHashCallbacks.RespectsValues (c : RangeHashCallbacks) : Prop :=
  (∀ x y h, x.val = y.val → c.scalar x h = c.scalar y h) ∧
  (∀ x y h, x.val = y.val → c.tuple1 x h = c.tuple1 y h)

/-- `base/range.jl:850,864`, `base/abstractarray.jl:452-453`:
StepRange's firstindex specialization, otherwise first of its OneTo axis.
`n` is the actual result of length(r), never the mathematical cardinality. -/
def rangeHashFirstindex (r : ResultRng) (n : Num) : Num :=
  match r with
  | .counted _ => Num.one n.ty
  | .ordinal r =>
    if r.kind = .step ∧ r.start.ty ≠ .bool ∧ r.stride.ty ≠ .bool then
      if r.start.ty.small then Num.lit (.bit .i64) 1
      else Num.one (Num.sub (last r) (first r)).ty
    else Num.one n.ty

/-- `base/range.jl:706`, `base/abstractarray.jl:100-102`,
`base/range.jl:511`: axes(r) is a singleton unchecked OneTo(length(r)).
Consequently its first is one of the length type and its last is the
unmodified length, including a wrapped negative length. -/
def rangeHashShape (c : RangeHashCallbacks) (n : Num) (h : RangeHashWord) : RangeHashWord :=
  c.tuple1 n (c.tuple1 (Num.one n.ty) h)

/-- `base/multidimensional.jl:2090-2093`: the direct, left-to-right chain. -/
def rangeHashChain (c : RangeHashCallbacks) (xs : List Num) (h : RangeHashWord) : RangeHashWord :=
  xs.foldl (fun h x => c.scalar x h) h

/-- `base/multidimensional.jl:2090-2093`, `base/range.jl:928-942`:
a complete iteration trace. Each yield carries the actual iteration state,
which is the element for ordinal ranges and an index for StepRangeLen.
No length-based truncation is imposed on iteration. -/
inductive RangeHashTrace (r : ResultRng) : Option Num → Jl (List Num) → Prop where
  | done {state} : countedResultIterate r state = .ok none → RangeHashTrace r state (.ok [])
  | error {state e} : countedResultIterate r state = .error e → RangeHashTrace r state (.error e)
  | next {state x nextState xs} : countedResultIterate r state = .ok (some (x, nextState)) →
      RangeHashTrace r (some nextState) (.ok xs) → RangeHashTrace r state (.ok (x :: xs))
  | nextError {state x nextState e} : countedResultIterate r state = .ok (some (x, nextState)) →
      RangeHashTrace r (some nextState) (.error e) → RangeHashTrace r state (.error e)

/-- `base/multidimensional.jl:2108-2110,2044`: accumulator streams, numbered from zero. -/
abbrev RangeHashStreams := Nat → RangeHashWord

/-- `base/multidimensional.jl:2101,2031`: assignment to exactly one accumulator. -/
def rangeHashSetStream (p : RangeHashStreams) (i : Nat) (h : RangeHashWord) : RangeHashStreams :=
  fun j => if j = i then h else p j

/-- `base/multidimensional.jl:2108-2110,2044-2045`: fold streams in source order. -/
def rangeHashFoldStreams (count : Nat) (p : RangeHashStreams) (h : RangeHashWord) : RangeHashWord :=
  rangeHashUInt ((List.range count).foldl (fun h i => rangeHashMixLinear (p i) h) h)

/-- `base/multidimensional.jl:2101`: the unrolled eight getindex calls, in order.
The Julia index expression is `(off + n + i) - 1`, with one-based stream i. -/
def rangeHashBlock (c : RangeHashCallbacks) (r : ResultRng) (off n : Num)
    (p : RangeHashStreams) : List Nat → Jl RangeHashStreams
  | [] => .ok p
  | j :: js => do
      let i := Num.lit (.bit .i64) (Int.ofNat (j + 1))
      let idx := Num.sub (Num.add (Num.add off n) i) (Num.lit (.bit .i64) 1)
      let x ← resultGetindex r idx
      rangeHashBlock c r off n (rangeHashSetStream p j (c.scalar x (p j))) js

/-- `base/multidimensional.jl:2022-2042,2097-2106`: source loop states.
In the Fibonacci branch keys, both linear maps, and first_linear use Int64:
LinearIndices converts the range axis to AbstractUnitRange{Int}.
`search` implements findprev(!isequal(elt), r, key) without replacing it by a
monotonicity shortcut. -/
inductive RangeHashState where
  | blocks (len off n : Num) (p : RangeHashStreams) (h : RangeHashWord)
  | tail (len off n : Num) (p : RangeHashStreams) (h : RangeHashWord)
  | fib (key skip prev n : Num) (p : RangeHashStreams) (h : RangeHashWord)
  | search (key elt skip prev n : Num) (p : RangeHashStreams) (h : RangeHashWord)

/-- `base/multidimensional.jl:2022-2045,2097-2112`, `base/array.jl:2671-2684`,
`base/operators.jl:914` (mod1):
one source loop transition, including the exact order of reads and checks.
Num operations preserve every Julia integer promotion and wrapping intermediate. -/
def rangeHashStep (c : RangeHashCallbacks) (r : ResultRng) :
    RangeHashState → Jl (Sum RangeHashWord RangeHashState)
  | .blocks len off n p h => do
      if n.val ≤ (Num.sub len (Num.lit (.bit .i64) 7)).val then
        let p ← rangeHashBlock c r off n p (List.range 8)
        pure (.inr (.blocks len off (Num.add n (Num.lit (.bit .i64) 8)) p h))
      else pure (.inr (.tail len off n p h))
  | .tail len off n p h => do
      if n.val ≤ len.val then
        let x ← resultGetindex r (Num.add off n)
        let p := rangeHashSetStream p 0 (c.scalar x (p 0))
        pure (.inr (.tail len off (Num.add n (Num.lit (.bit .i64) 1)) p h))
      else pure (.inl (rangeHashFoldStreams 8 p h))
  | .fib key skip prev n p h => do
      let n := Num.add n (Num.lit (.bit .i64) 1)
      let elt ← resultGetindex r key
      let m ← Num.mod n (Num.lit (.bit .i64) 4)
      let stream := if m.val = 0 then Num.lit (.bit .i64) 4 else m
      let j := (Num.sub stream (Num.lit (.bit .i64) 1)).val.toNat
      let p := rangeHashSetStream p j (rangeHashMixLinear (c.scalar key (p j)) (c.scalar elt (p j)))
      if key.val < (Num.add skip (Num.lit (.bit .i64) 1)).val then
        pure (.inl (rangeHashFoldStreams 4 p h))
      else
        let key := Num.sub key skip
        let rem ← Num.rem n (Num.lit (.bit .i64) 4096)
        let (skip, prev) := if rem.val = 0 then (Num.add skip prev, skip) else (skip, prev)
        pure (.inr (.search key elt skip prev n p h))
  | .search key elt skip prev n p h => do
      if key.val < 1 then pure (.inl (rangeHashFoldStreams 4 p h))
      else
        let x ← resultGetindex r key
        if x.val ≠ elt.val then pure (.inr (.fib key skip prev n p h))
        else if key.val = 1 then pure (.inl (rangeHashFoldStreams 4 p h))
        else pure (.inr (.search (Num.sub key (Num.lit (.bit .i64) 1)) elt skip prev n p h))

/-- Finite big-step semantics of the source while loops. A diverging execution
has no derivation; there is no arbitrary fuel limit or invented Julia exception. -/
inductive RangeHashRun (c : RangeHashCallbacks) (r : ResultRng) : RangeHashState → Jl RangeHashWord → Prop where
  | error {s e} : rangeHashStep c r s = .error e → RangeHashRun c r s (.error e)
  | done {s h} : rangeHashStep c r s = .ok (.inl h) → RangeHashRun c r s (.ok h)
  | next {s t out} : rangeHashStep c r s = .ok (.inr t) →
      RangeHashRun c r t out → RangeHashRun c r s out

/-- `base/multidimensional.jl:2080-2123`: hash(::AbstractArray) specialized to
ordinal and integer-element StepRangeLen ranges. All three length branches are retained. Long ranges
first construct keys(A) = LinearIndices(A), which converts the axis to Int64
and can throw even before the first element read (`base/indices.jl:464-476`).
Callbacks cover scalar numeric hashing and singleton tuple hashing only. -/
inductive RangeHash (c : RangeHashCallbacks) (r : ResultRng) (seed : RangeHashWord) : Jl RangeHashWord → Prop where
  | lengthError {e} : resultLength r = .error e → RangeHash c r seed (.error e)
  | short {n xs} : resultLength r = .ok n → n.val < 8 →
      RangeHashTrace r none (.ok xs) →
      RangeHash c r seed (.ok (rangeHashChain c xs
        (rangeHashShape c n (rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)))))
  | shortError {n e} : resultLength r = .ok n → n.val < 8 →
      RangeHashTrace r none (.error e) → RangeHash c r seed (.error e)
  | medium {n out} : resultLength r = .ok n → 8 ≤ n.val → n.val < 32768 →
      RangeHashRun c r (.blocks n
        (Num.sub (rangeHashFirstindex r n) (Num.lit (.bit .i64) 1))
        (Num.lit (.bit .i64) 1)
        (fun _ => rangeHashShape c n (rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)))
        (rangeHashShape c n (rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)))) out →
      RangeHash c r seed out
  | longIndexError {n e} : resultLength r = .ok n → 32768 ≤ n.val →
      Num.cast (.bit .i64) n = .error e → RangeHash c r seed (.error e)
  | long {n key out} : resultLength r = .ok n → 32768 ≤ n.val →
      Num.cast (.bit .i64) n = .ok key →
      RangeHashRun c r (.fib key (Num.lit (.bit .i64) 1) (Num.lit (.bit .i64) 1)
        (Num.lit (.bit .i64) 0)
        (fun _ => rangeHashShape c n (rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)))
        (rangeHashShape c n (rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)))) out →
      RangeHash c r seed out

private theorem rangeHashOne_val (ty : NType) : (Num.one ty).val = 1 := by
  cases ty with
  | bool => decide
  | bit t => cases t <;> decide

private theorem rangeHashChain_values (c : RangeHashCallbacks) (hc : c.RespectsValues)
    (xs ys : List Num) (hv : xs.map Num.val = ys.map Num.val) (h : RangeHashWord) :
    rangeHashChain c xs h = rangeHashChain c ys h := by
  induction xs generalizing ys h with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hv
  | cons x xs ih =>
      cases ys with
      | nil => simp at hv
      | cons y ys =>
          have hv' : x.val = y.val ∧ xs.map Num.val = ys.map Num.val := by simpa using hv
          simp only [rangeHashChain, List.foldl_cons]
          rw [hc.1 x y h hv'.1]
          exact ih ys hv'.2 (c.scalar y h)

/-- Inputs arise from keyword or StepRangeLen constructors, rather than arbitrary records. -/
def RangeHashConstructed (r : ResultRng) : Prop :=
  (∃ a s b n, rangeKw a s b n = some (.ok r)) ∨
  (∃ ty ref stride len offset, countedRange ty ref stride len offset = .ok r)

/-- Equal integer range contents and equal axes have equal hashes in the direct
branch, regardless of element or length storage types. Preconditions spell out
semantic array equality using complete actual iterate traces; both ranges must
come from constructors, and their machine lengths must select len < 8.
No equality assumption is made about hashes or about the stored range records. -/
def ShortEqualRangeHashConsistency : Prop :=
  ∀ (c : RangeHashCallbacks), c.RespectsValues →
  ∀ (r s : ResultRng) (nr ns : Num) (xs ys : List Num) (seed : RangeHashWord),
    RangeHashConstructed r → RangeHashConstructed s →
    resultLength r = .ok nr → resultLength s = .ok ns → nr.val = ns.val → nr.val < 8 →
    RangeHashTrace r none (.ok xs) → RangeHashTrace s none (.ok ys) →
    xs.map Num.val = ys.map Num.val →
    ∃ h, RangeHash c r seed (.ok h) ∧ RangeHash c s seed (.ok h)

theorem shortEqualRangeHashConsistency_proven : ShortEqualRangeHashConsistency := by
  intro c hc r s nr ns xs ys seed _ _ hr hs hn hsmall hx hy hvalues
  let initial := rangeHashXor seed (JInt.lit .u64 0x7e2d6fb6448beb77)
  have hshape : rangeHashShape c nr initial = rangeHashShape c ns initial := by
    unfold rangeHashShape
    rw [hc.2 (Num.one nr.ty) (Num.one ns.ty) initial
      ((rangeHashOne_val nr.ty).trans (rangeHashOne_val ns.ty).symm)]
    exact hc.2 nr ns _ hn
  refine ⟨rangeHashChain c xs (rangeHashShape c nr initial), ?_, ?_⟩
  · exact RangeHash.short hr hsmall hx
  · have heq : rangeHashChain c xs (rangeHashShape c nr initial) =
        rangeHashChain c ys (rangeHashShape c ns initial) := by
      rw [hshape]
      exact rangeHashChain_values c hc xs ys hvalues _
    rw [heq]
    exact RangeHash.short hs (by omega) hy

/-- `base/hashing.jl:55`: subtracting a key and folding retain UInt64 wrapping. -/
def RangeHashMixExact : Prop :=
  ∀ (x h : RangeHashWord), (rangeHashMixLinear x h).val =
    wrapInt .u64 (wrapInt .u64 (3 * h.val) - x.val)

theorem rangeHashMixExact_proven : RangeHashMixExact := by
  intro x h
  rfl

def hashEntries : List Entry := [
  { id := "ranges-hash-short-equal-consistency"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["hash(::AbstractArray, ::UInt)", "hash_shaped", "iterate(::OrdinalRange)", "iterate(::StepRangeLen)"]
    statement := "Constructor-produced integer ranges with equal axes and equal complete iteration contents hash equally in the len < 8 branch, assuming scalar and singleton-tuple hashing respect mathematical integer equality."
    source := "base/hashing.jl:12-16; base/abstractarray.jl isequal(::AbstractArray); base/multidimensional.jl:2080-2094"
    status := .proven
    prop := ``ShortEqualRangeHashConsistency
    thm := some ``shortEqualRangeHashConsistency_proven
    notes := "Quantifies two independent constructor-produced ordinal or integer-element StepRangeLen ranges, both callbacks, all machine length types, actual iteration traces and seeds. Scalar/tuple contracts are hypotheses, not axioms. The model also retains the eight-stream and Fibonacci algorithms, but this theorem covers the direct branch only. No claim that wrapped length equals mathematical cardinality is assumed." },
  { id := "ranges-hash-mix-wrapping"
    juliaFile := "base/hashing.jl"
    juliaFns := ["hash_mix_linear"]
    statement := "Linear hash mixing wraps the product before the subtraction, matching the UInt64 source operations."
    source := "base/hashing.jl:55"
    status := .proven
    prop := ``RangeHashMixExact
    thm := some ``rangeHashMixExact_proven }
]

end JuliaLean.Ranges
