import JuliaLean.base.bitset
import JuliaLean.base.int
import JuliaLean.Registry.Types

/-!
# Properties of `base/bitset.jl`

These statements specify BitSet's set behavior, ordering, iteration, and chunk
invariants independently of proofs. Each registry entry remains open for the
proof and refutation worker.
-/

namespace JuliaLean.Proofs.base.bitset

open JuliaLean
open JuliaLean.base.bitset
open JuliaLean.Registry

/-- A stored BitSet has no chunks at the sentinel offset and its active chunk span stays in Int's range. -/
def WF (s : BitSet) : Prop :=
  (s.offset = noOffset → s.bits = []) ∧
  (s.offset ≠ noOffset → -(2 ^ 57) ≤ s.offset ∧ s.offset + s.bits.length ≤ 2 ^ 57)

def inIntRange (n : Int) : Prop := IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64

def member (s : BitSet) (n : Int) : Bool := inInteger n s

def applyOps (s : BitSet) : List (Bool × I64) → BitSet
  | [] => s
  | op :: rest =>
      let next := if op.1 then
        match push s op.2.val with
        | .ok out => out
        | .error _ => s
      else deleteInt s op.2
      applyOps next rest

def idealOps (ops : List (Bool × I64)) : I64 → Bool :=
  ops.foldl (fun contains op => fun n => if n = op.2 then op.1 else contains n) (fun _ => false)

/-- Values obtained by repeatedly calling JuliaLean.base.bitset.iterate. -/
def iterated (s : BitSet) : List I64 :=
  let rec walk : Nat → U64 × Nat → List I64
    | 0, _ => []
    | fuel + 1, state =>
        match iterate s state with
        | none => []
        | some (n, next) => n :: walk fuel next
  walk (s.bits.length * 64 + 1) (zero64, 0)

def joinComma : List String → String
  | [] => ""
  | first :: rest => rest.foldl (fun out item => out ++ ", " ++ item) first

def unionArgMember (arg : UnionArg) (n : Int) : Bool :=
  match arg with
  | .bitset s => member s n
  | .range first last => decide (first.val ≤ n ∧ n ≤ last.val)
  | .iterator xs => xs.contains n

def unionArgValid : UnionArg → Prop
  | .bitset s => WF s
  | .range _ _ => True
  | .iterator xs => ∀ n ∈ xs, inIntRange n

/-- After any push/delete sequence, membership agrees with a mathematical set update. -/
def BitSetPushDeleteAgrees : Prop :=
  ∀ (ops : List (Bool × I64)) (n : I64),
    inInt n (applyOps new ops) = idealOps ops n

/-- `symdiff!` keeps exactly members in one of the input sets; duplicate iterator values count as repeated toggles. -/
def BitSetSymdiffAgrees : Prop :=
  ∀ (s : BitSet) (xs : List Int) (n : I64) (out : BitSet),
    symdiffIterator s xs = .ok out →
    inInt n out = (inInt n s ^^ decide (n.val ∈ xs))

/-- Every successful lookup selects a chunk inside the stored vector, and every generated zero-check index is in its requested chunk span. -/
def indexWithin (bits : List U64) (i : Int) : Prop := 1 ≤ i ∧ i ≤ bits.length

def spanWithin (bits : List U64) (start count : Int) : Prop :=
  0 ≤ count ∧ (count = 0 ∨ 1 ≤ start ∧ start + count - 1 ≤ bits.length)

def BitSetAccessesInBounds : Prop :=
  (∀ (s : BitSet) (n : I64), inInt n s = true →
    indexWithin s.bits (div64 n.val - s.offset + 1) ∧
    0 ≤ n.val % 64 ∧ n.val % 64 < 64) ∧
  (∀ (b : List U64) (n : Nat) (i : Int),
    i ∈ intRange (b.length + 1) (b.length + n) → indexWithin (growend0 b n) i) ∧
  (∀ (b : List U64) (n : Nat) (i : Int),
    i ∈ intRange 1 n → indexWithin (growbeg0 b n) i) ∧
  (∀ (s : BitSet) (a b : I64), WF s → a.val ≤ b.val →
    let out := unionRangeBits s a b
    indexWithin out.bits (div64 a.val - out.offset + 1) ∧
    indexWithin out.bits (div64 b.val - out.offset + 1) ∧
    ∀ i ∈ intRange (div64 a.val - out.offset + 1) (div64 b.val - out.offset + 1),
      indexWithin out.bits i) ∧
  (∀ (a1 a2 : List U64) (b1 b2 i : Int),
    i ∈ intRange (max 1 (1 + b2 - b1)) (min a1.length (a2.length + b2 - b1)) →
    indexWithin a1 i ∧ indexWithin a2 (i - (b2 - b1))) ∧
  (∀ (a1 a2 : List U64) (b1 b2 : Int) (leftFalseIsFalse : Bool),
    let l1 : Int := a1.length
    let l2 : Int := a2.length
    let bdiff := b2 - b1
    let e1 := l1 + b1
    let e2 := l2 + b2
    let ediff := e2 - e1
    let l1' := if l1 + 1 ≤ bdiff then bdiff else l1
    let copyCount := e2 - l1' - b1
    ediff > 0 → leftFalseIsFalse = false →
      spanWithin (bitsGrowEnd a1 ediff.toNat zero64) (l1' + 1) copyCount ∧
      spanWithin a2 (l2 + 1 - copyCount) copyCount) ∧
  (∀ (a1 a2 : List U64) (b1 b2 : Int) (leftFalseIsFalse : Bool),
    let bdiff := b2 - b1
    bdiff < 0 → leftFalseIsFalse = false →
      spanWithin (bitsGrowBeg a1 (-bdiff).toNat zero64) 1 (min (-bdiff) a2.length) ∧
      spanWithin a2 1 (min (-bdiff) a2.length)) ∧
  (∀ (s1 s2 : BitSet), WF s1 → WF s2 → s1.offset ≤ s2.offset →
    let l1 : Int := s1.bits.length
    let l2 : Int := s2.bits.length
    let overlap0 := max 0 (l1 + s1.offset - s2.offset)
    let overlap := if overlap0 ≥ l2 then l2 else overlap0
    overlap > 0 →
      spanWithin s1.bits (s2.offset - s1.offset + 1) overlap ∧
      spanWithin s2.bits 1 overlap) ∧
  (∀ (b : List U64) (lo hi i : Int),
    1 ≤ lo → hi ≤ b.length → i ∈ intRange lo hi → indexWithin b i) ∧
  (∀ (a b : BitSet) (i : Int), WF a → WF b →
    i ∈ intRange 1 (min a.bits.length (b.offset - a.offset)) →
      indexWithin a.bits i) ∧
  (∀ (a b : BitSet) (i : Int), WF a → WF b →
    i ∈ intRange (max 1 (b.offset - a.offset + 1))
      (min a.bits.length (b.offset - a.offset + b.bits.length)) →
      indexWithin a.bits i ∧
      indexWithin b.bits (i - (b.offset - a.offset))) ∧
  (∀ (a b : BitSet) (i : Int), WF a → WF b →
    i ∈ intRange (max 1 (b.offset - a.offset + b.bits.length + 1)) a.bits.length →
      indexWithin a.bits i) ∧
  ∀ (s : BitSet) (idx : Nat), idx < s.bits.length →
    indexWithin s.bits (idx + 1)

/-- Constructors and iterable insertion make membership exactly the union of inserted Int values. -/
def BitSetBuildSpec : Prop :=
  WF new ∧ new.offset = noOffset ∧ new.bits = [] ∧
  (∀ n, member new n = false) ∧
  (∀ (s : BitSet) (xs : List Int), WF s → (∀ n ∈ xs, inIntRange n) →
    ∃ out, unionIterator s xs = .ok out ∧ WF out ∧
      ∀ n, member out n = (member s n || decide (n ∈ xs))) ∧
  (∀ (s : BitSet) (xs : List Int),
    (∃ n ∈ xs, ¬ inIntRange n) →
      unionIterator s xs = .error (.julia (.inexactError "Int64"))) ∧
  (∀ xs : List Int, (∀ n ∈ xs, inIntRange n) →
    ∃ out, ofIterator xs = .ok out ∧ WF out ∧
      ∀ n, member out n = decide (n ∈ xs)) ∧
  (∀ xs : List Int, (∃ n ∈ xs, ¬ inIntRange n) →
    ofIterator xs = .error (.julia (.inexactError "Int64"))) ∧
  (∀ s : BitSet, empty s = new ∧ emptymutable s = new) ∧
  (∀ (s : BitSet) (xs : List Int), (∀ n ∈ xs, inIntRange n) →
    ∃ out, pushMany s xs = .ok out ∧ WF out ∧
      ∀ n, member out n = (member s n || decide (n ∈ xs))) ∧
  (∀ (s : BitSet) (xs : List Int), (∃ n ∈ xs, ¬ inIntRange n) →
    pushMany s xs = .error (.julia (.inexactError "Int64")))

/-- Copying preserves all chunks and the offset. -/
def BitSetCopySpec : Prop :=
  ∀ (dest src : BitSet),
    copyBang dest src = src ∧ copy src = src ∧ copymutable src = src

/-- `sizehint!` preserves elements and reports only an Int conversion failure for the chunk hint. -/
def BitSetSizehintSpec : Prop :=
  ∀ (t : IntTy) (s : BitSet) (n : JInt t),
    let adjusted := n + JInt.lit t 63
    let chunks := if t.signed then
      JuliaLean.base.int.ashr_int adjusted (JInt.lit t 6)
    else JuliaLean.base.int.lshr_int adjusted (JInt.lit t 6)
    if IntTy.min .i64 ≤ chunks.val ∧ chunks.val ≤ IntTy.max .i64 then sizehint s n = .ok s
    else sizehint s n = .error (.julia (.inexactError "Int64"))

/-- Membership reads the addressed UInt64 bit and rejects Integers outside Int's range. -/
def BitSetInSpec : Prop :=
  (∀ (b : List U64) (n : I64) (offset : Int),
    let ci := div64 n.val - offset + 1
    bitsGetindex b n offset =
      if 1 ≤ ci ∧ ci ≤ b.length then
        (bitsGet b ci.toNat).val.toNat.testBit (mod64 n.val)
      else false) ∧
  (∀ n : Int, isConvertibleInt n = decide (IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64)) ∧
  ∀ (s : BitSet) (n : Int),
    member s n = if IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64 then inInt (int64 n) s else false

/-- Deletion removes exactly its key; keyed pop returns that key or the supplied default. -/
def BitSetDeleteSpec : Prop :=
  (∀ (s : BitSet) (n : I64), WF s →
    WF (deleteInt s n) ∧ ∀ x, inInt x (deleteInt s n) = (inInt x s && decide (x ≠ n))) ∧
  (∀ (s : BitSet) (n : Int), WF s →
    WF (deleteInteger s n) ∧
    (∀ x, member (deleteInteger s n) x = (member s x && decide (x ≠ n))) ∧
    popKey s n = if member s n then .ok (n, deleteInteger s n) else .error (.keyError n)) ∧
  (∀ {α : Type} (s : BitSet) (n : Int) (default : α),
    popDefault s n default =
      if member s n then (.inl n, deleteInteger s n) else (.inr default, s))

/-- Emptying resets the sentinel; zero-checking and emptiness agree with chunk contents. -/
def BitSetEmptySpec : Prop :=
  (∀ (b : List U64) (lo hi : Int),
    check0 b lo hi = true ↔ ∀ i ∈ intRange lo hi, bitsGet b i.toNat = zero64) ∧
  ∀ (s : BitSet), WF s →
    emptyBang s = new ∧ (∀ n, member (emptyBang s) n = false) ∧
    (isempty s = true ↔ ∀ n, member s n = false)

/-- The growth helpers retain existing chunks and initialize each new chunk to zero. -/
def BitSetGrowSpec : Prop :=
  ∀ (b : List U64) (n : Nat) (i : Nat),
    (1 ≤ i ∧ i ≤ b.length → bitsGet (growend0 b n) i = bitsGet b i) ∧
    (b.length < i ∧ i ≤ b.length + n → bitsGet (growend0 b n) i = zero64) ∧
    (1 ≤ i ∧ i ≤ b.length → bitsGet (growbeg0 b n) (n + i) = bitsGet b i) ∧
    (1 ≤ i ∧ i ≤ n → bitsGet (growbeg0 b n) i = zero64)

/-- Union with an integer unit range adds each value between its endpoints. -/
def BitSetUnionRangeSpec : Prop :=
  (∀ {R T : Type} [JuliaLean.base.range.JIsempty R]
      [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
      [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R),
    JuliaLean.base.range.JIsempty.isempty r = .ok true →
      unionRange s r = .ok s) ∧
  (∀ {R T : Type} [JuliaLean.base.range.JIsempty R]
      [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
      [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R) (err : JuliaLean.base.range.Exc),
    JuliaLean.base.range.JIsempty.isempty r = .error err →
      unionRange s r = .error (.range err)) ∧
(∀ {R T : Type} [JuliaLean.base.range.JIsempty R]
    [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
    [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R)
    (firstValue lastValue : T) (err : JuliaLean.base.range.Exc),
  JuliaLean.base.range.JIsempty.isempty r = .ok false →
  JuliaLean.base.range.JFirst.first r = .ok firstValue →
  JuliaLean.base.range.JLast.last r = .ok lastValue →
  JuliaLean.base.range.JCtor.ctor (T := I64) firstValue = .error err →
  unionRange s r = .error (.range err)) ∧
(∀ {R T : Type} [JuliaLean.base.range.JIsempty R]
    [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
    [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R)
    (firstValue lastValue : T) (a : I64) (err : JuliaLean.base.range.Exc),
  JuliaLean.base.range.JIsempty.isempty r = .ok false →
  JuliaLean.base.range.JFirst.first r = .ok firstValue →
  JuliaLean.base.range.JLast.last r = .ok lastValue →
  JuliaLean.base.range.JCtor.ctor (T := I64) firstValue = .ok a →
  JuliaLean.base.range.JCtor.ctor (T := I64) lastValue = .error err →
  unionRange s r = .error (.range err)) ∧
  (∀ (s : BitSet) (a b n : I64), WF s → a.val ≤ b.val →
    member (unionRangeBits s a b) n.val =
      (member s n.val || decide (a.val ≤ n.val ∧ n.val ≤ b.val))) ∧
  ∀ {R T : Type} [JuliaLean.base.range.JIsempty R]
      [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
      [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R)
      (firstValue lastValue : T) (a b n : I64) (out : BitSet),
    WF s →
    JuliaLean.base.range.JIsempty.isempty r = .ok false →
    JuliaLean.base.range.JFirst.first r = .ok firstValue →
    JuliaLean.base.range.JLast.last r = .ok lastValue →
    JuliaLean.base.range.JCtor.ctor (T := I64) firstValue = .ok a →
    JuliaLean.base.range.JCtor.ctor (T := I64) lastValue = .ok b →
    a.val ≤ b.val →
    unionRange s r = .ok out →
    member out n.val = (member s n.val || decide (a.val ≤ n.val ∧ n.val ≤ b.val))
/-- Matched chunk mapping and its public set operations implement their elementwise Boolean operation. -/
def BitSetMatchedSpec : Prop :=
  ∀ (s1 s2 : BitSet) (n : I64), WF s1 → WF s2 →
    inInt n (unionBang s1 s2) = (inInt n s1 || inInt n s2) ∧
    inInt n (intersectBang s1 s2) = (inInt n s1 && inInt n s2) ∧
    inInt n (setdiffBang s1 s2) = (inInt n s1 && !inInt n s2) ∧
    inInt n (symdiffBitSet s1 s2) = (inInt n s1 ^^ inInt n s2) ∧
    inInt n (intersect s1 s2) = (inInt n s1 && inInt n s2)

/-- `union` preserves the first set and adds members supplied by each argument. -/
def BitSetUnionSpec : Prop :=
  ∀ (s : BitSet) (sets : List UnionArg) (n : I64), WF s →
    (∀ arg ∈ sets, unionArgValid arg) →
    ∀ out, union s sets = .ok out →
      member out n.val = (member s n.val || sets.any (fun arg => unionArgMember arg n.val))

/-- Symmetric difference with an AbstractSet toggles each distinct member once. -/
def BitSetSymdiffSetSpec : Prop :=
  ∀ (s : BitSet) (ns : List Int) (n : I64), WF s → ns.Nodup →
    (∀ x ∈ ns, inIntRange x) →
    ∀ out, symdiffSet s ns = .ok out →
      member out n.val = (member s n.val ^^ decide (n.val ∈ ns))

/-- In-place filtering retains exactly values accepted by its predicate. -/
def BitSetFilterSpec : Prop :=
  ∀ (f : I64 → Bool) (s : BitSet) (n : I64), WF s →
    inInt n (filter f s) = (inInt n s && f n)

/-- Search returns the nearest set bit on the requested side, or `-1`. -/
def BitSetFindSpec : Prop :=
  (∀ (b : List U64) (start : Int), start ≥ 0 →
    bitsFindnext b start =
      match (List.range (b.length * 64) : List Nat).find? (fun (p : Nat) =>
        decide (start ≤ (p : Int)) &&
          ((bitsGet b (p / 64 + 1)).val.toNat.testBit (p % 64))) with
      | some p => p
      | none => -1) ∧
  (∀ (b : List U64) (start : Int),
    bitsFindprev b start =
      match ((List.range (b.length * 64) : List Nat).reverse.find? (fun (p : Nat) =>
        decide ((p : Int) ≤ start) &&
          ((bitsGet b (p / 64 + 1)).val.toNat.testBit (p % 64)))) with
      | some p => p
      | none => -1)
 

def BitSetIterSpec : Prop :=
  ∀ (s : BitSet), WF s →
    let xs := iterated s
    (s.offset ≠ noOffset → 0 < s.bits.length → (intoffset s).val = 64 * s.offset) ∧
    (∀ n, (xs.any (fun x => x.val = n)) = (member s n)) ∧
    xs.Pairwise (fun a b => a.val < b.val) ∧
    (length s).val = xs.length ∧
    first s = (match xs.head? with
      | some x => .ok x
      | none => .error (.julia (.argumentError "collection must be non-empty"))) ∧
    last s = (match xs.getLast? with
      | some x => .ok x
      | none => .error (.julia (.argumentError "collection must be non-empty"))) ∧
    minimum s = first s ∧ maximum s = last s ∧
    extrema s = (match xs.head?, xs.getLast? with
      | some lo, some hi => .ok (lo, hi)
      | _, _ => .error (.julia (.argumentError "collection must be non-empty"))) ∧
    issorted s = true ∧
    showStr s = "BitSet([" ++ joinComma (xs.map (fun n => toString n.val)) ++ "])" ∧
    popLast s = (match xs.getLast? with
      | some x => .ok (x.val, deleteInteger s x.val)
      | none => .error (.julia (.argumentError "collection must be non-empty"))) ∧
    popfirst s = (match xs.head? with
      | some x => .ok (x.val, deleteInteger s x.val)
      | none => .error (.julia (.argumentError "collection must be non-empty")))

/-- Equality of chunks agrees exactly with equality of integer members. -/
def BitSetEqSpec : Prop :=
  ∀ (s1 s2 : BitSet), WF s1 → WF s2 →
    (eq s1 s2 = true ↔ ∀ n, member s1 n = member s2 n)

/-- Subset and strict subset agree with member inclusion and proper set inclusion. -/
def BitSetSubsetSpec : Prop :=
  (∀ x y : U64, subChunk x y = true ↔
    ∀ j, x.val.toNat.testBit j = true → y.val.toNat.testBit j = true) ∧
  ∀ (a b : BitSet), WF a → WF b →
    (issubset a b = true ↔ ∀ n, member a n = true → member b n = true) ∧
    (strictSubset a b = true ↔
      (∀ n, member a n = true → member b n = true) ∧ ∃ n, member a n ≠ member b n)

def entries : List Entry := [
  { id := "bitarrays-bitset-push-delete", juliaFile := "base/bitset.jl",
    juliaFns := ["push!(::BitSet, ::Integer)", "delete!(::BitSet, ::Integer)", "in(::Int, ::BitSet)", "_setint!"],
    statement := "After any sequence of push! and delete! on a BitSet, n in s agrees with Set{Int} for every Int n, including negative values and typemin/typemax.",
    source := "BitSet docstring (base/bitset.jl:25-32): a set of Ints; invariant: BitSet behaves as Set{Int}",
    status := .todo, prop := ``BitSetPushDeleteAgrees, thm := none },
  { id := "bitarrays-bitset-symdiff-duplicates", juliaFile := "base/bitset.jl",
    juliaFns := ["symdiff!(::BitSet, itr)", "int_symdiff!", "symdiff(::BitSet, itr)"],
    statement := "symdiff!(s::BitSet, itr) agrees with symdiff!(Set{Int}(s), itr): the result holds exactly the elements in exactly one of s and itr.",
    source := "symdiff! docstring (base/abstractset.jl:282-289) and symdiff!(::AbstractSet, itr) = symdiff!(s, Set(itr)) (base/abstractset.jl:297, #46397)",
    status := .todo, prop := ``BitSetSymdiffAgrees, thm := none,
    issue := "none found (related: #34686 and #44591 on symdiff multiplicity, fixed for AbstractSet/Vector by #46397, which left the BitSet method toggling; queries: symdiff, BitSet, symdiff multiplicity, symdiff! BitSet duplicates; PRs: symdiff, BitSet symdiff)" },
  { id := "memsafety-bitset-indexing", juliaFile := "base/bitset.jl",
    juliaFns := ["_bits_getindex", "_growend0!", "_growbeg0!", "union!", "_matched_map!", "iterate", "_check0", "==(::BitSet, ::BitSet)", "issubset"],
    statement := "Every chunk index and unsafe copy span computed by BitSet lookup, growth, range union, matched mapping, reachable iteration, equality, emptiness, and subset operations is within the vector length in force at that statement.",
    source := "BitSet representation and iteration invariants; base/bitset.jl:5-10,63-68,87-165,169-253,291-337,368-418",
    status := .todo, prop := ``BitSetAccessesInBounds, thm := none },
  { id := "bitsetscov-bitset-build", juliaFile := "base/bitset.jl",
    juliaFns := ["BitSet()", "BitSet(itr)", "union!(::BitSet, itr)", "empty(::BitSet)", "emptymutable(::BitSet)", "push!(::BitSet, ::Integer...)"],
    statement := "BitSet construction is empty, and iterable construction, union!, and variadic push! add exactly the convertible Int elements.",
    source := "BitSet docstring, base/bitset.jl:25-41; AbstractSet invariant",
    status := .todo, prop := ``BitSetBuildSpec, thm := none },
  { id := "bitsetscov-bitset-copy", juliaFile := "base/bitset.jl",
    juliaFns := ["copy!(::BitSet, ::BitSet)", "copy(::BitSet)", "copymutable(::BitSet)"],
    statement := "The three BitSet copy methods preserve every stored chunk and the offset.",
    source := "copy invariant; base/bitset.jl:48-56",
    status := .todo, prop := ``BitSetCopySpec, thm := none },
  { id := "bitsetscov-bitset-sizehint", juliaFile := "base/bitset.jl",
    juliaFns := ["sizehint!(::BitSet, ::Integer)"],
    statement := "sizehint! changes capacity only and either preserves the BitSet or reports an Int conversion failure for a 128-bit chunk count.",
    source := "sizehint! invariant; base/bitset.jl:58-61",
    status := .todo, prop := ``BitSetSizehintSpec, thm := none },
  { id := "bitsetscov-bitset-in", juliaFile := "base/bitset.jl",
    juliaFns := ["_bits_getindex", "_is_convertible_Int", "in(::Integer, ::BitSet)"],
    statement := "BitSet membership reads the selected chunk and rejects Integer values outside Int without changing the answer.",
    source := "BitSet set invariant; base/bitset.jl:63-68,279,331",
    status := .todo, prop := ``BitSetInSpec, thm := none },
  { id := "bitsetscov-bitset-delete-pop", juliaFile := "base/bitset.jl",
    juliaFns := ["delete!(::BitSet, ::Int)", "delete!(::BitSet, ::Integer)", "pop!(::BitSet, ::Integer)", "pop!(::BitSet, ::Integer, default)"],
    statement := "delete! removes exactly its key; keyed pop! removes and returns a present key, throws without a default, and returns the default when absent.",
    source := "AbstractSet delete!/pop! contract; base/bitset.jl:261-281",
    status := .todo, prop := ``BitSetDeleteSpec, thm := none },
  { id := "bitsetscov-bitset-empty", juliaFile := "base/bitset.jl",
    juliaFns := ["empty!(::BitSet)", "isempty(::BitSet)", "_check0"],
    statement := "empty! removes all members and resets the offset; isempty and _check0 hold exactly when the relevant chunks are zero.",
    source := "empty!/isempty contract; base/bitset.jl:285-291,368-373",
    status := .todo, prop := ``BitSetEmptySpec, thm := none },
  { id := "bitsetscov-bitset-grow", juliaFile := "base/bitset.jl",
    juliaFns := ["_growend0!", "_growbeg0!"],
    statement := "The two growth helpers preserve existing chunks and initialize every new chunk to zero.",
    source := "representation invariant; base/bitset.jl:116-129",
    status := .todo, prop := ``BitSetGrowSpec, thm := none },
  { id := "bitsetscov-bitset-union-range", juliaFile := "base/bitset.jl",
    juliaFns := ["union!(::BitSet, ::AbstractUnitRange{<:Integer})"],
    statement := "Range union adds exactly every Int in a nonempty range, leaves empty ranges unchanged, and checks conversion of both bounds.",
    source := "union contract; base/bitset.jl:131-167",
    status := .todo, prop := ``BitSetUnionRangeSpec, thm := none },
  { id := "bitsetscov-bitset-matched-map", juliaFile := "base/bitset.jl",
    juliaFns := ["_matched_map!(f, ::BitSet, ::BitSet)", "_matched_map!(f, ::Bits, ...)", "union!(::BitSet, ::BitSet)", "intersect(::BitSet, ::BitSet)", "intersect!(::BitSet, ::BitSet)", "setdiff!(::BitSet, ::BitSet)", "symdiff!(::BitSet, ::BitSet)"],
    statement := "The matched chunk loop implements memberwise union, intersection, difference, and symmetric difference and preserves the BitSet invariant.",
    source := "set-operation contracts; base/bitset.jl:169-253,296-326",
    status := .todo, prop := ``BitSetMatchedSpec, thm := none },
  { id := "bitsetscov-bitset-union", juliaFile := "base/bitset.jl",
    juliaFns := ["union(::BitSet, sets...)"],
    statement := "union copies the first BitSet and adds exactly the members of every following argument.",
    source := "union contract; base/bitset.jl:295",
    status := .todo, prop := ``BitSetUnionSpec, thm := none },
  { id := "bitsetscov-bitset-symdiff-set", juliaFile := "base/bitset.jl",
    juliaFns := ["symdiff!(::BitSet, ::AbstractSet)"],
    statement := "Symmetric difference with an AbstractSet toggles each distinct convertible Int member exactly once.",
    source := "symdiff! docstring; base/bitset.jl:312-317",
    status := .todo, prop := ``BitSetSymdiffSetSpec, thm := none },
  { id := "bitsetscov-bitset-filter-invariant", juliaFile := "base/bitset.jl",
    juliaFns := ["filter!(f, ::BitSet)"],
    statement := "The in-place filter loop preserves the BitSet representation invariant while deleting from the set it iterates.",
    source := "representation invariant; base/bitset.jl:328 and base/abstractset.jl:633-641",
    status := .todo, prop := ``BitSetFilterSpec, thm := none },
  { id := "bitsetscov-bitset-find", juliaFile := "base/bitset.jl",
    juliaFns := ["_bits_findnext", "_bits_findprev"],
    statement := "The BitSet search helpers return the first set position at or after the start and the last at or before it, or -1.",
    source := "search invariant; base/bitset.jl:70-84",
    status := .todo, prop := ``BitSetFindSpec, thm := none },
  { id := "bitsetscov-bitset-iteration", juliaFile := "base/bitset.jl",
    juliaFns := ["intoffset", "iterate(::BitSet)", "_throw_bitset_notempty_error", "first(::BitSet)", "last(::BitSet)", "length(::BitSet)", "show(::IO, ::BitSet)", "pop!(::BitSet)", "popfirst!(::BitSet)", "minimum(::BitSet)", "maximum(::BitSet)", "extrema(::BitSet)", "issorted(::BitSet)"],
    statement := "BitSet iteration lists every member in increasing order; its extrema, length, pop methods, and printed form agree with that sequence.",
    source := "BitSet sorted-set docstring and iteration invariant; base/bitset.jl:43,259,283,333-366,423-426",
    status := .todo, prop := ``BitSetIterSpec, thm := none },
  { id := "bitsetscov-bitset-equality", juliaFile := "base/bitset.jl",
    juliaFns := ["==(::BitSet, ::BitSet)"],
    statement := "Two BitSets compare equal exactly when they have the same integer members.",
    source := "AbstractSet equality invariant; base/bitset.jl:375-407",
    status := .todo, prop := ``BitSetEqSpec, thm := none },
  { id := "bitsetscov-bitset-subset", juliaFile := "base/bitset.jl",
    juliaFns := ["f(a,b)", "issubset(::BitSet, ::BitSet)", "⊊(::BitSet, ::BitSet)"],
    statement := "The chunk predicate and BitSet subset methods implement member inclusion, with ⊊ requiring a strict difference.",
    source := "subset contracts; base/bitset.jl:409-420",
    status := .todo, prop := ``BitSetSubsetSpec, thm := none }
]

end JuliaLean.Proofs.base.bitset

/-! Method -> property table:
BitSet() -> bitsetscov-bitset-build
BitSet(itr) -> bitsetscov-bitset-build
union!(::BitSet, itr) -> bitsetscov-bitset-build
intoffset -> bitsetscov-bitset-iteration
empty(::BitSet), emptymutable(::BitSet) -> bitsetscov-bitset-build
copy(::BitSet), copymutable(::BitSet), copy!(::BitSet, ::BitSet) -> bitsetscov-bitset-copy
sizehint!(::BitSet, ::Integer) -> bitsetscov-bitset-sizehint
_bits_getindex, _is_convertible_Int, in(::Int, ::BitSet), in(::Integer, ::BitSet) -> bitsetscov-bitset-in
_bits_findnext, _bits_findprev -> bitsetscov-bitset-find
_setint!, push!(::BitSet, ::Integer), push!(::BitSet, ::Integer...) -> bitarrays-bitset-push-delete
_growend0!, _growbeg0! -> bitsetscov-bitset-grow
union!(::BitSet, ::AbstractUnitRange{<:Integer}) -> bitsetscov-bitset-union-range
_matched_map!(f, ::BitSet, ::BitSet), _matched_map!(f, ::Bits, ...), union!(::BitSet, ::BitSet), intersect(::BitSet, ::BitSet), intersect!(::BitSet, ::BitSet), setdiff!(::BitSet, ::BitSet), symdiff!(::BitSet, ::BitSet) -> bitsetscov-bitset-matched-map
pop!(::BitSet), pop!(::BitSet, ::Integer), pop!(::BitSet, ::Integer, default), popfirst!(::BitSet), delete!(::BitSet, ::Int), delete!(::BitSet, ::Integer) -> bitsetscov-bitset-delete-pop
_is_convertible_Int, _bits_getindex -> bitsetscov-bitset-in
empty!(::BitSet), isempty(::BitSet), _check0 -> bitsetscov-bitset-empty
union(::BitSet, sets...) -> bitsetscov-bitset-union
symdiff!(::BitSet, itr), int_symdiff! -> bitarrays-bitset-symdiff-duplicates
symdiff!(::BitSet, ::AbstractSet) -> bitsetscov-bitset-symdiff-set
symdiff!(::BitSet, ::BitSet) -> bitsetscov-bitset-matched-map
filter!(f, ::BitSet) -> bitsetscov-bitset-filter-invariant
iterate(::BitSet), _throw_bitset_notempty_error, first(::BitSet), last(::BitSet), length(::BitSet), show(::IO, ::BitSet), minimum(::BitSet), maximum(::BitSet), extrema(::BitSet), issorted(::BitSet) -> bitsetscov-bitset-iteration
==(::BitSet, ::BitSet) -> bitsetscov-bitset-equality
f(a,b), issubset(::BitSet, ::BitSet), ⊊(::BitSet, ::BitSet) -> bitsetscov-bitset-subset
-/
