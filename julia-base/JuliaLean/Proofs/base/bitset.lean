import JuliaLean.Proofs.base.bitset.BitSetFilterProof
import JuliaLean.Proofs.base.bitset.Refutations
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

/-- Constructors and iterable insertion make membership exactly the union of inserted
Int values, preserving the representation invariant of every valid input BitSet.
Julia source: base/bitset.jl:5-23,25-46,255-257. -/
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
  (∀ (s : BitSet) (xs : List Int), WF s → (∀ n ∈ xs, inIntRange n) →
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
 


/-- Equality of chunks agrees exactly with equality of integer members. -/
def BitSetEqSpec : Prop :=
  ∀ (s1 s2 : BitSet), WF s1 → WF s2 →
    (eq s1 s2 = true ↔ ∀ n, member s1 n = member s2 n)


namespace Round1

open JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset

/-- Push and delete sequences update membership by their successfully converted Int keys.
Source: `base/bitset.jl:255,279-281,330-331`; the initial representation invariant is
`base/bitset.jl:5-10`. -/
def applyPushDeleteIntegerOps (s : BitSet) : List (Bool × Int) → Result BitSet
  | [] => .ok s
  | (true, n) :: rest => do
      let next ← JuliaLean.base.bitset.push s n
      applyPushDeleteIntegerOps next rest
  | (false, n) :: rest =>
      applyPushDeleteIntegerOps (JuliaLean.base.bitset.deleteInteger s n) rest

def idealPushDeleteMember (s : BitSet) (ops : List (Bool × Int)) (n : Int) : Bool :=
  ops.foldl (fun present op =>
    if JuliaLean.base.bitset.isConvertibleInt op.2 && (n = op.2) then op.1 else present)
    (member s n)


/-- Integer membership agrees with the values yielded by complete BitSet iteration.
Source: `base/bitset.jl:279-281,330-340`; BitSet is a sorted set of Ints at `base/bitset.jl:25-32`. -/
def BitSetMembershipMatchesIteration : Prop :=
  ∀ (s : BitSet) (n : Int), WF s →
    member s n = (iterated s).any (fun value => value.val = n)

/-- Delete removes exactly a present Int key; keyed pop returns it, while a missing-key pop
returns an error without claiming an undocumented error type. The default form returns the
supplied value when absent. Source: `base/bitset.jl:261-281`. -/
def BitSetDeleteContract : Prop :=
  (∀ (s : BitSet) (n : Int), WF s →
    WF (JuliaLean.base.bitset.deleteInteger s n) ∧
    ∀ x, member (JuliaLean.base.bitset.deleteInteger s n) x =
      (member s x && decide (x ≠ n))) ∧
  (∀ (s : BitSet) (n : Int), WF s →
    (member s n = true →
      JuliaLean.base.bitset.popKey s n = .ok (n, JuliaLean.base.bitset.deleteInteger s n)) ∧
    (member s n = false →
      ∃ error : JuliaLean.base.bitset.Error,
        JuliaLean.base.bitset.popKey s n = .error error)) ∧
  ∀ {α : Type} (s : BitSet) (n : Int) (default : α),
    JuliaLean.base.bitset.popDefault s n default =
      if member s n then (.inl n, JuliaLean.base.bitset.deleteInteger s n) else (.inr default, s)

/-- In-place filtering preserves the BitSet invariant and keeps exactly members accepted by the
predicate. Source: `base/bitset.jl:328`; `base/abstractset.jl:632-641`. -/
def BitSetFilterPreserves : Prop :=
  ∀ (f : I64 → Bool) (s : BitSet), WF s →
    WF (JuliaLean.base.bitset.filter f s) ∧
    ∀ n, inInt n (JuliaLean.base.bitset.filter f s) =
      (inInt n s && f n)


end Round1
namespace Round2

set_option linter.unusedVariables false

/-- The public empty! and isempty operations reset a well-formed BitSet and report empty
membership without exposing the private chunk-scanning helper. Source: `base/bitset.jl:285-291`;
BitSet representation invariant: `base/bitset.jl:5-10`. -/
def BitSetEmptyPublicSpec : Prop :=
  ∀ (s : BitSet), WF s →
    emptyBang s = new ∧
    (∀ n, member (emptyBang s) n = false) ∧
    (isempty s = true ↔ ∀ n, member s n = false)

/-- Public BitSet subset and strict-subset operations agree with integer-member inclusion and
proper set inclusion. This omits the private chunk and local helper predicates. Source:
`base/bitset.jl:409-420`; BitSet representation invariant: `base/bitset.jl:5-10`. -/
def BitSetSubsetPublicSpec : Prop :=
  ∀ (a b : BitSet), WF a → WF b →
    (issubset a b = true ↔ ∀ n, member a n = true → member b n = true) ∧
    (strictSubset a b = true ↔
      (∀ n, member a n = true → member b n = true) ∧
      ∃ n, member a n ≠ member b n)

end Round2
namespace Round3

open JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset
open JuliaLean.Proofs.base.bitset.Round1

/-- The initial chunk vector and the complete span touched by successful pushes fit within fewer
than 2^57 UInt64 chunks. Deletes do not grow the vector. -/
def PushDeleteChunkSpanFits (s : BitSet) (ops : List (Bool × Int)) : Prop :=
  s.bits.length < 2 ^ 57 ∧
    let origin : Int := if s.offset = noOffset then 0 else s.offset
    let margin : Int := (2 ^ 57 - (s.bits.length : Int) - 1) / 2
    ∀ op ∈ ops, op.1 = true →
      origin - margin ≤ div64 op.2 ∧ div64 op.2 ≤ origin + margin

/-- Push and delete sequences update membership by their successfully converted Int keys.
Source: `base/bitset.jl:255,279-281,330-331`; the initial representation invariant is
`base/bitset.jl:5-10`. The initial vector and successful-push chunk span are bounded to a
Julia-representable size. -/
def BitSetPushDeleteAgrees : Prop :=
  ∀ (s : BitSet) (ops : List (Bool × Int)) (n : Int) (out : BitSet),
    WF s → PushDeleteChunkSpanFits s ops →
    applyPushDeleteIntegerOps s ops = .ok out →
      member out n = idealPushDeleteMember s ops n


/-- The initial BitSet vectors and the combined occupied chunk span fit within fewer than
2^57 UInt64 chunks. Empty inputs add no span. -/
def MatchedChunkSpanFits (s1 s2 : BitSet) : Prop :=
  s1.bits.length < 2 ^ 57 ∧
  s2.bits.length < 2 ^ 57 ∧
  (s1.bits = [] ∨ s2.bits = [] ∨
    max (s1.offset + s1.bits.length) (s2.offset + s2.bits.length) -
      min s1.offset s2.offset < 2 ^ 57)

/-- Matched chunk mapping and its public set operations preserve the representation and implement
their elementwise Boolean operation. Source: `base/bitset.jl:295-326`. The input and output chunk
span is bounded to a Julia-representable size. -/
def BitSetMatchedPreserves : Prop :=
  ∀ (s1 s2 : BitSet) (n : I64), WF s1 → WF s2 →
    MatchedChunkSpanFits s1 s2 →
    WF (unionBang s1 s2) ∧
    WF (intersectBang s1 s2) ∧
    WF (setdiffBang s1 s2) ∧
    WF (symdiffBitSet s1 s2) ∧
    WF (intersect s1 s2) ∧
    inInt n (unionBang s1 s2) = (inInt n s1 || inInt n s2) ∧
    inInt n (intersectBang s1 s2) = (inInt n s1 && inInt n s2) ∧
    inInt n (setdiffBang s1 s2) = (inInt n s1 && !inInt n s2) ∧
    inInt n (symdiffBitSet s1 s2) = (inInt n s1 ^^ inInt n s2) ∧
    inInt n (intersect s1 s2) = (inInt n s1 && inInt n s2)

/-- Iteration yields every member in increasing order, and length, extrema, pop methods, and
printed output agree with that sequence. Fewer than 2^56 stored UInt64 chunks ensure even a full
vector has fewer than 2^62 members. Source: `base/bitset.jl:43,259,283,333-366,423-426`. -/
def BitSetIterSpec : Prop :=
  ∀ (s : BitSet), WF s → s.bits.length < 2 ^ 56 →
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

end Round3






namespace JuliaLean.ChatGPT.Batch3.Group3

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset
set_option maxRecDepth 4096

/-- The installed integer range includes exactly its two inclusive bounds. -/
theorem bs_intRange_mem (lo hi x : Int) :
    x ∈ intRange lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    change lo ≤ lo + (k : Int) ∧ lo + (k : Int) ≤ hi
    omega
  · intro h
    refine ⟨(x - lo).toNat, ?_, ?_⟩
    · omega
    · change lo + ((x - lo).toNat : Int) = x
      omega

/-- A zero scan is precisely a universal assertion over its requested chunk interval. -/
theorem bs_check0_iff (words : List U64) (lo hi : Int) :
    check0 words lo hi = true ↔
      ∀ i : Int, lo ≤ i → i ≤ hi → bitsGet words i.toNat = zero64 := by
  simp only [check0, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h i hlo hhi
    exact h i ((bs_intRange_mem lo hi i).mpr ⟨hlo, hhi⟩)
  · intro h i hi
    obtain ⟨hlo, hhi⟩ := (bs_intRange_mem lo _ i).mp hi
    exact h i hlo hhi

/-- The overlap comparison checks exactly the specified number of aligned chunks. -/
theorem bs_memeq_iff (left right : List U64) (start count : Int) :
    memeq left start right count = true ↔
      ∀ k : Nat, k < count.toNat →
        bitsGet left (start + k).toNat = bitsGet right (k + 1) := by
  simp only [memeq, List.all_eq_true, List.mem_range, beq_iff_eq]

/-- Updating one chunk never changes the chunk-vector length. -/
theorem bs_setBit_length (words : List U64) (value : Bool) (chunk bit : Nat) :
    (setBit words value chunk bit).length = words.length := by
  simp only [setBit, bitsSet, List.length_set]

/-- Deletion preserves the storage span and offset, including absent-key deletion. -/
theorem bs_deleteInt_shape (s : BitSet) (n : I64) :
    (deleteInt s n).offset = s.offset ∧ (deleteInt s n).bits.length = s.bits.length := by
  unfold deleteInt setint
  simp only [Bool.not_false, ite_true]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, bs_setBit_length s.bits false _ _⟩

/-- The frozen representation invariant is stable under every machine-integer deletion. -/
theorem bs_deleteInt_WF (s : BitSet) (n : I64) (h : WF s) : WF (deleteInt s n) := by
  obtain ⟨hoff, hlen⟩ := bs_deleteInt_shape s n
  constructor
  · intro hs
    apply List.length_eq_zero_iff.mp
    rw [hlen, h.1 (hoff ▸ hs)]
    rfl
  · intro hs
    have hold : s.offset ≠ noOffset := by simpa only [hoff] using hs
    simpa only [hoff, hlen] using h.2 hold

/-- Conversion dispatch preserves the invariant for arbitrary integer deletion. -/
theorem bs_deleteInteger_WF (s : BitSet) (n : Int) (h : WF s) :
    WF (deleteInteger s n) := by
  unfold deleteInteger
  split
  · exact bs_deleteInt_WF s _ h
  · exact h

/-- Keyed pop implements both documented present and missing branches. -/
theorem bs_popKey_branches (s : BitSet) (n : Int) :
    (member s n = true → popKey s n = .ok (n, deleteInteger s n)) ∧
    (member s n = false → ∃ error : Error, popKey s n = .error error) := by
  constructor
  · intro h
    simp only [popKey, show inInteger n s = true from h, ite_true]
  · intro h
    refine ⟨.keyError n, ?_⟩
    simp only [popKey, show inInteger n s = false from h, Bool.false_eq_true, ite_false]

/-- Default-valued pop exposes the exact original set on its missing branch. -/
theorem bs_popDefault_eq {α : Type} (s : BitSet) (n : Int) (default : α) :
    popDefault s n default =
      if member s n then (.inl n, deleteInteger s n) else (.inr default, s) := by
  rfl

/-- Every prefix of the filtering loop preserves the representation invariant. -/
theorem bs_filterLoop_WF (f : I64 → Bool) (fuel : Nat) (s : BitSet)
    (state : U64 × Nat) (h : WF s) : WF (filterLoop f fuel s state) := by
  induction fuel generalizing s state with
  | zero => exact h
  | succ fuel ih =>
    simp only [filterLoop]
    split
    · exact h
    · apply ih
      split
      · exact bs_deleteInt_WF s _ h
      · exact h

/-- Filtering preserves the full frozen representation invariant. -/
theorem bs_filter_WF (f : I64 → Bool) (s : BitSet) (h : WF s) :
    WF (filter f s) := bs_filterLoop_WF f _ s _ h

/-- Empty storage has no machine-integer members at any offset. -/
theorem bs_inInt_nil (offset : Int) (n : I64) : inInt n ⟨[], offset⟩ = false := by
  simp only [inInt, bitsGetindex, List.length_nil, Int.ofNat_zero]
  have h : ¬ (1 ≤ div64 n.val - offset + 1 ∧ div64 n.val - offset + 1 ≤ 0) := by omega
  simp only [h, ite_false]

/-- The public reset has empty membership for every mathematical integer. -/
theorem bs_emptyBang_members (s : BitSet) (n : Int) : member (emptyBang s) n = false := by
  unfold member inInteger emptyBang new
  split
  · exact bs_inInt_nil _ _
  · rfl

/-- Exact conversion leaves any in-range signed value unchanged. -/
theorem bs_int64_val (n : Int) (h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) :
    (int64 n).val = n := wrapInt_of_inRange .i64 n h

/-- Signed bitvector decoding lies inside the machine-integer range. -/
theorem bs_toI64_val (word : BitVec IntTy.i64.bits) : (toJInt .i64 word).val = word.toInt := by
  change wrapInt .i64 word.toInt = word.toInt
  apply wrapInt_of_inRange
  exact ⟨BitVec.le_toInt word, BitVec.toInt_le⟩

/-- The bit pattern of a signed model value decodes back to that value. -/
theorem bs_fromI64_int (value : I64) : (fromJInt value).toInt = value.val := by
  have h := value.property
  change -9223372036854775808 ≤ value.val ∧ value.val ≤ 9223372036854775807 at h
  change (BitVec.ofInt 64 value.val).toInt = value.val
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- Unsigned encoding exposes the natural value of the finite bitvector. -/
theorem bs_toU64_val (word : BitVec IntTy.u64.bits) :
    (toJInt .u64 word).val = (word.toNat : Int) := by
  change wrapInt .u64 (word.toNat : Int) = (word.toNat : Int)
  apply wrapInt_of_inRange
  have h := word.isLt
  change word.toNat < 18446744073709551616 at h
  change 0 ≤ (word.toNat : Int) ∧ (word.toNat : Int) ≤ 18446744073709551615
  omega

/-- Unsigned decoding is exact because model values already lie in the word range. -/
theorem bs_fromU64_nat (word : U64) : (fromJInt word).toNat = word.val.toNat := by
  rw [fromJInt, BitVec.toNat_ofInt]
  change (word.val % 18446744073709551616).toNat = word.val.toNat
  have h := word.property
  change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at h
  rw [Int.emod_eq_of_lt h.1 (by omega)]

/-- Every unsigned finite bitvector survives encoding and decoding unchanged. -/
theorem bs_roundtrip_U64 (word : BitVec IntTy.u64.bits) : fromJInt (toJInt .u64 word) = word := by
  apply BitVec.eq_of_toNat_eq
  rw [bs_fromU64_nat, bs_toU64_val, Int.toNat_natCast]

/-- Every signed finite bitvector survives encoding and decoding unchanged. -/
theorem bs_roundtrip_I64 (word : BitVec IntTy.i64.bits) : fromJInt (toJInt .i64 word) = word := by
  unfold fromJInt
  rw [bs_toI64_val, BitVec.ofInt_toInt]

/-- Equality of unsigned words follows from their 64 observable bits. -/
theorem bs_word_ext {a b : U64}
    (h : ∀ k, k < 64 → (fromJInt a).getLsbD k = (fromJInt b).getLsbD k) : a = b := by
  have he : fromJInt a = fromJInt b := BitVec.eq_of_getLsbD_eq_iff.mpr h
  have hn := congrArg BitVec.toNat he
  rw [bs_fromU64_nat, bs_fromU64_nat] at hn
  apply Subtype.ext
  have ha := a.property
  have hb := b.property
  change 0 ≤ a.val ∧ a.val ≤ 18446744073709551615 at ha
  change 0 ≤ b.val ∧ b.val ≤ 18446744073709551615 at hb
  omega

/-- Arithmetic shift by six is floored division by 64 on signed integers. -/
theorem bs_div64_eq (n : Int) (h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) :
    div64 n = n / 64 := by
  unfold div64 JuliaLean.base.bitarray.div64 ashr_int jlAshrInt
  change (toJInt .i64 (BitVec.ofInt IntTy.i64.bits ((fromJInt (int64 n)).toInt / 64))).val = n / 64
  rw [bs_toI64_val, bs_fromI64_int, bs_int64_val n h]
  change -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 at h
  change (BitVec.ofInt 64 (n / 64)).toInt = n / 64
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- The low six bits are the nonnegative remainder modulo 64. -/
theorem bs_mod64_eq (n : Int) (h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) :
    mod64 n = (n % 64).toNat := by
  have hnat : ((fromJInt (int64 n)) &&& (BitVec.ofNat IntTy.i64.bits 63)).toNat = (n % 64).toNat := by
    rw [BitVec.toNat_and]
    change (fromJInt (int64 n)).toNat &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, fromJInt, BitVec.toNat_ofInt, bs_int64_val n h]
    change (n % 18446744073709551616).toNat % 64 = (n % 64).toNat
    have hm : 0 ≤ n % 18446744073709551616 := Int.emod_nonneg _ (by decide)
    have h64 : 0 ≤ n % 64 := Int.emod_nonneg _ (by decide)
    have he : n % 18446744073709551616 % 64 = n % 64 :=
      Int.emod_emod_of_dvd _ (by decide)
    omega
  unfold mod64 JuliaLean.base.bitarray.mod64 and_int
  rw [bs_toI64_val]
  change (((fromJInt (int64 n)) &&& (BitVec.ofNat IntTy.i64.bits 63)).toInt).toNat = (n % 64).toNat
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [hnat]; change 2 * (n % 64).toNat < 18446744073709551616; have := Int.emod_lt_of_pos n (by decide : (0 : Int) < 64); omega),
    Int.toNat_natCast, hnat]

/-- The unsigned intrinsic conjunction is conjunction of observable bits. -/
theorem bs_and_bit (a b : U64) (k : Nat) :
    (fromJInt (and_int a b)).getLsbD k =
      ((fromJInt a).getLsbD k && (fromJInt b).getLsbD k) := by
  simp only [and_int, jlAndInt, bs_roundtrip_U64, BitVec.getLsbD_and]

/-- The unsigned intrinsic complement flips every bit inside the stored word. -/
theorem bs_not_bit (a : U64) (k : Nat) (hk : k < 64) :
    (fromJInt (not_int a)).getLsbD k = !(fromJInt a).getLsbD k := by
  unfold not_int
  rw [bs_roundtrip_U64]
  unfold jlNotInt
  rw [BitVec.getLsbD_not]
  change (decide (k < 64) && !(fromJInt a).getLsbD k) = !(fromJInt a).getLsbD k
  simp only [hk, decide_true, Bool.true_and]

/-- A one-bit shift mask marks exactly its requested position. -/
theorem bs_mask_bit (bit k : Nat) (hb : bit < 64) :
    (fromJInt (shl_int (uint64 1) (int64 (bit : Int)))).getLsbD k =
      decide (k = bit) := by
  have hi : (fromJInt (int64 (bit : Int))).toNat = bit := by
    rw [fromJInt, BitVec.toNat_ofInt, bs_int64_val _ (by
      change -9223372036854775808 ≤ (bit : Int) ∧ (bit : Int) ≤ 9223372036854775807
      omega)]
    change ((bit : Int) % 18446744073709551616).toNat = bit
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  unfold shl_int
  rw [bs_roundtrip_U64]
  unfold jlShlInt
  rw [hi, if_neg (show ¬ bit ≥ IntTy.u64.bits by exact Nat.not_le.mpr hb)]
  rw [BitVec.getLsbD_ofNat]
  change (decide (k < 64) && (1 * 2 ^ bit).testBit k) = decide (k = bit)
  rw [Nat.one_mul]
  simp only [Nat.testBit_two_pow, eq_comm (a := bit) (b := k)]
  by_cases hkb : k = bit
  · subst k
    simp only [hb, decide_true, Bool.true_and]
  · simp only [hkb, decide_false, Bool.and_false]

/-- The zero chunk has no observable bits. -/
theorem bs_zero_bit (k : Nat) : (fromJInt zero64).getLsbD k = false := by
  change (0#64).getLsbD k = false
  exact BitVec.getLsbD_zero

/-- The source mask-and-test primitive is exactly the selected word bit. -/
theorem bs_bitAt_eq (word : U64) (bit : Nat) (hb : bit < 64) :
    bitAt word bit = (fromJInt word).getLsbD bit := by
  have heq : and_int word (shl_int (uint64 1) (int64 bit)) = zero64 ↔
      (fromJInt word).getLsbD bit = false := by
    constructor
    · intro h
      have hh := congrArg (fun value : U64 => (fromJInt value).getLsbD bit) h
      simpa only [bs_and_bit, bs_mask_bit bit bit hb, decide_true, Bool.and_true,
        bs_zero_bit] using hh
    · intro h
      apply bs_word_ext
      intro k hk
      rw [bs_and_bit, bs_mask_bit bit k hb, bs_zero_bit]
      by_cases he : k = bit
      · subst k
        simp only [h, Bool.false_and]
      · simp only [he, decide_false, Bool.and_false]
  unfold bitAt
  cases hbit : (fromJInt word).getLsbD bit
  · have hz := heq.mpr hbit
    rw [hz]
    rfl
  · have hn : and_int word (shl_int (uint64 1) (int64 bit)) ≠ zero64 := by
      intro hz
      have := heq.mp hz
      rw [hbit] at this
      cases this
    exact bne_iff_ne.mpr hn

/-- A cleared word bit agrees with the original word at every other position. -/
theorem bs_clear_bit (word : U64) (bit k : Nat) (hb : bit < 64) (hk : k < 64) :
    (fromJInt (and_int word (not_int (shl_int (uint64 1) (int64 bit))))).getLsbD k =
      ((fromJInt word).getLsbD k && decide (k ≠ bit)) := by
  rw [bs_and_bit, bs_not_bit _ k hk, bs_mask_bit bit k hb]
  by_cases h : k = bit <;> simp [h]

/-- Bit offsets always lie in the 64 positions of a storage chunk. -/
theorem bs_mod64_lt (n : I64) : mod64 n.val < 64 := by
  rw [bs_mod64_eq n.val n.property]
  have := Int.emod_lt_of_pos n.val (by decide : (0 : Int) < 64)
  omega

/-- A chunk address and within-chunk bit uniquely identify a signed integer. -/
theorem bs_address_injective (a b : I64)
    (hc : div64 a.val = div64 b.val) (hb : mod64 a.val = mod64 b.val) : a = b := by
  rw [bs_div64_eq a.val a.property, bs_div64_eq b.val b.property] at hc
  rw [bs_mod64_eq a.val a.property, bs_mod64_eq b.val b.property] at hb
  have ha0 := Int.emod_nonneg a.val (by decide : (64 : Int) ≠ 0)
  have hb0 := Int.emod_nonneg b.val (by decide : (64 : Int) ≠ 0)
  apply Subtype.ext
  omega

/-- Chunk storage extended by zeros to absolute chunk coordinates. -/
def bs_chunkAt (s : BitSet) (chunk : Int) : U64 :=
  if 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length then
    bitsGet s.bits (chunk - s.offset + 1).toNat
  else zero64

/-- Scalar membership reads exactly one bit of the zero-extended chunk map. -/
theorem bs_inInt_chunk (s : BitSet) (n : I64) :
    inInt n s = (fromJInt (bs_chunkAt s (div64 n.val))).getLsbD (mod64 n.val) := by
  unfold inInt bitsGetindex bs_chunkAt
  dsimp only
  by_cases h : 1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length
  · simp only [h, ite_true]
    exact bs_bitAt_eq _ _ (bs_mod64_lt n)
  · simp only [h, ite_false]
    exact (bs_zero_bit _).symm

/-- The integer membership guard is equivalent to the declared conversion range. -/
theorem bs_member_range (s : BitSet) (n : Int) :
    member s n = if IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max then inInt (int64 n) s else false := by
  simp only [member, inInteger, isConvertibleInt, decide_eq_true_eq]

/-- Each stored chunk of a well-formed set expands entirely inside the machine range. -/
theorem bs_chunk_address_range (s : BitSet) (h : WF s) (chunk : Int) (bit : Nat)
    (hc : 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length)
    (hb : bit < 64) :
    IntTy.i64.min ≤ chunk * 64 + bit ∧ chunk * 64 + bit ≤ IntTy.i64.max := by
  have hne : s.offset ≠ noOffset := by
    intro hs
    have hnil := h.1 hs
    rw [hnil] at hc
    simp only [List.length_nil, Int.ofNat_zero] at hc
    omega
  have hr := h.2 hne
  change -(2 ^ 57) ≤ s.offset ∧ s.offset + s.bits.length ≤ 2 ^ 57 at hr
  change -9223372036854775808 ≤ chunk * 64 + (bit : Int) ∧
    chunk * 64 + (bit : Int) ≤ 9223372036854775807
  omega

/-- In-range chunk/bit assembly recovers the original address after division. -/
theorem bs_assemble_div (chunk : Int) (bit : Nat) (hb : bit < 64)
    (hr : IntTy.i64.min ≤ chunk * 64 + bit ∧ chunk * 64 + bit ≤ IntTy.i64.max) :
    div64 (chunk * 64 + bit) = chunk := by
  rw [bs_div64_eq _ hr]
  omega

/-- In-range chunk/bit assembly recovers the original bit after remainder. -/
theorem bs_assemble_mod (chunk : Int) (bit : Nat) (hb : bit < 64)
    (hr : IntTy.i64.min ≤ chunk * 64 + bit ∧ chunk * 64 + bit ≤ IntTy.i64.max) :
    mod64 (chunk * 64 + bit) = bit := by
  rw [bs_mod64_eq _ hr]
  omega

/-- Pointwise equal chunk maps have pointwise equal mathematical membership. -/
theorem bs_members_of_chunks (a b : BitSet)
    (h : ∀ chunk, bs_chunkAt a chunk = bs_chunkAt b chunk) :
    ∀ n, member a n = member b n := by
  intro n
  rw [bs_member_range, bs_member_range]
  split
  · rw [bs_inInt_chunk, bs_inInt_chunk, h]
  · rfl

/-- Membership equality detects every stored bit, including differing storage spans. -/
theorem bs_chunks_of_members (a b : BitSet) (ha : WF a) (hb : WF b)
    (h : ∀ n, member a n = member b n) : ∀ chunk, bs_chunkAt a chunk = bs_chunkAt b chunk := by
  intro chunk
  by_cases hia : 1 ≤ chunk - a.offset + 1 ∧ chunk - a.offset + 1 ≤ a.bits.length
  · apply bs_word_ext
    intro bit hbit
    have hr := bs_chunk_address_range a ha chunk bit hia hbit
    have hn := h (chunk * 64 + bit)
    rw [bs_member_range, bs_member_range, if_pos hr, if_pos hr,
      bs_inInt_chunk, bs_inInt_chunk, bs_int64_val _ hr,
      bs_assemble_div chunk bit hbit hr, bs_assemble_mod chunk bit hbit hr] at hn
    exact hn
  · by_cases hib : 1 ≤ chunk - b.offset + 1 ∧ chunk - b.offset + 1 ≤ b.bits.length
    · apply bs_word_ext
      intro bit hbit
      have hr := bs_chunk_address_range b hb chunk bit hib hbit
      have hn := h (chunk * 64 + bit)
      rw [bs_member_range, bs_member_range, if_pos hr, if_pos hr,
        bs_inInt_chunk, bs_inInt_chunk, bs_int64_val _ hr,
        bs_assemble_div chunk bit hbit hr, bs_assemble_mod chunk bit hbit hr] at hn
      exact hn
    · simp only [bs_chunkAt, hia, hib, ite_false]

/-- A nonpositive overlap requests no chunks and therefore compares equal. -/
theorem bs_memeq_nonpos (a b : List U64) (start count : Int) (h : count ≤ 0) :
    memeq a start b count = true := by
  have hn : count.toNat = 0 := by omega
  simp only [memeq, hn, List.range_zero, List.all_nil]

/-- The installed early failure guards are conjunction of the three checks. -/
theorem bs_guard_conjunction (left right overlap : Bool) :
    (if !left then false else if !right then false else overlap) =
      (left && (right && overlap)) := by
  cases left <;> cases right <;> rfl

/-- Sorted-offset equality is precisely its two exterior scans and aligned overlap. -/
theorem bs_eq_sorted_bool (a b : BitSet) (horder : a.offset ≤ b.offset) :
    let n : Int := a.bits.length
    let m : Int := b.bits.length
    let overlap0 := max 0 (n + a.offset - b.offset)
    let overlap := if overlap0 ≥ m then m else overlap0
    JuliaLean.base.bitset.eq a b =
      (check0 a.bits 1 (n - overlap0) &&
        ((if overlap0 ≥ m then check0 a.bits (b.offset - a.offset + m + 1) n
          else check0 b.bits (1 + overlap) m) &&
          memeq a.bits (b.offset - a.offset + 1) b.bits overlap)) := by
  dsimp only
  unfold JuliaLean.base.bitset.eq
  rw [if_neg (show ¬ a.offset > b.offset by omega)]
  dsimp only
  have hneg (p : Prop) [Decidable p] (x y : Bool) :
      (if p then !x else !y) = !(if p then x else y) := by
    split <;> rfl
  rw [hneg, bs_guard_conjunction]
  by_cases hpos : (if max 0 ((a.bits.length : Int) + a.offset - b.offset) ≥ (b.bits.length : Int)
      then (b.bits.length : Int) else max 0 ((a.bits.length : Int) + a.offset - b.offset)) > 0
  · rw [if_pos hpos]
  · rw [if_neg hpos, bs_memeq_nonpos _ _ _ _ (by omega)]

/-- Exterior zero scans plus overlap equality are exactly equality of absolute chunks. -/
theorem bs_eq_sorted_chunks (a b : BitSet) (horder : a.offset ≤ b.offset) :
    JuliaLean.base.bitset.eq a b = true ↔ ∀ chunk, bs_chunkAt a chunk = bs_chunkAt b chunk := by
  let n : Int := a.bits.length
  let m : Int := b.bits.length
  let d : Int := b.offset - a.offset
  let o : Int := max 0 (n + a.offset - b.offset)
  let t : Int := if o ≥ m then m else o
  have hn : 0 ≤ n := Int.natCast_nonneg _
  have hm : 0 ≤ m := Int.natCast_nonneg _
  have hd : 0 ≤ d := by dsimp only [d]; omega
  have ho : o = max 0 (n - d) := by dsimp only [o, d]; congr 1 <;> omega
  have hob : 0 ≤ o ∧ o ≤ n := by omega
  have htb : 0 ≤ t ∧ t ≤ m ∧ t ≤ o := by dsimp only [t]; split <;> omega
  have htc : t = m ∨ t = o := by dsimp only [t]; split <;> simp
  have heq : JuliaLean.base.bitset.eq a b =
      (check0 a.bits 1 (n - o) &&
        ((if o ≥ m then check0 a.bits (d + m + 1) n else check0 b.bits (1 + t) m) &&
          memeq a.bits (d + 1) b.bits t)) := bs_eq_sorted_bool a b horder
  rw [heq]
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    have hl := (bs_check0_iff a.bits 1 (n - o)).mp h.1
    have hr := h.2.1
    have hov := (bs_memeq_iff a.bits b.bits (d + 1) t).mp h.2.2
    intro chunk
    let i : Int := chunk - a.offset + 1
    let j : Int := chunk - b.offset + 1
    have hij : i = j + d := by dsimp only [i, j, d]; omega
    by_cases hia : 1 ≤ chunk - a.offset + 1 ∧ chunk - a.offset + 1 ≤ a.bits.length
    · by_cases hib : 1 ≤ chunk - b.offset + 1 ∧ chunk - b.offset + 1 ≤ b.bits.length
      · simp only [bs_chunkAt, hia, hib, ite_true]
        change bitsGet a.bits i.toNat = bitsGet b.bits j.toNat
        change 1 ≤ i ∧ i ≤ n at hia
        change 1 ≤ j ∧ j ≤ m at hib
        have hk : (j - 1).toNat < t.toNat := by omega
        have haidx : (d + 1 + ((j - 1).toNat : Int)).toNat = i.toNat := by omega
        have hbidx : (j - 1).toNat + 1 = j.toNat := by omega
        simpa only [haidx, hbidx] using hov (j - 1).toNat hk
      · simp only [bs_chunkAt, hia, hib, ite_true, ite_false]
        change bitsGet a.bits i.toNat = zero64
        change 1 ≤ i ∧ i ≤ n at hia
        change ¬ (1 ≤ j ∧ j ≤ m) at hib
        by_cases hj : j ≤ 0
        · exact hl i hia.1 (by omega)
        · have hinc : o ≥ m := by omega
          rw [if_pos hinc] at hr
          exact (bs_check0_iff a.bits (d + m + 1) n).mp hr i (by omega) hia.2
    · by_cases hib : 1 ≤ chunk - b.offset + 1 ∧ chunk - b.offset + 1 ≤ b.bits.length
      · simp only [bs_chunkAt, hia, hib, ite_true, ite_false]
        change zero64 = bitsGet b.bits j.toNat
        change ¬ (1 ≤ i ∧ i ≤ n) at hia
        change 1 ≤ j ∧ j ≤ m at hib
        have hinc : ¬ o ≥ m := by omega
        rw [if_neg hinc] at hr
        have ht : t = o := by simp only [t, hinc, ite_false]
        exact ((bs_check0_iff b.bits (1 + t) m).mp hr j (by omega) hib.2).symm
      · simp only [bs_chunkAt, hia, hib, ite_false]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (bs_check0_iff a.bits 1 (n - o)).mpr
      intro i hi1 hi2
      have hia : 1 ≤ a.offset + i - 1 - a.offset + 1 ∧
          a.offset + i - 1 - a.offset + 1 ≤ a.bits.length := by change 1 ≤ _ ∧ _ ≤ n; omega
      have hib : ¬ (1 ≤ a.offset + i - 1 - b.offset + 1 ∧
          a.offset + i - 1 - b.offset + 1 ≤ b.bits.length) := by
        change ¬ (1 ≤ _ ∧ _ ≤ m)
        dsimp only [d] at ho
        omega
      have hi : a.offset + i - 1 - a.offset + 1 = i := by omega
      have hh := h (a.offset + i - 1)
      unfold bs_chunkAt at hh
      rw [if_pos hia, if_neg hib, hi] at hh
      exact hh
    · by_cases hinc : o ≥ m
      · rw [if_pos hinc]
        apply (bs_check0_iff a.bits (d + m + 1) n).mpr
        intro i hi1 hi2
        have hia : 1 ≤ a.offset + i - 1 - a.offset + 1 ∧
            a.offset + i - 1 - a.offset + 1 ≤ a.bits.length := by change 1 ≤ _ ∧ _ ≤ n; omega
        have hib : ¬ (1 ≤ a.offset + i - 1 - b.offset + 1 ∧
            a.offset + i - 1 - b.offset + 1 ≤ b.bits.length) := by
          change ¬ (1 ≤ _ ∧ _ ≤ m)
          dsimp only [d] at hi1
          omega
        have hi : a.offset + i - 1 - a.offset + 1 = i := by omega
        have hh := h (a.offset + i - 1)
        unfold bs_chunkAt at hh
        rw [if_pos hia, if_neg hib, hi] at hh
        exact hh
      · rw [if_neg hinc]
        apply (bs_check0_iff b.bits (1 + t) m).mpr
        intro j hj1 hj2
        have ht : t = o := by simp only [t, hinc, ite_false]
        have hia : ¬ (1 ≤ b.offset + j - 1 - a.offset + 1 ∧
            b.offset + j - 1 - a.offset + 1 ≤ a.bits.length) := by
          change ¬ (1 ≤ _ ∧ _ ≤ n)
          dsimp only [d] at ho
          omega
        have hib : 1 ≤ b.offset + j - 1 - b.offset + 1 ∧
            b.offset + j - 1 - b.offset + 1 ≤ b.bits.length := by change 1 ≤ _ ∧ _ ≤ m; omega
        have hj : b.offset + j - 1 - b.offset + 1 = j := by omega
        have hh := (h (b.offset + j - 1)).symm
        unfold bs_chunkAt at hh
        rw [if_neg hia, if_pos hib, hj] at hh
        exact hh
    · apply (bs_memeq_iff a.bits b.bits (d + 1) t).mpr
      intro k hk
      have hia : 1 ≤ b.offset + (k : Int) - a.offset + 1 ∧
          b.offset + (k : Int) - a.offset + 1 ≤ a.bits.length := by
        change 1 ≤ _ ∧ _ ≤ n
        dsimp only [d] at ho
        omega
      have hib : 1 ≤ b.offset + (k : Int) - b.offset + 1 ∧
          b.offset + (k : Int) - b.offset + 1 ≤ b.bits.length := by change 1 ≤ _ ∧ _ ≤ m; omega
      have haidx : (b.offset + (k : Int) - a.offset + 1).toNat = (d + 1 + k).toNat := by
        dsimp only [d]
        congr 1
        omega
      have hbidx : (b.offset + (k : Int) - b.offset + 1).toNat = k + 1 := by omega
      have hh := h (b.offset + k)
      unfold bs_chunkAt at hh
      rw [if_pos hia, if_pos hib, haidx, hbidx] at hh
      exact hh

/-- The source equality implementation compares the complete zero-extended chunk maps. -/
theorem bs_eq_chunks (a b : BitSet) :
    JuliaLean.base.bitset.eq a b = true ↔ ∀ chunk, bs_chunkAt a chunk = bs_chunkAt b chunk := by
  by_cases horder : a.offset ≤ b.offset
  · exact bs_eq_sorted_chunks a b horder
  · have hswap : JuliaLean.base.bitset.eq a b = JuliaLean.base.bitset.eq b a := by
      unfold JuliaLean.base.bitset.eq
      rw [if_pos (show a.offset > b.offset by omega),
        if_neg (show ¬ b.offset > a.offset by omega)]
    rw [hswap, bs_eq_sorted_chunks b a (by omega)]
    constructor <;> intro h chunk <;> exact (h chunk).symm

/-- Frozen target: public BitSet equality is exactly equality of mathematical membership. -/
theorem BitsetscovBitsetEquality_proven : JuliaLean.Proofs.base.bitset.BitSetEqSpec := by
  intro a b ha hb
  rw [bs_eq_chunks]
  exact ⟨bs_members_of_chunks a b, bs_chunks_of_members a b ha hb⟩

/-- The finite search position used by the intrinsic trailing-zero counter. -/
def bs_firstBit (word : U64) : Nat :=
  ((List.range 64).find? (fun k => (fromJInt word).getLsbD k)).getD 64

/-- Every counter value from 0 through 64 converts exactly from UInt64 to Int64. -/
theorem bs_small_counter (n : Nat) (hn : n ≤ 64) :
    (remT .i64 (toJInt .u64 (BitVec.ofNat IntTy.u64.bits n))).val = (n : Int) := by
  have h : ∀ k : Fin 65,
      (remT .i64 (toJInt .u64 (BitVec.ofNat IntTy.u64.bits k.val))).val = (k.val : Int) := by
    decide
  exact h ⟨n, by omega⟩

/-- The finite first-bit search has its expected lower-zero and selected-one properties. -/
theorem bs_firstBit_spec (word : U64) :
    bs_firstBit word ≤ 64 ∧
    (∀ k, k < bs_firstBit word → (fromJInt word).getLsbD k = false) ∧
    (bs_firstBit word < 64 → (fromJInt word).getLsbD (bs_firstBit word) = true) := by
  unfold bs_firstBit
  cases hf : (List.range 64).find? (fun k => (fromJInt word).getLsbD k) with
  | none =>
    have h := List.find?_eq_none.mp hf
    simp only [Option.getD_none]
    refine ⟨Nat.le_refl _, fun k hk => ?_, fun hk => False.elim (by omega)⟩
    exact Bool.eq_false_iff.mpr (h k (List.mem_range.mpr hk))
  | some bit =>
    have h := List.find?_range_eq_some.mp hf
    simp only [Option.getD_some]
    refine ⟨Nat.le_of_lt (List.mem_range.mp h.2.1), fun k hk => ?_, fun _ => h.1⟩
    have hh := h.2.2 k hk
    cases hb : (fromJInt word).getLsbD k <;> simp_all

/-- A nonzero chunk always has a first bit strictly inside its 64 positions. -/
theorem bs_firstBit_lt (word : U64) (hword : word ≠ zero64) : bs_firstBit word < 64 := by
  obtain ⟨hle, hzero, _⟩ := bs_firstBit_spec word
  by_cases h : bs_firstBit word < 64
  · exact h
  · exfalso
    have he : bs_firstBit word = 64 := by omega
    apply hword
    apply bs_word_ext
    intro k hk
    rw [bs_zero_bit]
    exact hzero k (by omega)

/-- The actual Julia integer intrinsic returns the finite first-bit index exactly. -/
theorem bs_trailing_zeros_val (word : U64) : (trailing_zeros word).val = (bs_firstBit word : Int) := by
  unfold trailing_zeros cttz_int jlCttzInt
  have hp : (fun i => (fromJInt word).toNat / 2 ^ i % 2 == 1) =
      (fun i => (fromJInt word).getLsbD i) := by
    funext i
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    cases h : ((fromJInt word).toNat / 2 ^ i % 2 == 1) <;> simp_all
  rw [hp]
  exact bs_small_counter _ (bs_firstBit_spec word).1

/-- Two's-complement intersection isolates the first set bit of any finite word. -/
theorem bs_lowbit_isolated {w : Nat} (word : BitVec w) (first k : Nat)
    (hfirst : word.getLsbD first = true)
    (hlower : ∀ j < first, word.getLsbD j = false) (hk : k < w) :
    (word &&& (-word)).getLsbD k = decide (k = first) := by
  rw [BitVec.getLsbD_and, BitVec.getLsbD_neg]
  simp only [hk, decide_true, Bool.true_and]
  by_cases hlt : k < first
  · have hne : k ≠ first := by omega
    simp only [hlower k hlt, Bool.false_and, hne, decide_false]
  · by_cases heq : k = first
    · subst k
      have hn : ¬ ∃ j < first, word.getLsbD j = true := by
        rintro ⟨j, hj, hh⟩
        rw [hlower j hj] at hh
        cases hh
      simp only [hfirst, hn, decide_false, Bool.xor_false, Bool.true_and, decide_true]
    · have hx : ∃ j < k, word.getLsbD j = true := ⟨first, by omega, hfirst⟩
      simp only [hx, decide_true, heq, decide_false]
      cases word.getLsbD k <;> rfl

/-- The iterator's bit-reset intrinsic removes exactly the lowest present bit. -/
theorem bs_blsr_bit (word : U64) (hword : word ≠ zero64) (k : Nat) (hk : k < 64) :
    (fromJInt (JuliaLean.base.bitarray.blsr word)).getLsbD k =
      ((fromJInt word).getLsbD k && decide (k ≠ bs_firstBit word)) := by
  have hs := bs_firstBit_spec word
  have hf := hs.2.2 (bs_firstBit_lt word hword)
  have hlow := bs_lowbit_isolated (fromJInt word) (bs_firstBit word) k hf hs.2.1 hk
  unfold JuliaLean.base.bitarray.blsr
  rw [bs_and_bit]
  unfold sub_int
  rw [bs_roundtrip_U64]
  change ((fromJInt word).getLsbD k && ((fromJInt word) - 1#IntTy.u64.bits).getLsbD k) = _
  rw [← BitVec.not_neg, BitVec.getLsbD_not]
  change ((fromJInt word).getLsbD k && (decide (k < 64) && !(-fromJInt word).getLsbD k)) = _
  rw [BitVec.getLsbD_and] at hlow
  simp only [hk, decide_true, Bool.true_and]
  by_cases heq : k = bs_firstBit word
  · simp only [heq, decide_true] at hlow
    have hpair : (fromJInt word).getLsbD (bs_firstBit word) = true ∧
        (-fromJInt word).getLsbD (bs_firstBit word) = true := by
      simpa only [Bool.and_eq_true] using hlow
    obtain ⟨ha, hb⟩ := hpair
    simp [heq, ha, hb]
  · have hfalse : ((fromJInt word).getLsbD k && (-fromJInt word).getLsbD k) = false := by
      simpa only [heq, decide_false] using hlow
    simp only [heq, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
    cases ha : (fromJInt word).getLsbD k <;> cases hb : (-fromJInt word).getLsbD k <;>
      simp only [ha, hb] at hfalse ⊢
    all_goals first | rfl | cases hfalse

/-- A loaded nonzero iteration word immediately returns its first set bit and reset state. -/
theorem bs_iterate_loaded (s : BitSet) (word : U64) (idx : Nat) (hword : word ≠ zero64) :
    iterate s (word, idx) =
      some (add_int (trailing_zeros word)
        (shl_int (int64 (idx - 1 + s.offset)) (int64 6)),
        (JuliaLean.base.bitarray.blsr word, idx)) := by
  unfold iterate
  simp only [iterate.scan, bne_iff_ne.mpr hword, ite_true]

/-- An in-bounds chunk write is read back at the same one-based index. -/
theorem bs_bitsSet_same (words : List U64) (chunk : Nat) (word : U64)
    (hlo : 1 ≤ chunk) (hhi : chunk ≤ words.length) :
    bitsGet (bitsSet words chunk word) chunk = word := by
  simp only [bitsGet, bitsSet, List.getD_eq_getElem?_getD,
    List.getElem?_set_self (by omega : chunk - 1 < words.length), Option.getD_some]

/-- A chunk write leaves all other positive indices unchanged. -/
theorem bs_bitsSet_other (words : List U64) (chunk target : Nat) (word : U64)
    (hchunk : 1 ≤ chunk) (htarget : 1 ≤ target) (hne : target ≠ chunk) :
    bitsGet (bitsSet words chunk word) target = bitsGet words target := by
  simp only [bitsGet, bitsSet, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (by omega : chunk - 1 ≠ target - 1)]

/-- The deletion branch updates storage exactly when its addressed chunk exists. -/
theorem bs_deleteInt_eq (s : BitSet) (n : I64) :
    deleteInt s n =
      if 1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length then
        { s with bits := setBit s.bits false (div64 n.val - s.offset + 1).toNat (mod64 n.val) }
      else s := by
  unfold deleteInt setint
  simp only [Bool.not_false, ite_true]
  split
  · rename_i h
    rw [if_neg (by omega)]
  · rename_i h
    split
    · rename_i hlo
      rw [if_neg (by omega)]
    · rename_i hlo
      rw [if_pos (by omega)]

/-- Machine-integer deletion removes its key and preserves every other member. -/
theorem bs_deleteInt_member (s : BitSet) (n x : I64) :
    inInt x (deleteInt s n) = (inInt x s && decide (x ≠ n)) := by
  rw [bs_deleteInt_eq]
  by_cases hn : 1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length
  · rw [if_pos hn]
    by_cases hx : 1 ≤ div64 x.val - s.offset + 1 ∧ div64 x.val - s.offset + 1 ≤ s.bits.length
    · simp only [inInt, bitsGetindex, bs_setBit_length]
      rw [if_pos hx, if_pos hx, bs_bitAt_eq _ _ (bs_mod64_lt x), bs_bitAt_eq _ _ (bs_mod64_lt x)]
      unfold setBit
      simp only [Bool.false_eq_true, ite_false]
      by_cases hc : (div64 x.val - s.offset + 1).toNat = (div64 n.val - s.offset + 1).toNat
      · rw [hc, bs_bitsSet_same s.bits _ _ (by omega) (by omega), bs_clear_bit _ _ _ (bs_mod64_lt n) (bs_mod64_lt x)]
        have hdiv : div64 x.val = div64 n.val := by omega
        have hkey : mod64 x.val = mod64 n.val ↔ x = n := by
          constructor
          · exact bs_address_injective x n hdiv
          · intro he
            rw [he]
        simp only [ne_eq, hkey]
      · rw [bs_bitsSet_other s.bits _ _ _ (by omega) (by omega) hc]
        have hne : x ≠ n := by intro he; subst x; exact hc rfl
        simp [ne_eq, hne]
    · simp only [inInt, bitsGetindex, bs_setBit_length]
      simp only [hx, ite_false, Bool.false_and]
  · rw [if_neg hn]
    by_cases he : x = n
    · subst x
      simp only [inInt, bitsGetindex, hn, ite_false, Bool.false_and]
    · simp only [ne_eq, he, not_false_eq_true, decide_true, Bool.and_true]

/-- Conversion-checked integer deletion has the same exact membership contract. -/
theorem bs_deleteInteger_member (s : BitSet) (n x : Int) :
    member (deleteInteger s n) x = (member s x && decide (x ≠ n)) := by
  rw [bs_member_range, bs_member_range]
  unfold deleteInteger
  by_cases hn : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
  · have hcn : isConvertibleInt n = true := by simp [isConvertibleInt, hn]
    rw [hcn, if_pos rfl]
    by_cases hx : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max
    · rw [if_pos hx, if_pos hx, bs_deleteInt_member]
      have he : int64 x = int64 n ↔ x = n := by
        constructor
        · intro h
          have hh := congrArg Subtype.val h
          rw [bs_int64_val x hx, bs_int64_val n hn] at hh
          exact hh
        · intro h
          rw [h]
      simp only [ne_eq, he]
    · rw [if_neg hx, if_neg hx]
      rfl
  · have hcn : isConvertibleInt n = false := by simp [isConvertibleInt, hn]
    rw [hcn, if_neg (by decide : ¬ false = true)]
    by_cases he : x = n
    · subst x
      simp only [hn, ite_false, Bool.false_and]
    · simp only [ne_eq, he, not_false_eq_true, decide_true, Bool.and_true]

/-- Frozen target: deletion and both keyed-pop APIs satisfy their exact public contracts. -/
theorem BitsetscovBitsetDeletePop_proven : JuliaLean.Proofs.base.bitset.Round1.BitSetDeleteContract := by
  refine ⟨?_, ?_, ?_⟩
  · intro s n h
    exact ⟨bs_deleteInteger_WF s n h, bs_deleteInteger_member s n⟩
  · intro s n _
    exact bs_popKey_branches s n
  · intro α s n default
    exact bs_popDefault_eq s n default

/-- The reset representation satisfies both frozen well-formedness clauses. -/
theorem bs_new_WF : WF new := by
  constructor
  · intro _
    rfl
  · intro h
    exact False.elim (h rfl)

/-- The new set has the zero word at every absolute chunk coordinate. -/
theorem bs_new_chunk (chunk : Int) : bs_chunkAt new chunk = zero64 := by
  unfold bs_chunkAt new
  rw [if_neg (by simp only [List.length_nil, Int.ofNat_zero]; omega)]

/-- The public empty test is exactly the assertion that every absolute chunk is zero. -/
theorem bs_isempty_chunks (s : BitSet) :
    isempty s = true ↔ ∀ chunk, bs_chunkAt s chunk = zero64 := by
  rw [isempty, bs_check0_iff]
  constructor
  · intro h chunk
    unfold bs_chunkAt
    split
    · rename_i hc
      exact h _ hc.1 hc.2
    · rfl
  · intro h i hlo hhi
    have hc : 1 ≤ s.offset + i - 1 - s.offset + 1 ∧
        s.offset + i - 1 - s.offset + 1 ≤ s.bits.length := by omega
    have hi : s.offset + i - 1 - s.offset + 1 = i := by omega
    have hh := h (s.offset + i - 1)
    unfold bs_chunkAt at hh
    rw [if_pos hc, hi] at hh
    exact hh

/-- Frozen target: empty! resets membership and isempty detects precisely empty membership. -/
theorem BitsetscovBitsetEmpty_proven : JuliaLean.Proofs.base.bitset.Round2.BitSetEmptyPublicSpec := by
  intro s hs
  refine ⟨rfl, bs_emptyBang_members s, ?_⟩
  rw [bs_isempty_chunks]
  constructor
  · intro h n
    have hm := bs_members_of_chunks s new (fun chunk => (h chunk).trans (bs_new_chunk chunk).symm)
    rw [hm n]
    exact bs_emptyBang_members new n
  · intro h chunk
    have hm : ∀ n, member s n = member new n := fun n =>
      (h n).trans (bs_emptyBang_members new n).symm
    rw [bs_chunks_of_members s new hs bs_new_WF hm chunk, bs_new_chunk]

/-- An arbitrary Boolean scan over an integer range checks every requested index. -/
theorem bs_allRange_iff (p : Int → Bool) (lo hi : Int) :
    (intRange lo hi).all p = true ↔ ∀ i, lo ≤ i → i ≤ hi → p i = true := by
  simp only [List.all_eq_true]
  constructor
  · intro h i hlo hhi
    exact h i ((bs_intRange_mem lo hi i).mpr ⟨hlo, hhi⟩)
  · intro h i hi
    obtain ⟨hlo, hhi⟩ := (bs_intRange_mem lo _ i).mp hi
    exact h i hlo hhi

/-- Chunk inclusion is exactly implication between the 64 represented Boolean bits. -/
theorem bs_subChunk_bits (a b : U64) :
    subChunk a b = true ↔
      ∀ k, k < 64 → (fromJInt a).getLsbD k = true → (fromJInt b).getLsbD k = true := by
  unfold subChunk
  rw [beq_iff_eq]
  constructor
  · intro h k hk ha
    have hh := congrArg (fun word : U64 => (fromJInt word).getLsbD k) h
    rw [bs_and_bit, ha] at hh
    simpa only [Bool.true_and] using hh.symm
  · intro h
    apply bs_word_ext
    intro k hk
    rw [bs_and_bit]
    cases ha : (fromJInt a).getLsbD k
    · rfl
    · rw [h k hk ha]
      rfl

/-- A zero chunk is included in every chunk. -/
theorem bs_subChunk_zero_left (word : U64) : subChunk zero64 word = true := by
  apply (bs_subChunk_bits zero64 word).mpr
  intro k hk h
  rw [bs_zero_bit] at h
  cases h

/-- Inclusion in a zero chunk forces the original chunk to be zero. -/
theorem bs_subChunk_zero_right (word : U64) : subChunk word zero64 = true ↔ word = zero64 := by
  constructor
  · intro h
    apply bs_word_ext
    intro k hk
    rw [bs_zero_bit]
    cases hb : (fromJInt word).getLsbD k
    · rfl
    · have hh := (bs_subChunk_bits word zero64).mp h k hk hb
      rw [bs_zero_bit] at hh
      cases hh
  · intro h
    rw [h]
    exact bs_subChunk_zero_left zero64

/-- The three source subset scans implement inclusion at every absolute chunk coordinate. -/
theorem bs_issubset_chunks (a b : BitSet) :
    issubset a b = true ↔ ∀ chunk, subChunk (bs_chunkAt a chunk) (bs_chunkAt b chunk) = true := by
  let n : Int := a.bits.length
  let m : Int := b.bits.length
  let d : Int := b.offset - a.offset
  have hn : 0 ≤ n := Int.natCast_nonneg _
  have hm : 0 ≤ m := Int.natCast_nonneg _
  have hform : issubset a b = true ↔
      (∀ k : Int, 1 ≤ k → k ≤ min n d → bitsGet a.bits k.toNat = zero64) ∧
      (∀ k : Int, max 1 (d + 1) ≤ k → k ≤ min n (d + m) →
        subChunk (bitsGet a.bits k.toNat) (bitsGet b.bits (k - d).toNat) = true) ∧
      (∀ k : Int, max 1 (d + m + 1) ≤ k → k ≤ n → bitsGet a.bits k.toNat = zero64) := by
    simp only [issubset, Bool.and_eq_true, bs_allRange_iff, beq_iff_eq, and_assoc]
    rfl
  rw [hform]
  constructor
  · intro h chunk
    let i : Int := chunk - a.offset + 1
    let j : Int := chunk - b.offset + 1
    have hij : i = j + d := by dsimp only [i, j, d]; omega
    by_cases hia : 1 ≤ chunk - a.offset + 1 ∧ chunk - a.offset + 1 ≤ a.bits.length
    · by_cases hib : 1 ≤ chunk - b.offset + 1 ∧ chunk - b.offset + 1 ≤ b.bits.length
      · unfold bs_chunkAt
        rw [if_pos hia, if_pos hib]
        change subChunk (bitsGet a.bits i.toNat) (bitsGet b.bits j.toNat) = true
        change 1 ≤ i ∧ i ≤ n at hia
        change 1 ≤ j ∧ j ≤ m at hib
        have he : i - d = j := by omega
        simpa only [he] using h.2.1 i (by omega) (by omega)
      · unfold bs_chunkAt
        rw [if_pos hia, if_neg hib]
        change subChunk (bitsGet a.bits i.toNat) zero64 = true
        apply (bs_subChunk_zero_right _).mpr
        change 1 ≤ i ∧ i ≤ n at hia
        change ¬ (1 ≤ j ∧ j ≤ m) at hib
        by_cases hleft : i ≤ d
        · exact h.1 i hia.1 (by omega)
        · exact h.2.2 i (by omega) hia.2
    · unfold bs_chunkAt
      rw [if_neg hia]
      exact bs_subChunk_zero_left _
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i hlo hhi
      have hia : 1 ≤ a.offset + i - 1 - a.offset + 1 ∧
          a.offset + i - 1 - a.offset + 1 ≤ a.bits.length := by change 1 ≤ _ ∧ _ ≤ n; omega
      have hib : ¬ (1 ≤ a.offset + i - 1 - b.offset + 1 ∧
          a.offset + i - 1 - b.offset + 1 ≤ b.bits.length) := by
        change ¬ (1 ≤ _ ∧ _ ≤ m)
        dsimp only [d] at hhi
        omega
      have hi : a.offset + i - 1 - a.offset + 1 = i := by omega
      have hh := h (a.offset + i - 1)
      unfold bs_chunkAt at hh
      rw [if_pos hia, if_neg hib, hi] at hh
      exact (bs_subChunk_zero_right _).mp hh
    · intro i hlo hhi
      have hia : 1 ≤ a.offset + i - 1 - a.offset + 1 ∧
          a.offset + i - 1 - a.offset + 1 ≤ a.bits.length := by change 1 ≤ _ ∧ _ ≤ n; omega
      have hib : 1 ≤ a.offset + i - 1 - b.offset + 1 ∧
          a.offset + i - 1 - b.offset + 1 ≤ b.bits.length := by
        change 1 ≤ _ ∧ _ ≤ m
        dsimp only [d] at hlo hhi
        omega
      have hi : a.offset + i - 1 - a.offset + 1 = i := by omega
      have hj : a.offset + i - 1 - b.offset + 1 = i - d := by dsimp only [d]; omega
      have hh := h (a.offset + i - 1)
      unfold bs_chunkAt at hh
      rw [if_pos hia, if_pos hib, hi, hj] at hh
      exact hh
    · intro i hlo hhi
      have hia : 1 ≤ a.offset + i - 1 - a.offset + 1 ∧
          a.offset + i - 1 - a.offset + 1 ≤ a.bits.length := by change 1 ≤ _ ∧ _ ≤ n; omega
      have hib : ¬ (1 ≤ a.offset + i - 1 - b.offset + 1 ∧
          a.offset + i - 1 - b.offset + 1 ≤ b.bits.length) := by
        change ¬ (1 ≤ _ ∧ _ ≤ m)
        dsimp only [d] at hlo
        omega
      have hi : a.offset + i - 1 - a.offset + 1 = i := by omega
      have hh := h (a.offset + i - 1)
      unfold bs_chunkAt at hh
      rw [if_pos hia, if_neg hib, hi] at hh
      exact (bs_subChunk_zero_right _).mp hh

/-- Chunkwise inclusion implies inclusion of every mathematical integer member. -/
theorem bs_members_included_of_chunks (a b : BitSet)
    (h : ∀ chunk, subChunk (bs_chunkAt a chunk) (bs_chunkAt b chunk) = true) :
    ∀ n, member a n = true → member b n = true := by
  intro n hn
  rw [bs_member_range] at hn ⊢
  by_cases hr : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
  · rw [if_pos hr, bs_inInt_chunk] at hn ⊢
    exact (bs_subChunk_bits _ _).mp (h _) _ (bs_mod64_lt (int64 n)) hn
  · rw [if_neg hr] at hn
    cases hn

/-- Every stored bit witnesses any failure of chunkwise inclusion by a public integer member. -/
theorem bs_chunks_included_of_members (a b : BitSet) (ha : WF a)
    (h : ∀ n, member a n = true → member b n = true) :
    ∀ chunk, subChunk (bs_chunkAt a chunk) (bs_chunkAt b chunk) = true := by
  intro chunk
  apply (bs_subChunk_bits _ _).mpr
  intro bit hbit hvalue
  by_cases hia : 1 ≤ chunk - a.offset + 1 ∧ chunk - a.offset + 1 ≤ a.bits.length
  · have hr := bs_chunk_address_range a ha chunk bit hia hbit
    have hm : member a (chunk * 64 + bit) = true := by
      rw [bs_member_range, if_pos hr, bs_inInt_chunk, bs_int64_val _ hr,
        bs_assemble_div chunk bit hbit hr, bs_assemble_mod chunk bit hbit hr]
      exact hvalue
    have hout := h _ hm
    rw [bs_member_range, if_pos hr, bs_inInt_chunk, bs_int64_val _ hr,
      bs_assemble_div chunk bit hbit hr, bs_assemble_mod chunk bit hbit hr] at hout
    exact hout
  · simp only [bs_chunkAt, hia, ite_false, bs_zero_bit] at hvalue
    cases hvalue

/-- Frozen target: public subset and strict subset agree with inclusion and proper inclusion. -/
theorem BitsetscovBitsetSubset_proven : JuliaLean.Proofs.base.bitset.Round2.BitSetSubsetPublicSpec := by
  classical
  intro a b ha hb
  have hinclusion : issubset a b = true ↔ ∀ n, member a n = true → member b n = true := by
    rw [bs_issubset_chunks]
    exact ⟨bs_members_included_of_chunks a b, bs_chunks_included_of_members a b ha⟩
  refine ⟨hinclusion, ?_⟩
  constructor
  · intro h
    have hh : issubset a b = true ∧ Bool.not (JuliaLean.base.bitset.eq a b) = true := by
      simpa only [strictSubset, Bool.and_eq_true] using h
    refine ⟨hinclusion.mp hh.1, ?_⟩
    apply Classical.not_forall.mp
    intro hall
    have heq := (BitsetscovBitsetEquality_proven a b ha hb).mpr hall
    rw [heq] at hh
    cases hh.2
  · rintro ⟨hsub, n, hne⟩
    have hs := hinclusion.mpr hsub
    have heq : JuliaLean.base.bitset.eq a b = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      exact hne ((BitsetscovBitsetEquality_proven a b ha hb).mp he n)
    simp only [strictSubset, hs, heq, Bool.not_false, Bool.and_true]

/-- In-range signed arithmetic decoding agrees with the represented mathematical integer. -/
theorem bs_toI64_ofInt (n : Int) (h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) :
    (toJInt .i64 (BitVec.ofInt IntTy.i64.bits n)).val = n := by
  rw [bs_toI64_val]
  change (BitVec.ofInt 64 n).toInt = n
  change -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 at h
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- An in-range signed intrinsic sum equals the mathematical sum. -/
theorem bs_addI64_val (a b : I64)
    (h : IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max) :
    (add_int a b).val = a.val + b.val := by
  unfold add_int jlAddInt fromJInt
  rw [← BitVec.ofInt_add]
  exact bs_toI64_ofInt _ h

/-- An in-range shift by six equals multiplication by the chunk size. -/
theorem bs_shift6I64_val (a : I64)
    (h : IntTy.i64.min ≤ a.val * 64 ∧ a.val * 64 ≤ IntTy.i64.max) :
    (shl_int a (int64 6)).val = a.val * 64 := by
  unfold shl_int jlShlInt
  change (toJInt .i64 (BitVec.ofNat IntTy.i64.bits ((fromJInt a).toNat * 64))).val = _
  rw [BitVec.ofNat_mul]
  have he : BitVec.ofNat IntTy.i64.bits (fromJInt a).toNat = fromJInt a := by
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt (fromJInt a).isLt
  rw [he]
  change (toJInt .i64 (BitVec.ofInt IntTy.i64.bits a.val * BitVec.ofInt IntTy.i64.bits 64)).val = _
  rw [← BitVec.ofInt_mul]
  exact bs_toI64_ofInt _ h

/-- Filtering a duplicate-free list emits its first found value before the remaining accepted values. -/
theorem bs_filter_first {α : Type} [DecidableEq α] (items : List α) (p : α → Bool)
    (first : α) (hnodup : items.Nodup) (hfind : items.find? p = some first) :
    items.filter p = first :: items.filter (fun value => p value && decide (value ≠ first)) := by
  induction items with
  | nil => simp only [List.find?_nil] at hfind; cases hfind
  | cons item items ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnodup
    by_cases hp : p item = true
    · simp only [List.find?_cons, hp, ite_true] at hfind
      have he : item = first := Option.some.inj hfind
      subst first
      rw [List.filter_cons_of_pos hp]
      have hclear : (item :: items).filter (fun value => p value && decide (value ≠ item)) = items.filter p := by
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
          Bool.false_eq_true, ite_false]
        apply List.filter_congr
        intro value hv
        have hn : value ≠ item := by intro he; subst value; exact hnot hv
        simp [hn]
      rw [hclear]
    · have hfalse : p item = false := Bool.eq_false_iff.mpr hp
      simp only [List.find?_cons, hfalse, Bool.false_eq_true, ite_false] at hfind
      simp only [List.filter_cons, hfalse, Bool.false_and, Bool.false_eq_true, ite_false]
      exact ih htail hfind

/-- Ascending positions of the true bits in one storage word. -/
def bs_wordPositions (word : U64) : List Nat :=
  (List.range 64).filter (fun bit => (fromJInt word).getLsbD bit)

/-- Mathematical integers represented by one absolute storage chunk. -/
def bs_wordValues (chunk : Int) (word : U64) : List Int :=
  (bs_wordPositions word).map (fun bit : Nat => chunk * 64 + (bit : Int))

/-- Mathematical integers represented by consecutive storage chunks. -/
def bs_chunkValues : Int → List U64 → List Int
  | _, [] => []
  | offset, word :: words => bs_wordValues offset word ++ bs_chunkValues (offset + 1) words

/-- The unconsumed mathematical values at an iterator state. -/
def bs_stateValues (s : BitSet) (state : U64 × Nat) : List Int :=
  bs_wordValues (s.offset + (state.2 : Int) - 1) state.1 ++
    bs_chunkValues (s.offset + state.2) (s.bits.drop state.2)

/-- Public iteration states stay within storage and start with a zero prefetched word. -/
def bs_validState (s : BitSet) (state : U64 × Nat) : Prop :=
  state.2 ≤ s.bits.length ∧ (state.2 = 0 → state.1 = zero64)

/-- A zero word contributes no enumerated positions. -/
theorem bs_wordPositions_zero : bs_wordPositions zero64 = [] := by
  simp only [bs_wordPositions, bs_zero_bit]
  apply List.filter_eq_nil_iff.mpr
  intro bit hbit
  simp

/-- A zero word contributes no mathematical integer values. -/
theorem bs_wordValues_zero (chunk : Int) : bs_wordValues chunk zero64 = [] := by
  simp only [bs_wordValues, bs_wordPositions_zero, List.map_nil]

/-- Clearing the lowest set bit removes precisely the head of the word's ascending positions. -/
theorem bs_wordPositions_blsr (word : U64) (hword : word ≠ zero64) :
    bs_wordPositions word = bs_firstBit word :: bs_wordPositions (JuliaLean.base.bitarray.blsr word) := by
  have hfind : (List.range 64).find? (fun k => (fromJInt word).getLsbD k) = some (bs_firstBit word) := by
    cases hf : (List.range 64).find? (fun k => (fromJInt word).getLsbD k) with
    | none =>
      have he : bs_firstBit word = 64 := by simp only [bs_firstBit, hf, Option.getD_none]
      have := bs_firstBit_lt word hword
      omega
    | some bit =>
      have he : bs_firstBit word = bit := by simp only [bs_firstBit, hf, Option.getD_some]
      rw [he]
  unfold bs_wordPositions
  rw [bs_filter_first (List.range 64) _ (bs_firstBit word) List.nodup_range hfind]
  congr 1
  apply List.filter_congr
  intro bit hbit
  exact (bs_blsr_bit word hword bit (List.mem_range.mp hbit)).symm

/-- Clearing the lowest bit removes precisely the head value of its chunk. -/
theorem bs_wordValues_blsr (chunk : Int) (word : U64) (hword : word ≠ zero64) :
    bs_wordValues chunk word =
      (chunk * 64 + bs_firstBit word) :: bs_wordValues chunk (JuliaLean.base.bitarray.blsr word) := by
  simp only [bs_wordValues, bs_wordPositions_blsr word hword, List.map_cons]

/-- A word contributes at most 64 values. -/
theorem bs_wordValues_length (chunk : Int) (word : U64) : (bs_wordValues chunk word).length ≤ 64 := by
  simp only [bs_wordValues, bs_wordPositions, List.length_map]
  exact Nat.le_trans (List.length_filter_le ..) (by rw [List.length_range]; exact Nat.le_refl 64)

/-- Consecutive chunks contribute at most 64 values each. -/
theorem bs_chunkValues_length (offset : Int) (words : List U64) :
    (bs_chunkValues offset words).length ≤ words.length * 64 := by
  induction words generalizing offset with
  | nil => exact Nat.le_refl 0
  | cons word words ih =>
    simp only [bs_chunkValues, List.length_append, List.length_cons]
    have hw := bs_wordValues_length offset word
    have ht := ih (offset + 1)
    omega

/-- Loading the next word from storage does not change the iterator's remaining values. -/
theorem bs_stateValues_scan (s : BitSet) (idx : Nat) (hi : idx < s.bits.length) :
    bs_stateValues s (zero64, idx) = bs_stateValues s (bitsGet s.bits (idx + 1), idx + 1) := by
  unfold bs_stateValues
  simp only [bs_wordValues_zero, List.nil_append]
  rw [List.drop_eq_getElem_cons hi]
  simp only [bs_chunkValues]
  have hword : bitsGet s.bits (idx + 1) = s.bits[idx] := by
    simp only [bitsGet, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  have hc : s.offset + ((idx + 1 : Nat) : Int) - 1 = s.offset + idx := by omega
  have ht : s.offset + ((idx + 1 : Nat) : Int) = s.offset + idx + 1 := by omega
  rw [hword, hc, ht]

/-- An exhausted scan state has no remaining mathematical values. -/
theorem bs_stateValues_end (s : BitSet) : bs_stateValues s (zero64, s.bits.length) = [] := by
  simp only [bs_stateValues, bs_wordValues_zero, List.drop_length, bs_chunkValues, List.nil_append]

/-- Every valid state fits inside the fuel bound supplied by the frozen public iterator. -/
theorem bs_stateValues_length (s : BitSet) (state : U64 × Nat) (hstate : bs_validState s state) :
    (bs_stateValues s state).length ≤ s.bits.length * 64 := by
  have ht := bs_chunkValues_length (s.offset + state.2) (s.bits.drop state.2)
  rw [List.length_drop] at ht
  by_cases hz : state.2 = 0
  · have hw := hstate.2 hz
    simpa only [bs_stateValues, hw, bs_wordValues_zero, List.nil_append, hz, Nat.sub_zero] using ht
  · have hw := bs_wordValues_length (s.offset + (state.2 : Int) - 1) state.1
    simp only [bs_stateValues, List.length_append]
    have hi := hstate.1
    omega

/-- A loaded iterator word returns the exact integer represented by its first set bit. -/
theorem bs_iterate_value (s : BitSet) (hs : WF s) (word : U64) (idx : Nat)
    (hi : 1 ≤ idx ∧ idx ≤ s.bits.length) (hword : word ≠ zero64) :
    (add_int (trailing_zeros word)
      (shl_int (int64 (idx - 1 + s.offset)) (int64 6))).val =
        (s.offset + (idx : Int) - 1) * 64 + bs_firstBit word := by
  let chunk : Int := s.offset + (idx : Int) - 1
  have hc : 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length := by
    dsimp only [chunk]
    omega
  have hr0 := bs_chunk_address_range s hs chunk 0 hc (by decide)
  have hr := bs_chunk_address_range s hs chunk (bs_firstBit word) hc (bs_firstBit_lt word hword)
  have hci : (int64 (idx - 1 + s.offset)).val = chunk := by
    rw [bs_int64_val _ (by
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change -9223372036854775808 ≤ chunk * 64 + 0 ∧ chunk * 64 + 0 ≤ 9223372036854775807 at hr0
      dsimp only [chunk] at hr0
      omega)]
    dsimp only [chunk]
    omega
  have hb : (shl_int (int64 (idx - 1 + s.offset)) (int64 6)).val = chunk * 64 := by
    rw [bs_shift6I64_val _ (by rw [hci]; simpa only [Int.natCast_zero, Int.add_zero] using hr0), hci]
  rw [bs_addI64_val _ _ (by rw [bs_trailing_zeros_val, hb]; omega), bs_trailing_zeros_val, hb]
  dsimp only [chunk]
  omega

/-- A sufficiently fueled chunk scan either exhausts the remaining values or emits their head. -/
theorem bs_scan_semantics (s : BitSet) (hs : WF s) (fuel : Nat) (word : U64) (idx : Nat)
    (hstate : bs_validState s (word, idx)) (hbudget : s.bits.length - idx < fuel) :
    match iterate.scan s fuel word idx with
    | none => bs_stateValues s (word, idx) = []
    | some (value, next) =>
        bs_stateValues s (word, idx) = value.val :: bs_stateValues s next ∧
        bs_validState s next ∧ 1 ≤ next.2 ∧ div64 value.val = s.offset + (next.2 : Int) - 1 := by
  induction fuel generalizing word idx with
  | zero => omega
  | succ fuel ih =>
    by_cases hword : word = zero64
    · subst word
      rw [iterate.scan]
      simp only [show (zero64 != zero64) = false from rfl, Bool.false_eq_true, ite_false]
      by_cases hi : idx = s.bits.length
      · have hbeq : (idx == s.bits.length) = true := beq_iff_eq.mpr hi
        rw [hbeq, if_pos rfl]
        rw [hi]
        exact bs_stateValues_end s
      · have hbeq : (idx == s.bits.length) = false := by simp [hi]
        rw [hbeq, if_neg (by decide : ¬ false = true)]
        have hidx : idx < s.bits.length := by have := hstate.1; omega
        have hnext : bs_validState s (bitsGet s.bits (idx + 1), idx + 1) := by
          exact ⟨by omega, fun h => False.elim (by omega)⟩
        have hout := ih (bitsGet s.bits (idx + 1)) (idx + 1) hnext (by omega)
        rw [bs_stateValues_scan s idx hidx]
        exact hout
    · rw [iterate.scan, if_pos (bne_iff_ne.mpr hword)]
      have hidx : 1 ≤ idx ∧ idx ≤ s.bits.length := by
        have hlo : idx ≠ 0 := by intro hz; exact hword (hstate.2 hz)
        exact ⟨by omega, hstate.1⟩
      refine ⟨?_, ?_, hidx.1, ?_⟩
      · rw [bs_iterate_value s hs word idx hidx hword]
        unfold bs_stateValues
        rw [bs_wordValues_blsr _ word hword]
        rfl
      · exact ⟨hidx.2, fun h => False.elim (by omega)⟩
      · rw [bs_div64_eq _ (add_int (trailing_zeros word)
          (shl_int (int64 (idx - 1 + s.offset)) (int64 6))).property,
          bs_iterate_value s hs word idx hidx hword]
        have := bs_firstBit_lt word hword
        omega

/-- One public iterator call exactly consumes the head of its remaining mathematical values. -/
theorem bs_iterate_semantics (s : BitSet) (hs : WF s) (state : U64 × Nat)
    (hstate : bs_validState s state) :
    match iterate s state with
    | none => bs_stateValues s state = []
    | some (value, next) =>
        bs_stateValues s state = value.val :: bs_stateValues s next ∧
        bs_validState s next ∧ 1 ≤ next.2 ∧ div64 value.val = s.offset + (next.2 : Int) - 1 := by
  exact bs_scan_semantics s hs (s.bits.length + 1) state.1 state.2 hstate (by omega)

/-- Repeated public iterator calls enumerate the complete remaining list whenever enough fuel is supplied. -/
theorem bs_walk_values (s : BitSet) (hs : WF s) (fuel : Nat) (state : U64 × Nat)
    (hstate : bs_validState s state) (hbudget : (bs_stateValues s state).length ≤ fuel) :
    (iterated.walk s fuel state).map (fun value : I64 => value.val) = bs_stateValues s state := by
  induction fuel generalizing state with
  | zero =>
    have hz : bs_stateValues s state = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hz]
    rfl
  | succ fuel ih =>
    have hstep := bs_iterate_semantics s hs state hstate
    cases hi : iterate s state with
    | none =>
      rw [hi] at hstep
      simp only [iterated.walk, hi, List.map_nil]
      exact hstep.symm
    | some output =>
      obtain ⟨value, next⟩ := output
      rw [hi] at hstep
      simp only [iterated.walk, hi, List.map_cons]
      rw [ih next hstep.2.1 (by rw [hstep.1, List.length_cons] at hbudget; omega)]
      exact hstep.1.symm

/-- The frozen complete iterator enumerates exactly the consecutive stored chunk values. -/
theorem bs_iterated_values (s : BitSet) (hs : WF s) :
    (iterated s).map (fun value : I64 => value.val) = bs_chunkValues s.offset s.bits := by
  have hstate : bs_validState s (zero64, 0) := ⟨Nat.zero_le _, fun _ => rfl⟩
  change (iterated.walk s (s.bits.length * 64 + 1) (zero64, 0)).map _ = _
  rw [bs_walk_values s hs _ _ hstate (by have := bs_stateValues_length s _ hstate; omega)]
  simp only [bs_stateValues, bs_wordValues_zero, List.nil_append, Int.natCast_zero,
    Int.add_zero, List.drop_zero]

/-- Membership in a chunk's value list selects exactly one of its true bit positions. -/
theorem bs_wordValues_mem (chunk n : Int) (word : U64) :
    n ∈ bs_wordValues chunk word ↔
      ∃ bit : Nat, bit < 64 ∧ (fromJInt word).getLsbD bit = true ∧ chunk * 64 + bit = n := by
  simp only [bs_wordValues, bs_wordPositions, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨bit, ⟨hbit, hvalue⟩, he⟩
    exact ⟨bit, hbit, hvalue, he⟩
  · rintro ⟨bit, hbit, hvalue, he⟩
    exact ⟨bit, ⟨hbit, hvalue⟩, he⟩

/-- The consecutive-chunk list reads exactly the indexed stored words. -/
theorem bs_chunkValues_indexed (offset n : Int) (words : List U64) :
    n ∈ bs_chunkValues offset words ↔
      ∃ i : Nat, i < words.length ∧ n ∈ bs_wordValues (offset + i) (words.getD i zero64) := by
  induction words generalizing offset with
  | nil => simp [bs_chunkValues]
  | cons word words ih =>
    simp only [bs_chunkValues, List.mem_append]
    constructor
    · intro h
      cases h with
      | inl h =>
        refine ⟨0, by simp, ?_⟩
        simpa only [Int.natCast_zero, Int.add_zero, List.getD_cons_zero] using h
      | inr h =>
        obtain ⟨i, hi, hv⟩ := (ih (offset + 1)).mp h
        refine ⟨i + 1, by simp only [List.length_cons]; omega, ?_⟩
        change n ∈ bs_wordValues (offset + ((i + 1 : Nat) : Int)) (words.getD i zero64)
        have ho : offset + ((i + 1 : Nat) : Int) = offset + 1 + i := by omega
        rw [ho]
        exact hv
    · rintro ⟨i, hi, hv⟩
      cases i with
      | zero =>
        left
        simpa only [Int.natCast_zero, Int.add_zero, List.getD_cons_zero] using hv
      | succ i =>
        right
        apply (ih (offset + 1)).mpr
        refine ⟨i, by simp only [List.length_cons] at hi; omega, ?_⟩
        change n ∈ bs_wordValues (offset + ((i + 1 : Nat) : Int)) (words.getD i zero64) at hv
        have ho : offset + ((i + 1 : Nat) : Int) = offset + 1 + i := by omega
        rw [ho] at hv
        exact hv

/-- Mathematical integer membership agrees with the fully expanded chunk-value list. -/
theorem bs_member_chunkValues (s : BitSet) (hs : WF s) (n : Int) :
    member s n = true ↔ n ∈ bs_chunkValues s.offset s.bits := by
  constructor
  · intro h
    rw [bs_member_range] at h
    by_cases hr : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
    · rw [if_pos hr] at h
      simp only [inInt, bitsGetindex, bs_int64_val n hr] at h
      by_cases hc : 1 ≤ div64 n - s.offset + 1 ∧ div64 n - s.offset + 1 ≤ s.bits.length
      · rw [if_pos hc] at h
        have hmod : mod64 n < 64 := by
          simpa only [bs_int64_val n hr] using bs_mod64_lt (int64 n)
        rw [bs_bitAt_eq _ _ hmod] at h
        let i : Nat := (div64 n - s.offset).toNat
        have hi : i < s.bits.length := by dsimp only [i]; omega
        have hindex : (div64 n - s.offset + 1).toNat - 1 = i := by dsimp only [i]; omega
        have hchunk : s.offset + (i : Int) = div64 n := by dsimp only [i]; omega
        apply (bs_chunkValues_indexed s.offset n s.bits).mpr
        refine ⟨i, hi, (bs_wordValues_mem _ _ _).mpr ⟨mod64 n, hmod, ?_, ?_⟩⟩
        · simpa only [bitsGet, hindex] using h
        · rw [hchunk, bs_div64_eq n hr, bs_mod64_eq n hr]
          have := Int.emod_nonneg n (by decide : (64 : Int) ≠ 0)
          omega
      · rw [if_neg hc] at h
        cases h
    · rw [if_neg hr] at h
      cases h
  · intro h
    obtain ⟨i, hi, hv⟩ := (bs_chunkValues_indexed s.offset n s.bits).mp h
    obtain ⟨bit, hbit, hvalue, he⟩ := (bs_wordValues_mem _ _ _).mp hv
    subst n
    let chunk : Int := s.offset + (i : Int)
    have hc : 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length := by
      dsimp only [chunk]
      omega
    have hr := bs_chunk_address_range s hs chunk bit hc hbit
    rw [bs_member_range, if_pos hr, bs_inInt_chunk, bs_int64_val _ hr,
      bs_assemble_div chunk bit hbit hr, bs_assemble_mod chunk bit hbit hr]
    unfold bs_chunkAt
    rw [if_pos hc]
    have hindex : (chunk - s.offset + 1).toNat - 1 = i := by dsimp only [chunk]; omega
    simpa only [bitsGet, hindex] using hvalue

/-- Frozen target: Integer membership is exactly membership in complete public BitSet iteration. -/
theorem BitsetscovBitsetIn_proven : JuliaLean.Proofs.base.bitset.Round1.BitSetMembershipMatchesIteration := by
  intro s n hs
  have h := bs_member_chunkValues s hs n
  rw [← bs_iterated_values s hs] at h
  have ha : member s n = true ↔ (iterated s).any (fun value => value.val = n) = true := by
    simpa only [List.mem_map, List.any_eq_true, decide_eq_true_eq] using h
  cases hm : member s n <;> cases hi : (iterated s).any (fun value => value.val = n) <;> simp_all

/-- Deleting a bit at or before a consumed chunk leaves the unscanned suffix unchanged. -/
theorem bs_deleteInt_drop (s : BitSet) (n : I64) (idx : Nat)
    (haddr : div64 n.val - s.offset + 1 ≤ (idx : Int)) :
    (deleteInt s n).bits.drop idx = s.bits.drop idx := by
  rw [bs_deleteInt_eq]
  split
  · rename_i hc
    simp only [setBit, bitsSet]
    rw [List.drop_set, if_pos (by omega)]
  · rfl

/-- Deletion of the just-emitted value preserves its already-prefetched iterator continuation. -/
theorem bs_deleteInt_stateValues (s : BitSet) (n : I64) (state : U64 × Nat)
    (haddr : div64 n.val - s.offset + 1 ≤ (state.2 : Int)) :
    bs_stateValues (deleteInt s n) state = bs_stateValues s state := by
  simp only [bs_stateValues, (bs_deleteInt_shape s n).1, bs_deleteInt_drop s n state.2 haddr]

/-- Storage-preserving deletion preserves the validity of an iterator continuation. -/
theorem bs_deleteInt_validState (s : BitSet) (n : I64) (state : U64 × Nat)
    (hstate : bs_validState s state) : bs_validState (deleteInt s n) state := by
  simpa only [bs_validState, (bs_deleteInt_shape s n).2] using hstate

/-- Filtering a sufficiently fueled continuation tests exactly its remaining values. -/
theorem bs_filterLoop_member (f : I64 → Bool) (fuel : Nat) (s : BitSet) (hs : WF s)
    (state : U64 × Nat) (hstate : bs_validState s state)
    (hbudget : (bs_stateValues s state).length ≤ fuel) (n : I64) :
    inInt n (filterLoop f fuel s state) =
      (inInt n s && (if n.val ∈ bs_stateValues s state then f n else true)) := by
  induction fuel generalizing s state with
  | zero =>
    have hz : bs_stateValues s state = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [filterLoop, hz, List.not_mem_nil, ite_false, Bool.and_true]
  | succ fuel ih =>
    have hstep := bs_iterate_semantics s hs state hstate
    cases hi : iterate s state with
    | none =>
      rw [hi] at hstep
      simp only [filterLoop, hi, hstep, List.not_mem_nil, ite_false, Bool.and_true]
    | some output =>
      obtain ⟨value, next⟩ := output
      rw [hi] at hstep
      simp only [filterLoop, hi]
      have htail : (bs_stateValues s next).length ≤ fuel := by
        rw [hstep.1, List.length_cons] at hbudget
        omega
      by_cases hf : f value = true
      · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
        rw [ih s hs next hstep.2.1 htail]
        by_cases he : n = value
        · subst n
          simp only [hstep.1, List.mem_cons, true_or, ite_true, hf, ite_self, Bool.and_true]
        · have hne : n.val ≠ value.val := by intro hv; exact he (Subtype.ext hv)
          simp only [hstep.1, List.mem_cons, hne, false_or]
      · have hfalse : f value = false := Bool.eq_false_iff.mpr hf
        simp only [hfalse, Bool.not_false, ite_true]
        have haddr : div64 value.val - s.offset + 1 ≤ (next.2 : Int) := by
          have := hstep.2.2.2
          omega
        have hcont := bs_deleteInt_stateValues s value next haddr
        rw [ih (deleteInt s value) (bs_deleteInt_WF s value hs) next
          (bs_deleteInt_validState s value next hstep.2.1) (by rw [hcont]; exact htail),
          bs_deleteInt_member, hcont]
        by_cases he : n = value
        · subst n
          simp [hstep.1, hfalse]
        · have hne : n.val ≠ value.val := by intro hv; exact he (Subtype.ext hv)
          simp [hstep.1, he, hne]

/-- Public Integer membership at a machine integer's value is the direct machine lookup. -/
theorem bs_member_intval (s : BitSet) (n : I64) : member s n.val = inInt n s := by
  rw [bs_member_range, if_pos n.property]
  have he : int64 n.val = n := Subtype.ext (bs_int64_val n.val n.property)
  rw [he]

/-- Frozen target: in-place filtering preserves well-formedness and precisely the accepted members. -/
theorem BitsetscovBitsetFilterInvariant_proven : JuliaLean.Proofs.base.bitset.Round1.BitSetFilterPreserves := by
  intro f s hs
  refine ⟨bs_filter_WF f s hs, ?_⟩
  intro n
  have hstate : bs_validState s (zero64, 0) := ⟨Nat.zero_le _, fun _ => rfl⟩
  unfold filter
  rw [bs_filterLoop_member f _ s hs _ hstate (by have := bs_stateValues_length s _ hstate; omega)]
  simp only [bs_stateValues, bs_wordValues_zero, List.nil_append, Int.natCast_zero,
    Int.add_zero, List.drop_zero]
  by_cases hn : inInt n s = true
  · have hm : member s n.val = true := by rw [bs_member_intval]; exact hn
    have hlist := (bs_member_chunkValues s hs n.val).mp hm
    rw [if_pos hlist]
  · have hz : inInt n s = false := Bool.eq_false_iff.mpr hn
    simp only [hz, Bool.false_and]

end JuliaLean.ChatGPT.Batch3.Group3
end JuliaLean.Proofs.base.bitset

namespace JuliaLean.ChatGPT.Batch4.Group16
set_option maxRecDepth 8192
open JuliaLean
open JuliaLean.Proofs.base.bitset
open JuliaLean.base.bitset
open JuliaLean.ChatGPT.Batch3.Group3
open JuliaLean.C JuliaLean.base.int

theorem BitsetscovBitsetCopy_proven : JuliaLean.Proofs.base.bitset.BitSetCopySpec := by
  intro dest src
  exact ⟨rfl, rfl, rfl⟩

theorem BitsetscovBitsetSizehint_proven : JuliaLean.Proofs.base.bitset.BitSetSizehintSpec := by
  intro t s n
  dsimp only
  unfold sizehint toInt JInt.convert
  split <;> split <;> rename_i h <;> simp only [h, dite_false] <;> rfl

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16

open JuliaLean JuliaLean.base.bitset JuliaLean.Proofs.base.bitset
open JuliaLean.ChatGPT.Batch3.Group3

theorem g16_bitsSet_length (words : List U64) (index : Nat) (word : U64) :
    (bitsSet words index word).length = words.length := by
  exact List.length_set

theorem g16_bitsSetFold_length {α : Type} (items : List α)
    (index : α → Nat) (word : α → U64) (words : List U64) :
    (items.foldl (fun out item => bitsSet out (index item) (word item)) words).length =
      words.length := by
  induction items generalizing words with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [bitsSet, List.length_set]

theorem g16_growend0_length (words : List U64) (n : Nat) :
    (growend0 words n).length = words.length + n := by
  unfold growend0
  rw [g16_bitsSetFold_length]
  simp only [bitsGrowEnd, List.length_append, List.length_replicate]

theorem g16_growbeg0_length (words : List U64) (n : Nat) :
    (growbeg0 words n).length = n + words.length := by
  unfold growbeg0
  rw [g16_bitsSetFold_length]
  simp only [bitsGrowBeg, List.length_append, List.length_replicate]

theorem g16_bitset_lookup_bounds (s : BitSet) (n : I64)
    (h : inInt n s = true) :
    indexWithin s.bits (div64 n.val - s.offset + 1) ∧
      0 ≤ n.val % 64 ∧ n.val % 64 < 64 := by
  have hb : 1 ≤ div64 n.val - s.offset + 1 ∧
      div64 n.val - s.offset + 1 ≤ s.bits.length := by
    unfold inInt bitsGetindex at h
    dsimp only at h
    split at h
    · assumption
    · contradiction
  exact ⟨hb, Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem g16_unionRangeBits_shape (s : BitSet) (a b : I64) :
    let ca := div64 a.val
    let cb := div64 b.val
    let origin := if s.offset = noOffset then ca else s.offset
    (unionRangeBits s a b).offset = (if ca - origin < 0 then ca else origin) ∧
    (unionRangeBits s a b).bits.length =
      (if ca - origin < 0 then (-(ca - origin)).toNat else 0) +
      (if cb - origin ≥ (s.bits.length : Int) then
        s.bits.length + (cb - origin - s.bits.length + 1).toNat else s.bits.length) := by
  dsimp only
  unfold unionRangeBits
  dsimp only
  split <;> split <;> split <;> split <;>
    simp only [g16_growend0_length, g16_growbeg0_length, g16_bitsSet_length,
      Nat.zero_add, g16_bitsSetFold_length, and_self]

theorem g16_unionRangeBits_bounds (s : BitSet) (a b : I64) (hs : WF s)
    (hab : a.val ≤ b.val) :
    indexWithin (unionRangeBits s a b).bits
        (div64 a.val - (unionRangeBits s a b).offset + 1) ∧
    indexWithin (unionRangeBits s a b).bits
        (div64 b.val - (unionRangeBits s a b).offset + 1) ∧
    ∀ i ∈ intRange (div64 a.val - (unionRangeBits s a b).offset + 1)
        (div64 b.val - (unionRangeBits s a b).offset + 1),
      indexWithin (unionRangeBits s a b).bits i := by
  have order : div64 a.val ≤ div64 b.val := by
    rw [bs_div64_eq a.val a.property, bs_div64_eq b.val b.property]
    omega
  have shape := g16_unionRangeBits_shape s a b
  dsimp only at shape
  by_cases ho : s.offset = noOffset
  · have hempty := hs.1 ho
    simp only [ho, Int.sub_self, Int.lt_irrefl, ↓reduceIte,
      hempty, List.length_nil, Int.natCast_zero, Int.sub_zero, Nat.zero_add] at shape
    rcases shape with ⟨hoff, hlen⟩
    rw [hoff]
    unfold indexWithin
    have hnonneg : 0 ≤ div64 b.val - div64 a.val := by omega
    simp only [hnonneg, ↓reduceIte] at hlen
    rw [hlen]
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    have hmem := (bs_intRange_mem _ _ _).mp hi
    omega
  · simp only [ho, ↓reduceIte] at shape
    rcases shape with ⟨hoff, hlen⟩
    unfold indexWithin
    rw [hoff, hlen]
    by_cases hl : div64 a.val - s.offset < 0 <;>
      by_cases hr : div64 b.val - s.offset ≥ (s.bits.length : Int) <;>
      simp only [hl, hr, ↓reduceIte, Int.natCast_add, Int.natCast_zero] <;>
      refine ⟨by omega, by omega, ?_⟩ <;>
      intro i hi <;>
      have hmem := (bs_intRange_mem _ _ _).mp hi <;> omega

theorem MemsafetyBitsetIndexing_proven :
    JuliaLean.Proofs.base.bitset.BitSetAccessesInBounds := by
  refine ⟨g16_bitset_lookup_bounds, ?_, ?_, g16_unionRangeBits_bounds,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro words n i hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    rw [g16_growend0_length]
    omega
  · intro words n i hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    rw [g16_growbeg0_length]
    omega
  · intro a1 a2 b1 b2 i hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    omega
  · intro a1 a2 b1 b2 flag
    dsimp only
    intro hd hf
    unfold spanWithin bitsGrowEnd
    simp only [List.length_append, List.length_replicate, Int.natCast_add]
    by_cases hl : (a1.length : Int) + 1 ≤ b2 - b1 <;>
      simp only [hl, ↓reduceIte] <;> omega
  · intro a1 a2 b1 b2 flag
    dsimp only
    intro hd hf
    unfold spanWithin bitsGrowBeg
    simp only [List.length_append, List.length_replicate, Int.natCast_add]
    omega
  · intro s1 s2 h1 h2 ho
    dsimp only
    intro hp
    unfold spanWithin
    by_cases h : max 0 ((s1.bits.length : Int) + s1.offset - s2.offset) ≥
        (s2.bits.length : Int) <;>
      simp only [h, ↓reduceIte] at hp ⊢ <;> omega
  · intro words lo hi i hlo hhi hm
    have hb := (bs_intRange_mem _ _ _).mp hm
    unfold indexWithin
    omega
  · intro a b i ha hb hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    omega
  · intro a b i ha hb hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    omega
  · intro a b i ha hb hi
    have hm := (bs_intRange_mem _ _ _).mp hi
    unfold indexWithin
    omega
  · intro s idx hi
    unfold indexWithin
    omega

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16.PureBitset

theorem ones_bit (k : Nat) :
    (~~~(0 : BitVec 64)).getLsbD k = decide (k < 64) := by
  rw [BitVec.getLsbD_not]
  change (decide (k < 64) && !(0#64).getLsbD k) = decide (k < 64)
  rw [BitVec.getLsbD_zero, Bool.not_false, Bool.and_true]

theorem first_mask_bit (i k : Nat) (hi : i < 64) (hk : k < 64) :
    (((~~~(0 : BitVec 64)) >>> i) <<< i).getLsbD k = decide (i ≤ k) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, ones_bit]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

theorem last_mask_bit (j k : Nat) (hj : j < 64) (hk : k < 64) :
    (((~~~(0 : BitVec 64)) <<< (63 - j)) >>> (63 - j)).getLsbD k =
      decide (k ≤ j) := by
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, ones_bit]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

theorem single_mask_bit (i j k : Nat) (hi : i < 64) (hj : j < 64)
    (hij : i ≤ j) (hk : k < 64) :
    (((((~~~(0 : BitVec 64)) >>> i) <<< (i + 63 - j)) >>> (63 - j)).getLsbD k) =
      decide (i ≤ k ∧ k ≤ j) := by
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, ones_bit]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

theorem integer_interval (a b n : Int) (hab : a ≤ b) :
    (if a / 64 = b / 64 then
      decide (n / 64 = a / 64 ∧ a % 64 ≤ n % 64 ∧ n % 64 ≤ b % 64)
    else decide ((n / 64 = a / 64 ∧ a % 64 ≤ n % 64) ∨
      (n / 64 = b / 64 ∧ n % 64 ≤ b % 64) ∨
      a / 64 < n / 64 ∧ n / 64 < b / 64)) = decide (a ≤ n ∧ n ≤ b) := by
  split <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq] <;> omega

end JuliaLean.ChatGPT.Batch4.Group16.PureBitset

namespace JuliaLean.ChatGPT.Batch4.Group16
open JuliaLean JuliaLean.Proofs.base.bitset JuliaLean.base.bitset
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def g16_except_decidable {E A : Type} [DecidableEq E] [DecidableEq A]
    (left right : Except E A) : Decidable (left = right) :=
  match left, right with
  | .ok a, .ok b =>
    match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun he => h (Except.ok.inj he))
  | .error a, .error b =>
    match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun he => h (Except.error.inj he))
  | .ok _, .error _ => .isFalse (by intro h; cases h)
  | .error _, .ok _ => .isFalse (by intro h; cases h)

theorem BitarraysBitsetSymdiffDuplicates_refuted :
    ¬ JuliaLean.Proofs.base.bitset.BitSetSymdiffAgrees := by
  intro h
  have run : symdiffIterator new [1, 1] = .ok ⟨[zero64], 0⟩  := by
    letI : Decidable (symdiffIterator new [1, 1] = .ok ⟨[zero64], 0⟩) :=
      g16_except_decidable _ _
    decide
  have bad := h new [1, 1] (int64 1) ⟨[zero64], 0⟩ run
  change false = true at bad
  cases bad

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch8.Group6
section
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
open JuliaLean
open JuliaLean.Proofs.base.bitset
open JuliaLean.base.bitset
open JuliaLean.ChatGPT.Batch3.Group3
open JuliaLean.C JuliaLean.base.int

/-- A range of already-zero chunk writes has no observable effect. -/
theorem bs8_fold_zero_unchanged (items : List Int) (words : List U64)
    (h : ∀ i ∈ items, bitsSet words i.toNat zero64 = words) :
    items.foldl (fun out i => bitsSet out i.toNat zero64) words = words := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, h i (by simp only [List.mem_cons, true_or])]
    apply ih
    intro j hj
    exact h j (List.mem_cons_of_mem i hj)

/-- The appended zero part is unchanged by a write of zero within that part. -/
theorem bs8_set_append_zero (words : List U64) (n i : Nat)
    (hlo : words.length < i) (hhi : i ≤ words.length + n) :
    bitsSet (words ++ List.replicate n zero64) i zero64 =
      words ++ List.replicate n zero64 := by
  unfold bitsSet
  have hbound : i - 1 < (words ++ List.replicate n zero64).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hget : (words ++ List.replicate n zero64)[i - 1] = zero64 := by
    rw [List.getElem_append_right (by omega), List.getElem_replicate]
  have same := List.set_getElem_self hbound
  simpa only [hget] using same

/-- The prepended zero part is unchanged by a write of zero within that part. -/
theorem bs8_set_prepend_zero (words : List U64) (n i : Nat)
    (hlo : 1 ≤ i) (hhi : i ≤ n) :
    bitsSet (List.replicate n zero64 ++ words) i zero64 =
      List.replicate n zero64 ++ words := by
  unfold bitsSet
  have hbound : i - 1 < (List.replicate n zero64 ++ words).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hleft : i - 1 < (List.replicate n zero64).length := by
    simp only [List.length_replicate]
    omega
  have hget : (List.replicate n zero64 ++ words)[i - 1] = zero64 := by
    rw [List.getElem_append_left hleft, List.getElem_replicate]
  have same := List.set_getElem_self hbound
  simpa only [hget] using same

/-- End-growth is exact zero extension, including its explicit initialization loop. -/
theorem bs8_growend0_eq (words : List U64) (n : Nat) :
    growend0 words n = words ++ List.replicate n zero64 := by
  unfold growend0 bitsGrowEnd
  apply bs8_fold_zero_unchanged
  intro i hi
  obtain ⟨hlo, hhi⟩ := (bs_intRange_mem _ _ _).mp hi
  simp only [List.length_append, List.length_replicate] at hhi
  apply bs8_set_append_zero <;> omega

/-- Beginning-growth is exact zero extension with the old chunk order retained. -/
theorem bs8_growbeg0_eq (words : List U64) (n : Nat) :
    growbeg0 words n = List.replicate n zero64 ++ words := by
  unfold growbeg0 bitsGrowBeg
  apply bs8_fold_zero_unchanged
  intro i hi
  obtain ⟨hlo, hhi⟩ := (bs_intRange_mem _ _ _).mp hi
  apply bs8_set_prepend_zero <;> omega

/-- A single set bit is the disjunction of the old bit and its mask position. -/
theorem bs8_set_bit (word : U64) (bit k : Nat) (hb : bit < 64) :
    (fromJInt (or_int word (shl_int (uint64 1) (int64 bit)))).getLsbD k =
      ((fromJInt word).getLsbD k || decide (k = bit)) := by
  simp only [or_int, jlOrInt, bs_roundtrip_U64, BitVec.getLsbD_or]
  rw [bs_mask_bit bit k hb]

/-- Updating an existing chunk to set a bit inserts exactly its addressed integer. -/
theorem bs8_setBit_member (s : BitSet) (n x : I64)
    (hn : 1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length) :
    inInt x { s with bits := (setBit s.bits true
      (div64 n.val - s.offset + 1).toNat (mod64 n.val)) } =
      (inInt x s || decide (x = n)) := by
  by_cases hx : 1 ≤ div64 x.val - s.offset + 1 ∧ div64 x.val - s.offset + 1 ≤ s.bits.length
  · simp only [inInt, bitsGetindex, bs_setBit_length]
    rw [if_pos hx, if_pos hx, bs_bitAt_eq _ _ (bs_mod64_lt x), bs_bitAt_eq _ _ (bs_mod64_lt x)]
    unfold setBit
    simp only [ite_true]
    by_cases hc : (div64 x.val - s.offset + 1).toNat = (div64 n.val - s.offset + 1).toNat
    · rw [hc, bs_bitsSet_same s.bits _ _ (by omega) (by omega), bs8_set_bit _ _ _ (bs_mod64_lt n)]
      have hdiv : div64 x.val = div64 n.val := by omega
      have hkey : mod64 x.val = mod64 n.val ↔ x = n := by
        constructor
        · exact bs_address_injective x n hdiv
        · intro he
          simp only [he]
      simp only [hkey]
    · rw [bs_bitsSet_other s.bits _ _ _ (by omega) (by omega) hc]
      have hne : x ≠ n := by intro he; subst x; exact hc rfl
      simp only [hne, decide_false, Bool.or_false]
  · have hne : x ≠ n := by intro he; subst x; exact hx hn
    simp only [inInt, bitsGetindex, bs_setBit_length, hx, ite_false,
      hne, decide_false, Bool.or_false]

/-- Reading a zero vector with zero default is zero at every natural index. -/
theorem bs8_getD_zeros (n k : Nat) :
    (List.replicate n zero64).getD k zero64 = zero64 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

/-- Appending zero chunks preserves all defaulted reads. -/
theorem bs8_getD_append_zeros (words : List U64) (n k : Nat) :
    (words ++ List.replicate n zero64).getD k zero64 = words.getD k zero64 := by
  induction words generalizing k with
  | nil => exact bs8_getD_zeros n k
  | cons word rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

/-- An index past the end reads the explicit zero default. -/
theorem bs8_getD_large (words : List U64) (k : Nat) (h : words.length ≤ k) :
    words.getD k zero64 = zero64 := by
  induction words generalizing k with
  | nil => rfl
  | cons word rest ih =>
    cases k with
    | zero => simp only [List.length_cons] at h; omega
    | succ k => exact ih k (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using h)

/-- Prepending zeros shifts each original defaulted read by the new prefix length. -/
theorem bs8_getD_prepend_zeros (words : List U64) (n k : Nat) :
    (List.replicate n zero64 ++ words).getD (n + k) zero64 = words.getD k zero64 := by
  induction n with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ n ih =>
    rw [Nat.succ_add]
    exact ih

/-- Every index in a newly prepended prefix reads zero. -/
theorem bs8_getD_prepend_low (words : List U64) (n k : Nat) (h : k < n) :
    (List.replicate n zero64 ++ words).getD k zero64 = zero64 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (by omega)

/-- Zero-extension at the high end adds no members. -/
theorem bs8_append_zeros_member (words : List U64) (offset : Int) (n : Nat) (x : I64) :
    inInt x ⟨words ++ List.replicate n zero64, offset⟩ = inInt x ⟨words, offset⟩ := by
  simp only [inInt, bitsGetindex, List.length_append, List.length_replicate]
  by_cases old : 1 ≤ div64 x.val - offset + 1 ∧ div64 x.val - offset + 1 ≤ words.length
  · rw [if_pos old, if_pos (by omega)]
    unfold bitsGet
    rw [bs8_getD_append_zeros]
  · rw [if_neg old]
    split
    · rename_i fresh
      unfold bitsGet
      rw [bs8_getD_append_zeros, bs8_getD_large _ _ (by omega)]
      rw [bs_bitAt_eq _ _ (bs_mod64_lt x), bs_zero_bit]
    · rfl

/-- Zero-extension at the low end preserves the absolute coordinate of every old chunk. -/
theorem bs8_prepend_zeros_member (words : List U64) (offset : Int) (n : Nat) (x : I64) :
    inInt x ⟨List.replicate n zero64 ++ words, offset - n⟩ = inInt x ⟨words, offset⟩ := by
  simp only [inInt, bitsGetindex, List.length_append, List.length_replicate]
  have coord : div64 x.val - (offset - (n : Int)) + 1 = div64 x.val - offset + 1 + n := by omega
  rw [coord]
  by_cases old : 1 ≤ div64 x.val - offset + 1 ∧ div64 x.val - offset + 1 ≤ words.length
  · rw [if_pos old, if_pos (by omega)]
    unfold bitsGet
    have shifted : (div64 x.val - offset + 1 + n).toNat - 1 =
        n + ((div64 x.val - offset + 1).toNat - 1) := by omega
    rw [shifted, bs8_getD_prepend_zeros]
  · rw [if_neg old]
    split
    · rename_i fresh
      unfold bitsGet
      rw [bs8_getD_prepend_low _ _ _ (by omega)]
      rw [bs_bitAt_eq _ _ (bs_mod64_lt x), bs_zero_bit]
    · rfl

/-- Equal offsets and vector lengths transfer the representation invariant. -/
theorem bs8_WF_of_shape (source target : BitSet) (h : WF source)
    (hoff : target.offset = source.offset) (hlen : target.bits.length = source.bits.length) :
    WF target := by
  constructor
  · intro hs
    apply List.length_eq_zero_iff.mp
    rw [hlen, h.1 (hoff ▸ hs)] <;> rfl
  · intro hs
    have old : source.offset ≠ noOffset := by simpa only [hoff] using hs
    simpa only [hoff, hlen] using h.2 old

/-- The intermediate storage prepared by insertion before its single bit write. -/
def bs8_pushStorage (s : BitSet) (n : I64) : BitSet :=
  let chunk := div64 n.val
  let delta := chunk - s.offset
  if s.offset = noOffset then ⟨[zero64], chunk⟩
  else if delta ≥ (s.bits.length : Int) then
    ⟨s.bits ++ List.replicate (delta - s.bits.length + 1).toNat zero64, s.offset⟩
  else if delta < 0 then
    ⟨List.replicate (-delta).toNat zero64 ++ s.bits, chunk⟩
  else s

/-- Every machine integer selects a chunk in the full signed storage-coordinate interval. -/
theorem bs8_div64_bounds (n : I64) :
    -(2 ^ 57) ≤ div64 n.val ∧ div64 n.val + 1 ≤ 2 ^ 57 := by
  rw [bs_div64_eq n.val n.property]
  have hn := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hn
  omega

/-- Insertion is exactly storage preparation followed by an in-bounds bit write. -/
theorem bs8_setint_true_eq (s : BitSet) (n : I64) (hs : WF s) :
    setint s n true =
      let ready := bs8_pushStorage s n
      { ready with bits := (setBit ready.bits true
        (div64 n.val - ready.offset + 1).toNat (mod64 n.val)) } := by
  have hn := bs8_div64_bounds n
  by_cases sentinel : s.offset = noOffset
  · have empty := hs.1 sentinel
    have branch : div64 n.val - s.offset ≥ (s.bits.length : Int) := by
      rw [sentinel, empty]
      unfold noOffset
      simp only [List.length_nil, Int.natCast_zero]
      omega
    unfold setint bs8_pushStorage
    rw [if_pos branch]
    simp only [sentinel, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, empty, List.length_nil, Int.natCast_zero,
      Int.sub_self, Int.zero_sub, Int.sub_zero, Int.zero_add, Int.add_zero,
      Int.toNat_one, bs8_growend0_eq, List.nil_append, List.replicate_one]
  · unfold setint bs8_pushStorage
    simp only [sentinel, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    split
    · rename_i high
      simp only [high, ↓reduceIte, bs8_growend0_eq]
    · rename_i lowHigh
      split
      · rename_i low
        simp only [low, ↓reduceIte, bs8_growbeg0_eq, Int.sub_self, Int.zero_add, Int.toNat_one]
        congr 1
        omega
      · rename_i middle
        simp only [middle, ↓reduceIte]

/-- Extending storage alone preserves every old member. -/
theorem bs8_pushStorage_member (s : BitSet) (n x : I64) (hs : WF s) :
    inInt x (bs8_pushStorage s n) = inInt x s := by
  unfold bs8_pushStorage
  dsimp only
  split
  · rename_i sentinel
    have empty := hs.1 sentinel
    have left := bs8_append_zeros_member [] (div64 n.val) 1 x
    have leftEmpty : inInt x ⟨[zero64], div64 n.val⟩ = false := by
      simpa only [List.nil_append, List.replicate_one, bs_inInt_nil] using left
    have rightEmpty : inInt x s = false := by
      unfold inInt bitsGetindex
      simp only [empty, List.length_nil, Int.natCast_zero]
      rw [if_neg (by omega)]
    exact leftEmpty.trans rightEmpty.symm
  · split
    · exact bs8_append_zeros_member _ _ _ _
    · split
      · rename_i low
        have offset : s.offset - ((-(div64 n.val - s.offset)).toNat : Int) = div64 n.val := by omega
        simpa only [offset] using
          bs8_prepend_zeros_member s.bits s.offset (-(div64 n.val - s.offset)).toNat x
      · rfl

/-- The prepared storage is well formed and contains the index about to be written. -/
theorem bs8_pushStorage_bounds (s : BitSet) (n : I64) (hs : WF s) :
    WF (bs8_pushStorage s n) ∧
      1 ≤ div64 n.val - (bs8_pushStorage s n).offset + 1 ∧
      div64 n.val - (bs8_pushStorage s n).offset + 1 ≤ (bs8_pushStorage s n).bits.length := by
  have hn := bs8_div64_bounds n
  have nonsentinel : div64 n.val ≠ noOffset := by unfold noOffset; omega
  unfold bs8_pushStorage
  dsimp only
  split
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro impossible
      exact False.elim (nonsentinel impossible)
    · intro _
      exact hn
    · simp only [Int.sub_self, Int.zero_add]
      omega
    · simp only [Int.sub_self, Int.zero_add, List.length_cons, List.length_nil]
      omega
  · rename_i sentinel
    have old := hs.2 sentinel
    split
    · rename_i high
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro impossible
        exact False.elim (sentinel impossible)
      · intro _
        simp only [List.length_append, List.length_replicate, Int.natCast_add]
        exact ⟨old.1, by omega⟩
      · dsimp only
        omega
      · simp only [List.length_append, List.length_replicate, Int.natCast_add]
        omega
    · rename_i high
      split
      · rename_i low
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · intro impossible
          exact False.elim (nonsentinel impossible)
        · intro _
          simp only [List.length_append, List.length_replicate, Int.natCast_add]
          exact ⟨hn.1, by omega⟩
        · simp only [Int.sub_self, Int.zero_add]
          omega
        · simp only [Int.sub_self, Int.zero_add, List.length_append, List.length_replicate,
            Int.natCast_add]
          omega
      · rename_i middle
        exact ⟨hs, by omega, by omega⟩

/-- A successful insertion preserves the representation invariant. -/
theorem bs8_setint_true_WF (s : BitSet) (n : I64) (hs : WF s) : WF (setint s n true) := by
  rw [bs8_setint_true_eq s n hs]
  apply bs8_WF_of_shape (bs8_pushStorage s n)
  · exact (bs8_pushStorage_bounds s n hs).1
  · rfl
  · exact bs_setBit_length _ _ _ _

/-- Insertion adds exactly the addressed machine integer. -/
theorem bs8_setint_true_member (s : BitSet) (n x : I64) (hs : WF s) :
    inInt x (setint s n true) = (inInt x s || decide (x = n)) := by
  rw [bs8_setint_true_eq s n hs]
  rw [bs8_setBit_member _ n x (bs8_pushStorage_bounds s n hs).2]
  rw [bs8_pushStorage_member s n x hs]

/-- Successful checked conversion exposes the original mathematical integer. -/
theorem bs8_toInt_success (n : Int) (index : I64) (run : toInt n = .ok index) :
    inIntRange n ∧ index.val = n := by
  by_cases h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
  · simp only [toInt, JInt.convert, h, dite_true] at run
    cases run
    exact ⟨h, rfl⟩
  · simp only [toInt, JInt.convert, h, dite_false] at run
    cases run

/-- Machine insertion has the same contract for mathematical-integer membership. -/
theorem bs8_setint_true_member_integer (s : BitSet) (key : I64) (n : Int) (hs : WF s) :
    member (setint s key true) n = (member s n || decide (n = key.val)) := by
  rw [bs_member_range, bs_member_range]
  by_cases h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
  · rw [if_pos h, if_pos h, bs8_setint_true_member s key (int64 n) hs]
    have he : int64 n = key ↔ n = key.val := by
      constructor
      · intro eq
        have hv := congrArg Subtype.val eq
        rw [bs_int64_val n h] at hv
        exact hv
      · intro eq
        apply Subtype.ext
        rw [bs_int64_val n h, eq]
    simp only [he]
  · have ne : n ≠ key.val := by intro eq; subst n; exact h key.property
    simp only [h, ite_false, ne, decide_false, Bool.or_false]

/-- A normally returning push converts its key and inserts exactly that value. -/
theorem bs8_push_success (s out : BitSet) (key : Int) (hs : WF s)
    (run : push s key = .ok out) :
    inIntRange key ∧ WF out ∧ ∀ n, member out n = (member s n || decide (n = key)) := by
  unfold push at run
  cases converted : toInt key with
  | error err =>
    rw [converted] at run
    change (Except.error err : Result BitSet) = .ok out at run
    cases run
  | ok index =>
    rw [converted] at run
    change (Except.ok (setint s index true) : Result BitSet) = .ok out at run
    cases run
    have hc := bs8_toInt_success key index converted
    refine ⟨hc.1, bs8_setint_true_WF s index hs, ?_⟩
    intro n
    rw [bs8_setint_true_member_integer s index n hs, hc.2]

/-- The mathematical seed update exactly matches out-of-range and ordinary deletion. -/
theorem bs8_delete_seed (s : BitSet) (key n : Int) :
    member (deleteInteger s key) n =
      (if isConvertibleInt key && decide (n = key) then false else member s n) := by
  cases converted : isConvertibleInt key with
  | false => simp only [deleteInteger, converted, Bool.false_eq_true, ite_false, Bool.false_and]
  | true =>
    rw [bs_deleteInteger_member]
    by_cases same : n = key <;>
      simp only [converted, same, decide_true, decide_false, Bool.true_and,
        ite_true, Bool.false_eq_true, ite_false, ne_eq, not_true_eq_false,
        not_false_eq_true, Bool.and_false, Bool.and_true]

/-- Sequential push/delete operations preserve the invariant and their exact membership fold. -/
theorem bs8_pushDelete_sequence (s : BitSet) (ops : List (Bool × Int)) (out : BitSet)
    (hs : WF s) (run : Round1.applyPushDeleteIntegerOps s ops = .ok out) :
    WF out ∧ ∀ n, member out n = Round1.idealPushDeleteMember s ops n := by
  induction ops generalizing s out with
  | nil =>
    change (Except.ok s : Result BitSet) = .ok out at run
    cases run
    exact ⟨hs, fun _ => rfl⟩
  | cons operation rest ih =>
    rcases operation with ⟨insert, key⟩
    cases insert with
    | false =>
      change Round1.applyPushDeleteIntegerOps (deleteInteger s key) rest = .ok out at run
      have tail := ih (deleteInteger s key) out (bs_deleteInteger_WF s key hs) run
      refine ⟨tail.1, ?_⟩
      intro n
      simpa only [Round1.idealPushDeleteMember, List.foldl_cons, bs8_delete_seed]
        using tail.2 n
    | true =>
      simp only [Round1.applyPushDeleteIntegerOps] at run
      cases inserted : push s key with
      | error err =>
        rw [inserted] at run
        change (Except.error err : Result BitSet) = .ok out at run
        cases run
      | ok next =>
        rw [inserted] at run
        change Round1.applyPushDeleteIntegerOps next rest = .ok out at run
        have step := bs8_push_success s next key hs inserted
        have tail := ih next out step.2.1 run
        refine ⟨tail.1, ?_⟩
        intro n
        have converted : isConvertibleInt key = true := by
          exact decide_eq_true step.1
        have seed : member next n =
            (if isConvertibleInt key && decide (n = key) then true else member s n) := by
          rw [step.2.2 n]
          by_cases same : n = key <;>
            simp only [converted, same, decide_true, decide_false, Bool.true_and,
              ite_true, Bool.false_eq_true, ite_false, Bool.or_true, Bool.or_false]
        simpa only [Round1.idealPushDeleteMember, List.foldl_cons, seed] using tail.2 n

/-- The exact frozen push/delete target follows from the stronger sequential invariant. -/
theorem BitarraysBitsetPushDelete_proven :
    JuliaLean.Proofs.base.bitset.Round3.BitSetPushDeleteAgrees := by
  intro s ops n out wellFormed spanFits run
  exact (bs8_pushDelete_sequence s ops out wellFormed run).2 n


/-- Toggling an existing membership bit preserves the representation invariant. -/
theorem bs8_toggle_WF (s : BitSet) (key : I64) (hs : WF s) :
    WF (setint s key (!(inInt key s))) := by
  cases present : inInt key s with
  | false => exact bs8_setint_true_WF s key hs
  | true => exact bs_deleteInt_WF s key hs

/-- Toggling changes exactly the selected machine-integer membership. -/
theorem bs8_toggle_member (s : BitSet) (key n : I64) (hs : WF s) :
    inInt n (setint s key (!(inInt key s))) = (inInt n s ^^ decide (n = key)) := by
  cases present : inInt key s with
  | false =>
    rw [show (!false) = true from rfl, bs8_setint_true_member s key n hs]
    by_cases same : n = key
    · subst n
      have selfDecision : decide (key = key) = true := decide_eq_true rfl
      simp only [present, selfDecision, decide_true, Bool.or_true, Bool.false_xor]
    · simp only [same, decide_false, Bool.or_false, Bool.xor_false]
  | true =>
    rw [show (!true) = false from rfl]
    change inInt n (deleteInt s key) = _
    rw [bs_deleteInt_member]
    by_cases same : n = key
    · subst n
      have selfDecision : decide (key = key) = true := decide_eq_true rfl
      have neDecision : decide (key ≠ key) = false := decide_eq_false (fun h => h rfl)
      simp only [present, selfDecision, neDecision, decide_true, Bool.and_false,
        Bool.xor_true, Bool.not_true]
    · simp only [same, decide_false, ne_eq, not_false_eq_true, decide_true,
        Bool.and_true, Bool.xor_false]

/-- Toggling has the same exact equation for mathematical-integer membership. -/
theorem bs8_toggle_member_integer (s : BitSet) (key : I64) (n : Int) (hs : WF s) :
    member (setint s key (!(inInt key s))) n = (member s n ^^ decide (n = key.val)) := by
  rw [bs_member_range, bs_member_range]
  by_cases h : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max
  · rw [if_pos h, if_pos h, bs8_toggle_member s key (int64 n) hs]
    have he : int64 n = key ↔ n = key.val := by
      constructor
      · intro eq
        have hv := congrArg Subtype.val eq
        rw [bs_int64_val n h] at hv
        exact hv
      · intro eq
        apply Subtype.ext
        rw [bs_int64_val n h, eq]
    simp only [he]
  · have ne : n ≠ key.val := by intro eq; subst n; exact h key.property
    simp only [h, ite_false, ne, decide_false, Bool.xor_false]

/-- A successful scalar symmetric difference converts and toggles exactly its key. -/
theorem bs8_intSymdiff_success (s out : BitSet) (key : Int) (hs : WF s)
    (run : intSymdiff s key = .ok out) :
    WF out ∧ ∀ n, member out n = (member s n ^^ decide (n = key)) := by
  unfold intSymdiff at run
  cases converted : toInt key with
  | error err =>
    rw [converted] at run
    change (Except.error err : Result BitSet) = .ok out at run
    cases run
  | ok index =>
    rw [converted] at run
    change (Except.ok (setint s index (!(inInt index s))) : Result BitSet) = .ok out at run
    cases run
    have hc := bs8_toInt_success key index converted
    refine ⟨bs8_toggle_WF s index hs, ?_⟩
    intro n
    rw [bs8_toggle_member_integer s index n hs, hc.2]

/-- Distinct iterable values toggle exactly their membership set. -/
theorem bs8_symdiffLoop_success (s : BitSet) (keys : List Int) (out : BitSet)
    (hs : WF s) (distinct : keys.Nodup) (run : symdiffLoop s keys = .ok out) :
    WF out ∧ ∀ n, member out n = (member s n ^^ decide (n ∈ keys)) := by
  induction keys generalizing s out with
  | nil =>
    change (Except.ok s : Result BitSet) = .ok out at run
    cases run
    refine ⟨hs, ?_⟩
    intro n
    simp only [List.not_mem_nil, decide_false, Bool.xor_false]
  | cons key rest ih =>
    obtain ⟨notRepeated, tailDistinct⟩ := List.nodup_cons.mp distinct
    unfold symdiffLoop at run
    cases stepRun : intSymdiff s key with
    | error err =>
      rw [stepRun] at run
      change (Except.error err : Result BitSet) = .ok out at run
      cases run
    | ok next =>
      rw [stepRun] at run
      change symdiffLoop next rest = .ok out at run
      have step := bs8_intSymdiff_success s next key hs stepRun
      have tail := ih next out step.1 tailDistinct run
      refine ⟨tail.1, ?_⟩
      intro n
      rw [tail.2 n, step.2 n]
      by_cases same : n = key
      · subst n
        simp only [notRepeated, decide_false, Bool.xor_false, List.mem_cons,
          true_or, decide_true]
      · simp only [same, decide_false, Bool.xor_false, List.mem_cons, false_or]

/-- The exact frozen AbstractSet symmetric-difference contract. -/
theorem BitsetscovBitsetSymdiffSet_proven : JuliaLean.Proofs.base.bitset.BitSetSymdiffSetSpec := by
  intro s keys n hs distinct valid out run
  exact (bs8_symdiffLoop_success s keys out hs distinct run).2 n.val


/-- Every representable mathematical key converts to its exact machine value. -/
theorem bs8_push_of_range (s : BitSet) (key : Int) (h : inIntRange key) :
    push s key = .ok (setint s (int64 key) true) := by
  unfold push toInt JInt.convert
  have range : IntTy.i64.min ≤ key ∧ key ≤ IntTy.i64.max := h
  rw [dif_pos range]
  have converted : (⟨key, range⟩ : I64) = int64 key := by
    apply Subtype.ext
    exact (bs_int64_val key range).symm
  rw [converted] <;> rfl

/-- The iterable union executes no operations on an empty input. -/
theorem bs8_unionIterator_nil (s : BitSet) : unionIterator s [] = .ok s := rfl

/-- The source loop performs one push and then consumes its remaining iterable. -/
theorem bs8_unionIterator_cons (s : BitSet) (key : Int) (rest : List Int) :
    unionIterator s (key :: rest) = (do
      let next ← push s key
      unionIterator next rest) := by
  unfold unionIterator
  dsimp only
  rw [List.forIn_cons]
  cases step : push s key <;> rfl

/-- Iterable union of representable keys preserves the invariant and set membership. -/
theorem bs8_unionIterator_valid (s : BitSet) (keys : List Int) (hs : WF s)
    (valid : ∀ key ∈ keys, inIntRange key) :
    ∃ out, unionIterator s keys = .ok out ∧ WF out ∧
      ∀ n, member out n = (member s n || decide (n ∈ keys)) := by
  induction keys generalizing s with
  | nil =>
    refine ⟨s, rfl, hs, ?_⟩
    intro n
    simp only [List.not_mem_nil, decide_false, Bool.or_false]
  | cons key rest ih =>
    have keyValid := valid key (by simp only [List.mem_cons, true_or])
    have stepRun := bs8_push_of_range s key keyValid
    have step := bs8_push_success s (setint s (int64 key) true) key hs stepRun
    obtain ⟨out, tailRun, tailWF, tailMember⟩ :=
      ih (setint s (int64 key) true) step.2.1
        (fun n hn => valid n (List.mem_cons_of_mem key hn))
    refine ⟨out, ?_, tailWF, ?_⟩
    · rw [bs8_unionIterator_cons, stepRun]
      exact tailRun
    · intro n
      rw [tailMember n, step.2.2 n]
      simp only [List.mem_cons, Bool.decide_or, Bool.or_assoc]

/-- Variadic push and iterable union use the same source-level insertion loop. -/
theorem bs8_pushMany_eq_unionIterator (s : BitSet) (keys : List Int) :
    pushMany s keys = unionIterator s keys := rfl

/-- The valid variadic-push clause is available once its missing initial invariant is supplied. -/
theorem bs8_pushMany_valid (s : BitSet) (keys : List Int) (hs : WF s)
    (valid : ∀ key ∈ keys, inIntRange key) :
    ∃ out, pushMany s keys = .ok out ∧ WF out ∧
      ∀ n, member out n = (member s n || decide (n ∈ keys)) := by
  rw [bs8_pushMany_eq_unionIterator]
  exact bs8_unionIterator_valid s keys hs valid

theorem bs8_unionIterator_invalid (s : BitSet) (keys : List Int)
    (invalid : ∃ key ∈ keys, ¬ inIntRange key) :
    unionIterator s keys = .error (.julia (.inexactError "Int64")) := by
  induction keys generalizing s with
  | nil => simpa using invalid
  | cons key rest ih =>
    rw [bs8_unionIterator_cons]
    by_cases valid : inIntRange key
    · rw [bs8_push_of_range s key valid]
      apply ih
      obtain ⟨bad, mem, outside⟩ := invalid
      rcases List.mem_cons.mp mem with same | tail
      · subst bad
        exact False.elim (outside valid)
      · exact ⟨bad, tail, outside⟩
    · have outside : ¬ (IntTy.i64.min ≤ key ∧ key ≤ IntTy.i64.max) := valid
      have failed : push s key = .error (.julia (.inexactError "Int64")) := by
        simp [push, toInt, JInt.convert, outside, IntTy.name, Functor.map, Except.map]
      rw [failed]
      rfl

theorem BitsetscovBitsetBuild_proven : BitSetBuildSpec := by
  have emptyMember : ∀ n, member new n = false := by
    intro n
    exact bs_emptyBang_members new n
  refine ⟨bs_new_WF, rfl, rfl, emptyMember, bs8_unionIterator_valid,
    bs8_unionIterator_invalid, ?_, ?_, ?_, bs8_pushMany_valid, ?_⟩
  · intro keys valid
    obtain ⟨out, run, wf, members⟩ := bs8_unionIterator_valid new keys bs_new_WF valid
    refine ⟨out, run, wf, ?_⟩
    intro n
    simpa only [emptyMember n, Bool.false_or] using members n
  · intro keys invalid
    exact bs8_unionIterator_invalid new keys invalid
  · intro s
    exact ⟨rfl, rfl⟩
  · intro s keys invalid
    rw [bs8_pushMany_eq_unionIterator]
    exact bs8_unionIterator_invalid s keys invalid


end


set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false


section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- A small nonnegative Int shift count has its ordinary unsigned value. -/
theorem bs8_range_shift_count (n : Int) (hn : 0 ≤ n ∧ n < 64) :
    (fromJInt (int64 n)).toNat = n.toNat := by
  rw [fromJInt, BitVec.toNat_ofInt, bs_int64_val _ (by
    change -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807
    omega)]
  change (n % 18446744073709551616).toNat = n.toNat
  rw [Int.emod_eq_of_lt hn.1 (by omega)]

/-- Translate a source intrinsic left shift to its bit-vector operation. -/
theorem bs8_range_shl (word : U64) (n : Int) (hn : 0 ≤ n ∧ n < 64) :
    fromJInt (shl_int word (int64 n)) = fromJInt word <<< n.toNat := by
  unfold shl_int
  rw [bs_roundtrip_U64]
  unfold jlShlInt
  rw [bs8_range_shift_count n hn]
  have hb : ¬ n.toNat ≥ IntTy.u64.bits := by change ¬ n.toNat ≥ 64; omega
  rw [if_neg hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- Translate a source intrinsic logical right shift to its bit-vector operation. -/
theorem bs8_range_lshr (word : U64) (n : Int) (hn : 0 ≤ n ∧ n < 64) :
    fromJInt (lshr_int word (int64 n)) = fromJInt word >>> n.toNat := by
  unfold lshr_int
  rw [bs_roundtrip_U64]
  unfold jlLshrInt
  rw [bs8_range_shift_count n hn]
  have hb : ¬ n.toNat ≥ IntTy.u64.bits := by change ¬ n.toNat ≥ 64; omega
  rw [if_neg hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (fromJInt word).isLt

/-- The complement of the zero chunk has exactly its 64 in-range bits set. -/
theorem bs8_range_ones_bit (k : Nat) :
    (fromJInt (not_int zero64)).getLsbD k = decide (k < 64) := by
  unfold not_int
  rw [bs_roundtrip_U64]
  simp only [jlNotInt, BitVec.getLsbD_not, bs_zero_bit,
    Bool.not_false, Bool.and_true] <;> rfl

theorem bs8_range_ones_eq :
    fromJInt (not_int zero64) = ~~~(0 : BitVec 64) := by
  unfold not_int
  rw [bs_roundtrip_U64]
  rfl

/-- A lower range endpoint sets every bit at or above its position. -/
theorem bs8_range_firstMask (i k : Nat) (hi : i < 64) (hk : k < 64) :
    (fromJInt (shl_int (lshr_int (not_int zero64) (int64 i)) (int64 i))).getLsbD k =
      decide (i ≤ k) := by
  rw [bs8_range_shl _ _ (by omega), bs8_range_lshr _ _ (by omega), bs8_range_ones_eq]
  change (((~~~(0 : BitVec 64)) >>> i) <<< i).getLsbD k = decide (i ≤ k)
  exact JuliaLean.ChatGPT.Batch4.Group16.PureBitset.first_mask_bit i k hi hk

/-- An upper range endpoint sets every bit at or below its position. -/
theorem bs8_range_lastMask (j k : Nat) (hj : j < 64) (hk : k < 64) :
    (fromJInt (lshr_int (shl_int (not_int zero64) (int64 (63 - (j : Int))))
      (int64 (63 - (j : Int))))).getLsbD k = decide (k ≤ j) := by
  rw [bs8_range_lshr _ _ (by omega), bs8_range_shl _ _ (by omega), bs8_range_ones_eq]
  have hshift : (63 - (j : Int)).toNat = 63 - j := by omega
  rw [hshift]
  exact JuliaLean.ChatGPT.Batch4.Group16.PureBitset.last_mask_bit j k hj hk

/-- A range contained in one chunk uses an inclusive interval mask. -/
theorem bs8_range_singleMask (i j k : Nat) (hi : i < 64) (hj : j < 64)
    (hij : i ≤ j) (hk : k < 64) :
    (fromJInt (lshr_int
      (shl_int (lshr_int (not_int zero64) (int64 i))
        (int64 ((i : Int) + 63 - j))) (int64 (63 - (j : Int))))).getLsbD k =
      decide (i ≤ k ∧ k ≤ j) := by
  rw [bs8_range_lshr _ _ (by omega), bs8_range_shl _ _ (by omega),
    bs8_range_lshr _ _ (by omega), bs8_range_ones_eq]
  have hshift : (63 - (j : Int)).toNat = 63 - j := by omega
  have hmiddle : ((i : Int) + 63 - j).toNat = i + 63 - j := by omega
  rw [hshift, hmiddle, Int.toNat_natCast]
  exact JuliaLean.ChatGPT.Batch4.Group16.PureBitset.single_mask_bit i j k hi hj hij hk

end

section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- A chunk write changes exactly the membership queries in that chunk. -/
theorem bs8_range_write_member (s : BitSet) (chunk : Int) (word : U64) (n : I64)
    (hc : 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length) :
    inInt n {s with bits := bitsSet s.bits (chunk - s.offset + 1).toNat word} =
      if div64 n.val = chunk then bitAt word (mod64 n.val) else inInt n s := by
  have hlen : (bitsSet s.bits (chunk - s.offset + 1).toNat word).length = s.bits.length := by
    simp only [bitsSet, List.length_set]
  simp only [inInt, bitsGetindex, hlen]
  by_cases hn : 1 ≤ div64 n.val - s.offset + 1 ∧
      div64 n.val - s.offset + 1 ≤ s.bits.length
  · simp only [hn, ↓reduceIte, and_self]
    by_cases he : div64 n.val = chunk
    · simp only [he, ↓reduceIte, and_self]
      rw [bs_bitsSet_same _ _ _ (by omega) (by omega)]
    · simp only [he, ↓reduceIte, and_self]
      rw [bs_bitsSet_other _ _ _ _ (by omega) (by omega) (by omega)]
  · have he : div64 n.val ≠ chunk := by intro he; apply hn; simpa only [he] using hc
    simp only [hn, he, ↓reduceIte]

theorem bs8_range_or_bitAt (left right : U64) (k : Nat) (hk : k < 64) :
    bitAt (or_int left right) k = (bitAt left k || bitAt right k) := by
  rw [bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk]
  simp only [or_int, jlOrInt, bs_roundtrip_U64, BitVec.getLsbD_or]

/-- An in-place chunk disjunction adds precisely the selected mask bits. -/
theorem bs8_range_or_member (s : BitSet) (chunk : Int) (mask : U64) (n : I64)
    (hc : 1 ≤ chunk - s.offset + 1 ∧ chunk - s.offset + 1 ≤ s.bits.length) :
    inInt n {s with bits := (bitsSet s.bits (chunk - s.offset + 1).toNat
        (or_int (bitsGet s.bits (chunk - s.offset + 1).toNat) mask))} =
      (inInt n s || (decide (div64 n.val = chunk) && bitAt mask (mod64 n.val))) := by
  rw [bs8_range_write_member s chunk _ n hc]
  by_cases he : div64 n.val = chunk
  · simp only [he, ↓reduceIte, decide_true, Bool.true_and]
    rw [bs8_range_or_bitAt _ _ _ (bs_mod64_lt n)]
    simp only [inInt, bitsGetindex, he, hc, ↓reduceIte, and_self]
  · simp only [he, ↓reduceIte, decide_false, Bool.false_and, Bool.or_false]

/-- Filling any in-bounds list of zero-based chunks with ones takes a union
with those entire chunks, even if a chunk is listed more than once. -/
theorem bs8_range_fill_member (items : List Int) (s : BitSet) (n : I64)
    (hitems : ∀ i ∈ items, 0 ≤ i ∧ i < s.bits.length) :
    inInt n {s with bits := (items.foldl
        (fun words i => bitsSet words (i + 1).toNat (not_int zero64)) s.bits)} =
      (inInt n s || decide (div64 n.val - s.offset ∈ items)) := by
  induction items generalizing s with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, decide_false, Bool.or_false]
  | cons i rest ih =>
    have hi := hitems i (List.Mem.head _)
    let changed : BitSet := {s with bits := bitsSet s.bits (i + 1).toNat (not_int zero64)}
    have hrest : ∀ j ∈ rest, 0 ≤ j ∧ j < changed.bits.length := by
      intro j hj
      have hj' := hitems j (List.mem_cons_of_mem i hj)
      simpa only [changed, bitsSet, List.length_set] using hj'
    change inInt n {changed with bits := (rest.foldl
        (fun words i => bitsSet words (i + 1).toNat (not_int zero64)) changed.bits)} = _
    rw [ih changed hrest]
    have hc : 1 ≤ (s.offset + i) - s.offset + 1 ∧
        (s.offset + i) - s.offset + 1 ≤ s.bits.length := by omega
    have hrun := bs8_range_write_member s (s.offset + i) (not_int zero64) n hc
    have heq : s.offset + i - s.offset + 1 = i + 1 := by omega
    rw [heq] at hrun
    have hone : bitAt (not_int zero64) (mod64 n.val) = true := by
      rw [bs_bitAt_eq _ _ (bs_mod64_lt n), bs8_range_ones_bit]
      exact decide_eq_true (bs_mod64_lt n)
    change inInt n changed = _ at hrun
    rw [hrun, hone]
    change ((if div64 n.val = s.offset + i then true else inInt n s) ||
      decide (div64 n.val - s.offset ∈ rest)) =
      (inInt n s || decide (div64 n.val - s.offset ∈ i :: rest))
    by_cases he : div64 n.val - s.offset = i
    · have he' : div64 n.val = s.offset + i := by omega
      have hmem : div64 n.val - s.offset ∈ i :: rest :=
        List.mem_cons.mpr (Or.inl he)
      simp only [if_pos he', Bool.true_or, hmem, decide_true, Bool.or_true]
    · have he' : div64 n.val ≠ s.offset + i := by omega
      simp only [he', ↓reduceIte, List.mem_cons, he, false_or]

/-- The storage preparation phase of range union, before setting any range bits. -/
def bs8_rangeStorage (s : BitSet) (a b : I64) : BitSet :=
  let ca := div64 a.val
  let cb := div64 b.val
  let origin := if s.offset = noOffset then ca else s.offset
  let words := if cb - origin ≥ (s.bits.length : Int) then
    growend0 s.bits (cb - origin - s.bits.length + 1).toNat else s.bits
  if ca - origin < 0 then ⟨growbeg0 words (-(ca - origin)).toNat, ca⟩
  else ⟨words, origin⟩

theorem bs8_rangeStorage_shape (s : BitSet) (a b : I64) :
    let ca := div64 a.val
    let cb := div64 b.val
    let origin := if s.offset = noOffset then ca else s.offset
    (bs8_rangeStorage s a b).offset = (if ca - origin < 0 then ca else origin) ∧
    (bs8_rangeStorage s a b).bits.length =
      (if ca - origin < 0 then (-(ca - origin)).toNat else 0) +
      (if cb - origin ≥ (s.bits.length : Int) then
        s.bits.length + (cb - origin - s.bits.length + 1).toNat else s.bits.length) := by
  dsimp only
  unfold bs8_rangeStorage
  dsimp only
  split <;> split <;> split <;>
    simp only [JuliaLean.ChatGPT.Batch4.Group16.g16_growend0_length, JuliaLean.ChatGPT.Batch4.Group16.g16_growbeg0_length, Nat.zero_add, and_self]

theorem bs8_rangeStorage_bounds (s : BitSet) (a b : I64) (hs : WF s)
    (hab : a.val ≤ b.val) :
    indexWithin (bs8_rangeStorage s a b).bits
        (div64 a.val - (bs8_rangeStorage s a b).offset + 1) ∧
    indexWithin (bs8_rangeStorage s a b).bits
        (div64 b.val - (bs8_rangeStorage s a b).offset + 1) := by
  have firstShape := JuliaLean.ChatGPT.Batch4.Group16.g16_unionRangeBits_shape s a b
  have secondShape := bs8_rangeStorage_shape s a b
  dsimp only at firstShape secondShape
  have hoff := secondShape.1.trans firstShape.1.symm
  have hlen := secondShape.2.trans firstShape.2.symm
  have bounds := JuliaLean.ChatGPT.Batch4.Group16.g16_unionRangeBits_bounds s a b hs hab
  unfold indexWithin at bounds ⊢
  rw [hoff, hlen]
  exact ⟨bounds.1, bounds.2.1⟩

/-- Zero growth and offset initialization preserve all existing members. -/
theorem bs8_rangeStorage_member (s : BitSet) (a b n : I64) (hs : WF s) :
    inInt n (bs8_rangeStorage s a b) = inInt n s := by
  let ca := div64 a.val
  let cb := div64 b.val
  let origin := if s.offset = noOffset then ca else s.offset
  let words := if cb - origin ≥ (s.bits.length : Int) then
    growend0 s.bits (cb - origin - s.bits.length + 1).toNat else s.bits
  have hbase : inInt n ⟨s.bits, origin⟩ = inInt n s := by
    by_cases ho : s.offset = noOffset
    · have hz := hs.1 ho
      have he : s = ⟨[], s.offset⟩ := by
        cases s with
        | mk stored off =>
          change stored = [] at hz
          cases hz
          rfl
      rw [hz, bs_inInt_nil, he, bs_inInt_nil]
    · simp only [origin, ho, ↓reduceIte]
  have hend : inInt n ⟨words, origin⟩ = inInt n s := by
    dsimp only [words]
    split
    · rw [bs8_growend0_eq, bs8_append_zeros_member]
      exact hbase
    · exact hbase
  change inInt n (if ca - origin < 0 then
    ⟨growbeg0 words (-(ca - origin)).toNat, ca⟩ else ⟨words, origin⟩) = inInt n s
  split
  · rename_i hleft
    rw [bs8_growbeg0_eq]
    have hcoord : origin - ((-(ca - origin)).toNat : Int) = ca := by omega
    have h := bs8_prepend_zeros_member words origin (-(ca - origin)).toNat n
    rw [hcoord] at h
    exact h.trans hend
  · exact hend

/-- The bit-writing phase of range union, expressed in absolute chunk coordinates. -/
def bs8_rangeUpdate (s : BitSet) (ca cb : Int) (i j : Nat) : BitSet :=
  let lo := ca - s.offset
  let hi := cb - s.offset
  let ones := not_int zero64
  if ca = cb then
    let mask := lshr_int (shl_int (lshr_int ones (int64 i))
      (int64 ((i : Int) + 63 - j))) (int64 (63 - (j : Int)))
    {s with bits := (bitsSet s.bits (lo + 1).toNat
      (or_int (bitsGet s.bits (lo + 1).toNat) mask))}
  else
    let firstMask := shl_int (lshr_int ones (int64 i)) (int64 i)
    let lastMask := lshr_int (shl_int ones (int64 (63 - (j : Int))))
      (int64 (63 - (j : Int)))
    let words := bitsSet s.bits (lo + 1).toNat
      (or_int (bitsGet s.bits (lo + 1).toNat) firstMask)
    let words := bitsSet words (hi + 1).toNat
      (or_int (bitsGet words (hi + 1).toNat) lastMask)
    {s with bits := ((intRange (lo + 1) (hi - 1)).foldl
      (fun out index => bitsSet out (index + 1).toNat ones) words)}

theorem bs8_unionRangeBits_decompose (s : BitSet) (a b : I64) :
    unionRangeBits s a b =
      bs8_rangeUpdate (bs8_rangeStorage s a b) (div64 a.val) (div64 b.val)
        (mod64 a.val) (mod64 b.val) := by
  have hzero (x y : Int) : (0 = y - x) ↔ x = y := by omega
  have hdiff (x y z : Int) : (x - z = y - z) ↔ x = y := by omega
  have hshift (x y z : Int) : x - z - (y - z) = x - y := by omega
  unfold unionRangeBits bs8_rangeUpdate bs8_rangeStorage
  dsimp only
  by_cases ho : s.offset = noOffset
  · simp only [ho, ↓reduceIte, Int.sub_self, Int.lt_irrefl,
      hzero, hdiff, hshift, Int.zero_add]
    split <;> rfl
  · by_cases hl : div64 a.val - s.offset < 0 <;>
      simp only [ho, hl, ↓reduceIte,
        hzero, hdiff, hshift, Int.sub_self, Int.zero_add] <;>
      (split <;> rfl)

/-- The write phase adds its two endpoint masks and all intervening chunks. -/
theorem bs8_rangeUpdate_member (s : BitSet) (ca cb : Int) (i j : Nat) (n : I64)
    (hi : i < 64) (hj : j < 64) (hsame : ca = cb → i ≤ j)
    (hca : indexWithin s.bits (ca - s.offset + 1))
    (hcb : indexWithin s.bits (cb - s.offset + 1)) :
    inInt n (bs8_rangeUpdate s ca cb i j) =
      (inInt n s || if ca = cb then
        decide (div64 n.val = ca ∧ i ≤ mod64 n.val ∧ mod64 n.val ≤ j)
      else decide ((div64 n.val = ca ∧ i ≤ mod64 n.val) ∨
        (div64 n.val = cb ∧ mod64 n.val ≤ j) ∨ ca < div64 n.val ∧ div64 n.val < cb)) := by
  by_cases he : ca = cb
  · simp only [bs8_rangeUpdate, if_pos he]
    rw [bs8_range_or_member _ _ _ _ hca]
    rw [bs_bitAt_eq _ _ (bs_mod64_lt n),
      bs8_range_singleMask i j (mod64 n.val) hi hj (hsame he) (bs_mod64_lt n)]
    simp only [Bool.decide_and, Bool.and_assoc]
  · let firstMask := shl_int (lshr_int (not_int zero64) (int64 i)) (int64 i)
    let lastMask := lshr_int (shl_int (not_int zero64) (int64 (63 - (j : Int))))
      (int64 (63 - (j : Int)))
    let s1 : BitSet := {s with bits := (bitsSet s.bits (ca - s.offset + 1).toNat
      (or_int (bitsGet s.bits (ca - s.offset + 1).toNat) firstMask))}
    let s2 : BitSet := {s1 with bits := (bitsSet s1.bits (cb - s.offset + 1).toNat
      (or_int (bitsGet s1.bits (cb - s.offset + 1).toNat) lastMask))}
    let items := intRange (ca - s.offset + 1) (cb - s.offset - 1)
    have hlen1 : s1.bits.length = s.bits.length := by
      simp only [s1, bitsSet, List.length_set]
    have hlen2 : s2.bits.length = s.bits.length := by
      simp only [s2, bitsSet, List.length_set, hlen1]
    have hcb1 : indexWithin s1.bits (cb - s1.offset + 1) := by
      unfold indexWithin at hcb ⊢
      simpa only [hlen1] using hcb
    have hfirst := bs8_range_or_member s ca firstMask n hca
    have hsecond := bs8_range_or_member s1 cb lastMask n hcb1
    change inInt n s1 = _ at hfirst
    change inInt n s2 = _ at hsecond
    have hitems : ∀ index ∈ items, 0 ≤ index ∧ index < s2.bits.length := by
      intro index hindex
      have hb := (bs_intRange_mem _ _ _).mp hindex
      rw [hlen2]
      unfold indexWithin at hca hcb
      omega
    have hfill := bs8_range_fill_member items s2 n hitems
    simp only [bs8_rangeUpdate, he, ↓reduceIte]
    change inInt n {s2 with bits := (items.foldl
      (fun words index => bitsSet words (index + 1).toNat (not_int zero64)) s2.bits)} = _
    rw [hfill, hsecond, hfirst]
    rw [bs_bitAt_eq _ _ (bs_mod64_lt n), bs_bitAt_eq _ _ (bs_mod64_lt n)]
    rw [bs8_range_lastMask j (mod64 n.val) hj (bs_mod64_lt n),
      bs8_range_firstMask i (mod64 n.val) hi (bs_mod64_lt n)]
    have hmiddle : (div64 n.val - s2.offset ∈ items) ↔
        ca < div64 n.val ∧ div64 n.val < cb := by
      change (div64 n.val - s.offset ∈
        intRange (ca - s.offset + 1) (cb - s.offset - 1)) ↔ _
      rw [bs_intRange_mem]
      omega
    simp only [hmiddle, Bool.decide_or, Bool.decide_and, Bool.or_assoc]

/-- Chunk order and low-bit order together are exactly integer interval order. -/
theorem bs8_range_integer_interval (a b n : I64) (hab : a.val ≤ b.val) :
    (if div64 a.val = div64 b.val then
      decide (div64 n.val = div64 a.val ∧ mod64 a.val ≤ mod64 n.val ∧ mod64 n.val ≤ mod64 b.val)
    else decide ((div64 n.val = div64 a.val ∧ mod64 a.val ≤ mod64 n.val) ∨
      (div64 n.val = div64 b.val ∧ mod64 n.val ≤ mod64 b.val) ∨
      div64 a.val < div64 n.val ∧ div64 n.val < div64 b.val)) =
      decide (a.val ≤ n.val ∧ n.val ≤ b.val) := by
  rw [bs_div64_eq a.val a.property, bs_div64_eq b.val b.property,
    bs_div64_eq n.val n.property, bs_mod64_eq a.val a.property,
    bs_mod64_eq b.val b.property, bs_mod64_eq n.val n.property]
  split <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq] <;> omega

theorem bs8_unionRangeBits_member (s : BitSet) (a b n : I64)
    (hs : WF s) (hab : a.val ≤ b.val) :
    member (unionRangeBits s a b) n.val =
      (member s n.val || decide (a.val ≤ n.val ∧ n.val ≤ b.val)) := by
  rw [bs_member_intval, bs_member_intval, bs8_unionRangeBits_decompose]
  have hbounds := bs8_rangeStorage_bounds s a b hs hab
  have hlow : div64 a.val = div64 b.val → mod64 a.val ≤ mod64 b.val := by
    rw [bs_div64_eq a.val a.property, bs_div64_eq b.val b.property,
      bs_mod64_eq a.val a.property, bs_mod64_eq b.val b.property]
    intro h
    omega
  rw [bs8_rangeUpdate_member _ _ _ _ _ _ (bs_mod64_lt a) (bs_mod64_lt b)
    hlow hbounds.1 hbounds.2, bs8_rangeStorage_member s a b n hs,
    bs8_range_integer_interval a b n hab]

/-- The write phase changes no storage dimensions. -/
theorem bs8_rangeUpdate_shape (s : BitSet) (ca cb : Int) (i j : Nat) :
    (bs8_rangeUpdate s ca cb i j).offset = s.offset ∧
      (bs8_rangeUpdate s ca cb i j).bits.length = s.bits.length := by
  unfold bs8_rangeUpdate
  dsimp only
  split <;> simp only [JuliaLean.ChatGPT.Batch4.Group16.g16_bitsSetFold_length, JuliaLean.ChatGPT.Batch4.Group16.g16_bitsSet_length, and_self]

/-- Storage growth stays inside the signed chunk-coordinate interval. -/
theorem bs8_rangeStorage_WF (s : BitSet) (a b : I64) (hs : WF s) :
    WF (bs8_rangeStorage s a b) := by
  have ha := bs8_div64_bounds a
  have hb := bs8_div64_bounds b
  have shape := bs8_rangeStorage_shape s a b
  dsimp only at shape
  have bounds : -(2 ^ 57) ≤ (bs8_rangeStorage s a b).offset ∧
      (bs8_rangeStorage s a b).offset + (bs8_rangeStorage s a b).bits.length ≤ 2 ^ 57 := by
    by_cases ho : s.offset = noOffset
    · have hempty := hs.1 ho
      simp only [ho, Int.sub_self, Int.lt_irrefl, ↓reduceIte, hempty,
        List.length_nil, Int.natCast_zero, Int.sub_zero, Nat.zero_add] at shape
      rw [shape.1, shape.2]
      split <;> omega
    · have hold := hs.2 ho
      simp only [ho, ↓reduceIte] at shape
      rw [shape.1, shape.2]
      by_cases hl : div64 a.val - s.offset < 0 <;>
        by_cases hr : div64 b.val - s.offset ≥ (s.bits.length : Int) <;>
        simp only [hl, hr, ↓reduceIte, Int.natCast_add, Int.natCast_zero] <;> omega
  constructor
  · intro he
    have hlow := bounds.1
    change (bs8_rangeStorage s a b).offset = -(2 ^ 60) at he
    exfalso
    omega
  · intro _
    exact bounds

theorem bs8_unionRangeBits_WF (s : BitSet) (a b : I64) (hs : WF s) :
    WF (unionRangeBits s a b) := by
  rw [bs8_unionRangeBits_decompose]
  have shape := bs8_rangeUpdate_shape (bs8_rangeStorage s a b)
    (div64 a.val) (div64 b.val) (mod64 a.val) (mod64 b.val)
  exact bs8_WF_of_shape _ _ (bs8_rangeStorage_WF s a b hs) shape.1 shape.2

theorem BitsetscovBitsetUnionRange_proven :
    JuliaLean.Proofs.base.bitset.BitSetUnionRangeSpec := by
  refine ⟨?_, ?_, ?_, ?_, bs8_unionRangeBits_member, ?_⟩
  · intro R T instEmpty instFirst instLast instCtor s r hempty
    simp only [unionRange, hempty, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, Bool.true_eq, ↓reduceIte]
  · intro R T instEmpty instFirst instLast instCtor s r err hempty
    simp only [unionRange, hempty, Except.mapError, Bind.bind, Except.bind]
  · intro R T instEmpty instFirst instLast instCtor s r firstValue lastValue err
      hempty hfirst hlast hconvert
    simp only [unionRange, hempty, hfirst, hlast, hconvert, Except.mapError,
      Bind.bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  · intro R T instEmpty instFirst instLast instCtor s r firstValue lastValue a err
      hempty hfirst hlast hconvertA hconvertB
    simp only [unionRange, hempty, hfirst, hlast, hconvertA, hconvertB, Except.mapError,
      Bind.bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  · intro R T instEmpty instFirst instLast instCtor s r firstValue lastValue a b n out
      hs hempty hfirst hlast hconvertA hconvertB hab hrun
    have hexec : unionRange s r = .ok (unionRangeBits s a b) := by
      simp only [unionRange, hempty, hfirst, hlast, hconvertA, hconvertB, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
    rw [hexec] at hrun
    cases hrun
    exact bs8_unionRangeBits_member s a b n hs hab

end



section
set_option maxRecDepth 8192
open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- Repeated writes of a fixed word at each chunk are determined by the written index set. -/
theorem bs8m_overwrite_fold_member (items : List Int) (s : BitSet)
    (word : Int → U64) (n : I64)
    (bounds : ∀ i ∈ items, 0 ≤ i ∧ i < s.bits.length) :
    inInt n {s with bits := (items.foldl
        (fun words i => bitsSet words (i + 1).toNat (word i)) s.bits)} =
      if div64 n.val - s.offset ∈ items then
        bitAt (word (div64 n.val - s.offset)) (mod64 n.val)
      else inInt n s := by
  induction items generalizing s with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, ↓reduceIte]
  | cons i rest ih =>
    have hi := bounds i (List.Mem.head _)
    let changed : BitSet := {s with bits := bitsSet s.bits (i + 1).toNat (word i)}
    have remaining : ∀ j ∈ rest, 0 ≤ j ∧ j < changed.bits.length := by
      intro j hj
      have hb := bounds j (List.mem_cons_of_mem i hj)
      simpa only [changed, bitsSet, List.length_set] using hb
    change inInt n {changed with bits := (rest.foldl
      (fun words i => bitsSet words (i + 1).toNat (word i)) changed.bits)} = _
    rw [ih changed remaining]
    have hc : indexWithin s.bits (s.offset + i - s.offset + 1) := by
      unfold indexWithin
      omega
    have first := bs8_range_write_member s (s.offset + i) (word i) n hc
    have coord : s.offset + i - s.offset + 1 = i + 1 := by omega
    rw [coord] at first
    change inInt n changed = _ at first
    change (if div64 n.val - s.offset ∈ rest then
      bitAt (word (div64 n.val - s.offset)) (mod64 n.val) else inInt n changed) = _
    rw [first]
    by_cases inside : div64 n.val - s.offset ∈ rest
    · rw [if_pos inside, if_pos (List.mem_cons_of_mem i inside)]
    · by_cases same : div64 n.val - s.offset = i
      · have absolute : div64 n.val = s.offset + i := by omega
        have allMember : div64 n.val - s.offset ∈ i :: rest := List.mem_cons.mpr (Or.inl same)
        rw [if_neg inside, if_pos absolute, if_pos allMember, same]
      · have absolute : div64 n.val ≠ s.offset + i := by omega
        have outside : div64 n.val - s.offset ∉ i :: rest := by
          intro membership
          rcases List.mem_cons.mp membership with head | tail
          · exact same head
          · exact inside tail
        rw [if_neg inside, if_neg absolute, if_neg outside]

/-- One in-place chunk operation implements the supplied bitwise Boolean operation. -/
theorem bs8m_map_one_member (f : U64 → U64 → U64) (op : Bool → Bool → Bool)
    (bitLaw : ∀ a b k, k < 64 → bitAt (f a b) k = op (bitAt a k) (bitAt b k))
    (s : BitSet) (i : Int) (other : U64) (n : I64)
    (bounds : 0 ≤ i ∧ i < s.bits.length) :
    inInt n {s with bits := (bitsSet s.bits (i + 1).toNat
        (f (bitsGet s.bits (i + 1).toNat) other))} =
      if div64 n.val - s.offset = i then op (inInt n s) (bitAt other (mod64 n.val))
      else inInt n s := by
  have hc : indexWithin s.bits (s.offset + i - s.offset + 1) := by
    unfold indexWithin
    omega
  have write := bs8_range_write_member s (s.offset + i)
    (f (bitsGet s.bits (i + 1).toNat) other) n hc
  have coord : s.offset + i - s.offset + 1 = i + 1 := by omega
  rw [coord] at write
  rw [write]
  by_cases same : div64 n.val - s.offset = i
  · have absolute : div64 n.val = s.offset + i := by omega
    rw [if_pos absolute, if_pos same, bitLaw _ _ _ (bs_mod64_lt n)]
    have memberEq : inInt n s = bitAt (bitsGet s.bits (i + 1).toNat) (mod64 n.val) := by
      simp only [inInt, bitsGetindex]
      have coord' : div64 n.val - s.offset + 1 = i + 1 := by omega
      rw [coord', if_pos (by omega)]
    rw [memberEq]
  · have absolute : div64 n.val ≠ s.offset + i := by omega
    rw [if_neg absolute, if_neg same]

/-- Distinct chunk indices ensure each selected word is transformed exactly once. -/
theorem bs8m_map_fold_member (items : List Int) (s : BitSet)
    (f : U64 → U64 → U64) (op : Bool → Bool → Bool) (other : Int → U64)
    (bitLaw : ∀ a b k, k < 64 → bitAt (f a b) k = op (bitAt a k) (bitAt b k))
    (n : I64) (distinct : items.Nodup)
    (bounds : ∀ i ∈ items, 0 ≤ i ∧ i < s.bits.length) :
    inInt n {s with bits := (items.foldl
        (fun words i => bitsSet words (i + 1).toNat
          (f (bitsGet words (i + 1).toNat) (other i))) s.bits)} =
      if div64 n.val - s.offset ∈ items then
        op (inInt n s) (bitAt (other (div64 n.val - s.offset)) (mod64 n.val))
      else inInt n s := by
  induction items generalizing s with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, ↓reduceIte]
  | cons i rest ih =>
    obtain ⟨notRepeated, tailDistinct⟩ := List.nodup_cons.mp distinct
    have hi := bounds i (List.Mem.head _)
    let changed : BitSet := {s with bits := (bitsSet s.bits (i + 1).toNat
      (f (bitsGet s.bits (i + 1).toNat) (other i)))}
    have remaining : ∀ j ∈ rest, 0 ≤ j ∧ j < changed.bits.length := by
      intro j hj
      have hb := bounds j (List.mem_cons_of_mem i hj)
      simpa only [changed, bitsSet, List.length_set] using hb
    change inInt n {changed with bits := (rest.foldl
        (fun words i => bitsSet words (i + 1).toNat
          (f (bitsGet words (i + 1).toNat) (other i))) changed.bits)} = _
    rw [ih changed tailDistinct remaining]
    have first := bs8m_map_one_member f op bitLaw s i (other i) n hi
    change inInt n changed = _ at first
    change (if div64 n.val - s.offset ∈ rest then
      op (inInt n changed) (bitAt (other (div64 n.val - s.offset)) (mod64 n.val))
      else inInt n changed) = _
    rw [first]
    by_cases inside : div64 n.val - s.offset ∈ rest
    · have different : div64 n.val - s.offset ≠ i := by
        intro same
        rw [same] at inside
        exact notRepeated inside
      rw [if_pos inside, if_neg different, if_pos (List.mem_cons_of_mem i inside)]
    · by_cases same : div64 n.val - s.offset = i
      · have allMember : div64 n.val - s.offset ∈ i :: rest := List.mem_cons.mpr (Or.inl same)
        rw [if_neg inside, if_pos same, if_pos allMember, same]
      · have outside : div64 n.val - s.offset ∉ i :: rest := by
          intro membership
          rcases List.mem_cons.mp membership with head | tail
          · exact same head
          · exact inside tail
        rw [if_neg inside, if_neg same, if_neg outside]

/-- Every inclusive integer range contains each index at most once. -/
theorem bs8m_intRange_nodup (lo hi : Int) : (intRange lo hi).Nodup := by
  unfold intRange List.Nodup
  rw [List.pairwise_map]
  apply List.Pairwise.imp (R := fun a b : Nat => a ≠ b)
  · intro a b different same
    change lo + Int.ofNat a = lo + Int.ofNat b at same
    exact different (Int.ofNat_inj.mp (Int.add_left_cancel same))
  · exact List.nodup_range

/-- Mapping a list of chunk writes always retains the vector length. -/
theorem bs8m_chunkTransform_length {A : Type} (items : List A) (index : A → Nat)
    (word : List U64 → A → U64) (words : List U64) :
    (items.foldl (fun out i => bitsSet out (index i) (word out i)) words).length = words.length := by
  induction items generalizing words with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih]
    exact List.length_set

/-- The overwrite-fold lemma in the source's one-based chunk coordinates. -/
theorem bs8m_overwrite_fold_member1 (items : List Int) (s : BitSet)
    (word : Int → U64) (n : I64)
    (bounds : ∀ i ∈ items, 1 ≤ i ∧ i ≤ s.bits.length) :
    inInt n {s with bits := (items.foldl
        (fun words i => bitsSet words i.toNat (word i)) s.bits)} =
      if div64 n.val - s.offset + 1 ∈ items then
        bitAt (word (div64 n.val - s.offset + 1)) (mod64 n.val)
      else inInt n s := by
  let zeroItems := items.map (fun i => i - 1)
  have zeroBounds : ∀ i ∈ zeroItems, 0 ≤ i ∧ i < s.bits.length := by
    intro i membership
    obtain ⟨j, hj, same⟩ := List.mem_map.mp membership
    have h := bounds j hj
    omega
  have h := bs8m_overwrite_fold_member zeroItems s (fun i => word (i + 1)) n zeroBounds
  simp only [zeroItems, List.foldl_map, Int.sub_add_cancel] at h
  have memberEquiv : div64 n.val - s.offset ∈ items.map (fun i => i - 1) ↔
      div64 n.val - s.offset + 1 ∈ items := by
    constructor
    · intro membership
      obtain ⟨j, hj, same⟩ := List.mem_map.mp membership
      have eq : j = div64 n.val - s.offset + 1 := by omega
      simpa only [eq] using hj
    · intro membership
      exact List.mem_map.mpr ⟨div64 n.val - s.offset + 1, membership, by omega⟩
  simp only [memberEquiv] at h
  exact h

/-- The distinct-index map lemma in the source's one-based chunk coordinates. -/
theorem bs8m_map_fold_member1 (items : List Int) (s : BitSet)
    (f : U64 → U64 → U64) (op : Bool → Bool → Bool) (other : Int → U64)
    (bitLaw : ∀ a b k, k < 64 → bitAt (f a b) k = op (bitAt a k) (bitAt b k))
    (n : I64) (distinct : items.Nodup)
    (bounds : ∀ i ∈ items, 1 ≤ i ∧ i ≤ s.bits.length) :
    inInt n {s with bits := (items.foldl
        (fun words i => bitsSet words i.toNat
          (f (bitsGet words i.toNat) (other i))) s.bits)} =
      if div64 n.val - s.offset + 1 ∈ items then
        op (inInt n s) (bitAt (other (div64 n.val - s.offset + 1)) (mod64 n.val))
      else inInt n s := by
  let zeroItems := items.map (fun i => i - 1)
  have zeroBounds : ∀ i ∈ zeroItems, 0 ≤ i ∧ i < s.bits.length := by
    intro i membership
    obtain ⟨j, hj, same⟩ := List.mem_map.mp membership
    have h := bounds j hj
    omega
  have zeroDistinct : zeroItems.Nodup := by
    unfold zeroItems List.Nodup
    rw [List.pairwise_map]
    apply List.Pairwise.imp (R := fun a b : Int => a ≠ b)
    · intro a b different same
      apply different
      omega
    · exact distinct
  have h := bs8m_map_fold_member zeroItems s f op (fun i => other (i + 1))
    bitLaw n zeroDistinct zeroBounds
  simp only [zeroItems, List.foldl_map, Int.sub_add_cancel] at h
  have memberEquiv : div64 n.val - s.offset ∈ items.map (fun i => i - 1) ↔
      div64 n.val - s.offset + 1 ∈ items := by
    constructor
    · intro membership
      obtain ⟨j, hj, same⟩ := List.mem_map.mp membership
      have eq : j = div64 n.val - s.offset + 1 := by omega
      simpa only [eq] using hj
    · intro membership
      exact List.mem_map.mpr ⟨div64 n.val - s.offset + 1, membership, by omega⟩
  simp only [memberEquiv] at h
  exact h

/-- A destination-bounded copy changes exactly the selected destination chunks. -/
theorem bs8m_copyChunks_member (s : BitSet) (source : List U64)
    (destinationStart sourceStart count : Nat) (n : I64)
    (positive : 1 ≤ destinationStart)
    (span : destinationStart + count ≤ s.bits.length + 1) :
    inInt n {s with bits := copyChunks s.bits destinationStart source sourceStart count} =
      if (destinationStart : Int) ≤ div64 n.val - s.offset + 1 ∧
          div64 n.val - s.offset + 1 < (destinationStart + count : Nat) then
        bitAt (bitsGet source
          (sourceStart + ((div64 n.val - s.offset + 1).toNat - destinationStart))) (mod64 n.val)
      else inInt n s := by
  let indices := (List.range count).map (fun k => ((destinationStart + k : Nat) : Int))
  let values := fun i : Int => bitsGet source (sourceStart + (i.toNat - destinationStart))
  have bounds : ∀ i ∈ indices, 1 ≤ i ∧ i ≤ s.bits.length := by
    intro i membership
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp membership
    have hk' := List.mem_range.mp hk
    omega
  have writes : copyChunks s.bits destinationStart source sourceStart count =
      indices.foldl (fun words i => bitsSet words i.toNat (values i)) s.bits := by
    simp only [copyChunks, indices, values, List.foldl_map, Int.toNat_natCast,
      Nat.add_sub_cancel_left]
  rw [writes]
  have result := bs8m_overwrite_fold_member1 indices s values n bounds
  have contains : div64 n.val - s.offset + 1 ∈ indices ↔
      (destinationStart : Int) ≤ div64 n.val - s.offset + 1 ∧
        div64 n.val - s.offset + 1 < (destinationStart + count : Nat) := by
    constructor
    · intro membership
      obtain ⟨k, hk, same⟩ := List.mem_map.mp membership
      have hk' := List.mem_range.mp hk
      omega
    · intro inside
      refine List.mem_map.mpr ⟨(div64 n.val - s.offset + 1 - destinationStart).toNat,
        List.mem_range.mpr (by omega), ?_⟩
      omega
  simp only [contains] at result
  exact result

/-- The common chunk interval is transformed by the source's pointwise disjunction. -/
def bs8m_overlapOr (left right : BitSet) : BitSet :=
  let delta := right.offset - left.offset
  let items := intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))
  {left with bits := (items.foldl
    (fun words i => bitsSet words i.toNat
      (or_int (bitsGet words i.toNat) (bitsGet right.bits (i - delta).toNat))) left.bits)}

theorem bs8m_overlapOr_offset (left right : BitSet) :
    (bs8m_overlapOr left right).offset = left.offset := rfl

theorem bs8m_overlapOr_length (left right : BitSet) :
    (bs8m_overlapOr left right).bits.length = left.bits.length := by
  unfold bs8m_overlapOr
  exact bs8m_chunkTransform_length _ _ _ _

/-- The overlap phase takes union on existing left chunks and leaves its exterior empty. -/
theorem bs8m_overlapOr_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_overlapOr left right) =
      (inInt n left || (decide (1 ≤ div64 n.val - left.offset + 1 ∧
        div64 n.val - left.offset + 1 ≤ left.bits.length) && inInt n right)) := by
  let delta := right.offset - left.offset
  let items := intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))
  have bounds : ∀ i ∈ items, 1 ≤ i ∧ i ≤ left.bits.length := by
    intro i hi
    have range := (bs_intRange_mem _ _ _).mp hi
    omega
  have result := bs8m_map_fold_member1 items left or_int (· || ·)
    (fun i => bitsGet right.bits (i - delta).toNat)
    bs8_range_or_bitAt n (bs8m_intRange_nodup _ _) bounds
  have contains : div64 n.val - left.offset + 1 ∈ items ↔
      (1 ≤ div64 n.val - left.offset + 1 ∧ div64 n.val - left.offset + 1 ≤ left.bits.length) ∧
      (1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 ≤ right.bits.length) := by
    rw [bs_intRange_mem]
    dsimp only [delta]
    omega
  simp only [contains] at result
  have coordinate : div64 n.val - left.offset + 1 - delta = div64 n.val - right.offset + 1 := by
    dsimp only [delta]
    omega
  try dsimp only at result
  rw [coordinate] at result
  change inInt n (bs8m_overlapOr left right) = _ at result
  rw [result]
  by_cases hl : 1 ≤ div64 n.val - left.offset + 1 ∧ div64 n.val - left.offset + 1 ≤ left.bits.length
  · by_cases hr : 1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 ≤ right.bits.length
    · simp only [hl, hr, and_self, ↓reduceIte, decide_true, Bool.true_and, inInt, bitsGetindex]
    · simp only [hl, hr, and_false, ↓reduceIte, decide_true, Bool.true_and,
        inInt, bitsGetindex, hr, and_self, ↓reduceIte, Bool.and_false, Bool.or_false]
  · simp only [hl, false_and, ↓reduceIte, decide_false, Bool.false_and, Bool.or_false]


end

section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- Inside its stored span, membership reads the selected chunk bit. -/
theorem bs8m_inInt_at_index (s : BitSet) (n : I64)
    (inside : 1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length) :
    inInt n s = bitAt (bitsGet s.bits (div64 n.val - s.offset + 1).toNat) (mod64 n.val) := by
  simp only [inInt, bitsGetindex, inside, and_self, ↓reduceIte]

/-- Outside its stored span, membership is false. -/
theorem bs8m_inInt_outside (s : BitSet) (n : I64)
    (outside : ¬(1 ≤ div64 n.val - s.offset + 1 ∧ div64 n.val - s.offset + 1 ≤ s.bits.length)) :
    inInt n s = false := by
  simp only [inInt, bitsGetindex, outside, ↓reduceIte]

/-- An aligned copy replaces its destination span with the source's absolute members. -/
theorem bs8m_copyChunks_aligned_member (left right : BitSet)
    (destinationStart sourceStart count : Nat) (n : I64)
    (destinationPositive : 1 ≤ destinationStart) (sourcePositive : 1 ≤ sourceStart)
    (destinationSpan : destinationStart + count ≤ left.bits.length + 1)
    (sourceSpan : sourceStart + count ≤ right.bits.length + 1)
    (alignment : (sourceStart : Int) - destinationStart = left.offset - right.offset) :
    inInt n {left with bits := copyChunks left.bits destinationStart right.bits sourceStart count} =
      if (destinationStart : Int) ≤ div64 n.val - left.offset + 1 ∧
          div64 n.val - left.offset + 1 < (destinationStart + count : Nat) then
        inInt n right else inInt n left := by
  rw [bs8m_copyChunks_member left right.bits destinationStart sourceStart count n
    destinationPositive destinationSpan]
  by_cases inside : (destinationStart : Int) ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 < (destinationStart + count : Nat)
  · simp only [inside, ↓reduceIte]
    have rightInside : 1 ≤ div64 n.val - right.offset + 1 ∧
        div64 n.val - right.offset + 1 ≤ right.bits.length := by omega
    have coordinate : sourceStart + ((div64 n.val - left.offset + 1).toNat - destinationStart) =
        (div64 n.val - right.offset + 1).toNat := by omega
    rw [coordinate, bs8m_inInt_at_index right n rightInside]
  · simp only [inside, ↓reduceIte]

/-- Chunk copies preserve the length of their destination vector. -/
theorem bs8m_copyChunks_length (words : List U64) (destinationStart : Nat)
    (source : List U64) (sourceStart count : Nat) :
    (copyChunks words destinationStart source sourceStart count).length = words.length := by
  unfold copyChunks
  exact JuliaLean.ChatGPT.Batch4.Group16.g16_bitsSetFold_length _ _ _ _

/-- Explicit zero writes into a fresh appended region leave its initialized contents unchanged. -/
theorem bs8m_zero_after_append (words : List U64) (count : Nat) (lo hi : Int)
    (low : (words.length : Int) < lo) (high : hi ≤ (words.length + count : Nat)) :
    (intRange lo hi).foldl (fun out i => bitsSet out i.toNat zero64)
      (words ++ List.replicate count zero64) = words ++ List.replicate count zero64 := by
  apply bs8_fold_zero_unchanged
  intro i membership
  have bounds := (bs_intRange_mem _ _ _).mp membership
  apply bs8_set_append_zero <;> omega

/-- Explicit zero writes into a fresh prepended region leave it unchanged. -/
theorem bs8m_zero_after_prepend (words : List U64) (count : Nat) (lo hi : Int)
    (low : 1 ≤ lo) (high : hi ≤ (count : Int)) :
    (intRange lo hi).foldl (fun out i => bitsSet out i.toNat zero64)
      (List.replicate count zero64 ++ words) = List.replicate count zero64 ++ words := by
  apply bs8_fold_zero_unchanged
  intro i membership
  have bounds := (bs_intRange_mem _ _ _).mp membership
  apply bs8_set_prepend_zero <;> omega

/-- Union's trailing growth-and-copy phase with redundant zero initialization removed. -/
def bs8m_unionEnd (left right : BitSet) : BitSet :=
  let delta := right.offset - left.offset
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  if difference > 0 then
    let cut := if (left.bits.length : Int) + 1 ≤ delta then delta else left.bits.length
    let count := (right.bits.length : Int) + right.offset - cut - left.offset
    ⟨copyChunks (bitsGrowEnd left.bits difference.toNat zero64) (cut + 1).toNat
      right.bits ((right.bits.length : Int) + 1 - count).toNat count.toNat, left.offset⟩
  else left

/-- Union's leading growth-and-copy phase with redundant zero initialization removed. -/
def bs8m_unionBegin (left right : BitSet) : BitSet :=
  let delta := right.offset - left.offset
  if delta < 0 then
    ⟨copyChunks (bitsGrowBeg left.bits (-delta).toNat zero64) 1 right.bits 1
      (min (-delta) (right.bits.length : Int)).toNat, right.offset⟩
  else left

theorem bs8m_unionEnd_shape (left right : BitSet) :
    (bs8m_unionEnd left right).offset = left.offset ∧
    (bs8m_unionEnd left right).bits.length =
      let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
      if difference > 0 then left.bits.length + difference.toNat else left.bits.length := by
  unfold bs8m_unionEnd
  dsimp only
  split
  · exact ⟨rfl, by simp only [bs8m_copyChunks_length, bitsGrowEnd, List.length_append, List.length_replicate]⟩
  · exact ⟨rfl, rfl⟩

theorem bs8m_unionBegin_shape (left right : BitSet) :
    (bs8m_unionBegin left right).offset =
      (if right.offset - left.offset < 0 then right.offset else left.offset) ∧
    (bs8m_unionBegin left right).bits.length =
      (if right.offset - left.offset < 0 then
        (-(right.offset - left.offset)).toNat + left.bits.length else left.bits.length) := by
  unfold bs8m_unionBegin
  dsimp only
  split
  · exact ⟨rfl, by simp only [bs8m_copyChunks_length, bitsGrowBeg, List.length_append, List.length_replicate]⟩
  · exact ⟨rfl, rfl⟩

/-- The trailing union phase adds exactly right-hand members beyond the old left span. -/
theorem bs8m_unionEnd_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_unionEnd left right) =
      (inInt n left || (decide (left.offset + left.bits.length ≤ div64 n.val) && inInt n right)) := by
  let delta := right.offset - left.offset
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  by_cases grows : difference > 0
  · dsimp only [difference] at grows
    let cut := if (left.bits.length : Int) + 1 ≤ delta then delta else left.bits.length
    let count := (right.bits.length : Int) + right.offset - cut - left.offset
    let grown : BitSet := ⟨bitsGrowEnd left.bits difference.toNat zero64, left.offset⟩
    have cutFacts : (left.bits.length : Int) ≤ cut ∧ delta ≤ cut ∧
        (cut = delta ∨ cut = (left.bits.length : Int)) := by
      dsimp only [cut]
      split <;> omega
    have differenceEq : difference = (right.bits.length : Int) + delta - left.bits.length := by
      dsimp only [difference, delta]
      omega
    have countEq : count = (right.bits.length : Int) + delta - cut := by
      dsimp only [count, delta]
      omega
    have countBounds : 0 ≤ count ∧ count ≤ right.bits.length := by omega
    have grownLength : grown.bits.length = left.bits.length + difference.toNat := by
      simp only [grown, bitsGrowEnd, List.length_append, List.length_replicate]
    have copied := bs8m_copyChunks_aligned_member grown right (cut + 1).toNat
      ((right.bits.length : Int) + 1 - count).toNat count.toNat n
      (by omega) (by omega)
      (by rw [grownLength]; omega) (by omega) (by change _ = left.offset - right.offset; omega)
    have run : bs8m_unionEnd left right =
        {grown with bits := (copyChunks grown.bits (cut + 1).toNat right.bits
          ((right.bits.length : Int) + 1 - count).toNat count.toNat)} := by
      simp only [bs8m_unionEnd, grows, ↓reduceIte] <;> rfl
    have grownMember : inInt n grown = inInt n left :=
      bs8_append_zeros_member left.bits left.offset difference.toNat n
    have interval : ((cut + 1).toNat : Int) ≤ div64 n.val - grown.offset + 1 ∧
        div64 n.val - grown.offset + 1 < ((cut + 1).toNat + count.toNat : Nat) ↔
        left.offset + left.bits.length ≤ div64 n.val ∧ right.offset ≤ div64 n.val ∧
          div64 n.val < right.offset + right.bits.length := by
      change _ ≤ div64 n.val - left.offset + 1 ∧ div64 n.val - left.offset + 1 < _ ↔ _
      omega
    rw [run, copied, grownMember]
    simp only [Int.natCast_one, interval]
    by_cases after : left.offset + left.bits.length ≤ div64 n.val
    · have leftEmpty := bs8m_inInt_outside left n (by omega)
      by_cases rightInside : right.offset ≤ div64 n.val ∧ div64 n.val < right.offset + right.bits.length
      · rw [if_pos ⟨after, rightInside.1, rightInside.2⟩]
        simp only [leftEmpty, after, decide_true, Bool.true_and, Bool.false_or]
      · have rightEmpty := bs8m_inInt_outside right n (by omega)
        rw [if_neg (fun hit => rightInside ⟨hit.2.1, hit.2.2⟩)]
        simp only [leftEmpty, rightEmpty, Bool.and_false, Bool.or_false]
    · rw [if_neg (fun hit => after hit.1)]
      simp only [after, decide_false, Bool.false_and, Bool.or_false]
  · dsimp only [difference] at grows
    have run : bs8m_unionEnd left right = left := by
      simp only [bs8m_unionEnd, grows, ↓reduceIte]
    rw [run]
    by_cases after : left.offset + left.bits.length ≤ div64 n.val
    · have rightEmpty := bs8m_inInt_outside right n (by
        try dsimp only [difference] at grows
        omega)
      simp only [rightEmpty, Bool.and_false, Bool.or_false]
    · simp only [after, decide_false, Bool.false_and, Bool.or_false]

/-- The leading union phase adds exactly right-hand members below the old left span. -/
theorem bs8m_unionBegin_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_unionBegin left right) =
      (inInt n left || (decide (div64 n.val < left.offset) && inInt n right)) := by
  let delta := right.offset - left.offset
  by_cases grows : delta < 0
  · dsimp only [delta] at grows
    let count := min (-delta) (right.bits.length : Int)
    let grown : BitSet := ⟨bitsGrowBeg left.bits (-delta).toNat zero64, right.offset⟩
    have countFacts : 0 ≤ count ∧ count ≤ -delta ∧ count ≤ right.bits.length ∧
        (count = -delta ∨ count = (right.bits.length : Int)) := by
      dsimp only [count]
      omega
    have grownLength : grown.bits.length = (-delta).toNat + left.bits.length := by
      simp only [grown, bitsGrowBeg, List.length_append, List.length_replicate]
    have copied := bs8m_copyChunks_aligned_member grown right 1 1 count.toNat n
      (by omega) (by omega) (by rw [grownLength]; omega) (by omega)
      (by change (1 : Int) - 1 = right.offset - right.offset; omega)
    have run : bs8m_unionBegin left right =
        {grown with bits := copyChunks grown.bits 1 right.bits 1 count.toNat} := by
      simp only [bs8m_unionBegin, grows, ↓reduceIte] <;> rfl
    have offset : left.offset - ((-delta).toNat : Int) = right.offset := by
      dsimp only [delta] at grows ⊢
      omega
    have grownMember : inInt n grown = inInt n left := by
      simpa only [grown, bitsGrowBeg, offset] using bs8_prepend_zeros_member left.bits left.offset (-delta).toNat n
    have interval : (1 : Int) ≤ div64 n.val - grown.offset + 1 ∧
        div64 n.val - grown.offset + 1 < (1 + count.toNat : Nat) ↔
        div64 n.val < left.offset ∧ right.offset ≤ div64 n.val ∧
          div64 n.val < right.offset + right.bits.length := by
      change 1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 < _ ↔ _
      omega
    rw [run, copied, grownMember]
    simp only [Int.natCast_one, interval]
    by_cases before : div64 n.val < left.offset
    · have leftEmpty := bs8m_inInt_outside left n (by omega)
      by_cases rightInside : right.offset ≤ div64 n.val ∧ div64 n.val < right.offset + right.bits.length
      · rw [if_pos ⟨before, rightInside.1, rightInside.2⟩]
        simp only [leftEmpty, before, decide_true, Bool.true_and, Bool.false_or]
      · have rightEmpty := bs8m_inInt_outside right n (by omega)
        rw [if_neg (fun hit => rightInside ⟨hit.2.1, hit.2.2⟩)]
        simp only [leftEmpty, rightEmpty, Bool.and_false, Bool.or_false]
    · rw [if_neg (fun hit => before hit.1)]
      simp only [before, decide_false, Bool.false_and, Bool.or_false]
  · dsimp only [delta] at grows
    have run : bs8m_unionBegin left right = left := by
      simp only [bs8m_unionBegin, grows, ↓reduceIte]
    rw [run]
    by_cases before : div64 n.val < left.offset
    · have rightEmpty := bs8m_inInt_outside right n (by
        try dsimp only [delta] at grows
        omega)
      simp only [rightEmpty, Bool.and_false, Bool.or_false]
    · simp only [before, decide_false, Bool.false_and, Bool.or_false]

/-- Union as its overlap, trailing-copy, and leading-copy phases. -/
def bs8m_unionNormalized (left right : BitSet) : BitSet :=
  bs8m_unionBegin (bs8m_unionEnd (bs8m_overlapOr left right) right) right

/-- The normalized phases together implement memberwise disjunction. -/
theorem bs8m_unionNormalized_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_unionNormalized left right) = (inInt n left || inInt n right) := by
  have offset : (bs8m_unionEnd (bs8m_overlapOr left right) right).offset = left.offset :=
    (bs8m_unionEnd_shape (bs8m_overlapOr left right) right).1
  unfold bs8m_unionNormalized
  rw [bs8m_unionBegin_member, offset, bs8m_unionEnd_member, bs8m_overlapOr_length,
    bs8m_overlapOr_member, bs8m_overlapOr_offset]
  change (((inInt n left || (decide (1 ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 ≤ left.bits.length) && inInt n right)) ||
      (decide (left.offset + left.bits.length ≤ div64 n.val) && inInt n right)) ||
      (decide (div64 n.val < left.offset) && inInt n right)) = (inInt n left || inInt n right)
  cases memberRight : inInt n right with
  | false => simp only [memberRight, Bool.and_false, Bool.or_false]
  | true =>
    by_cases before : div64 n.val < left.offset
    · simp only [memberRight, before, decide_true, Bool.and_true, Bool.or_true]
    · by_cases after : left.offset + left.bits.length ≤ div64 n.val
      · simp only [memberRight, after, decide_true, Bool.and_true, Bool.or_true, Bool.true_or]
      · have inside : 1 ≤ div64 n.val - left.offset + 1 ∧
            div64 n.val - left.offset + 1 ≤ left.bits.length := by omega
        simp only [memberRight, inside, and_self, decide_true, Bool.and_true, Bool.or_true, Bool.true_or]

/-- Normalized union spans the lower input offset through the greater input endpoint. -/
theorem bs8m_unionNormalized_span (left right : BitSet) :
    (bs8m_unionNormalized left right).offset = min left.offset right.offset ∧
    (bs8m_unionNormalized left right).offset + (bs8m_unionNormalized left right).bits.length =
      max (left.offset + left.bits.length) (right.offset + right.bits.length) := by
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  have endOffset : (bs8m_unionEnd (bs8m_overlapOr left right) right).offset = left.offset :=
    (bs8m_unionEnd_shape (bs8m_overlapOr left right) right).1
  have endLength : (bs8m_unionEnd (bs8m_overlapOr left right) right).bits.length =
      if difference > 0 then left.bits.length + difference.toNat else left.bits.length := by
    simpa only [bs8m_overlapOr_length, bs8m_overlapOr_offset] using
      (bs8m_unionEnd_shape (bs8m_overlapOr left right) right).2
  have beginShape := bs8m_unionBegin_shape (bs8m_unionEnd (bs8m_overlapOr left right) right) right
  unfold bs8m_unionNormalized
  simp only [beginShape.1, beginShape.2, endOffset, endLength]
  by_cases leading : right.offset - left.offset < 0 <;>
    by_cases trailing : difference > 0 <;>
    simp only [leading, trailing, ↓reduceIte, Int.natCast_add] <;>
    constructor <;> dsimp only [difference] at * <;> omega

/-- The normalized union preserves the frozen representation bounds. -/
theorem bs8m_unionNormalized_WF (left right : BitSet) (hl : WF left) (hr : WF right)
    (leftPresent : left.offset ≠ noOffset) (rightPresent : right.offset ≠ noOffset) :
    WF (bs8m_unionNormalized left right) := by
  have leftBounds := hl.2 leftPresent
  have rightBounds := hr.2 rightPresent
  have shape := bs8m_unionNormalized_span left right
  have low : -(2 ^ 57) ≤ (bs8m_unionNormalized left right).offset := by
    rw [shape.1]
    omega
  have high : (bs8m_unionNormalized left right).offset +
      (bs8m_unionNormalized left right).bits.length ≤ 2 ^ 57 := by
    rw [shape.2]
    omega
  constructor
  · intro impossible
    rw [impossible] at low
    unfold noOffset at low
    omega
  · intro _
    exact ⟨low, high⟩

/-- The frozen union specialization equals its normalized three-phase execution. -/
theorem bs8m_unionMapBits_normal (left right : BitSet) :
    let result := matchedMapBits or_int left.bits left.offset right.bits right.offset false false
    (⟨result.1, result.2⟩ : BitSet) = bs8m_unionNormalized left right := by
  let delta := right.offset - left.offset
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  let commonWords := (intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))).foldl
    (fun words i => bitsSet words i.toNat
      (or_int (bitsGet words i.toNat) (bitsGet right.bits (i - delta).toNat))) left.bits
  have commonLength : commonWords.length = left.bits.length :=
    bs8m_chunkTransform_length _ _ _ _
  have highZero (high : difference > 0) :
      (intRange ((left.bits.length : Int) + 1) delta).foldl
        (fun words i => bitsSet words i.toNat zero64)
        (bitsGrowEnd commonWords difference.toNat zero64) =
          bitsGrowEnd commonWords difference.toNat zero64 := by
    apply bs8m_zero_after_append
    · rw [commonLength]
      omega
    · rw [commonLength]
      dsimp only [difference, delta] at high ⊢
      omega
  have lowZero (words : List U64) (low : delta < 0) :
      (intRange ((right.bits.length : Int) + 1) (-delta)).foldl
        (fun words i => bitsSet words i.toNat zero64)
        (bitsGrowBeg words (-delta).toNat zero64) = bitsGrowBeg words (-delta).toNat zero64 := by
    apply bs8m_zero_after_prepend
    · omega
    · omega
  have offsetEq : left.offset + (right.offset - left.offset) = right.offset := by omega
  unfold matchedMapBits bs8m_unionNormalized bs8m_unionBegin bs8m_unionEnd bs8m_overlapOr
  dsimp only
  simp only [bs8m_chunkTransform_length, Bool.false_eq_true, ite_false, ite_self]
  by_cases high : difference > 0 <;>
    by_cases gap : (left.bits.length : Int) + 1 ≤ delta <;>
    by_cases low : delta < 0 <;>
    dsimp only [difference, delta] at high gap low <;>
    try simp only [high, gap, low, ↓reduceIte, ite_self]
  all_goals try rw [highZero high]
  all_goals try rw [lowZero _ low]
  all_goals (try simp only [offsetEq]) <;> rfl

/-- BitSet union preserves its invariant and implements pointwise membership disjunction. -/
theorem bs8m_unionBang_spec (left right : BitSet) (hl : WF left) (hr : WF right) :
    WF (unionBang left right) ∧ ∀ n, inInt n (unionBang left right) = (inInt n left || inInt n right) := by
  by_cases leftEmpty : left.offset = noOffset
  · have nilLeft := hl.1 leftEmpty
    have result : unionBang left right = right := by
      simp only [unionBang, matchedMap, leftEmpty, ↓reduceIte, copyBang] <;> rfl
    rw [result]
    refine ⟨hr, ?_⟩
    intro n
    have absent : inInt n left = false := by
      apply bs8m_inInt_outside
      rw [nilLeft]
      simp only [List.length_nil, Int.natCast_zero]
      omega
    simp only [absent, Bool.false_or]
  · by_cases rightEmpty : right.offset = noOffset
    · have nilRight := hr.1 rightEmpty
      have result : unionBang left right = left := by
        simp only [unionBang, matchedMap, leftEmpty, rightEmpty, ↓reduceIte] <;> rfl
      rw [result]
      refine ⟨hl, ?_⟩
      intro n
      have absent : inInt n right = false := by
        apply bs8m_inInt_outside
        rw [nilRight]
        simp only [List.length_nil, Int.natCast_zero]
        omega
      simp only [absent, Bool.or_false]
    · have result : unionBang left right = bs8m_unionNormalized left right := by
        simp only [unionBang, matchedMap, leftEmpty, rightEmpty, ↓reduceIte]
        exact bs8m_unionMapBits_normal left right
      rw [result]
      exact ⟨bs8m_unionNormalized_WF left right hl hr leftEmpty rightEmpty,
        bs8m_unionNormalized_member left right⟩

end

section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- The overlap transformation, parameterized by its chunk operation. -/
def bs8m_overlapMap (operation : U64 → U64 → U64) (left right : BitSet) : BitSet :=
  let delta := right.offset - left.offset
  let items := intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))
  {left with bits := (items.foldl
    (fun words i => bitsSet words i.toNat
      (operation (bitsGet words i.toNat) (bitsGet right.bits (i - delta).toNat))) left.bits)}

theorem bs8m_overlapMap_offset (operation : U64 → U64 → U64) (left right : BitSet) :
    (bs8m_overlapMap operation left right).offset = left.offset := rfl

theorem bs8m_overlapMap_length (operation : U64 → U64 → U64) (left right : BitSet) :
    (bs8m_overlapMap operation left right).bits.length = left.bits.length := by
  unfold bs8m_overlapMap
  exact bs8m_chunkTransform_length _ _ _ _

/-- The common interval applies the supplied Boolean operation exactly once per stored bit. -/
theorem bs8m_overlapMap_member (operation : U64 → U64 → U64) (op : Bool → Bool → Bool)
    (bitLaw : ∀ a b k, k < 64 → bitAt (operation a b) k = op (bitAt a k) (bitAt b k))
    (left right : BitSet) (n : I64) :
    inInt n (bs8m_overlapMap operation left right) =
      if (1 ≤ div64 n.val - left.offset + 1 ∧ div64 n.val - left.offset + 1 ≤ left.bits.length) ∧
          (1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 ≤ right.bits.length) then
        op (inInt n left) (inInt n right) else inInt n left := by
  let delta := right.offset - left.offset
  let items := intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))
  have bounds : ∀ i ∈ items, 1 ≤ i ∧ i ≤ left.bits.length := by
    intro i membership
    have range := (bs_intRange_mem _ _ _).mp membership
    omega
  have result := bs8m_map_fold_member1 items left operation op
    (fun i => bitsGet right.bits (i - delta).toNat)
    bitLaw n (bs8m_intRange_nodup _ _) bounds
  have contains : div64 n.val - left.offset + 1 ∈ items ↔
      (1 ≤ div64 n.val - left.offset + 1 ∧ div64 n.val - left.offset + 1 ≤ left.bits.length) ∧
      (1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 ≤ right.bits.length) := by
    rw [bs_intRange_mem]
    dsimp only [delta]
    omega
  simp only [contains] at result
  have coordinate : div64 n.val - left.offset + 1 - delta = div64 n.val - right.offset + 1 := by
    dsimp only [delta]
    omega
  try dsimp only at result
  rw [coordinate] at result
  change inInt n (bs8m_overlapMap operation left right) = _ at result
  rw [result]
  by_cases both : (1 ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 ≤ left.bits.length) ∧
      (1 ≤ div64 n.val - right.offset + 1 ∧ div64 n.val - right.offset + 1 ≤ right.bits.length)
  · simp only [both, and_self, ↓reduceIte]
    rw [bs8m_inInt_at_index right n both.2]
  · simp only [both, and_self, ↓reduceIte]

/-- Intrinsic conjunction with complement computes bitwise set difference. -/
theorem bs8m_difference_bitAt (left right : U64) (k : Nat) (hk : k < 64) :
    bitAt (and_int left (not_int right)) k = (bitAt left k && !(bitAt right k)) := by
  rw [bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk,
    bs_and_bit, bs_not_bit _ _ hk]

/-- Difference's source flags remove every storage-growth and storage-deletion branch. -/
theorem bs8m_setdiffBang_storage (left right : BitSet)
    (leftPresent : left.offset ≠ noOffset) (rightPresent : right.offset ≠ noOffset) :
    setdiffBang left right =
      bs8m_overlapMap (fun a b => and_int a (not_int b)) left right := by
  unfold setdiffBang matchedMap matchedMapBits bs8m_overlapMap
  simp only [Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_beq, Bool.true_beq, Bool.false_eq_true, Bool.true_eq, leftPresent, rightPresent, ↓reduceIte, ite_self]

/-- The difference specialization preserves shape and implements the exact membership difference. -/
theorem bs8m_setdiffBang_spec (left right : BitSet) (hl : WF left) (hr : WF right) :
    WF (setdiffBang left right) ∧
      ∀ n, inInt n (setdiffBang left right) = (inInt n left && !(inInt n right)) := by
  by_cases leftEmpty : left.offset = noOffset
  · have nilLeft := hl.1 leftEmpty
    have result : setdiffBang left right = left := by
      simp only [setdiffBang, matchedMap, leftEmpty, ↓reduceIte] <;> rfl
    rw [result]
    refine ⟨hl, ?_⟩
    intro n
    have absent : inInt n left = false := by
      apply bs8m_inInt_outside
      rw [nilLeft]
      simp only [List.length_nil, Int.natCast_zero]
      omega
    simp only [absent, Bool.false_and]
  · by_cases rightEmpty : right.offset = noOffset
    · have nilRight := hr.1 rightEmpty
      have result : setdiffBang left right = left := by
        simp only [setdiffBang, matchedMap, leftEmpty, rightEmpty, ↓reduceIte] <;> rfl
      rw [result]
      refine ⟨hl, ?_⟩
      intro n
      have absent : inInt n right = false := by
        apply bs8m_inInt_outside
        rw [nilRight]
        simp only [List.length_nil, Int.natCast_zero]
        omega
      simp only [absent, Bool.not_false, Bool.and_true]
    · rw [bs8m_setdiffBang_storage left right leftEmpty rightEmpty]
      refine ⟨bs8_WF_of_shape left _ hl rfl (bs8m_overlapMap_length _ left right), ?_⟩
      intro n
      rw [bs8m_overlapMap_member (fun a b => and_int a (not_int b))
        (fun a b => a && !b) bs8m_difference_bitAt left right n]
      by_cases leftBounds : 1 ≤ div64 n.val - left.offset + 1 ∧
          div64 n.val - left.offset + 1 ≤ left.bits.length
      · by_cases rightBounds : 1 ≤ div64 n.val - right.offset + 1 ∧
            div64 n.val - right.offset + 1 ≤ right.bits.length
        · rw [if_pos ⟨leftBounds, rightBounds⟩]
        · rw [if_neg (fun h => rightBounds h.2), bs8m_inInt_outside right n rightBounds]
          simp only [Bool.not_false, Bool.and_true]
      · rw [if_neg (fun h => leftBounds h.1), bs8m_inInt_outside left n leftBounds]
        simp only [Bool.false_and]

end

section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- The intrinsic XOR computes Boolean exclusive disjunction at each bit. -/
theorem bs8m_xor_bitAt (left right : U64) (k : Nat) (hk : k < 64) :
    bitAt (xor_int left right) k = (bitAt left k ^^ bitAt right k) := by
  rw [bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk]
  simp only [xor_int, jlXorInt, bs_roundtrip_U64, BitVec.getLsbD_xor]

/-- XOR uses the same outer copy phases as union, after changing its common chunks. -/
def bs8m_xorNormalized (left right : BitSet) : BitSet :=
  bs8m_unionBegin (bs8m_unionEnd (bs8m_overlapMap xor_int left right) right) right

theorem bs8m_xorNormalized_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_xorNormalized left right) = (inInt n left ^^ inInt n right) := by
  have offset : (bs8m_unionEnd (bs8m_overlapMap xor_int left right) right).offset = left.offset :=
    (bs8m_unionEnd_shape (bs8m_overlapMap xor_int left right) right).1
  unfold bs8m_xorNormalized
  rw [bs8m_unionBegin_member, offset, bs8m_unionEnd_member, bs8m_overlapMap_length,
    bs8m_overlapMap_member xor_int (fun a b => a ^^ b) bs8m_xor_bitAt, bs8m_overlapMap_offset]
  change (((if (1 ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 ≤ left.bits.length) ∧
      (1 ≤ div64 n.val - right.offset + 1 ∧
      div64 n.val - right.offset + 1 ≤ right.bits.length) then
      (inInt n left ^^ inInt n right) else inInt n left) ||
      (decide (left.offset + left.bits.length ≤ div64 n.val) && inInt n right)) ||
      (decide (div64 n.val < left.offset) && inInt n right)) =
      (inInt n left ^^ inInt n right)
  by_cases leftInside : 1 ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 ≤ left.bits.length
  · have notBefore : ¬ div64 n.val < left.offset := by omega
    have notAfter : ¬ left.offset + left.bits.length ≤ div64 n.val := by omega
    simp only [notBefore, notAfter, decide_false, Bool.false_and, Bool.or_false]
    by_cases rightInside : 1 ≤ div64 n.val - right.offset + 1 ∧
        div64 n.val - right.offset + 1 ≤ right.bits.length
    · rw [if_pos ⟨leftInside, rightInside⟩]
    · rw [if_neg (fun h => rightInside h.2), bs8m_inInt_outside right n rightInside]
      cases inInt n left <;> rfl
  · rw [if_neg (fun h => leftInside h.1), bs8m_inInt_outside left n leftInside]
    by_cases before : div64 n.val < left.offset
    · simp only [before, decide_true, Bool.true_and]
      cases inInt n right <;> simp only [Bool.and_false, Bool.or_false, Bool.or_true] <;> rfl
    · have after : left.offset + left.bits.length ≤ div64 n.val := by omega
      simp only [before, after, decide_false, decide_true, Bool.false_and,
        Bool.true_and, Bool.or_false, Bool.false_or]
      cases inInt n right <;> rfl

/-- XOR storage has the same spanning endpoints as union storage. -/
theorem bs8m_xorNormalized_span (left right : BitSet) :
    (bs8m_xorNormalized left right).offset = min left.offset right.offset ∧
    (bs8m_xorNormalized left right).offset + (bs8m_xorNormalized left right).bits.length =
      max (left.offset + left.bits.length) (right.offset + right.bits.length) := by
  let difference := (right.bits.length : Int) + right.offset -
    ((left.bits.length : Int) + left.offset)
  have endOffset : (bs8m_unionEnd (bs8m_overlapMap xor_int left right) right).offset = left.offset :=
    (bs8m_unionEnd_shape (bs8m_overlapMap xor_int left right) right).1
  have endLength : (bs8m_unionEnd (bs8m_overlapMap xor_int left right) right).bits.length =
      if difference > 0 then left.bits.length + difference.toNat else left.bits.length := by
    simpa only [bs8m_overlapMap_length, bs8m_overlapMap_offset] using
      (bs8m_unionEnd_shape (bs8m_overlapMap xor_int left right) right).2
  have beginShape := bs8m_unionBegin_shape
    (bs8m_unionEnd (bs8m_overlapMap xor_int left right) right) right
  unfold bs8m_xorNormalized
  simp only [beginShape.1, beginShape.2, endOffset, endLength]
  by_cases leading : right.offset - left.offset < 0 <;>
    by_cases trailing : difference > 0 <;>
    simp only [leading, trailing, ↓reduceIte, Int.natCast_add] <;>
    constructor <;> dsimp only [difference] at * <;> omega

theorem bs8m_xorNormalized_WF (left right : BitSet) (hl : WF left) (hr : WF right)
    (leftPresent : left.offset ≠ noOffset) (rightPresent : right.offset ≠ noOffset) :
    WF (bs8m_xorNormalized left right) := by
  have leftBounds := hl.2 leftPresent
  have rightBounds := hr.2 rightPresent
  have shape := bs8m_xorNormalized_span left right
  have low : -(2 ^ 57) ≤ (bs8m_xorNormalized left right).offset := by
    rw [shape.1]
    omega
  have high : (bs8m_xorNormalized left right).offset +
      (bs8m_xorNormalized left right).bits.length ≤ 2 ^ 57 := by
    rw [shape.2]
    omega
  constructor
  · intro impossible
    rw [impossible] at low
    unfold noOffset at low
    omega
  · intro _
    exact ⟨low, high⟩

/-- Both false-annihilation flags are false for XOR; its outside spans are copied. -/
theorem bs8m_xorMapBits_normal (left right : BitSet) :
    let result := matchedMapBits xor_int left.bits left.offset right.bits right.offset false false
    (⟨result.1, result.2⟩ : BitSet) = bs8m_xorNormalized left right := by
  let delta := right.offset - left.offset
  let difference := (right.bits.length : Int) + right.offset -
    ((left.bits.length : Int) + left.offset)
  let commonWords := (intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))).foldl
    (fun words i => bitsSet words i.toNat
      (xor_int (bitsGet words i.toNat) (bitsGet right.bits (i - delta).toNat))) left.bits
  have commonLength : commonWords.length = left.bits.length :=
    bs8m_chunkTransform_length _ _ _ _
  have highZero (high : difference > 0) :
      (intRange ((left.bits.length : Int) + 1) delta).foldl
        (fun words i => bitsSet words i.toNat zero64)
        (bitsGrowEnd commonWords difference.toNat zero64) =
          bitsGrowEnd commonWords difference.toNat zero64 := by
    apply bs8m_zero_after_append
    · rw [commonLength]
      omega
    · rw [commonLength]
      dsimp only [difference, delta] at high ⊢
      omega
  have lowZero (words : List U64) (low : delta < 0) :
      (intRange ((right.bits.length : Int) + 1) (-delta)).foldl
        (fun words i => bitsSet words i.toNat zero64)
        (bitsGrowBeg words (-delta).toNat zero64) =
          bitsGrowBeg words (-delta).toNat zero64 := by
    apply bs8m_zero_after_prepend
    · omega
    · omega
  have offsetEq : left.offset + (right.offset - left.offset) = right.offset := by omega
  unfold matchedMapBits bs8m_xorNormalized bs8m_unionBegin bs8m_unionEnd bs8m_overlapMap
  dsimp only
  simp only [bs8m_chunkTransform_length, Bool.false_eq_true, ite_false, ite_self]
  by_cases high : difference > 0 <;>
    by_cases gap : (left.bits.length : Int) + 1 ≤ delta <;>
    by_cases low : delta < 0 <;>
    dsimp only [difference, delta] at high gap low <;>
    try simp only [high, gap, low, ↓reduceIte, ite_self]
  all_goals try rw [highZero high]
  all_goals try rw [lowZero _ low]
  all_goals (try simp only [offsetEq]) <;> rfl

theorem bs8m_symdiffBitSet_spec (left right : BitSet) (hl : WF left) (hr : WF right) :
    WF (symdiffBitSet left right) ∧
      ∀ n, inInt n (symdiffBitSet left right) = (inInt n left ^^ inInt n right) := by
  by_cases leftEmpty : left.offset = noOffset
  · have nilLeft := hl.1 leftEmpty
    have result : symdiffBitSet left right = right := by
      simp only [symdiffBitSet, matchedMap, leftEmpty, ↓reduceIte, copyBang] <;> rfl
    rw [result]
    refine ⟨hr, ?_⟩
    intro n
    have absent : inInt n left = false := by
      apply bs8m_inInt_outside
      rw [nilLeft]
      simp only [List.length_nil, Int.natCast_zero]
      omega
    rw [absent]
    cases inInt n right <;> rfl
  · by_cases rightEmpty : right.offset = noOffset
    · have nilRight := hr.1 rightEmpty
      have result : symdiffBitSet left right = left := by
        simp only [symdiffBitSet, matchedMap, leftEmpty, rightEmpty, ↓reduceIte] <;> rfl
      rw [result]
      refine ⟨hl, ?_⟩
      intro n
      have absent : inInt n right = false := by
        apply bs8m_inInt_outside
        rw [nilRight]
        simp only [List.length_nil, Int.natCast_zero]
        omega
      rw [absent]
      cases inInt n left <;> rfl
    · have result : symdiffBitSet left right = bs8m_xorNormalized left right := by
        simp only [symdiffBitSet, matchedMap, leftEmpty, rightEmpty, ↓reduceIte]
        exact bs8m_xorMapBits_normal left right
      rw [result]
      exact ⟨bs8m_xorNormalized_WF left right hl hr leftEmpty rightEmpty,
        bs8m_xorNormalized_member left right⟩

end

section

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- Taking a prefix preserves every read before the chosen cutoff. -/
theorem bs8m_getD_take (words : List U64) (count index : Nat) (h : index < count) :
    (words.take count).getD index zero64 = words.getD index zero64 := by
  induction count generalizing words index with
  | zero => omega
  | succ count ih =>
    cases words with
    | nil => rfl
    | cons word rest =>
      cases index with
      | zero => rfl
      | succ index => exact ih rest index (by omega)

/-- Dropping a prefix translates defaulted reads by its length. -/
theorem bs8m_getD_drop (words : List U64) (count index : Nat) :
    (words.drop count).getD index zero64 = words.getD (count + index) zero64 := by
  induction count generalizing words with
  | zero => simp only [List.drop_zero, Nat.zero_add]
  | succ count ih =>
    cases words with
    | nil => rfl
    | cons word rest =>
      rw [Nat.succ_add]
      exact ih rest

/-- Taking stored chunks removes exactly members at or beyond the absolute cutoff. -/
theorem bs8m_take_member (s : BitSet) (count : Nat) (n : I64) :
    inInt n {s with bits := s.bits.take count} =
      (inInt n s && decide (div64 n.val < s.offset + count)) := by
  by_cases original : 1 ≤ div64 n.val - s.offset + 1 ∧
      div64 n.val - s.offset + 1 ≤ s.bits.length
  · by_cases retained : div64 n.val < s.offset + count
    · have inside : 1 ≤ div64 n.val - s.offset + 1 ∧
          div64 n.val - s.offset + 1 ≤ (s.bits.take count).length := by
        rw [List.length_take]
        omega
      rw [bs8m_inInt_at_index _ n inside, bs8m_inInt_at_index s n original]
      simp only [retained, decide_true, Bool.and_true]
      unfold bitsGet
      rw [bs8m_getD_take _ _ _ (by omega)]
    · have outside : ¬(1 ≤ div64 n.val - s.offset + 1 ∧
          div64 n.val - s.offset + 1 ≤ (s.bits.take count).length) := by
        rw [List.length_take]
        omega
      rw [bs8m_inInt_outside _ n outside]
      simp only [retained, decide_false, Bool.and_false]
  · have outside : ¬(1 ≤ div64 n.val - s.offset + 1 ∧
        div64 n.val - s.offset + 1 ≤ (s.bits.take count).length) := by
      rw [List.length_take]
      omega
    rw [bs8m_inInt_outside _ n outside, bs8m_inInt_outside s n original] <;>
      simp only [Bool.false_and]

/-- Dropping chunks and shifting their origin removes exactly members below the new origin. -/
theorem bs8m_drop_member (s : BitSet) (count : Nat) (n : I64) :
    inInt n ⟨s.bits.drop count, s.offset + count⟩ =
      (inInt n s && decide (s.offset + count ≤ div64 n.val)) := by
  by_cases original : 1 ≤ div64 n.val - s.offset + 1 ∧
      div64 n.val - s.offset + 1 ≤ s.bits.length
  · by_cases retained : s.offset + count ≤ div64 n.val
    · have inside : 1 ≤ div64 n.val - (s.offset + count) + 1 ∧
          div64 n.val - (s.offset + count) + 1 ≤ (s.bits.drop count).length := by
        rw [List.length_drop]
        omega
      rw [bs8m_inInt_at_index _ n inside, bs8m_inInt_at_index s n original]
      simp only [retained, decide_true, Bool.and_true]
      unfold bitsGet
      rw [bs8m_getD_drop]
      have coordinate : count + ((div64 n.val - (s.offset + count) + 1).toNat - 1) =
          (div64 n.val - s.offset + 1).toNat - 1 := by omega
      rw [coordinate]
    · have outside : ¬(1 ≤ div64 n.val - (s.offset + count) + 1 ∧
          div64 n.val - (s.offset + count) + 1 ≤ (s.bits.drop count).length) := by
        omega
      rw [bs8m_inInt_outside _ n outside]
      simp only [retained, decide_false, Bool.and_false]
  · have outside : ¬(1 ≤ div64 n.val - (s.offset + count) + 1 ∧
        div64 n.val - (s.offset + count) + 1 ≤ (s.bits.drop count).length) := by
      rw [List.length_drop]
      omega
    rw [bs8m_inInt_outside _ n outside, bs8m_inInt_outside s n original] <;>
      simp only [Bool.false_and]

/-- A capped prefix deletion equals the uncapped deletion once the cap covers the vector. -/
theorem bs8m_drop_min_int (words : List U64) (bound : Nat) (count : Int)
    (lengthBound : words.length ≤ bound) (nonnegative : 0 ≤ count) :
    words.drop (min (bound : Int) count).toNat = words.drop count.toNat := by
  by_cases capped : (bound : Int) ≤ count
  · rw [Int.min_eq_left capped, Int.toNat_natCast]
    rw [List.drop_eq_nil_of_le lengthBound,
      List.drop_eq_nil_of_le (show words.length ≤ count.toNat by omega)]
  · rw [Int.min_eq_right (by omega)]

/-- Intersection's trailing deletion, after mapping the common chunks. -/
def bs8m_intersectionEnd (left right : BitSet) : BitSet :=
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  if difference < 0 then
    {left with bits := bitsDeleteEnd left.bits (min (left.bits.length : Int) (-difference)).toNat}
  else left

theorem bs8m_intersectionEnd_shape (left right : BitSet) :
    (bs8m_intersectionEnd left right).offset = left.offset ∧
    (bs8m_intersectionEnd left right).bits.length ≤ left.bits.length := by
  unfold bs8m_intersectionEnd
  dsimp only
  split
  · refine ⟨rfl, ?_⟩
    simp only [bitsDeleteEnd, List.length_take]
    omega
  · exact ⟨rfl, Nat.le_refl _⟩

/-- Trailing deletion filters precisely at the right operand's endpoint. -/
theorem bs8m_intersectionEnd_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_intersectionEnd left right) =
      (inInt n left && decide (div64 n.val < right.offset + right.bits.length)) := by
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  by_cases shrinks : difference < 0
  · dsimp only [difference] at shrinks
    have run : bs8m_intersectionEnd left right =
        {left with bits := (left.bits.take
          (left.bits.length - (min (left.bits.length : Int) (-difference)).toNat))} := by
      simp only [bs8m_intersectionEnd, difference, shrinks, ↓reduceIte, bitsDeleteEnd]
    rw [run, bs8m_take_member]
    by_cases inside : 1 ≤ div64 n.val - left.offset + 1 ∧
        div64 n.val - left.offset + 1 ≤ left.bits.length
    · have cutoff : div64 n.val < left.offset +
          (left.bits.length - (min (left.bits.length : Int) (-difference)).toNat : Nat) ↔
          div64 n.val < right.offset + right.bits.length := by
        try dsimp only [difference] at shrinks ⊢
        omega
      simp only [cutoff]
    · rw [bs8m_inInt_outside left n inside]
      simp only [Bool.false_and]
  · dsimp only [difference] at shrinks
    have run : bs8m_intersectionEnd left right = left := by
      simp only [bs8m_intersectionEnd, shrinks, ↓reduceIte]
    rw [run]
    by_cases inside : 1 ≤ div64 n.val - left.offset + 1 ∧
        div64 n.val - left.offset + 1 ≤ left.bits.length
    · have cutoff : div64 n.val < right.offset + right.bits.length := by
        try dsimp only [difference] at shrinks
        omega
      simp only [cutoff, decide_true, Bool.and_true]
    · rw [bs8m_inInt_outside left n inside]
      simp only [Bool.false_and]

/-- Intersection's leading deletion, with its matching origin shift. -/
def bs8m_intersectionBegin (left right : BitSet) : BitSet :=
  let delta := right.offset - left.offset
  if delta > 0 then ⟨bitsDeleteBeg left.bits delta.toNat, right.offset⟩ else left

theorem bs8m_intersectionBegin_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_intersectionBegin left right) =
      (inInt n left && decide (right.offset ≤ div64 n.val)) := by
  by_cases shrinks : right.offset - left.offset > 0
  · have origin : left.offset + ((right.offset - left.offset).toNat : Int) = right.offset := by omega
    have result := bs8m_drop_member left (right.offset - left.offset).toNat n
    simpa only [bs8m_intersectionBegin, shrinks, ↓reduceIte, bitsDeleteBeg, origin] using result
  · simp only [bs8m_intersectionBegin, shrinks, ↓reduceIte]
    by_cases inside : 1 ≤ div64 n.val - left.offset + 1 ∧
        div64 n.val - left.offset + 1 ≤ left.bits.length
    · have cutoff : right.offset ≤ div64 n.val := by omega
      simp only [cutoff, decide_true, Bool.and_true]
    · rw [bs8m_inInt_outside left n inside]
      simp only [Bool.false_and]

/-- The normalized trailing trim preserves the input's representation invariant. -/
theorem bs8m_intersectionEnd_WF (left right : BitSet) (hl : WF left) :
    WF (bs8m_intersectionEnd left right) := by
  have shape := bs8m_intersectionEnd_shape left right
  constructor
  · intro sentinel
    apply List.length_eq_zero_iff.mp
    have empty := hl.1 (shape.1 ▸ sentinel)
    have bound := shape.2
    rw [empty, List.length_nil] at bound
    omega
  · intro present
    have oldPresent : left.offset ≠ noOffset := by simpa only [shape.1] using present
    have bounds := hl.2 oldPresent
    rw [shape.1]
    exact ⟨bounds.1, by omega⟩

/-- Shifting to the other operand's origin preserves the signed chunk bounds. -/
theorem bs8m_intersectionBegin_WF (left right : BitSet) (hl : WF left) (hr : WF right)
    (leftPresent : left.offset ≠ noOffset) (rightPresent : right.offset ≠ noOffset) :
    WF (bs8m_intersectionBegin left right) := by
  have leftBounds := hl.2 leftPresent
  have rightBounds := hr.2 rightPresent
  unfold bs8m_intersectionBegin
  dsimp only
  split
  · rename_i shrinks
    constructor
    · intro impossible
      exact False.elim (rightPresent impossible)
    · intro _
      simp only [bitsDeleteBeg, List.length_drop]
      exact ⟨rightBounds.1, by omega⟩
  · exact hl

/-- The common-AND map followed by the two shrinking phases. -/
def bs8m_intersectionNormalized (left right : BitSet) : BitSet :=
  bs8m_intersectionBegin (bs8m_intersectionEnd (bs8m_overlapMap and_int left right) right) right

theorem bs8m_intersectionNormalized_member (left right : BitSet) (n : I64) :
    inInt n (bs8m_intersectionNormalized left right) = (inInt n left && inInt n right) := by
  have bitLaw : ∀ a b k, k < 64 → bitAt (and_int a b) k = (bitAt a k && bitAt b k) := by
    intro a b k hk
    rw [bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk, bs_bitAt_eq _ _ hk, bs_and_bit]
  unfold bs8m_intersectionNormalized
  rw [bs8m_intersectionBegin_member, bs8m_intersectionEnd_member,
    bs8m_overlapMap_member and_int (· && ·) bitLaw]
  by_cases leftBounds : 1 ≤ div64 n.val - left.offset + 1 ∧
      div64 n.val - left.offset + 1 ≤ left.bits.length
  · by_cases rightBounds : 1 ≤ div64 n.val - right.offset + 1 ∧
        div64 n.val - right.offset + 1 ≤ right.bits.length
    · have before : div64 n.val < right.offset + right.bits.length := by omega
      have after : right.offset ≤ div64 n.val := by omega
      simp only [leftBounds, rightBounds, and_self, ↓reduceIte, before, after, decide_true, Bool.and_true]
    · rw [if_neg (fun h => rightBounds h.2), bs8m_inInt_outside right n rightBounds]
      by_cases before : div64 n.val < right.offset + right.bits.length
      · have notAfter : ¬right.offset ≤ div64 n.val := by omega
        simp only [notAfter, decide_false, Bool.and_false]
      · simp only [before, decide_false, Bool.and_false, Bool.false_and]
  · rw [if_neg (fun h => leftBounds h.1), bs8m_inInt_outside left n leftBounds]
    simp only [Bool.false_and]

theorem bs8m_intersectionNormalized_WF (left right : BitSet) (hl : WF left) (hr : WF right)
    (leftPresent : left.offset ≠ noOffset) (rightPresent : right.offset ≠ noOffset) :
    WF (bs8m_intersectionNormalized left right) := by
  have mappedWF : WF (bs8m_overlapMap and_int left right) :=
    bs8_WF_of_shape left _ hl rfl (bs8m_overlapMap_length _ left right)
  have endWF := bs8m_intersectionEnd_WF (bs8m_overlapMap and_int left right) right mappedWF
  have endPresent : (bs8m_intersectionEnd (bs8m_overlapMap and_int left right) right).offset ≠ noOffset := by
    rw [(bs8m_intersectionEnd_shape (bs8m_overlapMap and_int left right) right).1]
    exact leftPresent
  exact bs8m_intersectionBegin_WF _ right endWF hr endPresent rightPresent

/-- The source's two true flags reduce matched mapping to the normalized shrinking phases. -/
theorem bs8m_intersectionMapBits_normal (left right : BitSet) :
    let result := matchedMapBits and_int left.bits left.offset right.bits right.offset true true
    (⟨result.1, result.2⟩ : BitSet) = bs8m_intersectionNormalized left right := by
  let delta := right.offset - left.offset
  let difference := (right.bits.length : Int) + right.offset - ((left.bits.length : Int) + left.offset)
  let commonWords := (intRange (max 1 (1 + delta))
    (min (left.bits.length : Int) (right.bits.length + delta))).foldl
    (fun words i => bitsSet words i.toNat
      (and_int (bitsGet words i.toNat) (bitsGet right.bits (i - delta).toNat))) left.bits
  have commonLength : commonWords.length = left.bits.length :=
    bs8m_chunkTransform_length _ _ _ _
  have commonUncapped (nonnegative : 0 ≤ delta) :
      bitsDeleteBeg commonWords (min (left.bits.length : Int) delta).toNat =
        bitsDeleteBeg commonWords delta.toNat :=
    bs8m_drop_min_int commonWords left.bits.length delta (by omega) nonnegative
  have trimmedUncapped (nonnegative : 0 ≤ delta) :
      bitsDeleteBeg
        (bitsDeleteEnd commonWords (min (left.bits.length : Int) (-difference)).toNat)
        (min (left.bits.length : Int) delta).toNat =
      bitsDeleteBeg
        (bitsDeleteEnd commonWords (min (left.bits.length : Int) (-difference)).toNat)
        delta.toNat := by
    apply bs8m_drop_min_int
    · simp only [bitsDeleteEnd, List.length_take, commonLength]
      omega
    · exact nonnegative
  have origin : left.offset + (right.offset - left.offset) = right.offset := by omega
  unfold matchedMapBits bs8m_intersectionNormalized bs8m_intersectionBegin
    bs8m_intersectionEnd bs8m_overlapMap
  dsimp only
  simp only [bs8m_chunkTransform_length, ↓reduceIte]
  by_cases high : difference > 0 <;> by_cases low : difference < 0 <;>
    by_cases before : delta < 0 <;> by_cases after : delta > 0 <;>
    dsimp only [difference, delta] at high low before after <;>
    try simp only [high, low, before, after, ↓reduceIte]
  all_goals try omega
  all_goals try rw [commonUncapped (by omega)]
  all_goals try rw [trimmedUncapped (by omega)]
  all_goals (try simp only [origin]) <;> rfl

/-- In-place intersection preserves the invariant and implements pointwise conjunction. -/
theorem bs8m_intersectBang_spec (left right : BitSet) (hl : WF left) (hr : WF right) :
    WF (intersectBang left right) ∧
      ∀ n, inInt n (intersectBang left right) = (inInt n left && inInt n right) := by
  by_cases leftEmpty : left.offset = noOffset
  · have nilLeft := hl.1 leftEmpty
    have run : intersectBang left right = left := by
      simp only [intersectBang, matchedMap, leftEmpty, ↓reduceIte] <;> rfl
    rw [run]
    refine ⟨hl, ?_⟩
    intro n
    have absent : inInt n left = false := by
      apply bs8m_inInt_outside
      rw [nilLeft]
      simp only [List.length_nil, Int.natCast_zero]
      omega
    simp only [absent, Bool.false_and]
  · by_cases rightEmpty : right.offset = noOffset
    · have nilRight := hr.1 rightEmpty
      have run : intersectBang left right = new := by
        simp only [intersectBang, matchedMap, leftEmpty, rightEmpty, ↓reduceIte, emptyBang] <;> rfl
      rw [run]
      refine ⟨bs_new_WF, ?_⟩
      intro n
      have absent : inInt n right = false := by
        apply bs8m_inInt_outside
        rw [nilRight]
        simp only [List.length_nil, Int.natCast_zero]
        omega
      simp only [new, bs_inInt_nil, absent, Bool.and_false]
    · have run : intersectBang left right = bs8m_intersectionNormalized left right := by
        simp only [intersectBang, matchedMap, leftEmpty, rightEmpty, ↓reduceIte]
        exact bs8m_intersectionMapBits_normal left right
      rw [run]
      exact ⟨bs8m_intersectionNormalized_WF left right hl hr leftEmpty rightEmpty,
        bs8m_intersectionNormalized_member left right⟩

/-- Choosing the smaller copied argument leaves nonmutating intersection's semantics unchanged. -/
theorem bs8m_intersect_spec (left right : BitSet) (hl : WF left) (hr : WF right) :
    WF (intersect left right) ∧
      ∀ n, inInt n (intersect left right) = (inInt n left && inInt n right) := by
  have copiedLeft : copy left = left := (JuliaLean.ChatGPT.Batch4.Group16.BitsetscovBitsetCopy_proven left left).2.1
  have copiedRight : copy right = right := (JuliaLean.ChatGPT.Batch4.Group16.BitsetscovBitsetCopy_proven right right).2.1
  unfold intersect
  rw [copiedLeft, copiedRight]
  split
  · exact bs8m_intersectBang_spec left right hl hr
  · have result := bs8m_intersectBang_spec right left hr hl
    refine ⟨result.1, ?_⟩
    intro n
    rw [result.2 n, Bool.and_comm]

/-- The exact frozen matched-map target follows from the five public operation contracts. -/
theorem BitsetscovBitsetMatchedMap_proven :
    JuliaLean.Proofs.base.bitset.Round3.BitSetMatchedPreserves := by
  intro left right n hl hr spanFits
  have unionResult := bs8m_unionBang_spec left right hl hr
  have intersectionResult := bs8m_intersectBang_spec left right hl hr
  have differenceResult := bs8m_setdiffBang_spec left right hl hr
  have xorResult := bs8m_symdiffBitSet_spec left right hl hr
  have copiedIntersectionResult := bs8m_intersect_spec left right hl hr
  exact ⟨unionResult.1, intersectionResult.1, differenceResult.1, xorResult.1,
    copiedIntersectionResult.1, unionResult.2 n, intersectionResult.2 n,
    differenceResult.2 n, xorResult.2 n, copiedIntersectionResult.2 n⟩

end

section

open JuliaLean JuliaLean.base.bitset JuliaLean.Proofs.base.bitset
open JuliaLean.ChatGPT.Batch3.Group3

/-- The concrete Int64 unit-range interface either returns unchanged or performs its range update. -/
theorem bs8m_unionRange_unit (s : BitSet) (first last : I64) :
    unionRange s (UnitRangeI64.mk first last) =
      if first.val > last.val then .ok s else .ok (unionRangeBits s first last) := by
  change (if decide (first.val > last.val) = true then (Except.ok s : Result BitSet)
    else Except.ok (unionRangeBits s first last)) = _
  simp only [decide_eq_true_eq]

/-- Each normal-returning heterogeneous union fold preserves the invariant and its membership union. -/
theorem bs8m_unionArgs_success (s : BitSet) (arguments : List UnionArg) (out : BitSet)
    (hs : WF s) (valid : ∀ arg ∈ arguments, unionArgValid arg)
    (run : unionArgs s arguments = .ok out) :
    WF out ∧ ∀ n : I64, member out n.val =
      (member s n.val || arguments.any (fun arg => unionArgMember arg n.val)) := by
  induction arguments generalizing s out with
  | nil =>
    change (Except.ok s : Result BitSet) = .ok out at run
    cases run
    refine ⟨hs, ?_⟩
    intro n
    simp only [List.any_nil, Bool.or_false]
  | cons argument rest ih =>
    have headValid := valid argument (List.Mem.head _)
    have tailValid : ∀ arg ∈ rest, unionArgValid arg :=
      fun arg h => valid arg (List.mem_cons_of_mem argument h)
    cases argument with
    | bitset other =>
      change unionArgs (unionBang s other) rest = .ok out at run
      have step := bs8m_unionBang_spec s other hs headValid
      have tail := ih (unionBang s other) out step.1 tailValid run
      refine ⟨tail.1, ?_⟩
      intro n
      have stepMember : member (unionBang s other) n.val = (member s n.val || member other n.val) := by
        simpa only [bs_member_intval] using step.2 n
      rw [tail.2 n, stepMember]
      simp only [List.any_cons, unionArgMember, Bool.or_assoc]
    | range first last =>
      change (do
        let next ← unionRange s (UnitRangeI64.mk first last)
        unionArgs next rest) = .ok out at run
      rw [bs8m_unionRange_unit] at run
      by_cases empty : first.val > last.val
      · rw [if_pos empty] at run
        change unionArgs s rest = .ok out at run
        have tail := ih s out hs tailValid run
        refine ⟨tail.1, ?_⟩
        intro n
        have impossible : ¬(first.val ≤ n.val ∧ n.val ≤ last.val) := by omega
        simpa only [List.any_cons, unionArgMember, impossible, decide_false, Bool.false_or]
          using tail.2 n
      · rw [if_neg empty] at run
        change unionArgs (unionRangeBits s first last) rest = .ok out at run
        have stepWF := bs8_unionRangeBits_WF s first last hs
        have tail := ih (unionRangeBits s first last) out stepWF tailValid run
        refine ⟨tail.1, ?_⟩
        intro n
        rw [tail.2 n, bs8_unionRangeBits_member s first last n hs (by omega)]
        simp only [List.any_cons, unionArgMember, Bool.or_assoc]
    | iterator values =>
      change (do
        let next ← unionIterator s values
        unionArgs next rest) = .ok out at run
      obtain ⟨next, nextRun, nextWF, nextMember⟩ :=
        bs8_unionIterator_valid s values hs headValid
      rw [nextRun] at run
      change unionArgs next rest = .ok out at run
      have tail := ih next out nextWF tailValid run
      refine ⟨tail.1, ?_⟩
      intro n
      rw [tail.2 n, nextMember n.val]
      simp only [List.any_cons, unionArgMember, List.contains_eq_mem, Bool.or_assoc]

/-- The exact frozen public heterogeneous union contract. -/
theorem BitsetscovBitsetUnion_proven : JuliaLean.Proofs.base.bitset.BitSetUnionSpec := by
  intro s arguments n hs valid out run
  have copied : copy s = s := (JuliaLean.ChatGPT.Batch4.Group16.BitsetscovBitsetCopy_proven s s).2.1
  unfold union at run
  rw [copied] at run
  exact (bs8m_unionArgs_success s arguments out hs valid run).2 n

end



section
open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.bitset
open JuliaLean.Proofs.base.bitset JuliaLean.ChatGPT.Batch3.Group3

/-- Within a chunk, the iterator's mathematical values are strictly increasing. -/
theorem bs8i_word_sorted (chunk : Int) (word : U64) :
    (bs_wordValues chunk word).Pairwise (· < ·) := by
  rw [bs_wordValues, List.pairwise_map]
  have h : (bs_wordPositions word).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  exact h.imp (by intro a b hab; omega)

/-- Consecutive storage chunks preserve the strict order across their boundary. -/
theorem bs8i_chunks_sorted (offset : Int) (words : List U64) :
    (bs_chunkValues offset words).Pairwise (· < ·) := by
  induction words generalizing offset with
  | nil => exact .nil
  | cons word words ih =>
    rw [bs_chunkValues, List.pairwise_append]
    refine ⟨bs8i_word_sorted offset word, ih (offset + 1), ?_⟩
    intro a ha b hb
    obtain ⟨bit, hbit, _, heqa⟩ := (bs_wordValues_mem offset a word).mp ha
    obtain ⟨i, _, hi⟩ := (bs_chunkValues_indexed (offset + 1) b words).mp hb
    obtain ⟨bit', hbit', _, heqb⟩ := (bs_wordValues_mem _ _ _).mp hi
    omega

/-- The native iterator therefore visits its members in strictly increasing order. -/
theorem bs8i_iterated_sorted (s : BitSet) (hs : WF s) :
    (iterated s).Pairwise (fun a b => a.val < b.val) := by
  have h : ((iterated s).map (fun x : I64 => x.val)).Pairwise (· < ·) := by
    rw [bs_iterated_values s hs]
    exact bs8i_chunks_sorted _ _
  simpa only [List.pairwise_map] using h

/-- Full iterator membership is exactly mathematical integer membership. -/
theorem bs8i_iterated_members (s : BitSet) (hs : WF s) (n : Int) :
    (iterated s).any (fun x => x.val = n) = member s n := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, bs_member_chunkValues s hs n, ← bs_iterated_values s hs]
  simp only [List.mem_map, decide_eq_true_eq]

/-- A nonempty valid storage interval has an exactly representable bit offset. -/
theorem bs8i_offset (s : BitSet) (hs : WF s) (hne : s.offset ≠ noOffset)
    (hlen : 0 < s.bits.length) : (intoffset s).val = 64 * s.offset := by
  have hr := hs.2 hne
  have hoff : IntTy.i64.min ≤ s.offset ∧ s.offset ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ s.offset ∧ s.offset ≤ 9223372036854775807
    change -144115188075855872 ≤ s.offset ∧ s.offset + s.bits.length ≤ 144115188075855872 at hr
    omega
  have hbase : IntTy.i64.min ≤ s.offset * 64 ∧ s.offset * 64 ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ s.offset * 64 ∧ s.offset * 64 ≤ 9223372036854775807
    change -144115188075855872 ≤ s.offset ∧ s.offset + s.bits.length ≤ 144115188075855872 at hr
    omega
  unfold intoffset
  rw [bs_shift6I64_val _ (by rw [bs_int64_val _ hoff]; exact hbase), bs_int64_val _ hoff]
  omega

/-- The intrinsic population-count fold counts exactly the accepted bit positions. -/
theorem bs8i_fold_count (p : Nat) (positions : List Nat) (acc : Nat) :
    positions.foldl (fun r i => r + p / 2 ^ i % 2) acc =
      acc + positions.countP (fun i => p.testBit i) := by
  induction positions generalizing acc with
  | nil => simp only [List.foldl_nil, List.countP_nil, Nat.add_zero]
  | cons bit positions ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    have hb : p / 2 ^ bit % 2 = if p.testBit bit then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ bit) with h | h <;> simp only [h] <;> rfl
    rw [hb]
    cases p.testBit bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Count-ones agrees with the iterator's position list without another proof-module import. -/
theorem bs8i_word_count (word : U64) :
    (count_ones word).val = (bs_wordPositions word).length := by
  unfold count_ones ctpop_int jlCtpopInt
  rw [bs8i_fold_count, Nat.zero_add]
  have hc : (List.range IntTy.u64.bits).countP
      (fun bit => (fromJInt word).toNat.testBit bit) ≤ 64 :=
    Nat.le_trans List.countP_le_length (by rw [List.length_range]; decide)
  rw [bs_small_counter _ hc]
  simp only [List.countP_eq_length_filter, bs_wordPositions, BitVec.getLsbD] <;> rfl

/-- A chunk-value list has the same length at every absolute offset. -/
theorem bs8i_chunk_length_offset (a b : Int) (words : List U64) :
    (bs_chunkValues a words).length = (bs_chunkValues b words).length := by
  induction words generalizing a b with
  | nil => rfl
  | cons word words ih =>
    simp only [bs_chunkValues, List.length_append, bs_wordValues, List.length_map]
    rw [ih (a + 1) (b + 1)]

/-- The count fold cannot wrap when its initial value and entire remaining budget fit. -/
theorem bs8i_count_fold (words : List U64) (acc : I64)
    (hlo : 0 ≤ acc.val)
    (hhi : acc.val + (words.length : Int) * 64 ≤ IntTy.i64.max) :
    (words.foldl (fun count word => count + count_ones word) acc).val =
      acc.val + (bs_chunkValues 0 words).length := by
  induction words generalizing acc with
  | nil => simp only [List.foldl_nil, bs_chunkValues, List.length_nil, Int.natCast_zero, Int.add_zero]
  | cons word words ih =>
    have hw := bs_wordValues_length 0 word
    have hlen : (bs_wordPositions word).length ≤ 64 := by
      simpa only [bs_wordValues, List.length_map] using hw
    have hcount := bs8i_word_count word
    have hacc : (acc + count_ones word).val = acc.val + (bs_wordPositions word).length := by
      change wrapInt .i64 (acc.val + (count_ones word).val) = _
      rw [hcount]
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
      change acc.val + ((word :: words).length : Int) * 64 ≤ 9223372036854775807 at hhi
      simp only [List.length_cons] at hhi
      omega
    rw [List.foldl_cons, ih (acc + count_ones word) (by rw [hacc]; omega) (by
      rw [hacc]
      simp only [List.length_cons] at hhi
      omega)]
    rw [hacc, bs_chunkValues, List.length_append,
      bs_wordValues, List.length_map, Int.zero_add, bs8i_chunk_length_offset 1 0 words]
    omega

/-- Under the frozen chunk bound, cardinality is the length of the complete iterator. -/
theorem bs8i_length (s : BitSet) (hs : WF s) (hsize : s.bits.length < 2^56) :
    (JuliaLean.base.bitset.length s).val = (iterated s).length := by
  have hbudget : (int64 0).val + (s.bits.length : Int) * 64 ≤ IntTy.i64.max := by
    change (0 : Int) + (s.bits.length : Int) * 64 ≤ 9223372036854775807
    change s.bits.length < 72057594037927936 at hsize
    omega
  unfold JuliaLean.base.bitset.length
  rw [bs8i_count_fold _ _ (by decide) hbudget]
  have hlen := congrArg List.length (bs_iterated_values s hs)
  simp only [List.length_map] at hlen
  rw [bs8i_chunk_length_offset 0 s.offset s.bits, ← hlen]
  simp only [show (int64 0).val = 0 from rfl, Int.zero_add]

/-- The printing loop's noninitial branch is a comma-separated fold over its iteration trace. -/
theorem bs8i_show_loop (s : BitSet) (fuel : Nat) (state : U64 × Nat) (out : String) :
    showStr.loop s fuel state out false =
      ((iterated.walk s fuel state).map (fun n => toString n.val)).foldl
        (fun text item => text ++ ", " ++ item) out := by
  induction fuel generalizing state out with
  | zero => rfl
  | succ fuel ih =>
    cases h : iterate s state with
    | none => simp only [showStr.loop, iterated.walk, h, List.map_nil, List.foldl_nil]
    | some next =>
      rcases next with ⟨value, next⟩
      simp only [showStr.loop, iterated.walk, h, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.foldl_cons]
      exact ih next (out ++ ", " ++ toString value.val)

/-- The initial printing branch contributes no separator before its first value. -/
theorem bs8i_show_first (s : BitSet) (fuel : Nat) (state : U64 × Nat) :
    showStr.loop s fuel state "" true =
      joinComma ((iterated.walk s fuel state).map (fun n => toString n.val)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases h : iterate s state with
    | none => simp only [showStr.loop, iterated.walk, h, List.map_nil, joinComma]
    | some next =>
      rcases next with ⟨value, next⟩
      simp only [showStr.loop, iterated.walk, h, ↓reduceIte,
        List.map_cons, joinComma, String.empty_append]
      exact bs8i_show_loop s fuel next (toString value.val)

theorem bs8i_show (s : BitSet) :
    showStr s = "BitSet([" ++ joinComma ((iterated s).map (fun n => toString n.val)) ++ "])" := by
  unfold showStr iterated
  rw [bs8i_show_first]

/-- The flat bit-position list used by the extrema search routines. -/
def bs8i_flatPositions (words : List U64) : List Nat :=
  (List.range (words.length * 64)).filter
    (fun p => bitAt (bitsGet words (p / 64 + 1)) (p % 64))

def bs8i_flatValues (offset : Int) (words : List U64) : List Int :=
  (bs8i_flatPositions words).map (fun (p : Nat) => offset * 64 + (p : Int))

/-- Flat and chunk-wise enumerations select the same mathematical integers. -/
theorem bs8i_flat_members (offset n : Int) (words : List U64) :
    n ∈ bs8i_flatValues offset words ↔ n ∈ bs_chunkValues offset words := by
  simp only [bs8i_flatValues, List.mem_map, bs8i_flatPositions,
    List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨p, ⟨hp, hv⟩, rfl⟩
    apply (bs_chunkValues_indexed offset _ words).mpr
    have hdiv : p / 64 < words.length := by omega
    refine ⟨p / 64, hdiv, ?_⟩
    apply (bs_wordValues_mem _ _ _).mpr
    refine ⟨p % 64, Nat.mod_lt _ (by decide), ?_, ?_⟩
    · rw [bs_bitAt_eq _ _ (Nat.mod_lt p (by decide))] at hv
      simpa only [bitsGet, Nat.add_sub_cancel] using hv
    · have he := Nat.mod_add_div p 64
      omega
  · intro hn
    obtain ⟨i, hi, hv⟩ := (bs_chunkValues_indexed offset n words).mp hn
    obtain ⟨bit, hbit, hv, he⟩ := (bs_wordValues_mem _ _ _).mp hv
    refine ⟨i * 64 + bit, ⟨by omega, ?_⟩, ?_⟩
    · have hdiv : (i * 64 + bit) / 64 = i := by omega
      have hmod : (i * 64 + bit) % 64 = bit := by omega
      rw [hdiv, hmod, bs_bitAt_eq _ _ hbit]
      simpa only [bitsGet, Nat.add_sub_cancel] using hv
    · omega

theorem bs8i_flat_sorted (offset : Int) (words : List U64) :
    (bs8i_flatValues offset words).Pairwise (· < ·) := by
  rw [bs8i_flatValues, List.pairwise_map]
  have h : (bs8i_flatPositions words).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  exact h.imp (by intro a b hab; omega)

/-- Strictly ordered lists with the same membership coincide, connecting search and iteration. -/
theorem bs8i_flat_values (offset : Int) (words : List U64) :
    bs_chunkValues offset words = bs8i_flatValues offset words := by
  have hc := bs8i_chunks_sorted offset words
  have hf := bs8i_flat_sorted offset words
  have hcn : (bs_chunkValues offset words).Nodup := hc.imp (by intro a b hab; omega)
  have hfn : (bs8i_flatValues offset words).Nodup := hf.imp (by intro a b hab; omega)
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => by omega) hc hf
  apply (List.perm_ext_iff_of_nodup hcn hfn).mpr
  intro n
  exact (bs8i_flat_members offset n words).symm

/-- A search predicate can be changed using facts about the searched list only. -/
theorem bs8i_find_congr {A : Type} (items : List A) (p q : A → Bool)
    (h : ∀ item ∈ items, p item = q item) : items.find? p = items.find? q := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [List.find?_cons, List.find?_cons, h item List.mem_cons_self]
    split
    · rfl
    · exact ih (fun x hx => h x (List.mem_cons_of_mem item hx))

/-- The first-position search is the head of the flat accepted positions. -/
theorem bs8i_findnext (words : List U64) :
    bitsFindnext words 0 =
      match (bs8i_flatPositions words).head? with
      | none => -1
      | some p => (p : Int) := by
  unfold bitsFindnext bs8i_flatPositions
  rw [List.head?_filter]
  have hfun : (fun p : Nat => decide ((0 : Int) ≤ p ∧
      bitAt (bitsGet words (p / 64 + 1)) (p % 64) = true)) =
      (fun p : Nat => bitAt (bitsGet words (p / 64 + 1)) (p % 64)) := by
    funext p
    simp only [Int.natCast_nonneg, true_and]
    cases bitAt (bitsGet words (p / 64 + 1)) (p % 64) <;> rfl
  rw [hfun]
  cases (List.find? (fun p => bitAt (bitsGet words (p / 64 + 1)) (p % 64)) (List.range (words.length * 64))) <;> rfl

/-- The reverse-position search is the last of the flat accepted positions. -/
theorem bs8i_findprev (words : List U64) :
    bitsFindprev words ((words.length : Int) * 64 - 1) =
      match (bs8i_flatPositions words).getLast? with
      | none => -1
      | some p => (p : Int) := by
  unfold bitsFindprev bs8i_flatPositions
  rw [List.getLast?_filter]
  have hfind := bs8i_find_congr (List.range (words.length * 64)).reverse
    (fun p : Nat => decide ((p : Int) ≤ (words.length : Int) * 64 - 1 ∧
      bitAt (bitsGet words (p / 64 + 1)) (p % 64) = true))
    (fun p : Nat => bitAt (bitsGet words (p / 64 + 1)) (p % 64))
    (by
      intro p hp
      have hr : p < words.length * 64 := List.mem_range.mp (List.mem_reverse.mp hp)
      have hb : (p : Int) ≤ (words.length : Int) * 64 - 1 := by omega
      simp only [hb, true_and]
      cases bitAt (bitsGet words (p / 64 + 1)) (p % 64) <;> rfl)
  rw [hfind]
  cases (List.find? (fun p => bitAt (bitsGet words (p / 64 + 1)) (p % 64)) (List.range (words.length * 64)).reverse) <;> rfl

/-- A valid flat bit position reconstructs without overflow at the frozen chunk bound. -/
theorem bs8i_position_value (s : BitSet) (hs : WF s)
    (hsize : s.bits.length < 2^56) (p : Nat) (hp : p < s.bits.length * 64) :
    (add_int (int64 (p : Int)) (int64 (s.offset * 64))).val = s.offset * 64 + (p : Int) := by
  have hsent : s.offset ≠ noOffset := by
    intro h
    have he := hs.1 h
    rw [he, List.length_nil, Nat.zero_mul] at hp
    omega
  have hr := hs.2 hsent
  change -144115188075855872 ≤ s.offset ∧ s.offset + s.bits.length ≤ 144115188075855872 at hr
  change s.bits.length < 72057594037927936 at hsize
  have hb : IntTy.i64.min ≤ s.offset * 64 ∧ s.offset * 64 ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    omega
  have hi : IntTy.i64.min ≤ (p : Int) ∧ (p : Int) ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    omega
  have hsum : IntTy.i64.min ≤ (p : Int) + s.offset * 64 ∧
      (p : Int) + s.offset * 64 ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    omega
  rw [bs_addI64_val _ _ (by rw [bs_int64_val _ hi, bs_int64_val _ hb]; exact hsum),
    bs_int64_val _ hi, bs_int64_val _ hb]
  omega

/-- Head membership, stated locally for the extrema proof. -/
theorem bs8i_head_mem {A : Type} (items : List A) (x : A)
    (h : items.head? = some x) : x ∈ items := by
  cases items with
  | nil => cases h
  | cons a items => cases h; exact List.mem_cons_self

/-- Last membership follows by reversing the list and using its head. -/
theorem bs8i_last_mem {A : Type} (items : List A) (x : A)
    (h : items.getLast? = some x) : x ∈ items := by
  have hr : items.reverse.head? = some x := by
    simpa only [List.getLast?_eq_head?_reverse] using h
  exact List.mem_reverse.mp (bs8i_head_mem items.reverse x hr)

/-- The first returned bit position is the first value of the complete iterator. -/
theorem bs8i_first (s : BitSet) (hs : WF s) (hsize : s.bits.length < 2^56) :
    first s = match (iterated s).head? with
      | some x => .ok x
      | none => .error (.julia (.argumentError "collection must be non-empty")) := by
  have hvalues := (bs_iterated_values s hs).trans (bs8i_flat_values s.offset s.bits)
  have hhead := congrArg List.head? hvalues
  simp only [List.head?_map, bs8i_flatValues] at hhead
  unfold first
  rw [bs8i_findnext]
  cases hp : (bs8i_flatPositions s.bits).head? with
  | none =>
    simp only [hp] at hhead
    cases hx : (iterated s).head? with
    | none => rfl
    | some x => rw [hx] at hhead; cases hhead
  | some p =>
    simp only [hp] at hhead
    have hpmem := bs8i_head_mem (bs8i_flatPositions s.bits) p hp
    have hpr : p < s.bits.length * 64 := by
      exact List.mem_range.mp (List.mem_filter.mp hpmem).1
    cases hx : (iterated s).head? with
    | none => rw [hx] at hhead; cases hhead
    | some x =>
      simp only [hx, Option.map_some] at hhead
      have hv : x.val = s.offset * 64 + (p : Int) := Option.some.inj hhead
      have hne : ((p : Int) == -1) = false := by rw [beq_eq_false_iff_ne]; omega
      dsimp only
      rw [hne, if_neg (by decide : ¬ false = true)]
      congr 1
      apply Subtype.ext
      rw [bs8i_position_value s hs hsize p hpr]
      exact hv.symm

/-- The last returned bit position is the last value of the complete iterator. -/
theorem bs8i_last (s : BitSet) (hs : WF s) (hsize : s.bits.length < 2^56) :
    last s = match (iterated s).getLast? with
      | some x => .ok x
      | none => .error (.julia (.argumentError "collection must be non-empty")) := by
  have hvalues := (bs_iterated_values s hs).trans (bs8i_flat_values s.offset s.bits)
  have hlast := congrArg List.getLast? hvalues
  simp only [List.getLast?_map, bs8i_flatValues] at hlast
  unfold last
  rw [bs8i_findprev]
  cases hp : (bs8i_flatPositions s.bits).getLast? with
  | none =>
    simp only [hp] at hlast
    cases hx : (iterated s).getLast? with
    | none => rfl
    | some x => rw [hx] at hlast; cases hlast
  | some p =>
    simp only [hp] at hlast
    have hpmem := bs8i_last_mem (bs8i_flatPositions s.bits) p hp
    have hpr : p < s.bits.length * 64 := by
      exact List.mem_range.mp (List.mem_filter.mp hpmem).1
    cases hx : (iterated s).getLast? with
    | none => rw [hx] at hlast; cases hlast
    | some x =>
      simp only [hx, Option.map_some] at hlast
      have hv : x.val = s.offset * 64 + (p : Int) := Option.some.inj hlast
      have hne : ((p : Int) == -1) = false := by rw [beq_eq_false_iff_ne]; omega
      dsimp only
      rw [hne, if_neg (by decide : ¬ false = true)]
      congr 1
      apply Subtype.ext
      rw [bs8i_position_value s hs hsize p hpr]
      exact hv.symm

/-- Every value emitted by the complete iterator passes the public membership test. -/
theorem bs8i_member_of_iterated (s : BitSet) (hs : WF s) (x : I64)
    (hx : x ∈ iterated s) : member s x.val = true := by
  rw [← bs8i_iterated_members s hs x.val]
  apply List.any_eq_true.mpr
  exact ⟨x, hx, decide_eq_true rfl⟩

theorem BitsetscovBitsetIteration_proven : JuliaLean.Proofs.base.bitset.Round3.BitSetIterSpec := by
  intro s hs hsize
  dsimp only
  have hfirst := bs8i_first s hs hsize
  have hlast := bs8i_last s hs hsize
  refine ⟨bs8i_offset s hs, bs8i_iterated_members s hs,
    bs8i_iterated_sorted s hs, bs8i_length s hs hsize,
    hfirst, hlast, rfl, rfl, ?_, rfl, bs8i_show s, ?_, ?_⟩
  · unfold extrema
    rw [hfirst, hlast]
    cases (iterated s).head? <;> cases (iterated s).getLast? <;> rfl
  · unfold popLast
    rw [hlast]
    cases hx : (iterated s).getLast? with
    | none => rfl
    | some x =>
      have hm := bs8i_member_of_iterated s hs x (bs8i_last_mem (iterated s) x hx)
      change inInteger x.val s = true at hm
      simp only [Bind.bind, Except.bind, popKey, hm, ↓reduceIte]
  · unfold popfirst
    rw [hfirst]
    cases hx : (iterated s).head? with
    | none => rfl
    | some x =>
      have hm := bs8i_member_of_iterated s hs x (bs8i_head_mem (iterated s) x hx)
      change inInteger x.val s = true at hm
      simp only [Bind.bind, Except.bind, popKey, hm, ↓reduceIte]

end

end JuliaLean.ChatGPT.Batch8.Group6
namespace JuliaLean.Proofs.base.bitset
open JuliaLean.Registry

def entries : List Entry := [
  { id := "bitarrays-bitset-push-delete", juliaFile := "base/bitset.jl",
    juliaFns := ["push!(::BitSet, ::Integer)", "delete!(::BitSet, ::Integer)"],
    statement := "Starting from a well-formed BitSet, a normal-returning sequence of push! and delete! updates membership by its successfully converted Int keys; out-of-range deletes do nothing.",
    source := "BitSet invariant; base/bitset.jl:5-10,255,279-281,330-331",
    status := .proven, prop := ``Round3.BitSetPushDeleteAgrees, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitarraysBitsetPushDelete_proven },
  { id := "bitarrays-bitset-symdiff-duplicates", juliaFile := "base/bitset.jl",
    juliaFns := ["symdiff!(::BitSet, itr)", "int_symdiff!", "symdiff(::BitSet, itr)"],
    statement := "symdiff!(s::BitSet, itr) agrees with symdiff!(Set{Int}(s), itr): the result holds exactly the elements in exactly one of s and itr.",
    source := "symdiff! docstring (base/abstractset.jl:282-289) and symdiff!(::AbstractSet, itr) = symdiff!(s, Set(itr)) (base/abstractset.jl:297, #46397)",
    status := .refuted, prop := ``BitSetSymdiffAgrees, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.BitarraysBitsetSymdiffDuplicates_refuted,
    issue := "duplicate JuliaLang/julia#64145 (open); proposed fix #64442 (open); related #46397 (merged), #34686 (closed), #44591 (closed)" },
  { id := "memsafety-bitset-indexing", juliaFile := "base/bitset.jl",
    juliaFns := ["_bits_getindex", "_growend0!", "_growbeg0!", "union!", "_matched_map!", "iterate", "_check0", "==(::BitSet, ::BitSet)", "issubset"],
    statement := "Every chunk index and unsafe copy span computed by BitSet lookup, growth, range union, matched mapping, reachable iteration, equality, emptiness, and subset operations is within the vector length in force at that statement.",
    source := "BitSet representation and iteration invariants; base/bitset.jl:5-10,63-68,87-165,169-253,291-337,368-418",
    status := .proven, prop := ``BitSetAccessesInBounds, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.MemsafetyBitsetIndexing_proven },
  { id := "bitsetscov-bitset-build", juliaFile := "base/bitset.jl",
    juliaFns := ["BitSet()", "BitSet(itr)", "union!(::BitSet, itr)", "empty(::BitSet)", "emptymutable(::BitSet)", "push!(::BitSet, ::Integer...)"],
    statement := "BitSet construction is empty. Iterable construction, union!, and variadic push! add exactly the convertible Int elements and preserve the representation invariant for every valid input BitSet, including an empty insertion list.",
    source := "BitSet docstring and representation invariant, base/bitset.jl:5-41,45-46,255-257",
    status := .proven, prop := ``BitSetBuildSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetBuild_proven },
  { id := "bitsetscov-bitset-copy", juliaFile := "base/bitset.jl",
    juliaFns := ["copy!(::BitSet, ::BitSet)", "copy(::BitSet)", "copymutable(::BitSet)"],
    statement := "The three BitSet copy methods preserve every stored chunk and the offset.",
    source := "copy invariant; base/bitset.jl:48-56",
    status := .proven, prop := ``BitSetCopySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.BitsetscovBitsetCopy_proven },
  { id := "bitsetscov-bitset-sizehint", juliaFile := "base/bitset.jl",
    juliaFns := ["sizehint!(::BitSet, ::Integer)"],
    statement := "sizehint! changes capacity only and either preserves the BitSet or reports an Int conversion failure for a 128-bit chunk count.",
    source := "sizehint! invariant; base/bitset.jl:58-61",
    status := .proven, prop := ``BitSetSizehintSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.BitsetscovBitsetSizehint_proven },
  { id := "bitsetscov-bitset-in", juliaFile := "base/bitset.jl",
    juliaFns := ["in(::Integer, ::BitSet)"],
    statement := "Integer membership agrees with the values yielded by complete BitSet iteration for well-formed BitSets.",
    source := "BitSet set invariant; base/bitset.jl:279-281,330-340",
    status := .proven, prop := ``Round1.BitSetMembershipMatchesIteration,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetIn_proven },
  { id := "bitsetscov-bitset-delete-pop", juliaFile := "base/bitset.jl",
    juliaFns := ["delete!(::BitSet, ::Int)", "delete!(::BitSet, ::Integer)", "pop!(::BitSet, ::Integer)", "pop!(::BitSet, ::Integer, default)"],
    statement := "delete! removes exactly its key; keyed pop! removes and returns a present key, throws without a default, and returns the default when absent.",
    source := "AbstractSet delete!/pop! contract; base/bitset.jl:261-281",
    status := .proven, prop := ``Round1.BitSetDeleteContract,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetDeletePop_proven },
  { id := "bitsetscov-bitset-empty", juliaFile := "base/bitset.jl",
    juliaFns := ["empty!(::BitSet)", "isempty(::BitSet)"],
    statement := "For every well-formed BitSet, empty! returns the empty BitSet; its membership is false for every Int, and isempty is true exactly when the original set has no members.",
    source := "empty!/isempty contract; BitSet invariant; base/bitset.jl:5-10,285-291",
    status := .proven, prop := ``Round2.BitSetEmptyPublicSpec,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetEmpty_proven },
  { id := "bitsetscov-bitset-union-range", juliaFile := "base/bitset.jl",
    juliaFns := ["union!(::BitSet, ::AbstractUnitRange{<:Integer})"],
    statement := "Range union adds exactly every Int in a nonempty range, leaves empty ranges unchanged, and checks conversion of both bounds.",
    source := "union contract; base/bitset.jl:131-167",
    status := .proven, prop := ``BitSetUnionRangeSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetUnionRange_proven },
  { id := "bitsetscov-bitset-matched-map", juliaFile := "base/bitset.jl",
    juliaFns := ["union!(::BitSet, ::BitSet)", "intersect(::BitSet, ::BitSet)", "intersect!(::BitSet, ::BitSet)", "setdiff!(::BitSet, ::BitSet)", "symdiff!(::BitSet, ::BitSet)"],
    statement := "The BitSet set operations implement memberwise union, intersection, difference, and symmetric difference while preserving the representation invariant.",
    source := "set-operation contracts; base/bitset.jl:169-253,296-326",
    status := .proven, prop := ``Round3.BitSetMatchedPreserves, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetMatchedMap_proven },
  { id := "bitsetscov-bitset-union", juliaFile := "base/bitset.jl",
    juliaFns := ["union(::BitSet, sets...)"],
    statement := "union copies the first BitSet and adds exactly the members of every following argument.",
    source := "union contract; base/bitset.jl:295",
    status := .proven, prop := ``BitSetUnionSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetUnion_proven },
  { id := "bitsetscov-bitset-symdiff-set", juliaFile := "base/bitset.jl",
    juliaFns := ["symdiff!(::BitSet, ::AbstractSet)"],
    statement := "Symmetric difference with an AbstractSet toggles each distinct convertible Int member exactly once.",
    source := "symdiff! docstring; base/bitset.jl:312-317",
    status := .proven, prop := ``BitSetSymdiffSetSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetSymdiffSet_proven },
  { id := "bitsetscov-bitset-filter-invariant", juliaFile := "base/bitset.jl",
    juliaFns := ["filter!(f, ::BitSet)"],
    statement := "In-place filtering preserves the BitSet invariant and keeps exactly members accepted by the predicate.",
    source := "representation invariant; base/bitset.jl:328 and base/abstractset.jl:633-641",
    status := .proven, prop := ``Round1.BitSetFilterPreserves,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetFilterInvariant_proven },
  { id := "bitsetscov-bitset-iteration", juliaFile := "base/bitset.jl",
    juliaFns := ["intoffset", "iterate(::BitSet)", "_throw_bitset_notempty_error", "first(::BitSet)", "last(::BitSet)", "length(::BitSet)", "show(::IO, ::BitSet)", "pop!(::BitSet)", "popfirst!(::BitSet)", "minimum(::BitSet)", "maximum(::BitSet)", "extrema(::BitSet)", "issorted(::BitSet)"],
    statement := "BitSet iteration lists every member in increasing order; its extrema, length, pop methods, and printed form agree with that sequence.",
    source := "BitSet sorted-set docstring and iteration invariant; base/bitset.jl:43,259,283,333-366,423-426",
    status := .proven, prop := ``Round3.BitSetIterSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group6.BitsetscovBitsetIteration_proven },
  { id := "bitsetscov-bitset-equality", juliaFile := "base/bitset.jl",
    juliaFns := ["==(::BitSet, ::BitSet)"],
    statement := "Two BitSets compare equal exactly when they have the same integer members.",
    source := "AbstractSet equality invariant; base/bitset.jl:375-407",
    status := .proven, prop := ``BitSetEqSpec,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetEquality_proven },
  { id := "bitsetscov-bitset-subset", juliaFile := "base/bitset.jl",
    juliaFns := ["issubset(::BitSet, ::BitSet)", "⊊(::BitSet, ::BitSet)"],
    statement := "For every pair of well-formed BitSets, issubset is true exactly when every member of the first belongs to the second, and strict subset is true exactly when that inclusion is proper.",
    source := "issubset/strict-subset contracts; base/abstractset.jl:315-316,406; base/bitset.jl:409-420",
    status := .proven, prop := ``Round2.BitSetSubsetPublicSpec,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.BitsetscovBitsetSubset_proven },
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

