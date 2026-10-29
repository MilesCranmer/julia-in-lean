import JuliaLean.base.strings.search
import JuliaLean.Registry.Types

/-!
# Specifications of `base/strings/search.jl`

These statements are intentionally open (`todo`). There are no theorems in this
file. `TextView` and `ByteView` describe contents independently of the search
algorithms. Their interface laws describe the primitive string, array,
conversion, iterator and C-library calls. They impose no well-formed-UTF-8
precondition: a text may contain every UInt8 value, including malformed or
truncated character encodings.
-/

namespace JuliaLean.Proofs.base.strings.search

open JuliaLean JuliaLean.base.strings.search JuliaLean.Registry

/-- A string's byte storage and indexed sequence of decoded characters. -/
structure TextView (S C : Type) where
  bytes : S → List UInt8
  characters : S → List (Index × C)

def validAt {S C : Type} (v : TextView S C) (s : S) (i : Index) : Prop :=
  ∃ c, (i, c) ∈ v.characters s

def endIndex {S C : Type} (v : TextView S C) (s : S) : Int :=
  Int.ofNat (v.bytes s).length + 1

def lastIndex {S C : Type} (v : TextView S C) (s : S) : Index :=
  ((v.characters s).getLast?.map (·.1)).getD (int 0)

def nextPosition {S C : Type} (v : TextView S C) (s : S) (i : Index) : Index :=
  (((v.characters s).filter (fun p => p.1.val > i.val)).head?.map (·.1)).getD (int (endIndex v s))

def prevPosition {S C : Type} (v : TextView S C) (s : S) (i : Index) : Index :=
  (((v.characters s).filter (fun p => p.1.val < i.val)).getLast?.map (·.1)).getD (int 0)

/-- Primitive AbstractString laws, including errors and index progression. -/
structure TextLaws {S C E : Type} (ops : SearchStringOps S C E) (v : TextView S C) : Prop where
  sizeFits : ∀ s, Int.ofNat (v.bytes s).length ≤ IntTy.max .i64
  ncodeunits : ∀ s, (ops.ncodeunits s).val = Int.ofNat (v.bytes s).length
  iterationBound : ∀ s, (v.bytes s).length ≤ ops.iterationBound s
  sorted : ∀ s, (v.characters s).Pairwise (fun a b => a.1.val < b.1.val)
  indices : ∀ s p, p ∈ v.characters s → 1 ≤ p.1.val ∧ p.1.val < endIndex v s
  nonempty : ∀ s, (v.characters s).isEmpty = (v.bytes s).isEmpty
  first : ∀ s p, (v.characters s).head? = some p → p.1 = int 1
  lastindex : ∀ s, ops.lastindex s = .ok (lastIndex v s)
  isvalid : ∀ s i, ops.isvalid s i = .ok ((v.characters s).any (fun p => p.1 == i))
  getindex : ∀ s i c, (i, c) ∈ v.characters s → ops.getindex s i = .ok c
  nextind : ∀ s i, validAt v s i ∨ i = int 0 → ops.nextind s i = .ok (nextPosition v s i)
  prevind : ∀ s i, validAt v s i ∨ i.val = endIndex v s →
    ops.prevind s i = .ok (prevPosition v s i)
  iterate : ∀ s i c, (i, c) ∈ v.characters s →
    ops.iterate s i = .ok (some (c, nextPosition v s i))

/-- Integer conversion succeeds precisely on the representable Int values. -/
def IntegerLaws {I E : Type} (ix : IntegerOps I E) : Prop :=
  (∀ i, IntTy.min .i64 ≤ ix.value i → ix.value i ≤ IntTy.max .i64 →
    ix.toInt i = .ok (int (ix.value i))) ∧
  (∀ i j, ix.toInt i = .ok j → j.val = ix.value i)

/-- Raw Char bytes are packed in the high bytes of the UInt32 representation. -/
structure CharEncoding (ncodeunits : JChar → Index) where
  bytes : JChar → List UInt8
  nonempty : ∀ c, (bytes c).isEmpty = false
  length : ∀ c, (bytes c).length ≤ 4
  ncodeunits_eq : ∀ c, (ncodeunits c).val = Int.ofNat (bytes c).length
  packed : ∀ c, c.toNat = ((bytes c).zipIdx.foldl
    (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0)

/-- UTF-8 string iteration preserves arbitrary input bytes. Standalone bytes
cannot occur inside a character with more than one byte. -/
structure Utf8TextLaws {S E : Type} (ops : SearchStringOps S JChar E)
    (v : TextView S JChar) (ncodeunitsChar : JChar → Index)
    (enc : CharEncoding ncodeunitsChar) : Prop extends TextLaws ops v where
  concatenation : ∀ s, (v.characters s).flatMap (fun p => enc.bytes p.2) = v.bytes s
  offsets : ∀ s k p, (v.characters s)[k]? = some p →
    p.1.val = 1 + Int.ofNat (((v.characters s).take k).flatMap (fun q => enc.bytes q.2)).length
  standalone : ∀ s p b, p ∈ v.characters s → b ∈ enc.bytes p.2 →
    (b.toNat < 128 ∨ 247 < b.toNat) → enc.bytes p.2 = [b]

structure ByteView (A B : Type) where
  first : A → Int
  elements : A → List B

def byteAt {A B : Type} (v : ByteView A B) (a : A) (i : Int) : Option B :=
  (v.elements a)[(i - v.first a).toNat]?

/-- Abstract byte-vector axes may have any representable first index. -/
structure ByteLaws {A B E : Type} (ops : ByteOps A B E) (v : ByteView A B) : Prop where
  firstindex : ∀ a, (ops.firstindex a).val = v.first a
  lastindex : ∀ a, (ops.lastindex a).val = v.first a + Int.ofNat (v.elements a).length - 1
  length : ∀ a, (ops.length a).val = Int.ofNat (v.elements a).length
  getindex : ∀ a k b, (v.elements a)[k]? = some b →
    ops.getindex a (int (v.first a + Int.ofNat k)) = .ok b
  getindexOutside : ∀ a i, i.val < v.first a ∨
    v.first a + Int.ofNat (v.elements a).length ≤ i.val →
    ops.getindex a i = .error (ops.boundsError a i.val)
  byteValue : ∀ b, -128 ≤ ops.value b ∧ ops.value b ≤ 255

/-- Least/greatest matching positions, stated without reference to a search loop. -/
def FirstIndex {E : Type} (accepts : Int → Prop) (start : Int)
    (result : Except E (Option Index)) : Prop :=
  (∀ i, result = .ok (some i) ↔
    start ≤ i.val ∧ accepts i.val ∧ ∀ j, start ≤ j → accepts j → i.val ≤ j) ∧
  (result = .ok none ↔ ∀ j, start ≤ j → ¬ accepts j)

def LastIndex {E : Type} (accepts : Int → Prop) (start : Int)
    (result : Except E (Option Index)) : Prop :=
  (∀ i, result = .ok (some i) ↔
    i.val ≤ start ∧ accepts i.val ∧ ∀ j, j ≤ start → accepts j → j ≤ i.val) ∧
  (result = .ok none ↔ ∀ j, j ≤ start → ¬ accepts j)

def charMatches {S C : Type} (v : TextView S C) (p : C → Prop) (s : S) (i : Int) : Prop :=
  ∃ k c, (k, c) ∈ v.characters s ∧ k.val = i ∧ p c

def byteMatches {A B : Type} (v : ByteView A B) (equal : B → Bool) (a : A) (i : Int) : Prop :=
  v.first a ≤ i ∧ ∃ b, byteAt v a i = some b ∧ equal b = true

/-- A contiguous byte subsequence, using numeric Int8/UInt8 equality. -/
def byteSequenceAt {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (sv : ByteView A B) (tv : ByteView T C) (s : A) (t : T) (i : Int) : Prop :=
  sv.first s ≤ i ∧ i + Int.ofNat (tv.elements t).length ≤
    sv.first s + Int.ofNat (sv.elements s).length ∧
  ∀ k b, (tv.elements t)[k]? = some b →
    ∃ a, byteAt sv s (i + Int.ofNat k) = some a ∧ sops.value a = tops.value b

/-- A character-sequence match and its inclusive Julia character endpoints. -/
def textSequenceAt {S T C : Type} (sv : TextView S C) (pattern : T → List C)
    (s : S) (t : T) (r : MatchRange) : Prop :=
  if (pattern t).isEmpty then r.first.val = r.last.val + 1 ∧
    1 ≤ r.first.val ∧ r.first.val ≤ endIndex sv s
  else ∃ k, ((sv.characters s)[k]?.map (·.1)) = some r.first ∧
    (((sv.characters s).drop k).take (pattern t).length).map (·.2) = pattern t ∧
    (((sv.characters s)[k + (pattern t).length - 1]?.map (·.1)) = some r.last)

def FirstRange {E : Type} (accepts : MatchRange → Prop) (start : Int)
    (result : Except E (Option MatchRange)) : Prop :=
  (∀ r, result = .ok (some r) ↔ accepts r ∧ start ≤ r.first.val ∧
    ∀ q, accepts q → start ≤ q.first.val → r.first.val ≤ q.first.val) ∧
  (result = .ok none ↔ ∀ r, start ≤ r.first.val → ¬ accepts r)

def LastRange {E : Type} (accepts : MatchRange → Prop) (start : Int)
    (result : Except E (Option MatchRange)) : Prop :=
  (∀ r, result = .ok (some r) ↔ accepts r ∧ r.last.val ≤ start ∧
    ∀ q, accepts q → q.last.val ≤ start → q.first.val ≤ r.first.val) ∧
  (result = .ok none ↔ ∀ r, r.last.val ≤ start → ¬ accepts r)

/-- C memory search laws concern only the external C calls and preservation. -/
structure CMemoryLaws {A B E : Type} (ops : DenseOps A B E) (v : ByteView A B) : Prop where
  bytes : ByteLaws ops.toByteOps v
  nonnull : ∀ a, (ops.pointer a).val ≠ 0
  addressRange : ∀ a, (ops.pointer a).val + Int.ofNat (v.elements a).length < 2 ^ 64
  preserve : ∀ a f, ops.preserve a f = f ()
  memchr : ∀ a start count needle,
    0 ≤ start → 0 ≤ count → start + count ≤ Int.ofNat (v.elements a).length →
    ops.memchrCall (JInt.wrap .u64 ((ops.pointer a).val + start)) needle
      (JInt.wrap .u64 count) =
    .ok (match ((v.elements a).drop start.toNat).take count.toNat |>.findIdx?
        (fun b => (ops.value b) % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 ((ops.pointer a).val + start + Int.ofNat offset))
  memrchr : ∀ a count needle, 0 ≤ count → count ≤ Int.ofNat (v.elements a).length →
    ops.memrchrCall (ops.pointer a) needle (JInt.wrap .u64 count) =
    .ok (match ((v.elements a).take count.toNat).reverse.findIdx?
        (fun b => (ops.value b) % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 ((ops.pointer a).val + count - 1 - Int.ofNat offset))

/-- The codeunits view has one-based byte axes and the same underlying bytes. -/
def CodeunitLaws {S A E : Type} (codeunits : S → A) (bytes : DenseOps A UInt8 E)
    (v : TextView S JChar) (bv : ByteView A UInt8) : Prop :=
  CMemoryLaws bytes bv ∧ (∀ s, bv.first (codeunits s) = 1) ∧
    (∀ s, bv.elements (codeunits s) = v.bytes s) ∧
    (∀ b, bytes.value b = Int.ofNat b.toNat)

structure GenericForwardLaws {S T C Sub E : Type} [DecidableEq C]
    (ops : GenericForwardOps S T C Sub E) (v : TextView S C) (pattern : T → List C) : Prop where
  string : TextLaws ops.string v
  firstindex : ∀ s, ops.firstindex s = int 1
  peel : ∀ t, ops.peel t = .ok ((pattern t).head?.map (fun c => (c, (pattern t).drop 1)))
  substring : ∀ s i sub, ops.substring s i = .ok sub →
    ops.characters sub = .ok (((v.characters s).filter (fun p => i.val ≤ p.1.val)).map (·.2))
  substringExists : ∀ s i, validAt v s i ∨ i.val = endIndex v s → ∃ sub, ops.substring s i = .ok sub
  equal : ∀ c d, ops.equal c d = .ok (decide (c = d))

structure GenericReverseLaws {S T R C Sub E : Type} [DecidableEq C]
    (ops : GenericReverseOps S T R C Sub E) (v : TextView S C) (pattern : T → List C) : Prop where
  string : TextLaws ops.string v
  isempty : ∀ t, ops.isempty t = (pattern t).isEmpty
  peel : ∀ t c cs, (pattern t).reverse = c :: cs → ops.peel (ops.reverse t) = .ok (c, cs)
  substring : ∀ s i sub, ops.substring s (int 1) i = .ok sub →
    ops.reversePairs sub = .ok (((v.characters s).filter (fun p => p.1.val ≤ i.val)).reverse)
  substringExists : ∀ s i, validAt v s i ∨ i.val = 0 → ∃ sub, ops.substring s (int 1) i = .ok sub
  equal : ∀ c d, ops.equal c d = .ok (decide (c = d))

structure DenseLaws {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar) : Prop where
  source : Utf8TextLaws cfg.source sv cfg.ncodeunitsChar enc
  pattern : Utf8TextLaws cfg.pattern tv cfg.ncodeunitsChar enc
  codeunits : CodeunitLaws cfg.codeunitsSource cfg.sourceBytes sv bv
  patternBytes : ByteLaws cfg.patternBytes pv
  patternFirst : ∀ t, pv.first (cfg.codeunitsPattern t) = 1
  patternContents : ∀ t, pv.elements (cfg.codeunitsPattern t) = tv.bytes t
  patternValues : ∀ b, cfg.patternBytes.value b = Int.ofNat b.toNat
  sizeof : ∀ s, (cfg.sizeof s).val = Int.ofNat (sv.bytes s).length

structure BytePatternLaws {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) : Prop where
  source : ByteLaws cfg.source sv
  pattern : ByteLaws cfg.pattern tv
  findnext : ∀ a c i, sv.first a ≤ i.val →
    FirstIndex (byteMatches sv (fun b => cfg.source.value b == cfg.pattern.value c) a) i.val
      (cfg.findnext c a i)
  findprev : ∀ a c i, i.val < sv.first a + Int.ofNat (sv.elements a).length →
    LastIndex (byteMatches sv (fun b => cfg.source.value b == cfg.pattern.value c) a) i.val
      (cfg.findprev c a i)
  findprevAboveLast : ∀ a c i,
    (cfg.source.lastindex a).val < i.val →
    cfg.findprev c a i = .error (cfg.source.boundsError a i.val)

def byteRangeAt {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (a : A) (t : T) (r : MatchRange) : Prop :=
  byteSequenceAt cfg.source cfg.pattern sv tv a t r.first.val ∧
    r.last.val + 1 = r.first.val + Int.ofNat (tv.elements t).length

/-- Julia string slicing returns the complete character at the inclusive stop. -/
def SliceLaws {E : Type} (v : TextView JString JChar)
    (slice : JString → Index → Index → Except E JString) : Prop :=
  (∀ s, v.bytes s = s.bytes) ∧ ∀ s i j t,
    slice s i j = .ok t ↔
      (j.val < i.val ∧ 1 ≤ i.val ∧ i.val ≤ endIndex v s ∧ t.bytes = []) ∨
      (i.val ≤ j.val ∧ validAt v s i ∧ validAt v s j ∧
        t.bytes = (s.bytes.drop (i.val - 1).toNat).take ((nextPosition v s j).val - i.val).toNat)

/-- A regexp engine is external to search.jl. Both callbacks are the methods
of regex.jl; `accepts` is its documented matching relation. -/
structure RegexInterface (S P E : Type) where
  findnext : P → S → Index → Except E (Option MatchRange)
  eachmatchRanges : P → S → Except E (List MatchRange)
  accepts : P → S → MatchRange → Prop

/-- The list obtained by repeatedly calling findnext, using the documented
non-overlapping advancement rule. -/
def repeatedFindnext {S P E : Type}
    (findnext : P → S → Index → Except E (Option MatchRange))
    (firstindex : S → Index) (lastindex : S → Except E Index)
    (nextind : S → Index → Except E Index) (iterationBound : S → Nat)
    (p : P) (s : S) : Except E (List MatchRange) := do
  let last ← lastindex s
  let rec loop : Nat → Index → List MatchRange → Except E (List MatchRange)
    | 0, _, ranges => .ok ranges
    | fuel + 1, start, ranges => do
        match ← findnext p s start with
        | none => pure ranges
        | some range =>
            let ranges := ranges ++ [range]
            let stop := if rangeEmpty range then range.first else range.last
            if stop.val > last.val then return ranges
            loop fuel (← nextind s stop) ranges
  loop (iterationBound s + 2) (firstindex s) []
structure RegexInterfaceLaws {S P E : Type} (ops : RegexInterface S P E)
    (string : SearchStringOps S JChar E) (v : TextView S JChar) : Prop where
  next : ∀ p s i r, 1 ≤ i.val → i.val ≤ endIndex v s →
    ops.findnext p s i = .ok (some r) →
    ops.accepts p s r ∧ i.val ≤ r.first.val ∧
      ∀ q, ops.accepts p s q → i.val ≤ q.first.val → r.first.val ≤ q.first.val
  nextNone : ∀ p s i, 1 ≤ i.val → i.val ≤ endIndex v s →
    (ops.findnext p s i = .ok none ↔ ∀ r, i.val ≤ r.first.val → ¬ ops.accepts p s r)
  eachmatch : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    (∀ r ∈ rs, ops.accepts p s r) ∧ rs.Pairwise (fun a b => a.last.val < b.first.val)
  eachmatchComplete : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    ∀ r, ops.accepts p s r →
      (∃ q ∈ rs, q = r ∨ (q.first.val ≤ r.first.val ∧ r.first.val ≤ q.last.val))
  eachmatchFindnext : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    repeatedFindnext ops.findnext JuliaLean.base.strings.basic.firstindexString
      string.lastindex string.nextind string.iterationBound p s = .ok rs

/-- The final byte returned for any stored Char, including malformed Char values, is the final byte of its encoded representation. -/
def LastUtf8ByteSpec : Prop :=
∀ (ncodeunits : JChar → Index) (encoding : CharEncoding ncodeunits) (c : JChar),
    (encoding.bytes c).getLast? = some (lastUtf8Byte ncodeunits c)

/-- The bloom mask has exactly one bit set, at the input value modulo 64. -/
def BloomBitSpec : Prop :=
∀ (B E : Type) (value : B → Int) (b : B) (mask : UInt64),
    byteBloom (E := E) value b = .ok mask →
      ∀ k : Fin 64, mask.toNat.testBit k.val = decide (k.val = (value b % 64).toNat)

/-- memchr returns the least matching byte index in the requested suffix, restores offset axes, and returns nothing exactly when the suffix has no match. -/
def MemchrFirstSpec : Prop :=
(∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun x => x == b) a) i.val (memchrUInt8 ops a b i)) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun x => x.val == b.val) a) i.val (memchrInt8 ops a b i))

/-- memrchr returns the greatest matching byte index in the requested prefix, restores offset axes, and returns nothing exactly when the prefix has no match. -/
def MemrchrLastSpec : Prop :=
(∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      LastIndex (byteMatches v (fun x => x == b) a) i.val (memrchrUInt8 ops a b i)) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      LastIndex (byteMatches v (fun x => x.val == b.val) a) i.val (memrchrInt8 ops a b i))

/-- Dense signed and unsigned byte findnext returns the first match at or after the start, rejects a start below the array, and preserves Int conversion errors. -/
def DenseByteForwardSpec : Prop :=
(∀ (A I E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b start, match ix.toInt start with
      | .error e => findnextUInt8 ops ix b a start = .error e
      | .ok i => if i.val < v.first a then
          findnextUInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else FirstIndex (byteMatches v (fun x => x == b) a) i.val (findnextUInt8 ops ix b a start)) ∧
  (∀ (A I E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = b.val) →
    ∀ a b start, match ix.toInt start with
      | .error e => findnextInt8 ops ix b a start = .error e
      | .ok i => if i.val < v.first a then
          findnextInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else FirstIndex (byteMatches v (fun x => x.val == b.val) a) i.val (findnextInt8 ops ix b a start))

/-- Dense signed and unsigned byte findprev returns the last match at or before the start, rejects a start above the array, and preserves Int conversion errors. -/
def DenseByteReverseSpec : Prop :=
(∀ (A I E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b start, match ix.toInt start with
      | .error e => findprevUInt8 ops ix b a start = .error e
      | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
          findprevUInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else LastIndex (byteMatches v (fun x => x == b) a) i.val (findprevUInt8 ops ix b a start)) ∧
  (∀ (A I E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = b.val) →
    ∀ a b start, match ix.toInt start with
      | .error e => findprevInt8 ops ix b a start = .error e
      | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
          findprevInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else LastIndex (byteMatches v (fun x => x.val == b.val) a) i.val (findprevInt8 ops ix b a start))

/-- Predicate findnext returns exactly the least accepted character index at or after a valid start, or nothing when no character is accepted. -/
def PredicateForwardSpec : Prop :=
∀ (S C I E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → Except E Bool) (accepted : C → Bool),
    TextLaws ops v → IntegerLaws ix → (∀ c, testf c = .ok (accepted c)) →
    ∀ s start, 1 ≤ ix.value start → ix.value start ≤ endIndex v s →
      (validAt v s (int (ix.value start)) ∨ ix.value start = endIndex v s) →
      FirstIndex (charMatches v (fun c => accepted c = true) s) (ix.value start)
        (findnextPredicate ops ix testf s start)

/-- Predicate findprev returns exactly the greatest accepted character index at or before a valid start, or nothing when no character is accepted. -/
def PredicateReverseSpec : Prop :=
∀ (S C I E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → Except E Bool) (accepted : C → Bool),
    TextLaws ops v → IntegerLaws ix → (∀ c, testf c = .ok (accepted c)) →
    ∀ s start, 0 ≤ ix.value start → ix.value start < endIndex v s →
      (validAt v s (int (ix.value start)) ∨ ix.value start = 0) →
      LastIndex (charMatches v (fun c => accepted c = true) s) (ix.value start)
        (findprevPredicate ops ix testf s start)

/-- Predicate search throws BoundsError outside its start domain and StringIndexError for a byte position inside a character, including in strings containing invalid UTF-8 bytes. -/
def PredicateStartErrorsSpec : Prop :=
∀ (S C I E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → Except E Bool),
    TextLaws ops v → IntegerLaws ix → ∀ s start,
    (∀ i, ix.toInt start = .ok i →
      ((i.val < 1 ∨ endIndex v s < i.val) →
        findnextPredicate ops ix testf s start = .error (ops.boundsError s i.val)) ∧
      ((i.val < 0 ∨ endIndex v s < i.val) →
        findprevPredicate ops ix testf s start = .error (ops.boundsError s i.val)) ∧
      ((1 ≤ i.val ∧ i.val < endIndex v s ∧ ¬ validAt v s i) →
        findnextPredicate ops ix testf s start = .error (ops.stringIndexError s i) ∧
        findprevPredicate ops ix testf s start = .error (ops.stringIndexError s i)))

/-- A predicate exception at the first tested position after a false-only prefix is returned unchanged in either search direction. -/
def PredicateErrorSpec : Prop :=
∀ (S C E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (testf : C → Except E Bool), TextLaws ops v → ∀ s start i c e,
    validAt v s start → (i, c) ∈ v.characters s → testf c = .error e →
    ((start.val ≤ i.val ∧ ∀ j d, (j, d) ∈ v.characters s → start.val ≤ j.val → j.val < i.val →
        testf d = .ok false) → findnextPredicate ops indexOps testf s start = .error e) ∧
    ((i.val ≤ start.val ∧ ∀ j d, (j, d) ∈ v.characters s → i.val < j.val → j.val ≤ start.val →
        testf d = .ok false) → findprevPredicate ops indexOps testf s start = .error e)

/-- Every occurrence of a byte classified standalone begins a one-byte character, even when the surrounding input contains malformed UTF-8 bytes. -/
def StandalonePositionsSpec : Prop :=
∀ (S E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (ncodeunitsChar : JChar → Index) (enc : CharEncoding ncodeunitsChar),
    Utf8TextLaws ops v ncodeunitsChar enc → ∀ s b k,
      isStandaloneByte b = true → (v.bytes s)[k]? = some b →
      ∃ c, (int (Int.ofNat k + 1), c) ∈ v.characters s ∧ enc.bytes c = [b]

/-- Forward character-position iteration yields the least complete matching character from a valid start and returns nothing exactly when no such character remains. -/
def ForwardIteratorSpec : Prop :=
∀ (S A C E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (encoding : CharEncoding chars.ncodeunits),
    Utf8TextLaws ops v chars.ncodeunits encoding → CodeunitLaws codeunits bytes v bv →
    ∀ s target c start, chars.toChar target = .ok c →
      (validAt v s start ∨ start.val = endIndex v s) →
      FirstIndex (charMatches v (fun d => d = c) s) start.val
        (do let iter ← fwCharPosIter chars s target
            tryNext (fun it st => fwIterate ops bytes codeunits chars.ncodeunits it st) iter start)

/-- Reverse character-position iteration yields the greatest complete matching character at or before a valid start and returns nothing exactly when none remains. -/
def ReverseIteratorSpec : Prop :=
∀ (S A C E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (encoding : CharEncoding chars.ncodeunits),
    Utf8TextLaws ops v chars.ncodeunits encoding → CodeunitLaws codeunits bytes v bv →
    ∀ s target c start, chars.toChar target = .ok c →
      (validAt v s start ∨ start.val = 0) →
      LastIndex (charMatches v (fun d => d = c) s) start.val
        (do let iter ← rvCharPosIter chars s target
            tryNext (fun it st => rvIterate ops bytes codeunits chars.ncodeunits it (some st)) iter start)

/-- Character findnext and findprev return the first or last matching decoded character at valid string indices, including for malformed input bytes. -/
def CharSearchSpec : Prop :=
∀ (S A C I E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (encoding : CharEncoding chars.ncodeunits) (ix : IntegerOps I E),
    Utf8TextLaws ops v chars.ncodeunits encoding → CodeunitLaws codeunits bytes v bv →
    IntegerLaws ix → ∀ s target c start, chars.toChar target = .ok c →
      ((validAt v s (int (ix.value start)) ∨ ix.value start = endIndex v s) →
        FirstIndex (charMatches v (fun d => d = c) s) (ix.value start)
          (findnextChar ops bytes codeunits chars ix target s start)) ∧
      ((validAt v s (int (ix.value start)) ∨ ix.value start = 0) →
        LastIndex (charMatches v (fun d => d = c) s) (ix.value start)
          (findprevChar ops bytes codeunits chars ix target s start))

/-- Character searches throw BoundsError for starts outside their bounds. Only the
forward Char method also rejects an interior byte position with StringIndexError. -/
def CharStartErrorsSpec : Prop :=
  ∀ (S A C I E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (encoding : CharEncoding chars.ncodeunits) (ix : IntegerOps I E),
    Utf8TextLaws ops v chars.ncodeunits encoding → CodeunitLaws codeunits bytes v bv →
    IntegerLaws ix → ∀ s target c start, chars.toChar target = .ok c →
      ((ix.value start < 1 ∨ endIndex v s < ix.value start) →
        findnextChar ops bytes codeunits chars ix target s start =
          .error (ops.boundsError s (ix.value start))) ∧
      ((ix.value start < 0 ∨ endIndex v s < ix.value start) →
        findprevChar ops bytes codeunits chars ix target s start =
          .error (ops.boundsError s (ix.value start))) ∧
      ((1 ≤ ix.value start ∧ ix.value start < endIndex v s ∧
        ¬ validAt v s (int (ix.value start))) →
        findnextChar ops bytes codeunits chars ix target s start =
          .error (ops.stringIndexError s (int (ix.value start))))

/-- Character findall returns all and only the matching character indices in increasing order, including in malformed UTF-8 strings. -/
def FindallCharSpec : Prop :=
∀ (S A C E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (encoding : CharEncoding chars.ncodeunits)
    (findallBytes : UInt8 → A → Except E (List Index)),
    Utf8TextLaws ops v chars.ncodeunits encoding → CodeunitLaws codeunits bytes v bv →
    (∀ b a, findallBytes b a = .ok (((bv.elements a).zipIdx.filter (fun p => p.1 == b)).map
      (fun p => int (bv.first a + Int.ofNat p.2)))) →
    ∀ s target c, chars.toChar target = .ok c →
      findallChar ops bytes codeunits chars findallBytes target s =
        .ok (((v.characters s).filter (fun p => p.2 == c)).map (·.1))

/-- Generic substring search returns the least complete pattern match from the start, including the empty-pattern start, and returns its sentinel exactly when no match exists. -/
def GenericForwardSpec : Prop :=
  (∀ (S T C Sub E : Type) (ops : GenericForwardOps S T C Sub E) (s : S) (t : T) (i last z : Index),
    ops.peel t = .ok none → ops.string.lastindex s = .ok last →
    ops.string.nextind s last = .ok z →
      (((ops.firstindex s).val ≤ i.val ∧ i.val ≤ z.val) →
        searchindexGeneric ops indexOps s t i = .ok i) ∧
      ((i.val < (ops.firstindex s).val ∨ z.val < i.val) →
        searchindexGeneric ops indexOps s t i = .error (ops.string.boundsError s i.val))) ∧
  (∀ (S T C Sub E : Type) [DecidableEq C] (ops : GenericForwardOps S T C Sub E)
    (v : TextView S C) (pattern : T → List C), GenericForwardLaws ops v pattern →
    ∀ s t i, 1 ≤ i.val → i.val ≤ endIndex v s →
      (validAt v s i ∨ i.val = endIndex v s) →
      FirstIndex (fun j => ∃ r, textSequenceAt v pattern s t r ∧ r.first.val = j) i.val
        ((searchindexGeneric (genericForwardStringOps ops) indexOps s t i).map
          (fun j => if j.val = 0 then none else some j)))

/-- Generic reverse substring search returns the latest complete match ending at or before the start; an empty pattern matches at the start. -/
def GenericReverseSpec : Prop :=
∀ (S T R C Sub E : Type) [DecidableEq C] (ops : GenericReverseOps S T R C Sub E)
    (v : TextView S C) (pattern : T → List C), GenericReverseLaws ops v pattern →
    ∀ s t i, 1 ≤ i.val → i.val ≤ endIndex v s →
      (validAt v s i ∨ i.val = endIndex v s) →
      if (pattern t).isEmpty then
        rsearchindexGeneric (genericReverseStringOps ops) indexOps s t i = .ok i
      else LastIndex
        (fun j => ∃ r, textSequenceAt v pattern s t r ∧ r.first.val = j ∧ r.last.val ≤ i.val) i.val
        ((rsearchindexGeneric (genericReverseStringOps ops) indexOps s t i).map
          (fun j => if j.val = 0 then none else some j))

/-- String findnext returns exactly the earliest complete match range at or after a valid start and returns nothing exactly when no matching range exists. -/
def DenseForwardSpec : Prop :=
∀ (S T A D I E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar) (ix : IntegerOps I E),
    DenseLaws cfg sv tv bv pv enc → IntegerLaws ix → ∀ s t start,
      1 ≤ ix.value start → ix.value start ≤ endIndex sv s →
      (validAt sv s (int (ix.value start)) ∨ ix.value start = endIndex sv s) →
      FirstRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
        (ix.value start) (denseNext cfg ix t s start)

/-- Every range returned by string findnext indexes the complete needle: slicing the haystack by that range succeeds and equals the needle, including for invalid input bytes. -/
def FindnextMatches : Prop :=
∀ (A D E : Type) (cfg : DenseStringSearch JString JString A D E)
    (sv tv : TextView JString JChar) (bv : ByteView A UInt8) (pv : ByteView D UInt8)
    (enc : CharEncoding cfg.ncodeunitsChar) (slice : JString → Index → Index → Except E JString),
    DenseLaws cfg sv tv bv pv enc → SliceLaws sv slice → (∀ t, tv.bytes t = t.bytes) →
    ∀ t s i r, denseNext cfg indexOps t s i = .ok (some r) → slice s r.first r.last = .ok t

/-- String findfirst and findlast return the earliest and latest complete
occurrence ranges, including the empty-pattern range at lastindex. -/
def DenseFirstLastSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t,
      FirstRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t) 1
        (denseFirst cfg t s) ∧
      LastRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
        (lastIndex sv s).val (denseLast cfg t s)
/-- For an empty pattern, reverse search follows the documented empty-range
contract and the source's three cases. -/
def DenseReverseEmptySpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i, tv.bytes t = [] →
      ((i.val > (cfg.sizeof s).val →
        densePrev cfg indexOps t s i = .ok (some ⟨int 0, int (-1)⟩)) ∧
       (i.val = 0 →
        densePrev cfg indexOps t s i = .ok (some ⟨int 1, int 0⟩)) ∧
       (i.val ≤ (cfg.sizeof s).val → i.val ≠ 0 →
        densePrev cfg indexOps t s i = .ok (some ⟨i, i - int 1⟩)))

/-- Every successful findprev range matches the pattern and ends at or before
the requested start. -/
def FindprevLatest : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ t s i r,
      0 ≤ i.val → i.val ≤ endIndex sv s →
      densePrev cfg indexOps t s i = .ok (some r) →
      textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r ∧
      r.last.val ≤ i.val

/-- For nonempty needles, string findprev returns exactly the latest complete match whose inclusive end is at or before the start, or nothing if none exists. -/
def DenseReverseSpec : Prop :=
∀ (S T A D I E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar) (ix : IntegerOps I E),
    DenseLaws cfg sv tv bv pv enc → IntegerLaws ix → ∀ s t start,
      (tv.bytes t).isEmpty = false →
      0 ≤ ix.value start → ix.value start ≤ endIndex sv s →
      (validAt sv s (int (ix.value start)) ∨ ix.value start = 0 ∨ ix.value start = endIndex sv s) →
      LastRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
        (ix.value start) (densePrev cfg ix t s start)

/-- An empty string pattern matches the empty range at the requested valid start, including one past the final code unit. -/
def EmptyPatternStartSpec : Prop :=
∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i, tv.bytes t = [] →
      1 ≤ i.val → i.val ≤ endIndex sv s →
      (validAt sv s i ∨ i.val = endIndex sv s) →
      denseNext cfg indexOps t s i = .ok (some ⟨i, i - int 1⟩) ∧
      densePrev cfg indexOps t s i = .ok (some ⟨i, i - int 1⟩)

/-- String-pattern findnext throws BoundsError outside its source-checked byte
range. This claim makes no error assertion about reverse-search starts. -/
def StringStartErrorsSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i,
      (i.val < 1 ∨ endIndex sv s < i.val) →
        denseNext cfg indexOps t s i = .error (cfg.source.boundsError s i.val)

/-- Byte-vector findnext returns the first matching sequence range at or after the start, or nothing if none exists, for arbitrary offset axes and mixed signed/unsigned byte element types. -/
def BytePatternForwardSpec : Prop :=
∀ (A T B C I E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (ix : IntegerOps I E),
    BytePatternLaws cfg sv tv → IntegerLaws ix → ∀ a t start,
      sv.first a ≤ ix.value start → ix.value start ≤ sv.first a + Int.ofNat (sv.elements a).length →
      FirstRange (byteRangeAt cfg sv tv a t) (ix.value start) (vectorNext cfg ix t a start)

/-- Byte-vector findprev returns the last nonempty sequence range ending at or before the start, or nothing if none exists, for arbitrary offset axes. -/
def BytePatternReverseSpec : Prop :=
∀ (A T B C I E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (ix : IntegerOps I E),
    BytePatternLaws cfg sv tv → IntegerLaws ix → ∀ a t start,
      (tv.elements t).isEmpty = false →
      sv.first a - 1 ≤ ix.value start → ix.value start < sv.first a + Int.ofNat (sv.elements a).length →
      LastRange (byteRangeAt cfg sv tv a t) (ix.value start) (vectorPrev cfg ix t a start)

/-- Byte-vector findfirst and findlast return the earliest and latest complete
sequence occurrence ranges, including the empty-pattern range at lastindex. -/
def BytePatternFirstLastSpec : Prop :=
  ∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv → ∀ a t,
      FirstRange (byteRangeAt cfg sv tv a t) (sv.first a) (vectorFirst cfg t a) ∧
      LastRange (byteRangeAt cfg sv tv a t)
        (sv.first a + Int.ofNat (sv.elements a).length - 1) (vectorLast cfg t a)

/-- Every returned nonempty byte-pattern range has the pattern length, independently of both vectors first indices. -/
def OffsetPatternRangeSpec : Prop :=
∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv →
    ∀ a t i r, (tv.elements t).isEmpty = false →
      (vectorNext cfg indexOps t a i = .ok (some r) ∨
       vectorPrev cfg indexOps t a i = .ok (some r) ∨
       vectorFirst cfg t a = .ok (some r) ∨ vectorLast cfg t a = .ok (some r)) →
      r.last.val - r.first.val + 1 = Int.ofNat (tv.elements t).length

/-- An empty byte-vector pattern matches the empty range at the requested haystack index, including on offset axes. -/
def ByteEmptyPatternSpec : Prop :=
∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv →
    ∀ a t i, tv.elements t = [] →
      sv.first a ≤ i.val → i.val ≤ sv.first a + Int.ofNat (sv.elements a).length →
      vectorNext cfg indexOps t a i = .ok (some ⟨i, i - int 1⟩) ∧
      vectorPrev cfg indexOps t a i = .ok (some ⟨i, i - int 1⟩)

/-- The forward byte-pattern method rejects starts before the first element or
after its one-past-end index. Reverse search rejects starts below firstindex-1.
Its one-byte path compares the normalized start with lastindex. -/
def BytePatternStartErrorsSpec : Prop :=
  ∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv → ∀ a t i,
      ((i.val < sv.first a ∨ sv.first a + Int.ofNat (sv.elements a).length < i.val) →
        vectorNext cfg indexOps t a i = .error (cfg.source.boundsError a i.val)) ∧
      (i.val < sv.first a - 1 →
        vectorPrev cfg indexOps t a i = .error (cfg.source.boundsError a i.val)) ∧
      ((tv.elements t).length = 1 ∧
        i.val - (sv.first a - 1) >
          sv.first a + Int.ofNat (sv.elements a).length - 1) →
        vectorPrev cfg indexOps t a i =
          .error (cfg.source.boundsError a (i.val - (sv.first a - 1)))

/-- String occursin and its fixed-haystack function are true exactly when a complete match exists, agreeing with findfirst returning a match. -/
def OccursinSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t,
      (denseOccursin cfg t s = .ok true ↔ ∃ r, denseFirst cfg t s = .ok (some r)) ∧
      (denseOccursin cfg t s = .ok true ↔
        ∃ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r) ∧
      (applyFix2 (denseOccursinFix cfg s) t = .ok true ↔
        ∃ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r)
/-- String-pattern findall returns valid matching ranges in increasing order, disjoint ranges when overlap is false, and every match when overlap is true. -/
def FindallRangeSpec : Prop :=
∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (enc : CharEncoding cfg.ncodeunitsChar),
    DenseLaws cfg sv tv bv pv enc → ∀ s t overlap ranges,
      denseAll cfg t s overlap = .ok ranges →
      (∀ r ∈ ranges, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r) ∧
      ranges.Pairwise (fun a b => a.first.val < b.first.val) ∧
      (overlap = false → ranges.Pairwise (fun a b => a.last.val < b.first.val)) ∧
      (overlap = true → ∀ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r → r ∈ ranges)

/-- String findall's match ranges equal the sequence of repeated findnext
results returned by regex eachmatch when its documented iteration contract holds. -/
def FindallRangesOfEachmatch : Prop :=
  ∀ (S P E : Type) [AbstractPattern P] (string : SearchStringOps S JChar E)
    (v : TextView S JChar) (regex : RegexInterface S P E),
    TextLaws string v → RegexInterfaceLaws regex string v → ∀ re s,
      findallRanges regex.findnext JuliaLean.base.strings.basic.firstindexString
        string.lastindex string.nextind (fun s => (string.ncodeunits s).val.toNat) re s false =
          regex.eachmatchRanges re s

/-- The iszero specializations return the first or last zero-valued byte in the requested direction, for both signed and unsigned storage. -/
def ZeroByteSpec : Prop :=
(∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) → ops.zero = 0 →
    ∀ a i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun b => b == 0) a) i.val
        (findnextZero ops indexOps (memchrUInt8 ops) a i) ∧
      LastIndex (byteMatches v (fun b => b == 0) a) i.val
        (findprevZero ops indexOps (memrchrUInt8 ops) a i)) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) → ops.zero.val = 0 →
    ∀ a i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun b => b.val == 0) a) i.val
        (findnextZero ops indexOps (memchrInt8 ops) a i) ∧
      LastIndex (byteMatches v (fun b => b.val == 0) a) i.val
        (findprevZero ops indexOps (memrchrInt8 ops) a i))

/-- AbstractChar search wrappers return the first or last character that compares equal to the target at or beyond the valid start. -/
def CharWrapperSpec : Prop :=
∀ (S C D E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (equal : C → D → Except E Bool) (accepts : C → D → Bool),
    TextLaws ops v → (∀ c d, equal c d = .ok (accepts c d)) →
    ∀ s target start, validAt v s start →
      FirstIndex (charMatches v (fun c => accepts c target = true) s) start.val
        (findnextCharWrapper equal (findnextPredicate ops indexOps) target s start) ∧
      LastIndex (charMatches v (fun c => accepts c target = true) s) start.val
        (findprevCharWrapper equal (findprevPredicate ops indexOps) target s start)

/-- Character findfirst and findlast return exactly the first and last equal character index or nothing if the character is absent. -/
def CharFirstLastSpec : Prop :=
∀ (S C D E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (equal : C → D → Except E Bool) (accepts : C → D → Bool)
    (first last : (C → Except E Bool) → S → Except E (Option Index)),
    TextLaws ops v → (∀ c d, equal c d = .ok (accepts c d)) →
    (∀ (test : C → Except E Bool) (accept : C → Bool) (s : S), (∀ c, test c = .ok (accept c)) →
      FirstIndex (charMatches v (fun c => accept c = true) s) 1 (first test s)) →
    (∀ (test : C → Except E Bool) (accept : C → Bool) (s : S), (∀ c, test c = .ok (accept c)) →
      LastIndex (charMatches v (fun c => accept c = true) s) (lastIndex v s).val (last test s)) →
    ∀ target s,
      FirstIndex (charMatches v (fun c => accepts c target = true) s) 1
        (findfirstChar equal first target s) ∧
      LastIndex (charMatches v (fun c => accepts c target = true) s) (lastIndex v s).val
        (findlastChar equal last target s)

/-- Character occursin and dense character membership are true exactly when the decoded character occurs in the string, including malformed input bytes. -/
def CharOccursinSpec : Prop :=
∀ (S A E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (ncodeunitsChar : JChar → Index) (enc : CharEncoding ncodeunitsChar),
    Utf8TextLaws ops v ncodeunitsChar enc → CodeunitLaws codeunits bytes v bv → ∀ s c,
      (charOccurrence ops bytes codeunits ncodeunitsChar c s = .ok true
        ↔ ∃ p ∈ v.characters s, p.2 = c) ∧
      (inCharDense ops bytes codeunits ncodeunitsChar c s = .ok true
        ↔ ∃ p ∈ v.characters s, p.2 = c)

/-- Character and byte membership agree with element occurrence; string-in-string rejects the call and directs the caller to occursin. -/
def MembershipSpec : Prop :=
(∀ (S C D E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (equal : C → D → Except E Bool) (accepts : C → D → Bool)
    (first : (C → Except E Bool) → S → Except E (Option Index)),
    TextLaws ops v → (∀ c d, equal c d = .ok (accepts c d)) →
    (∀ (test : C → Except E Bool) (accept : C → Bool) (s : S), (∀ c, test c = .ok (accept c)) →
      FirstIndex (charMatches v (fun c => accept c = true) s) 1 (first test s)) →
    ∀ s c, inChar equal first c s = .ok true ↔ ∃ p ∈ v.characters s, accepts p.2 c = true) ∧
  (∀ (A E : Type) (v : ByteView A UInt8)
    (first : UInt8 → A → Except E (Option Index)),
    (∀ a b, FirstIndex (byteMatches v (fun c => c == b) a) (v.first a) (first b a)) →
    ∀ a b, inUInt8 first b a = .ok true ↔ b ∈ v.elements a) ∧
  (∀ (A E : Type) (v : ByteView A (JInt .i8))
    (first : JInt .i8 → A → Except E (Option Index)),
    (∀ a b, FirstIndex (byteMatches v (fun c => c.val == b.val) a) (v.first a) (first b a)) →
    ∀ a b, inInt8 first b a = .ok true ↔ b ∈ v.elements a) ∧
  (∀ (S T E : Type) (error : String → E) (needle : T) (haystack : S),
    inString error needle haystack = .error (error "use occursin(needle, haystack) for string containment"))

/-- Byte-pattern findall returns matching sequence ranges in order, excludes overlap when requested, and includes every match when overlap is enabled. -/
def ByteFindallSpec : Prop :=
∀ (A T E : Type) (cfg : BytePatternSearch A T UInt8 UInt8 E)
    (sv : ByteView A UInt8) (tv : ByteView T UInt8), BytePatternLaws cfg sv tv →
    ∀ a t overlap ranges,
      findallRanges (vectorNext cfg indexOps) cfg.source.firstindex
        (fun a => .ok (cfg.source.lastindex a)) (fun _ i => .ok (i + int 1))
        (fun a => (cfg.source.length a).val.toNat) t a overlap = .ok ranges →
      (∀ r ∈ ranges, byteRangeAt cfg sv tv a t r) ∧
      ranges.Pairwise (fun a b => a.first.val < b.first.val) ∧
      (overlap = false → ranges.Pairwise (fun a b => a.last.val < b.first.val)) ∧
      (overlap = true → ∀ r, byteRangeAt cfg sv tv a t r → r ∈ ranges)

def entries : List Entry := [
  { id := "strings-search-last-encoded-byte", juliaFile := "base/strings/search.jl",
    juliaFns := ["last_utf8_byte(::Char)"],
    statement := "The final byte returned for any stored Char, including malformed Char values, is the final byte of its encoded representation.",
    source := "invariant: Char byte representation; base/strings/search.jl:34-38", status := .todo, prop := ``LastUtf8ByteSpec, thm := none },
  { id := "strings-search-bloom-bit", juliaFile := "base/strings/search.jl",
    juliaFns := ["_search_bloom_mask"],
    statement := "The bloom mask has exactly one bit set, at the input value modulo 64.",
    source := "invariant: bloom-filter membership; base/strings/search.jl:388-390", status := .todo, prop := ``BloomBitSpec, thm := none },
  { id := "strings-search-memchr-first", juliaFile := "base/strings/search.jl",
    juliaFns := ["memchr(::DenseUInt8,::UInt8,::Int)", "memchr(::DenseInt8,::Int8,::Int)"],
    statement := "memchr returns the least matching byte index in the requested suffix, restores offset axes, and returns nothing exactly when the suffix has no match.",
    source := "C17 7.24.5.1; base/strings/search.jl:182-198", status := .todo, prop := ``MemchrFirstSpec, thm := none },
  { id := "strings-search-memrchr-last", juliaFile := "base/strings/search.jl",
    juliaFns := ["memrchr(::DenseUInt8,::UInt8,::Int)", "memrchr(::DenseInt8,::Int8,::Int)"],
    statement := "memrchr returns the greatest matching byte index in the requested prefix, restores offset axes, and returns nothing exactly when the prefix has no match.",
    source := "memrchr reverse-memory-search contract; base/strings/search.jl:246-262", status := .todo, prop := ``MemrchrLastSpec, thm := none },
  { id := "strings-search-dense-byte-forward", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},Int8},::DenseInt8,::Integer)", "findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8},::DenseUInt8,::Integer)"],
    statement := "Dense signed and unsigned byte findnext returns the first match at or after the start, rejects a start below the array, and preserves Int conversion errors.",
    source := "findnext contract and byte-array indexing invariant; base/strings/search.jl:168-180", status := .todo, prop := ``DenseByteForwardSpec, thm := none },
  { id := "strings-search-dense-byte-reverse", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},Int8},::DenseInt8,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8},::DenseUInt8,::Integer)"],
    statement := "Dense signed and unsigned byte findprev returns the last match at or before the start, rejects a start above the array, and preserves Int conversion errors.",
    source := "findprev contract and byte-array indexing invariant; base/strings/search.jl:232-244", status := .todo, prop := ``DenseByteReverseSpec, thm := none },
  { id := "strings-search-predicate-forward", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)"],
    statement := "Predicate findnext returns exactly the least accepted character index at or after a valid start, or nothing when no character is accepted.",
    source := "findnext contract; base/strings/search.jl:343-354", status := .todo, prop := ``PredicateForwardSpec, thm := none },
  { id := "strings-search-predicate-reverse", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::Function,::AbstractString,::Integer)"],
    statement := "Predicate findprev returns exactly the greatest accepted character index at or before a valid start, or nothing when no character is accepted.",
    source := "findprev contract; base/strings/search.jl:668-679", status := .todo, prop := ``PredicateReverseSpec, thm := none },
  { id := "strings-search-predicate-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)", "findprev(::Function,::AbstractString,::Integer)"],
    statement := "Predicate search throws BoundsError outside its start domain and StringIndexError for a byte position inside a character, including in strings containing invalid UTF-8 bytes.",
    source := "string-indexing manual and explicit start checks; base/strings/search.jl:343-354,668-679", status := .todo, prop := ``PredicateStartErrorsSpec, thm := none },
  { id := "strings-search-predicate-error-propagation", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)", "findprev(::Function,::AbstractString,::Integer)"],
    statement := "A predicate exception at the first tested position after a false-only prefix is returned unchanged in either search direction.",
    source := "generic Function call semantics; base/strings/search.jl:350,675", status := .todo, prop := ``PredicateErrorSpec, thm := none },
  { id := "strings-search-standalone-character-indices", juliaFile := "base/strings/search.jl",
    juliaFns := ["is_standalone_byte(::UInt8)"],
    statement := "Every occurrence of a byte classified standalone begins a one-byte character, even when the surrounding input contains malformed UTF-8 bytes.",
    source := "source invariant base/strings/search.jl:40-42,65-67", status := .todo, prop := ``StandalonePositionsSpec, thm := none },
  { id := "strings-search-forward-character-iterator", juliaFile := "base/strings/search.jl",
    juliaFns := ["FwCharPosIter(::UTF8String,::AbstractChar)", "iterate(::FwCharPosIter,::Int)", "try_next"],
    statement := "Forward character-position iteration yields the least complete matching character from a valid start and returns nothing exactly when no such character remains.",
    source := "character-position iterator invariant; base/strings/search.jl:54-93,138-141", status := .todo, prop := ``ForwardIteratorSpec, thm := none },
  { id := "strings-search-reverse-character-iterator", juliaFile := "base/strings/search.jl",
    juliaFns := ["RvCharPosIter(::UTF8String,::AbstractChar)", "iterate(::RvCharPosIter,::Int)", "try_next"],
    statement := "Reverse character-position iteration yields the greatest complete matching character at or before a valid start and returns nothing exactly when none remains.",
    source := "character-position iterator invariant; base/strings/search.jl:105-141", status := .todo, prop := ``ReverseIteratorSpec, thm := none },
  { id := "strings-search-character-extrema", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)"],
    statement := "Character findnext and findprev return the first or last matching decoded character at valid string indices, including for malformed input bytes.",
    source := "findnext/findprev character docstrings; base/strings/search.jl:143-166,209-230,510-512,824-826", status := .todo, prop := ``CharSearchSpec, thm := none },
  { id := "strings-search-character-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)"],
    statement := "Forward Char search rejects a start inside a character; both Char directions throw BoundsError only at starts outside their source-checked bounds.",
    source := "explicit BoundsError and StringIndexError sites; base/strings/search.jl:148-160,214-220", status := .todo, prop := ``CharStartErrorsSpec, thm := none },
  { id := "strings-search-all-character-matches", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String)"],
    statement := "Character findall returns all and only the matching character indices in increasing order, including in malformed UTF-8 strings.",
    source := "findall contract and character-index invariant; base/strings/search.jl:272-284", status := .todo, prop := ``FindallCharSpec, thm := none },
  { id := "stringscova-search-searchindex-generic-rebuilt", juliaFile := "base/strings/search.jl",
    juliaFns := ["_searchindex(::Union{AbstractString,DenseUInt8OrInt8},::Union{AbstractString,AbstractChar,Int8,UInt8},::Integer)"],
    statement := "Generic substring search returns the least complete pattern match from the start, including the empty-pattern start, and returns its sentinel exactly when no match exists.",
    source := "findnext first-occurrence contract; base/strings/search.jl:365-384", status := .todo, prop := ``GenericForwardSpec, thm := none,
    notes := "Restated on the source-mirrored generic method with primitive iterator and SubString laws." },
  { id := "strings-search-generic-reverse-last", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::AbstractString,::Union{AbstractString,AbstractChar,Int8,UInt8},::Integer)"],
    statement := "Generic reverse substring search returns the latest complete match ending at or before the start; an empty pattern matches at the start.",
    source := "findprev docstring; base/strings/search.jl:681-703,799-807", status := .todo, prop := ``GenericReverseSpec, thm := none },
  { id := "strings-search-forward-first-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_searchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_search", "findnext(::AbstractString,::AbstractString,::Integer)"],
    statement := "String findnext returns exactly the earliest complete match range at or after a valid start and returns nothing exactly when no matching range exists.",
    source := "findnext docstring base/strings/search.jl:481-507", status := .todo, prop := ``DenseForwardSpec, thm := none },
  { id := "strings-findnext-inside-char", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)", "findfirst(::AbstractString,::AbstractString)"],
    statement := "Every range returned by string findnext indexes the complete needle: slicing the haystack by that range succeeds and equals the needle, including for invalid input bytes.",
    source := "findnext docstring base/strings/search.jl:489-493", status := .todo, prop := ``FindnextMatches, thm := none,
    notes := "Historical refutation retained as an open statement on the new model; this assignment adds no theorem." },
  { id := "strings-search-first-last-string", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractString,::AbstractString)", "findlast(::AbstractString,::AbstractString)"],
    statement := "String findfirst and findlast return the earliest and latest complete pattern ranges, including the empty-pattern range at lastindex for an empty string.",
    source := "findfirst/findlast docstrings base/strings/search.jl:286-302,553-569", status := .todo, prop := ``DenseFirstLastSpec, thm := none },
  { id := "strings-findprev-empty-end", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "Every range returned by findprev matches the pattern and ends at or before the requested start.",
    source := "findprev docstring base/strings/search.jl:799-807", status := .todo, prop := ``FindprevLatest, thm := none,
    notes := "Historical refutation retained as an open statement on the new model; the one-past-end case is not excluded." },
  { id := "strings-search-reverse-last-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_rsearch", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "For nonempty needles, string findprev returns exactly the latest complete match whose inclusive end is at or before the start, or nothing if none exists.",
    source := "findprev docstring base/strings/search.jl:798-821", status := .todo, prop := ``DenseReverseSpec, thm := none },
  { id := "strings-search-dense-reverse-empty-integer", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_rsearch", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "For an empty pattern, reverse search returns 0:-1 when i>sizeof(s), 1:0 when i=0, and i:i-1 otherwise.",
    source := "findprev docstring and empty-pattern contract; base/strings/search.jl:705-719,799-821", status := .todo, prop := ``DenseReverseEmptySpec, thm := none },
  { id := "strings-search-empty-pattern-start", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "An empty string pattern matches the empty range at the requested valid start, including one past the final code unit.",
    source := "empty-pattern invariant and findnext/findprev docs; base/strings/search.jl:365-373,705-719", status := .todo, prop := ``EmptyPatternStartSpec, thm := none },
  { id := "strings-search-string-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)"],
    statement := "String-pattern findnext throws BoundsError outside [1,ncodeunits+1]; this entry makes no error claim about reverse starts or valid interior byte positions.",
    source := "byte-search bounds check; base/strings/search.jl:395-408", status := .todo, prop := ``StringStartErrorsSpec, thm := none },
  { id := "strings-search-byte-pattern-first", juliaFile := "base/strings/search.jl",
    juliaFns := ["_nthbyte(::AbstractVector,index)", "_searchindex(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "_search", "findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-vector findnext returns the first matching sequence range at or after the start, or nothing if none exists, for arbitrary offset axes and mixed signed/unsigned byte element types.",
    source := "byte-vector findnext docstring base/strings/search.jl:529-551", status := .todo, prop := ``BytePatternForwardSpec, thm := none },
  { id := "strings-search-byte-pattern-last", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "_rsearch", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-vector findprev returns the last nonempty sequence range ending at or before the start, or nothing if none exists, for arbitrary offset axes.",
    source := "byte-vector findprev docstring base/strings/search.jl:843-862", status := .todo, prop := ``BytePatternReverseSpec, thm := none },
  { id := "strings-search-first-last-byte-pattern", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}})", "findlast(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}})"],
    statement := "Byte-vector findfirst and findlast return the earliest and latest complete pattern ranges, including the empty-pattern range selected from lastindex on an empty vector.",
    source := "findfirst/findlast byte-vector docstrings base/strings/search.jl:323-340,571-586", status := .todo, prop := ``BytePatternFirstLastSpec, thm := none },
  { id := "stringscova-search-offset-pattern-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_search", "_rsearch", "findnext/findprev/findfirst/findlast byte-vector wrappers"],
    statement := "Every returned nonempty byte-pattern range has the pattern length, independently of both vectors first indices.",
    source := "documented match-range invariant; base/strings/search.jl:468-479,785-796", status := .todo, prop := ``OffsetPatternRangeSpec, thm := none },
  { id := "strings-search-byte-empty-pattern-start", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "An empty byte-vector pattern matches the empty range at the requested haystack index, including on offset axes.",
    source := "empty-sequence matching invariant; base/strings/search.jl:401-416,721-734", status := .todo, prop := ``ByteEmptyPatternSpec, thm := none },
  { id := "strings-search-byte-pattern-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-pattern findnext throws BoundsError before firstindex or after its one-past-end index; findprev throws below firstindex-1, and its one-byte path also throws when the normalized start exceeds lastindex.",
    source := "byte-vector search checks; base/strings/search.jl:401-408,721-734", status := .todo, prop := ``BytePatternStartErrorsSpec, thm := none },
  { id := "strings-search-occursin-first-match", juliaFile := "base/strings/search.jl",
    juliaFns := ["occursin(::Union{AbstractString,AbstractChar},::AbstractString)", "occursin(haystack)"],
    statement := "String occursin and its fixed-haystack function are true exactly when a complete match exists, agreeing with findfirst returning a match.",
    source := "occursin docstrings base/strings/search.jl:863-911", status := .todo, prop := ``OccursinSpec, thm := none },
  { id := "strings-search-all-pattern-ranges", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}},::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}};overlap)"],
    statement := "String-pattern findall returns valid matching ranges in increasing order, disjoint ranges when overlap is false, and every match when overlap is true.",
    source := "findall docstring base/strings/search.jl:607-665", status := .todo, prop := ``FindallRangeSpec, thm := none },
  { id := "regexunicode-findall-skips-nonempty", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Regex,::AbstractString)", "findall(t::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}}, s::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}}, ; overlap::Bool=false)", "eachmatch(::Regex,::AbstractString)"],
    statement := "Regex findall returns the same ranges as eachmatch; the interface law states eachmatch's ranges are repeated findnext results, including empty matches.",
    source := "findall docstring base/strings/search.jl:619-621; eachmatch contract base/regex.jl", status := .todo, prop := ``FindallRangesOfEachmatch, thm := none,
    notes := "Historical refutation retained as an open statement on the new model. Regex engine operations are external typed parameters." },
  { id := "strings-search-zero-byte-extrema", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::typeof(iszero),::DenseUInt8OrInt8,::Integer)", "findprev(::typeof(iszero),::DenseUInt8OrInt8,::Integer)"],
    statement := "The iszero specializations return the first or last zero-valued byte in the requested direction, for both signed and unsigned storage.",
    source := "iszero byte-pattern invariant; base/strings/search.jl:200-207,264-270", status := .todo, prop := ``ZeroByteSpec, thm := none },
  { id := "strings-search-abstract-character-wrappers", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractChar,::AbstractString,::Integer)", "findprev(::AbstractChar,::AbstractString,::Integer)"],
    statement := "AbstractChar search wrappers return the first or last character that compares equal to the target at or beyond the valid start.",
    source := "character findnext/findprev docstrings; base/strings/search.jl:509-527,823-841", status := .todo, prop := ``CharWrapperSpec, thm := none },
  { id := "strings-search-first-last-character", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractChar,::AbstractString)", "findlast(::AbstractChar,::AbstractString)"],
    statement := "Character findfirst and findlast return exactly the first and last equal character index or nothing if the character is absent.",
    source := "character findfirst/findlast docstrings; base/strings/search.jl:304-321,588-605", status := .todo, prop := ``CharFirstLastSpec, thm := none },
  { id := "strings-search-character-occurrence", juliaFile := "base/strings/search.jl",
    juliaFns := ["_searchindex(::AbstractString,::AbstractChar,::Integer)", "occursin(::Union{AbstractString,AbstractChar},::AbstractString)", "in(::Char,::Union{String,SubString{String}})"],
    statement := "Character occursin and dense character membership are true exactly when the decoded character occurs in the string, including malformed input bytes.",
    source := "occursin and character-membership contract; base/strings/search.jl:360-363,386,886-887", status := .todo, prop := ``CharOccursinSpec, thm := none },
  { id := "strings-search-membership", juliaFile := "base/strings/search.jl",
    juliaFns := ["in(::AbstractChar,::AbstractString)", "in(::UInt8,::DenseUInt8)", "in(::Int8,::DenseInt8)", "in(::AbstractString,::AbstractString)"],
    statement := "Character and byte membership agree with element occurrence; string-in-string rejects the call and directs the caller to occursin.",
    source := "membership invariant and string-containment guidance; base/strings/search.jl:356,913-916", status := .todo, prop := ``MembershipSpec, thm := none },
  { id := "strings-search-byte-pattern-all", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}},::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}};overlap)"],
    statement := "Byte-pattern findall returns matching sequence ranges in order, excludes overlap when requested, and includes every match when overlap is enabled.",
    source := "findall byte-vector docstring base/strings/search.jl:607-665", status := .todo, prop := ``ByteFindallSpec, thm := none }
]

/-! ## Nothing to promise

IteratorSize@102: returns fixed iterator metadata without selecting a search result.
eltype@103: returns the fixed index element type without searching any input.
_nthbyte@392: forwards the unchanged index to codeunit; storage and bounds are the string.jl callee's contract.

The constructors, try_next, vector _nthbyte, and public forwarding methods are
used by the iterator, sequence-search, membership, and public-search statements.
-/

end JuliaLean.Proofs.base.strings.search
