import JuliaLean.BitSetsCov.BitSetLemmas

/-!
# Properties of `BitSet` (`base/bitset.jl`)

`BitSet` "Construct[s] a sorted set of `Int`s" (docstring `base/bitset.jl:25-32`)
and is an `AbstractSet{Int}`, so it must behave as `Set{Int}`: every property
below states the membership (`BS.mem`) or the value Julia promises, for every
state satisfying the type invariant `BS.WF`, every `Integer` argument and every
content `dirty` of freshly allocated memory.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

/-- `BitSet()`, `empty`, `emptymutable` are empty; `BitSet(itr)`, `union!(s, itr)`
and `push!(s, ns...)` add exactly the elements of `itr`, or throw `InexactError`
when one of them is not an `Int`. -/
def BitSetBuildSpec : Prop :=
  BS.WF BS.new ∧ (∀ x, BS.mem BS.new x = false) ∧
  (∀ s : BitSetS, BS.empty s = BS.new ∧ BS.emptymutable s = BS.new) ∧
  (∀ (s : BitSetS) (xs : List Int), BS.WF s → (∀ x ∈ xs, inIntRange x) →
    ∃ s', BS.unionItr s xs = .ok s' ∧ BS.pushMany s xs = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s x || decide (x ∈ xs))) ∧
  (∀ (s : BitSetS) (xs : List Int), (∃ x ∈ xs, ¬ inIntRange x) →
    BS.unionItr s xs = .error .inexactError) ∧
  (∀ xs : List Int, (∀ x ∈ xs, inIntRange x) →
    ∃ s', BS.ofItr xs = .ok s' ∧ BS.WF s' ∧ ∀ x, BS.mem s' x = decide (x ∈ xs))

/-- `copy!(dest, src)`, `copy(src)` and `copymutable(src)` give exactly the state of `src`. -/
def BitSetCopySpec : Prop :=
  ∀ (dest src : BitSetS) (dirty : U64),
    BS.copyBang dest src dirty = .ok src ∧ BS.copy src dirty = .ok src ∧
    BS.copymutable src dirty = .ok src

/-- `sizehint!(s, n)` keeps the set for every `BitInteger` `n` (only a 128-bit
`n` can make the `Int` conversion of the chunk count throw). -/
def BitSetSizehintSpec : Prop :=
  ∀ (t : IntTy) (s : BitSetS) (n : JInt t),
    BS.sizehint s n = .ok s ∨ (t.bits = 128 ∧ BS.sizehint s n = .error .inexactError)

/-- `in(n, s)` for every `Integer` `n` (through `_is_convertible_Int`,
`in(::Int, s)` and `_bits_getindex`) is membership. -/
def BitSetInSpec : Prop :=
  (∀ (b : List U64) (m : JInt64) (off : Int), BS.bitsGetindex b m off = BS.mem ⟨b, off⟩ m.val) ∧
  (∀ n : Int, BS.isConvertibleInt n = decide (inIntRange n)) ∧
  ∀ (s : BitSetS), BS.WF s → ∀ n : Int, BS.inInteger n s = BS.mem s n

/-- `delete!(s, n)` removes exactly `n` for every `Integer` `n`; `pop!(s, n)`
returns `n` and deletes it, or throws `KeyError`; `pop!(s, n, default)`
returns `default` when `n` is absent. -/
def BitSetDeleteSpec : Prop :=
  (∀ (s : BitSetS), BS.WF s → ∀ n : JInt64,
    BS.WF (BS.deleteInt s n) ∧
    ∀ x, BS.mem (BS.deleteInt s n) x = (BS.mem s x && decide (x ≠ n.val))) ∧
  ∀ (s : BitSetS), BS.WF s → ∀ n : Int,
    BS.WF (BS.deleteInteger s n) ∧
    (∀ x, BS.mem (BS.deleteInteger s n) x = (BS.mem s x && decide (x ≠ n))) ∧
    BS.popKey s n = (if BS.mem s n then .ok (n, BS.deleteInteger s n) else .error .keyError) ∧
    BS.popDefault s n = (if BS.mem s n then (some n, BS.deleteInteger s n) else (none, s))

/-- `empty!(s)` removes every element and resets the offset; `isempty(s)`
(`_check0` over all chunks) holds exactly when no integer is a member. -/
def BitSetEmptySpec : Prop :=
  (∀ (a : List U64) (b e : Int), 1 ≤ b →
    (BS.check0 a b e = true ↔ ∀ i : Int, b ≤ i → i ≤ e → a.getD (i - 1).toNat 0 = 0)) ∧
  ∀ s : BitSetS, BS.WF s →
    BS.WF (BS.emptyBang s) ∧ (∀ x, BS.mem (BS.emptyBang s) x = false) ∧
    (BS.emptyBang s).offset = noOffset ∧
    (BS.isempty s = true ↔ ∀ x, BS.mem s x = false)

/-- `symdiff!(s, ns::AbstractSet)` toggles each element of the set `ns`. -/
def BitSetSymdiffSetSpec : Prop :=
  ∀ (s : BitSetS) (ns : List Int), BS.WF s → ns.Nodup → (∀ x ∈ ns, inIntRange x) →
    ∃ s', BS.symdiffSet s ns = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s x ^^ decide (x ∈ ns))

/-- `_growend0!` and `_growbeg0!` add zero chunks at the end or the front,
whatever the fresh memory held. -/
def BitSetGrowSpec : Prop :=
  ∀ (b : List U64) (k : Nat) (dirty : U64),
    BS.growend0 b k dirty = b ++ List.replicate k 0 ∧
    BS.growbeg0 b k dirty = List.replicate k 0 ++ b

/-- `union!(s, a:b)` adds exactly the integers of `a:b`; it throws
`InexactError` when a bound of a nonempty range is not an `Int`. -/
def BitSetUnionRangeSpec : Prop :=
  ∀ (s : BitSetS) (a b : Int) (dirty : U64), BS.WF s →
    (b < a → BS.unionRange s a b dirty = .ok s) ∧
    (a ≤ b → inIntRange a → inIntRange b →
      ∃ s', BS.unionRange s a b dirty = .ok s' ∧ BS.WF s' ∧
        ∀ x, BS.mem s' x = (BS.mem s x || decide (a ≤ x ∧ x ≤ b))) ∧
    (a ≤ b → (¬ inIntRange a ∨ ¬ inIntRange b) → BS.unionRange s a b dirty = .error .inexactError)

/-- `union!(s1, s2)`, `intersect!`, `setdiff!`, `symdiff!` between two
`BitSet`s (all through `_matched_map!`), and `intersect(s1, s2)` and
`union(s, sets...)`, give the elementwise `|`, `&`, `&!` and `xor`
of the memberships and keep the invariant. -/
def BitSetMatchedSpec : Prop :=
  (∀ (f : BS.MapOp) (s1 s2 : BitSetS) (dirty : U64), BS.WF s1 → BS.WF s2 →
    ∃ s', BS.matchedMap f s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = f.bool (BS.mem s1 x) (BS.mem s2 x)) ∧
  (∀ (s1 s2 : BitSetS) (dirty : U64), BS.WF s1 → BS.WF s2 →
    (∃ s', BS.unionBS s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s1 x || BS.mem s2 x)) ∧
    (∃ s', BS.intersectBang s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s1 x && BS.mem s2 x)) ∧
    (∃ s', BS.setdiffBang s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s1 x && !BS.mem s2 x)) ∧
    (∃ s', BS.symdiffBS s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s1 x ^^ BS.mem s2 x)) ∧
    (∃ s', BS.intersect s1 s2 dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s1 x && BS.mem s2 x)))

/-- `s1 == s2` for `BitSet`s is equality of the member sets. -/
def BitSetEqSpec : Prop :=
  ∀ (s1 s2 : BitSetS), BS.WF s1 → BS.WF s2 →
    (BS.eq s1 s2 = true ↔ ∀ x, BS.mem s1 x = BS.mem s2 x)

/-- `issubset(a, b)` (with its chunk test `f(a, b) = a == a & b`) is inclusion
of the member sets, and `a ⊊ b` is strict inclusion. -/
def BitSetSubsetSpec : Prop :=
  (∀ x y : U64, BS.subChunk x y = true ↔ ∀ j, x.getLsbD j = true → y.getLsbD j = true) ∧
  ∀ (a b : BitSetS), BS.WF a → BS.WF b →
    (BS.issubset a b = true ↔ ∀ x, BS.mem a x = true → BS.mem b x = true) ∧
    (BS.psubset a b = true ↔
      (∀ x, BS.mem a x = true → BS.mem b x = true) ∧ ∃ x, BS.mem a x ≠ BS.mem b x)

/-- Joining printed elements with `", "` (what the `show` loop produces). -/
def joinComma : List String → String
  | [] => ""
  | [a] => a
  | a :: rest => a ++ ", " ++ joinComma rest

/-- `_bits_findnext(b, start)` is the first set position `≥ start` (0-based) or
`-1`; `_bits_findprev(b, start)` the last set position `≤ start` or `-1`. -/
def BitSetFindSpec : Prop :=
  (∀ (b : List U64) (start : Nat), BS.bitsFindnext b start =
    match (List.range (64 * b.length)).find? (fun p => decide (start ≤ p) && bitOf b p) with
    | some p => (p : Int) | none => -1) ∧
  (∀ (b : List U64) (start : Int), start < 64 * b.length → BS.bitsFindprev b start =
    match (List.range (64 * b.length)).reverse.find? (fun (p : Nat) => decide ((p : Int) ≤ start) && bitOf b p) with
    | some p => (p : Int) | none => -1)

/-- Iteration yields the members in increasing order; `intoffset` is the
first value of chunk 1; `length`, `first`, `last`, `minimum`, `maximum`,
`extrema`, `issorted`, `pop!(s)`, `popfirst!(s)` and `show` agree with that
sequence (for sets whose chunks fit in memory); `first` and `last` of an empty
set throw the `ArgumentError` of `_throw_bitset_notempty_error`. -/
def BitSetIterSpec : Prop :=
  ∀ s : BitSetS, BS.WF s → s.bits.length < 2 ^ 57 →
    let xs := BS.elems s
    (s.offset ≠ noOffset → BS.intoffset s = shl6 s.offset) ∧
    (∀ x, x ∈ xs.map (·.val) ↔ BS.mem s x = true) ∧
    (xs.map (·.val)).Pairwise (· < ·) ∧
    (BS.length s).val = xs.length ∧
    BS.first s = (match xs.head? with | some x => .ok x | none => .error .argumentError) ∧
    BS.last s = (match xs.getLast? with | some x => .ok x | none => .error .argumentError) ∧
    BS.minimum s = (match xs.head? with | some x => .ok x | none => .error .argumentError) ∧
    BS.maximum s = (match xs.getLast? with | some x => .ok x | none => .error .argumentError) ∧
    BS.extrema s = (match xs.head?, xs.getLast? with
      | some x, some y => .ok (x, y) | _, _ => .error .argumentError) ∧
    BS.issorted s = true ∧
    BS.pop s = (match xs.getLast? with
      | some x => .ok (x.val, BS.deleteInteger s x.val) | none => .error .argumentError) ∧
    BS.popfirst s = (match xs.head? with
      | some x => .ok (x.val, BS.deleteInteger s x.val) | none => .error .argumentError) ∧
    BS.showStr s = "BitSet([" ++ joinComma (xs.map (fun n => toString n.val)) ++ "])"

/-- The members of a `union` argument. -/
def BS.Arg.mem : BS.Arg → Int → Bool
  | .bitset t, x => BS.mem t x
  | .range a b, x => decide (a ≤ x ∧ x ≤ b)
  | .itr xs, x => decide (x ∈ xs)

/-- The arguments a `union` call accepts without throwing: valid `BitSet`s,
ranges of `Int`s and iterables of `Int`s. -/
def BS.Arg.ok : BS.Arg → Prop
  | .bitset t => BS.WF t
  | .range a b => b < a ∨ (inIntRange a ∧ inIntRange b)
  | .itr xs => ∀ x ∈ xs, inIntRange x

/-- `union(s, sets...)` copies `s` and adds every argument (by `union!` dispatch). -/
def BitSetUnionSpec : Prop :=
  ∀ (s : BitSetS) (sets : List BS.Arg) (dirty : U64), BS.WF s → (∀ a ∈ sets, a.ok) →
    ∃ s', BS.union s sets dirty = .ok s' ∧ BS.WF s' ∧
      ∀ x, BS.mem s' x = (BS.mem s x || sets.any (fun a => a.mem x))

/-- `filter!(f, s)` preserves the `BitSet` representation invariant while its
`mapfilter(!f, delete!, s, s)` loop deletes from the set being iterated. -/
def BitSetFilterSpec : Prop :=
  ∀ (f : JInt64 → Bool) (s : BitSetS), BS.WF s →
    BS.WF (BS.filterBang f s)

end JuliaLean.BitSetsCov
