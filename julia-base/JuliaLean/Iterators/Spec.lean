import JuliaLean.Iterators.Props

/-!
# Properties of `base/iterators.jl` that hold

Statements only; the proofs are in `JuliaLean/Iterators/Proofs.lean`.
Vectors have fewer than `2^59` elements (`Fits`), as any vector in memory:
8-byte slots for `2^59` elements already exceed `MAXINTVAL` bytes.
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- A vector that fits in memory. -/
def Fits {α : Type} (xs : List α) : Prop := xs.length < 2 ^ 59

/-- `enumerate` pairs `(i, x)` counting from `i`. -/
def enumSpec : Int → List Val → List Val
  | _, [] => []
  | i, x :: xs => .tup [.int i, x] :: enumSpec (i + 1) xs

/-- Chunks of `k` consecutive elements, the last one possibly shorter. -/
def chunksSpec {α : Type} (k : Nat) (xs : List α) : List (List α) :=
  (List.range ((xs.length + k - 1) / k)).map fun i => (xs.drop (i * k)).take k

/-- `Iterators.accumulate(f, xs; init)`: the running reductions. -/
def accSpec (f : Val → Val → Val) : Option Val → List Val → List Val
  | _, [] => []
  | none, x :: xs => x :: accFrom f x xs
  | some i, x :: xs => f i x :: accFrom f (f i x) xs
where
  accFrom (f : Val → Val → Val) : Val → List Val → List Val
    | _, [] => []
    | a, x :: xs => f a x :: accFrom f (f a x) xs

/-- `take(v, n)` of a vector yields its first `n` elements, and `length`
agrees with that count (iterators.jl:790 "generates at most the first `n`
elements"). -/
def TakeCorrect : Prop :=
  ∀ (xs : List Int) (n : JInt64), 0 ≤ n.val → Fits xs →
    ∃ t, take (vecI xs) n = .ok t ∧ len t = .ok (i64 (min n.val xs.length)) ∧
      ∀ fuel, xs.length < fuel → elems fuel t = .ok (ints (xs.take n.val.toNat))

/-- `take(take(v, a), b)` yields the first `min(a, b)` elements. -/
def TakeTakeCorrect : Prop :=
  ∀ (xs : List Int) (a b : JInt64), 0 ≤ a.val → 0 ≤ b.val →
    ∃ t, (do take (← take (vecI xs) a) b) = .ok t ∧
      ∀ fuel, xs.length < fuel → elems fuel t = .ok (ints (xs.take (min a.val b.val).toNat))

/-- `drop(v, n)` of a vector yields all but its first `n` elements, and
`length` agrees (iterators.jl:849). -/
def DropCorrect : Prop :=
  ∀ (xs : List Int) (n : JInt64), 0 ≤ n.val → Fits xs →
    ∃ d, drop (vecI xs) n = .ok d ∧ len d = .ok (i64 (max (xs.length - n.val) 0)) ∧
      ∀ fuel, xs.length < fuel → elems fuel d = .ok (ints (xs.drop n.val.toNat))

/-- `take(v, n)` and `drop(v, n)` together yield `v`. -/
def TakeDropComplement : Prop :=
  ∀ (xs : List Int) (n : JInt64) (t d : Itr) (fuel : Nat), 0 ≤ n.val → xs.length < fuel →
    take (vecI xs) n = .ok t → drop (vecI xs) n = .ok d →
    (do pure ((← elems fuel t) ++ (← elems fuel d))) = .ok (ints xs)

/-- `takewhile(p, v)` yields the longest prefix satisfying `p`, and
`dropwhile(p, v)` the rest (iterators.jl:905, 952). -/
def TakeWhileDropWhile : Prop :=
  ∀ (p : Val → Bool) (xs : List Val) (fuel : Nat), xs.length < fuel →
    elems fuel (.takeWhile p (.vec .int xs)) = .ok (xs.takeWhile p) ∧
    elems fuel (.dropWhile p (.vec .int xs)) = .ok (xs.dropWhile p)

/-- `enumerate(v)` yields `(i, v[i])` for `i = 1, 2, ...`, has `length(v)`
elements, and `Iterators.reverse(enumerate(v))` yields them backwards
(iterators.jl:173). -/
def EnumerateCorrect : Prop :=
  ∀ (xs : List Val) (fuel : Nat), Fits xs → xs.length < fuel →
    elems fuel (.enumerate (.vec .int xs)) = .ok (enumSpec 1 xs) ∧
    len (.enumerate (.vec .int xs)) = .ok (i64 xs.length) ∧
    ∃ r, reverse (.enumerate (.vec .int xs)) = .ok r ∧ elems fuel r = .ok (enumSpec 1 xs).reverse

/-- `zip(a, b)` of vectors yields the pairs up to the shorter length, which is
its `length` (iterators.jl:343). -/
def ZipCorrect : Prop :=
  ∀ (xs ys : List Val) (fuel : Nat), Fits xs → Fits ys → xs.length < fuel →
    elems fuel (.zip [.vec .int xs, .vec .int ys]) =
      .ok (List.zipWith (fun a b => .tup [a, b]) xs ys) ∧
    len (.zip [.vec .int xs, .vec .int ys]) = .ok (i64 (min xs.length ys.length))

/-- `Iterators.reverse(zip(a, b))` yields the pairs backwards when the lengths
agree, and throws `ArgumentError` when they differ (iterators.jl:521-526). -/
def ZipReverse : Prop :=
  ∀ (xs ys : List Val) (fuel : Nat), Fits xs → Fits ys → xs.length < fuel →
    (xs.length = ys.length → ∃ r, reverse (.zip [.vec .int xs, .vec .int ys]) = .ok r ∧
      elems fuel r = .ok (List.zipWith (fun a b => .tup [a, b]) xs ys).reverse) ∧
    (xs.length ≠ ys.length → ∃ msg,
      reverse (.zip [.vec .int xs, .vec .int ys]) = .error (.jl (.argumentError msg)))

/-- `product(a, b)` of vectors yields all pairs with the first iterator
changing fastest (iterators.jl:1131-1133), and `size` is
`(length(a), length(b))`. -/
def ProductCorrect : Prop :=
  ∀ (xs ys : List Val) (fuel : Nat), Fits xs → Fits ys → xs.length * ys.length < fuel →
    elems fuel (.product [.vec .int xs, .vec .int ys]) =
      .ok (ys.flatMap fun y => xs.map fun x => .tup [x, y]) ∧
    size (.product [.vec .int xs, .vec .int ys]) = .ok [i64 xs.length, i64 ys.length]

/-- `flatten(vs)` of a vector of vectors yields their concatenation
(iterators.jl:1268-1270). -/
def FlattenCorrect : Prop :=
  ∀ (vs : List (List Val)) (fuel : Nat),
    (vs.map List.length).sum + vs.length < fuel →
    elems fuel (.flatten (.vec (.vector .int) (vs.map (.vec .int)))) = .ok vs.flatten

/-- `length(flatten(v))` for a vector of `k`-tuples is `k * length(v)`, or an
`OverflowError` when that does not fit (master; 1.13.2 wraps). -/
def FlattenTupleLength : Prop :=
  ∀ (k : Nat) (xs : List Val), Fits xs → k < 2 ^ 62 →
    (k * xs.length ≤ maxIntVal →
      len (.flatten (.vec (.tuple (List.replicate k .int)) xs)) = .ok (i64 (k * xs.length))) ∧
    (maxIntVal < k * xs.length →
      ∃ msg, len (.flatten (.vec (.tuple (List.replicate k .int)) xs)) = .error (.jl (.overflowError msg)))

/-- `cycle(v, m)` yields `v` `m` times (iterators.jl:1031, 1034:
"the lazy equivalent of `repeat(vector, n)`"). -/
def CycleNCorrect : Prop :=
  ∀ (xs : List Val) (m : JInt64) (fuel : Nat), 0 ≤ m.val →
    (xs.length + 1) * m.val.toNat + 2 < fuel →
    ∃ c, cycleN (.vec .int xs) m = .ok c ∧ elems fuel c = .ok (List.replicate m.val.toNat xs).flatten

/-- `repeated(x, n)` yields `x` `n` times and has length `n` (iterators.jl:1088). -/
def RepeatedNCorrect : Prop :=
  ∀ (x : Val) (n : JInt64) (fuel : Nat), 0 ≤ n.val → n.val < fuel →
    ∃ r, repeatedN x n = .ok r ∧ elems fuel r = .ok (List.replicate n.val.toNat x) ∧ len r = .ok n

/-- `partition(v, n)` of a vector yields chunks of `n` elements, the last one
possibly shorter, and `length` is the number of chunks (iterators.jl:1426). -/
def PartitionVectorCorrect : Prop :=
  ∀ (xs : List Val) (n : JInt64) (fuel : Nat), 1 ≤ n.val → Fits xs → xs.length < fuel →
    ∃ p, partition (.vec .int xs) n = .ok p ∧
      elems fuel p = .ok ((chunksSpec n.val.toNat xs).map (.vec .int)) ∧
      len p = .ok (i64 ((xs.length + n.val - 1) / n.val))

/-- `Iterators.Stateful` that has produced `pos` elements: `isdone` and
`isempty` say whether elements remain, `peek` and `popfirst!` return the next
one (or the sentinel / `EOFError` when none remain), and `collect` returns the
rest (iterators.jl:1505-1627). -/
def StatefulConsistent : Prop :=
  ∀ (xs : List Val) (pos fuel : Nat) (sentinel : Val), xs.length < fuel →
    isdone0 (.stateful .int xs pos) = .ok (some (decide (xs.length ≤ pos))) ∧
    isempty fuel (.stateful .int xs pos) = .ok (decide (xs.length ≤ pos)) ∧
    (pos < xs.length →
      popfirst (.stateful .int xs pos) = .ok (xs.getD pos .undef, .stateful .int xs (pos + 1)) ∧
      peek sentinel (.stateful .int xs pos) = .ok (xs.getD pos .undef)) ∧
    (xs.length ≤ pos →
      popfirst (.stateful .int xs pos) = .error .eof ∧
      peek sentinel (.stateful .int xs pos) = .ok sentinel) ∧
    collect fuel (.stateful .int xs pos) = .ok (xs.drop pos)

/-- `only(v)` returns the element of a one-element vector and throws
`ArgumentError` otherwise (iterators.jl:1632-1633). -/
def OnlyCorrect : Prop :=
  ∀ (xs : List Val) (fuel : Nat),
    (∀ x, xs = [x] → only fuel (.vec .int xs) = .ok x) ∧
    (xs.length ≠ 1 → ∃ msg, only fuel (.vec .int xs) = .error (.jl (.argumentError msg)))

/-- `Iterators.accumulate(f, v; init)` yields the running reductions and has
`length(v)` elements (iterators.jl:612-616). -/
def AccumulateCorrect : Prop :=
  ∀ (f : Val → Val → Val) (init : Option Val) (xs : List Val) (fuel : Nat), xs.length < fuel →
    Fits xs →
    elems fuel (.accumulate f (.vec .int xs) init) = .ok (accSpec f init xs) ∧
    len (.accumulate f (.vec .int xs) init) = .ok (i64 xs.length)

/-- `Iterators.nth(v, n)` of a vector is `v[n]` for `1 ≤ n ≤ length(v)` and
throws `BoundsError` otherwise, for `n` of every integer type
(iterators.jl:1730). -/
def NthVectorCorrect : Prop :=
  ∀ (t : IntTy) (xs : List Val) (n : JInt t) (fuel : Nat), Fits xs →
    nthJ fuel (.vec .int xs) n =
      if 1 ≤ n.val ∧ n.val ≤ xs.length then .ok (xs.getD (n.val - 1).toNat .undef)
      else .error (.jl .boundsError)

/-- `first(v, n)` and `last(v, n)` of a vector return its first and last
`min(n, length(v))` elements for `n ≥ 0` of every integer type
(abstractarray.jl:481-484, 533-536). -/
def FirstLastVector : Prop :=
  ∀ (t : IntTy) (xs : List Val) (n : JInt t) (fuel : Nat), 0 ≤ n.val →
    firstN fuel (.vec .int xs) n = .ok (xs.take n.val.toNat) ∧
    lastN fuel (.vec .int xs) n = .ok (xs.drop (xs.length - n.val.toNat))

/-- `first(itr, n)` of a tuple with an `Int` count returns its first
`min(n, length)` elements (abstractarray.jl:505). -/
def FirstNTupleInt : Prop :=
  ∀ (xs : List Val) (n : JInt64) (fuel : Nat), 0 ≤ n.val → Fits xs → xs.length + 1 < fuel →
    firstN fuel (.tuple xs) n = .ok (xs.take n.val.toNat)

/-- `countfrom(s, d)` yields `s, s + d, s + 2d, ...` with `Int` wraparound
(iterators.jl:751). -/
def CountfromCorrect : Prop :=
  ∀ (s d : JInt64) (k fuel : Nat),
    prefixElems fuel (.count s d) k = .ok ((List.range k).map fun (i : Nat) => .int (s + i64 (i : Int) * d).val)

end JuliaLean.Iterators
