import JuliaLean.Iterators.Funs

/-!
# Refuted properties of `base/iterators.jl`

Each property states what the documentation or an obvious invariant promises;
each refutation evaluates the model on the counterexample that
`repro/iterators-*.jl` runs in Julia.
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- A `Vector{Int64}`. -/
def vecI (xs : List Int) : Itr := .vec .int (xs.map Val.int)

/-- The values of a list of `Int64`s. -/
def ints (xs : List Int) : List Val := xs.map Val.int

/-- `UnitRange{Int64}` `1:l`. -/
def oneTo (l : JInt64) : Itr := .urange .unit (i64 1) l 0

/-- Product of a list of integers. -/
def prodInts : List Int → Int
  | [] => 1
  | x :: xs => x * prodInts xs

/-- The first `k` elements an iterator yields (fewer if it ends). -/
def prefixElems (fuel : Nat) (it : Itr) (k : Nat) : M (List Val) := do
  runPrefix (fun s => iter fuel it (some s)) k (← iter fuel it none)
where
  runPrefix (step : St → M (Option (Val × St))) : Nat → Option (Val × St) → M (List Val)
    | _, none => pure []
    | 0, some _ => pure []
    | j + 1, some (x, s) => do pure (x :: (← runPrefix step j (← step s)))

/-! ## `isempty(take(itr, 0))` -/

/-- `isempty(take(itr, n))` holds exactly when `take(itr, n)` yields nothing,
for `itr` a vector or an `Iterators.Stateful` of a vector. -/
def TakeIsemptyCorrect : Prop :=
  ∀ (xs : List Int) (pos : Nat) (n : JInt64) (fuel : Nat) (t : Itr) (b : Bool),
    0 ≤ n.val → (take (.stateful .int (ints xs) pos) n = .ok t ∨ take (vecI xs) n = .ok t) →
    isempty fuel t = .ok b → (b = true ↔ iter fuel t none = .ok none)

theorem takeIsemptyCorrect_refuted : ¬ TakeIsemptyCorrect := by
  intro h
  have := h [1] 0 (i64 0) 1 (.take (.stateful .int (ints [1]) 0) (i64 0)) false (by decide)
    (Or.inl rfl) rfl
  exact absurd (this.mpr rfl) (by decide)

/-! ## `isempty` of the rest returned by `peel` -/

/-- For `(x, r) = Iterators.peel(itr)`, `isempty(r)` holds exactly when `r`
yields nothing. -/
def PeelRestIsempty : Prop :=
  ∀ (it : Itr) (fuel : Nat) (x : Val) (r : Itr) (b : Bool),
    peel fuel it = .ok (some (x, r)) → isempty fuel r = .ok b →
    (b = true ↔ iter fuel r none = .ok none)

/-- `Iterators.take(Iterators.Stateful([1, 2, 3]), 1)`. -/
def takeStateful1 : Itr := .take (.stateful .int (ints [1, 2, 3]) 0) (i64 1)

theorem peelRestIsempty_refuted : ¬ PeelRestIsempty := by
  intro h
  have := h takeStateful1 1 (.int 1) (.rest takeStateful1 (.tup [.int 0, .nat 1])) false rfl rfl
  exact absurd (this.mpr rfl) (by decide)

/-! ## `drop(drop(itr, a), b)` -/

/-- `drop(drop(v, a), b)` of a vector succeeds and yields all but the first
`a + b` elements, for any `a, b ≥ 0`. -/
def DropDropCorrect : Prop :=
  ∀ (xs : List Int) (a b : JInt64), 0 ≤ a.val → 0 ≤ b.val →
    ∃ d, (do drop (← drop (vecI xs) a) b) = .ok d ∧
      ∀ fuel, xs.length < fuel → elems fuel d = .ok (ints (xs.drop (a.val + b.val).toNat))

theorem dropDropCorrect_refuted : ¬ DropDropCorrect := by
  intro h
  obtain ⟨d, hd, _⟩ := h [1, 2, 3] (JInt.typemax .i64) (i64 1) (by decide) (by decide)
  have e : (do drop (← drop (vecI [1, 2, 3]) (JInt.typemax .i64)) (i64 1)) =
      (.error (.jl (.argumentError "Drop length must be non-negative")) : M Itr) := rfl
  rw [e] at hd
  cases hd

/-! ## `nth(cycle(v, m), k)` -/

/-- `Iterators.nth(Iterators.cycle(v, m), k)` is `v[mod1(k, length(v))]` for
every `1 ≤ k ≤ length(v) * m`. -/
def NthCycleCorrect : Prop :=
  ∀ (xs : List Int) (m k : JInt64) (fuel : Nat) (c : Itr),
    cycleN (.vec .int (ints xs)) m = .ok c → 1 ≤ k.val → k.val ≤ xs.length * m.val →
    nthJ fuel c k = .ok (.int (xs.getD ((k.val - 1) % xs.length).toNat 0))

theorem nthCycleCorrect_refuted : ¬ NthCycleCorrect := by
  intro h
  have := h [1, 2, 3] (i64 (2 ^ 62)) (i64 1) 1
    (.flatten (.take (.repeated (.vec .int (ints [1, 2, 3]))) (i64 (2 ^ 62)))) rfl
    (by decide) (by decide)
  have e : nthJ 1 (.flatten (.take (.repeated (.vec .int (ints [1, 2, 3]))) (i64 (2 ^ 62))))
      (i64 1) = .error (.jl .boundsError) := rfl
  rw [e] at this
  cases this

/-! ## `nth(zip(), n)` for `n ≤ 0` -/

/-- `Iterators.nth(zip(vs...), n)` throws `BoundsError` for `n ≤ 0`. -/
def NthZipNonpositive : Prop :=
  ∀ (vs : List (List Int)) (n : JInt64) (fuel : Nat), n.val ≤ 0 →
    nthJ fuel (.zip (vs.map vecI)) n = .error (.jl .boundsError)

theorem nthZipNonpositive_refuted : ¬ NthZipNonpositive := by
  intro h
  have := h [] (i64 0) 1 (by decide)
  have e : nthJ 1 (.zip (([] : List (List Int)).map vecI)) (i64 0) = .ok (.tup []) := rfl
  rw [e] at this
  cases this

/-! ## `nth(A, n)` with an unsigned `n` -/

/-- `Iterators.nth(A, n)` for `A = Base.IdentityUnitRange(fi:li)` returns the
`n`-th element `fi + n - 1` for every in-range `n` of every integer type. -/
def NthAnyIntegerType : Prop :=
  ∀ (t : IntTy) (fi li : JInt64) (n : JInt t) (fuel : Nat),
    1 ≤ n.val → n.val ≤ li.val - fi.val + 1 →
    nthJ fuel (.urange .identity fi li 0) n = .ok (.int (fi.val + n.val - 1))

theorem nthAnyIntegerType_refuted : ¬ NthAnyIntegerType := by
  intro h
  have := h .u64 (i64 (-5)) (i64 (-3)) (JInt.lit .u64 1) 1 (by decide) (by decide)
  have e : nthJ 1 (.urange .identity (i64 (-5)) (i64 (-3)) 0) (JInt.lit .u64 1) =
      .error (.jl .boundsError) := rfl
  rw [e] at this
  cases this

/-! ## `length(product(...))` -/

/-- `length(product(1:l₁, ..., 1:lₖ))` is `l₁ ⋯ lₖ` whenever that count fits
in an `Int`. -/
def ProductLengthExact : Prop :=
  ∀ (ls : List JInt64), (∀ l ∈ ls, 0 ≤ l.val) → prodInts (ls.map (·.val)) ≤ maxIntVal →
    len (.product (ls.map oneTo)) = .ok (i64 (prodInts (ls.map (·.val))))

theorem productLengthExact_refuted : ¬ ProductLengthExact := by
  intro h
  have := h [i64 (2 ^ 32), i64 (2 ^ 32), i64 0] (by decide) (by decide)
  have e : len (.product ([i64 (2 ^ 32), i64 (2 ^ 32), i64 0].map oneTo)) =
      .error (.jl (.overflowError "")) := rfl
  rw [e] at this
  cases this

/-! ## `last(product(...))` of an empty product -/

/-- `last(product(1:l₁, ..., 1:lₖ))` returns only when the product is
nonempty. -/
def ProductLastNonempty : Prop :=
  ∀ (ls : List JInt64) (v : Val), lastOf (.product (ls.map oneTo)) = .ok v →
    ∀ l ∈ ls, 1 ≤ l.val

theorem productLastNonempty_refuted : ¬ ProductLastNonempty := by
  intro h
  have := h [i64 2, i64 0] (.tup [.int 2, .int 0]) rfl (i64 0) (.tail _ (.head _))
  exact absurd this (by decide)

/-! ## `first(cycle(v), n)` -/

/-- The first `n` elements of the infinite repetition of `xs` (none if `xs` is
empty). -/
def cycleList (xs : List Val) (n : Nat) : List Val :=
  (List.range n).filterMap fun i => xs[i % xs.length]?

/-- `first(Iterators.cycle(v), n)` (`collect(take(cycle(v), n))`) returns the
first `n` elements of the repetition of `v`; it is empty when `v` is. -/
def CycleFirstN : Prop :=
  ∀ (xs : List Int) (n : JInt64) (fuel : Nat) (ys : List Val), 0 ≤ n.val →
    firstN fuel (.cycle (vecI xs)) n = .ok ys → ys = cycleList (ints xs) n.val.toNat

theorem cycleFirstN_refuted : ¬ CycleFirstN := by
  intro h
  have := h [] (i64 3) 10 [.undef, .undef, .undef] (by decide) rfl
  have e : cycleList (ints []) (i64 3).val.toNat = [] := rfl
  rw [e] at this
  cases this

/-! ## `partition` of a unit range near `typemax` -/

/-- The chunks `fi:fi+n-1, fi+n:fi+2n-1, ...` of `fi:li` as value ranges. -/
def specChunks (fi li n : Int) : List Val :=
  (List.range ((li - fi + n) / n).toNat).map fun (i : Nat) =>
    .rng (fi + (i : Int) * n) (min (fi + ((i : Int) + 1) * n - 1) li)

/-- `partition(r, n)` of `r = Base.IdentityUnitRange(fi:li)` yields the chunks
of `n` consecutive elements of `r`, the last one possibly shorter. -/
def PartitionRangeChunks : Prop :=
  ∀ (fi li n : JInt64) (k fuel : Nat) (p : Itr) (cs : List Val),
    fi.val ≤ li.val → 1 ≤ n.val → partition (.urange .identity fi li 0) n = .ok p →
    prefixElems fuel p k = .ok cs → cs = (specChunks fi.val li.val n.val).take k

/-- `Base.IdentityUnitRange(typemax(Int)-2:typemax(Int))`. -/
def topRange : Itr := .urange .identity (i64 (2 ^ 63 - 3)) (i64 (2 ^ 63 - 1)) 0

theorem partitionRangeChunks_refuted : ¬ PartitionRangeChunks := by
  intro h
  have := h (i64 (2 ^ 63 - 3)) (i64 (2 ^ 63 - 1)) (i64 2) 2 5 (.partition topRange (i64 2))
    [.rng (2 ^ 63 - 3) (2 ^ 63 - 2), .rng (2 ^ 63 - 1) (2 ^ 63 - 2)] (by decide) (by decide) rfl rfl
  have e : (specChunks (i64 (2 ^ 63 - 3)).val (i64 (2 ^ 63 - 1)).val (i64 2).val).take 2 =
      [.rng (2 ^ 63 - 3) (2 ^ 63 - 2), .rng (2 ^ 63 - 1) (2 ^ 63 - 1)] := rfl
  rw [e] at this
  have t := congrArg (fun l : List Val => match l with | [_, .rng _ hi] => hi | _ => 0) this
  exact absurd t (by decide)

/-- `collect(partition(topRange, 2))` stores past the end of its result array
(the Julia segmentation fault). -/
theorem partition_topRange_collect_oob :
    collect 10 (.partition topRange (i64 2)) = .error .oob := rfl

/-! ## `partition` of a non-array iterator with a large `n` -/

/-- The first chunk of `partition(itr, n)` for a nonempty tuple `itr` holds
its first `min(n, length(itr))` elements. -/
def PartitionFirstChunk : Prop :=
  ∀ (xs : List Int) (n : JInt64) (fuel : Nat) (p : Itr), xs ≠ [] → 1 ≤ n.val →
    xs.length < fuel → partition (.tuple (ints xs)) n = .ok p →
    ∃ s, iter fuel p none = .ok (some (.vec .int (ints (xs.take n.val.toNat)), s))

theorem partitionFirstChunk_refuted : ¬ PartitionFirstChunk := by
  intro h
  obtain ⟨s, hs⟩ := h [1, 2, 3] (JInt.typemax .i64) 5 (.partition (.tuple (ints [1, 2, 3]))
    (JInt.typemax .i64)) (by decide) (by decide) (by decide) rfl
  have e : iter 5 (.partition (.tuple (ints [1, 2, 3])) (JInt.typemax .i64)) none =
      .error (.jl (.argumentError "invalid GenericMemory size")) := rfl
  rw [e] at hs
  cases hs

/-! ## `first(itr, n)` for counts beyond `typemax(Int)` -/

/-- `first(itr, n)` returns the first `min(n, length(itr))` elements for a
nonnegative `n` of any integer type. -/
def FirstNAnyInteger : Prop :=
  ∀ (t : IntTy) (xs : List Int) (n : JInt t) (fuel : Nat), 0 ≤ n.val → xs.length + 1 < fuel →
    firstN fuel (.tuple (ints xs)) n = .ok (ints (xs.take n.val.toNat))

theorem firstNAnyInteger_refuted : ¬ FirstNAnyInteger := by
  intro h
  have := h .u64 [1, 2, 3] (JInt.typemax .u64) 10 (by decide) (by decide)
  have e : firstN 10 (.tuple (ints [1, 2, 3])) (JInt.typemax .u64) =
      .error (.jl (.inexactError "Int64")) := rfl
  rw [e] at this
  cases this

/-! ## `product` of a single exhausted stateful iterator -/

/-- `product(itr)` yields the 1-tuples of the elements of `itr`, for `itr` a
vector or an `Iterators.Stateful` of a vector. -/
def ProductOneFactor : Prop :=
  ∀ (xs : List Int) (fuel : Nat), xs.length + 1 < fuel →
    elems fuel (.product [.stateful .int (ints xs) 0]) = .ok ((ints xs).map fun y => .tup [y]) ∧
    elems fuel (.product [vecI xs]) = .ok ((ints xs).map fun y => .tup [y])

theorem productOneFactor_refuted : ¬ ProductOneFactor := by
  intro h
  have := (h [1] 5 (by decide)).1
  have e : elems 5 (.product [.stateful .int (ints [1]) 0]) =
      .error (.jl (.argumentError "tuple must be non-empty")) := rfl
  rw [e] at this
  cases this

end JuliaLean.Iterators
