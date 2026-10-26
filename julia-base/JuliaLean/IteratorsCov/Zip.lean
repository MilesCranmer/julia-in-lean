import JuliaLean.IteratorsCov.Enumerate

/-!
# `Iterators.Zip` (base/iterators.jl:376-526)

A `Zip` holds a tuple of component iterators `is`. Its state is the tuple of
component states; a component that has not been started yet is iterated with
`iterate(is[k])`, modelled by the position `none` (`ss[k] = ()` in Julia).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `iterate(it, o...)`: `iterate(it)` at the start, `iterate(it, s)` later. -/
def stepOf (it : It) : Option V → Step
  | none => it.first
  | some s => it.next s

/-- `isdone(it, o...)`. -/
def doneOf (it : It) : Option V → R (Option Bool)
  | none => it.done0
  | some s => it.doneS s

/-! ## Iteration -/

/-- `_zip_isdone(is, ss)`, base/iterators.jl:496-501. -/
def zipIsdone : List (It × Option V) → R (Bool × List (Option Bool))
  | [] => .ok (false, [])
  | (it, o) :: cs => do
    let d ← doneOf it o
    let (d', ds) ← zipIsdone cs
    pure (decide (d = some true) || d', d :: ds)

/-- `_zip_all_missing(ds)`, base/iterators.jl:462-463. -/
def zipAllMissing : List (Option Bool) → Bool
  | [] => true
  | d :: ds => d.isNone && zipAllMissing ds

/-- `_zip_iterate_in_order(is, ss)`, base/iterators.jl:465-472. -/
def zipInOrder : List (It × Option V) → R (Option (List (V × V)))
  | [] => .ok (some [])
  | (it, o) :: cs => do
    match ← stepOf it o with
    | none => pure none
    | some x =>
      match ← zipInOrder cs with
      | none => pure none
      | some y => pure (some (x :: y))

/-- An entry of `_zip_iterate_unknown`: `_ZipSkip()` or an `iterate` result. -/
inductive ZX where
  | skip
  | got (p : V × V)

/-- `_zip_iterate_unknown(is, ss, ds)`, base/iterators.jl:478-485: iterate the
components whose `isdone` was `missing`. -/
def zipUnknown : List (It × Option V) → List (Option Bool) → R (Option (List ZX))
  | [], [] => .ok (some [])
  | (it, o) :: cs, d :: ds => do
    let x ← if d.isNone then
        (do match ← stepOf it o with
            | none => pure none
            | some p => pure (some (ZX.got p)))
      else pure (some ZX.skip)
    match x with
    | none => pure none
    | some x =>
      match ← zipUnknown cs ds with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _ => jthrow .boundsError

/-- `_zip_iterate_rest(is, ss, xs)`, base/iterators.jl:487-494: iterate the
skipped components. -/
def zipRest : List (It × Option V) → List ZX → R (Option (List (V × V)))
  | [], [] => .ok (some [])
  | (it, o) :: cs, x :: xs => do
    let r ← match x with
      | .skip => stepOf it o
      | .got p => pure (some p)
    match r with
    | none => pure none
    | some p =>
      match ← zipRest cs xs with
      | none => pure none
      | some y => pure (some (p :: y))
  | _, _ => jthrow .boundsError

/-- `_zip_iterate_all(is, ss)`, base/iterators.jl:448-460. -/
def zipAll (cs : List (It × Option V)) : Step :=
  match zipIsdone cs with
  | .error e => .error e
  | .ok (d, ds) =>
    if d then .ok none else
    let xs := if zipAllMissing ds then zipInOrder cs else
      match zipUnknown cs ds with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some xs1) => zipRest cs xs1
    match xs with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some xs) => .ok (some (.tup (xs.map Prod.fst), .tup (xs.map Prod.snd)))

/-- `iterate(z::Zip, ss) = _zip_iterate_all(z.is, map(tuple, ss))`, 441. -/
def zipNext (its : List It) : V → Step
  | .tup ss => if ss.length = its.length then zipAll (its.zip (ss.map some)) else jthrow .boundsError
  | _ => jthrow (.methodError "iterate")

/-- `_zip_any_isdone(is, ss)`, base/iterators.jl:433-438. -/
def zipAnyIsdone : List (It × Option V) → R (Option Bool)
  | [] => .ok (some false)
  | (it, o) :: cs => do
    let d1 ← doneOf it o
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdone cs))

/-- `isdone(z::Zip, ss) = _zip_any_isdone(z.is, map(tuple, ss))`, 431. -/
def zipDoneS (its : List It) : V → R (Option Bool)
  | .tup ss => if ss.length = its.length then zipAnyIsdone (its.zip (ss.map some)) else jthrow .boundsError
  | _ => jthrow (.methodError "isdone")

/-! ## `length`, `size`, `axes` -/

/-- `_zip_min_length(is)`, base/iterators.jl:385-394 (`nothing` is `none`). -/
def zipMinLength : List It → R (Option JInt64)
  | [] => .ok none
  | i :: is => do
    let n ← zipMinLength is
    if i.isz = .isInfinite then pure n else
    match n with
    | none => do pure (some (← i.len))
    | some n => do pure (some (jmin n (← i.len)))

/-- `length(z::Zip)`, base/iterators.jl:380-384. -/
def zipLength (its : List It) : R JInt64 := do
  match ← zipMinLength its with
  | none => jthrow (.argumentError "iterator is of undefined length")
  | some n => pure n

/-- `_zip_lengths_finite_equal(is)`, base/iterators.jl:401-411. -/
def zipLFE : List It → R (Bool × Option JInt64)
  | [] => .ok (true, none)
  | i :: is =>
    if i.isz = .isInfinite ∨ i.isz = .sizeUnknown then .ok (false, none) else do
    let m ← i.len
    let (b, n) ← zipLFE is
    pure (b && (match n with | none => true | some n => decide (n = m)), some m)

/-- `promote_shape(a::Dims, b::Dims)` (base/indices.jl:112-130): the longer
shape, provided the shorter one is a prefix of it and the extra dimensions are 1. -/
def promoteShape (a b : List JInt64) : R (List JInt64) :=
  let (a, b) := if a.length < b.length then (b, a) else (a, b)
  if a.take b.length = b ∧ ∀ d ∈ a.drop b.length, d.val = 1 then .ok a
  else .error .dimensionMismatch

/-- `_promote_tuple_shape(a, b)`, base/iterators.jl:414-416; the `OneTo` axes
method (414) is the `Integer` one on the axis lengths. -/
def pts2 : List JInt64 → List JInt64 → R (List JInt64)
  | [m], [n] => .ok [jmin m n]
  | a, b => promoteShape a b

/-- `_promote_tuple_shape(a, b...)` and `_promote_tuple_shape(a)`,
base/iterators.jl:417-418; there is no method without arguments. -/
def pts : List (List JInt64) → R (List JInt64)
  | [] => jthrow (.methodError "_promote_tuple_shape")
  | [a] => .ok a
  | a :: b :: rest => do pts2 a (← pts (b :: rest))

/-- `size(z::Zip)` (412) and, on axis lengths, `axes(z::Zip)` (413). -/
def zipSize (its : List It) : R (List JInt64) := do pts (← its.mapM (·.size))

/-! ## `nth`, `last` -/

/-- The loop of the generic `_nth(::IteratorSize, itr, n)`,
base/iterators.jl:1780-1784: `for _ in 1:n-1; y === nothing && break;
y = iterate(itr, y[2]); end`. -/
def nthLoop (nx : V → Step) : Nat → Step → Step
  | 0, y => y
  | _ + 1, .ok none => .ok none
  | k + 1, .ok (some (_, s)) => nthLoop nx k (nx s)
  | _ + 1, .error e => .error e

/-- The generic `_nth(::IteratorSize, itr, n)`, base/iterators.jl:1777-1787. -/
def nthGen (it : It) (n : Int) : R V :=
  if ¬ 0 < n then jthrow .boundsError else
  match nthLoop it.next (n - 1).toNat it.first with
  | .ok none => jthrow .boundsError
  | .ok (some (x, _)) => .ok x
  | .error e => .error e

/-- `last(z::Zip) = nth(z, length(z))` (519) with
`_nth(::IteratorSize, z::Zip, n) = map(nth(n), z.is)` (1789) and the generic
`nth` of each component. -/
def zipLast (its : List It) : R V := do
  let n ← zipLength its
  let xs ← its.mapM fun it => nthGen it n.val
  pure (.tup xs)

/-- `zip(a...) = Zip(a)` (379) with the `Zip` methods: `iterate` (440-441),
`isdone` (430-431), `length` (380), `size` (412), `eltype` (425),
`IteratorSize` and `IteratorEltype` (503-504) and `last` (519). -/
def zipIt (its : List It) : It where
  first := zipAll (its.map (·, none))
  next := zipNext its
  isz := zipTypeIsz (its.map (·.isz))
  iel := zipTypeIel (its.map (·.iel))
  elt := tupleOrBottom (its.map (·.elt))
  len := zipLength its
  size := zipSize its
  done0 := zipAnyIsdone (its.map (·, none))
  doneS := zipDoneS its
  lastv := zipLast its

/-! ## Specification -/

/-- The first `m` zipped tuples of the element lists `rs`. -/
def zipSpec : Nat → List (List V) → List V
  | 0, _ => []
  | m + 1, rs => .tup (rs.map (·.headD .nothing)) :: zipSpec m (rs.map List.tail)

/-- Component states that immediately yield the listed value-state pairs and
report \`missing\` from \`isdone\`. This is the branch where Julia's zip
implementation iterates every component in source order. -/
inductive Live : List (It × Option V) → List (V × V) → Prop
  | nil : Live [] []
  | cons {it : It} {o : Option V} {p : V × V}
      {cs : List (It × Option V)} {ps : List (V × V)} :
      doneOf it o = .ok none →
      stepOf it o = .ok (some p) →
      Live cs ps →
      Live ((it, o) :: cs) (p :: ps)

theorem zipIsdone_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) :
    zipIsdone cs = .ok (false, List.replicate ps.length (none : Option Bool)) := by
  induction h with
  | nil => rfl
  | cons hd _ _ ih => simp [zipIsdone, hd, ih]; rfl

theorem zipInOrder_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) : zipInOrder cs = .ok (some ps) := by
  induction h with
  | nil => rfl
  | cons _ hs _ ih => simp [zipInOrder, hs, ih]; rfl

theorem zipAllMissing_replicate (n : Nat) :
    zipAllMissing (List.replicate n (none : Option Bool)) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (none.isNone && zipAllMissing (List.replicate n (none : Option Bool))) = true
      rw [ih]
      rfl

/-- When every component yields immediately and reports \`missing\` from
\`isdone\`, \`_zip_iterate_all\` returns the tuple of yielded values and the
tuple of next states (base/iterators.jl:448-472). -/
theorem zipAll_live {cs : List (It × Option V)} {ps : List (V × V)}
    (h : Live cs ps) :
    zipAll cs = .ok (some (.tup (ps.map Prod.fst), .tup (ps.map Prod.snd))) := by
  simp only [zipAll, zipIsdone_live h]
  rw [zipAllMissing_replicate, zipInOrder_live h]
  rfl

/-- Every component answers \`false\` to \`isdone\`. -/
def ReadyFalse (cs : List (It × Option V)) : Prop :=
  ∀ c ∈ cs, doneOf c.1 c.2 = .ok (some false)

theorem zipAnyIsdone_false (cs : List (It × Option V)) (h : ReadyFalse cs) :
    zipAnyIsdone cs = .ok (some false) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc := h c (List.mem_cons_self ..)
      have ht : ReadyFalse cs :=
        fun c' hc' => h c' (List.mem_cons_of_mem c hc')
      simp [zipAnyIsdone, hc, ih ht, or3]
      rfl

theorem zipAnyIsdone_true (pre : List (It × Option V)) (c : It × Option V)
    (post : List (It × Option V)) (hp : ReadyFalse pre)
    (hc : doneOf c.1 c.2 = .ok (some true)) :
    zipAnyIsdone (pre ++ c :: post) = .ok (some true) := by
  induction pre with
  | nil => simp [zipAnyIsdone, hc]; rfl
  | cons a pre ih =>
      have ha := hp a (List.mem_cons_self ..)
      have ht : ReadyFalse pre :=
        fun c' hc' => hp c' (List.mem_cons_of_mem a hc')
      simp [zipAnyIsdone, ha, ih ht, or3]
      rfl

/-- The zip iteration and \`isdone\` methods agree with their source bodies:
live components are stepped in order, all-false answers remain false, and the
first true answer stops the \`isdone\` scan (base/iterators.jl:430-501). -/
def ZipProtocol : Prop :=
  (∀ (cs : List (It × Option V)) (ps : List (V × V)), Live cs ps →
    zipAll cs = .ok (some (.tup (ps.map Prod.fst), .tup (ps.map Prod.snd)))) ∧
  (∀ cs, ReadyFalse cs → zipAnyIsdone cs = .ok (some false)) ∧
  (∀ pre c post, ReadyFalse pre → doneOf c.1 c.2 = .ok (some true) →
    zipAnyIsdone (pre ++ c :: post) = .ok (some true))

theorem zipProtocol : ZipProtocol :=
  ⟨fun _ _ => zipAll_live, zipAnyIsdone_false, zipAnyIsdone_true⟩

/-! ## Metadata and helper equations -/

/-- The remaining Zip helpers expose the shortest finite length, equal finite
length test, promoted size/axes, tuple eltype, last value and wrapper fields
exactly as `base/iterators.jl:380-425,503-521` specify. -/
def ZipMetadata : Prop :=
  (∀ its, zipLength its = do
    match ← zipMinLength its with
    | none => jthrow (.argumentError "iterator is of undefined length")
    | some n => pure n) ∧
  (zipMinLength [] = .ok none) ∧
  (∀ i is, zipMinLength (i :: is) = do
    let n ← zipMinLength is
    if i.isz = .isInfinite then pure n else
    match n with
    | none => do pure (some (← i.len))
    | some n => do pure (some (jmin n (← i.len)))) ∧
  (zipLFE [] = .ok (true, none)) ∧
  (∀ i is, zipLFE (i :: is) =
    if i.isz = .isInfinite ∨ i.isz = .sizeUnknown then .ok (false, none) else do
    let m ← i.len
    let (b, n) ← zipLFE is
    pure (b && (match n with | none => true | some n => decide (n = m)), some m)) ∧
  (∀ its, zipSize its = do pts (← its.mapM (·.size))) ∧
  (∀ m n, pts2 [m] [n] = .ok [jmin m n]) ∧
  (∀ a, pts [a] = .ok a) ∧
  (∀ its, (zipIt its).isz = zipTypeIsz (its.map (·.isz)) ∧
    (zipIt its).iel = zipTypeIel (its.map (·.iel)) ∧
    (zipIt its).elt = tupleOrBottom (its.map (·.elt)) ∧
    (zipIt its).len = zipLength its ∧ (zipIt its).size = zipSize its ∧
    (zipIt its).lastv = zipLast its) ∧
  (∀ its, zipLast its = do
    let n ← zipLength its
    let xs ← its.mapM fun it => nthGen it n.val
    pure (.tup xs))

theorem zipMetadata : ZipMetadata := by
  refine ⟨fun _ => rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ => rfl⟩

end JuliaLean.IteratorsCov
