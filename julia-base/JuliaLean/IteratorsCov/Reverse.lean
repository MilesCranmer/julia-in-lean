import JuliaLean.IteratorsCov.TakeDrop

/-!
# `Iterators.reverse` and `Iterators.Reverse` (base/iterators.jl:81-162)

`Iterators.reverse` dispatches on the type of its argument, so its argument
is a small deep embedding `Obj` of the Julia objects it has methods for:
numbers and characters, pairs, unit ranges `lo:hi`, descending ranges
`hi:-1:lo`, vectors, tuples, `Iterators.Reverse` objects and generators.
`Obj.it` is the object's iterator: `iterate` of numbers (base/number.jl:329-330),
pairs (base/pair.jl:41), ranges (base/range.jl:935-942), vectors and tuples
(`Leaves`), the `iterate` methods of `Reverse` (base/iterators.jl:136-162) and
of `Generator` (base/generator.jl:44-50).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Julia objects `Iterators.reverse` dispatches on. `urange lo hi` is the
`UnitRange` `lo:hi` (normalised: `hi ≥ lo - 1`); `drange hi lo` is the
`StepRange` `hi:-1:lo` (empty when `hi < lo`); `rev o` is
`Iterators.Reverse(o)`; `gen f o` is `Base.Generator(f, o)`. -/
inductive Obj where
  | num (v : V)
  | pair (a b : V)
  | urange (lo hi : JInt64)
  | drange (hi lo : JInt64)
  | vec (xs : List V)
  | tup (xs : List V)
  | rev (o : Obj)
  | gen (f : V → V) (o : Obj)

/-! ## Leaf iterators -/

/-- `iterate(r::OrdinalRange, i)` for `lo:hi`: `i == last(r) && return nothing`,
then `i + 1`. -/
def urNext (hi : JInt64) : V → Step
  | .int i => if i = hi.val then .ok none else
    let nx := (i64 i + i64 1).val
    .ok (some (.int nx, .int nx))
  | _ => jthrow (.methodError "iterate")

/-- `iterate(r::OrdinalRange)` for `lo:hi`: `isempty(r) ? nothing : (first(r), first(r))`. -/
def urFirst (lo hi : JInt64) : Step :=
  if hi < lo then .ok none else .ok (some (.int lo.val, .int lo.val))

/-- `iterate(r, i)` for `hi:-1:lo`: `i == last(r)` ends, else `i - 1`. -/
def drNext (lo : JInt64) : V → Step
  | .int i => if i = lo.val then .ok none else
    let nx := (i64 i - i64 1).val
    .ok (some (.int nx, .int nx))
  | _ => jthrow (.methodError "iterate")

def drFirst (hi lo : JInt64) : Step :=
  if hi < lo then .ok none else .ok (some (.int hi.val, .int hi.val))

/- Unfolding these during unification decides `hi < lo` on `Int64` literals,
which evaluates wraparound by well-founded recursion; the proofs unfold them
explicitly. -/
attribute [local irreducible] urFirst drFirst

/-- `iterate(p::Pair, i=1) = i > 2 ? nothing : (getfield(p, i), i + 1)`. -/
def pairNext (a b : V) : V → Step
  | .int i => if i > 2 then .ok none else
    if i = 1 then .ok (some (a, .int 2)) else if i = 2 then .ok (some (b, .int 3))
    else jthrow .boundsError
  | _ => jthrow (.methodError "iterate")

/-- `Generator` iteration, base/generator.jl:44-50: `y = iterate(g.iter, s...)`,
`nothing` stays `nothing`, otherwise `(g.f(y[1]), y[2])`. -/
def genCont (f : V → V) : Step → Step
  | .ok (some (x, s)) => .ok (some (f x, s))
  | y => y

/-- The step of `iterate(A::Reverse{<:AbstractArray}, state)` and of the generic
`iterate(A::Reverse, state)` (base/iterators.jl:136-150), whose bodies are
identical: `y = iterate(state...)` on the reversed index range `r`, then
`(A.itr[idx], (state[1], itrs))`. -/
def revArrCont (get : V → R V) (r : V) : Step → Step
  | .ok none => .ok none
  | .ok (some (idx, itrs)) => do
    let v ← get idx
    pure (some (v, .tup [r, itrs]))
  | .error e => .error e

/-- `iterate(r::Reverse{<:Union{Tuple, NamedTuple}}, i::Int = length(r.itr)) =
i < 1 ? nothing : (r.itr[i], i-1)`, base/iterators.jl:162. -/
def revTupStep (xs : List V) (i : Int) : Step :=
  if i < 1 then .ok none else
  if i ≤ xs.length then .ok (some (getIdx xs i, .int (i - 1))) else jthrow .boundsError

def revTupNext (xs : List V) : V → Step
  | .int i => revTupStep xs i
  | _ => jthrow (.methodError "iterate")

/-- `iterate(r::Reverse{Union{}})` and `iterate(r::Reverse{Union{}}, state)`,
base/iterators.jl:153-154. -/
def revBottomIt : It where
  first := jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}")
  next := fun _ => jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}")

/-- The reversed index range `reverse(eachindex(A))` of an array with `n`
elements, `n:-1:1`, as the value carried in the state. -/
def revIdxObj (n : Nat) : V := .tup [.int n, .int (-1), .int 1]

/-- `A[i]` of a unit range, descending range or vector (`BoundsError` outside). -/
def arrGet (len : Nat) (g : Int → V) (i : V) : R V :=
  match i with
  | .int i => if 1 ≤ i ∧ i ≤ len then .ok (g i) else jthrow .boundsError
  | _ => jthrow (.methodError "getindex")

/-- Number of elements of `lo:hi`. -/
def urLen (lo hi : JInt64) : Nat := (hi.val - lo.val + 1).toNat

/-- `first(itr)` (base/abstractarray.jl:474-478) from `iterate(itr)`. -/
def firstOf (y : Step) : R V :=
  y.bind fun
    | some (x, _) => .ok x
    | none => jthrow (.argumentError "collection must be non-empty")

/-- `iterate(A::Reverse, state)` on a state `(r, itrs)`: the index iterator's
`iterate(r, itrs)` is `ix itrs`. -/
def revArrNext (get : V → R V) (ix : V → Step) : V → Step
  | .tup [r, itrs] => revArrCont get r (ix itrs)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.Reverse(A)` of an array with `n` elements and `A[i] = g i`:
`eltype`, `length`, `size`, `IteratorSize`, `IteratorEltype` of the wrapped
type (base/iterators.jl:128-132), `last(r) = first(r.itr)` (133) and the
`iterate` methods (136-150). -/
def revArrIt (inner : It) (n : Nat) (N : JInt64) (g : Int → V) : It where
  first := revArrCont (arrGet n g) (revIdxObj n) (drFirst N (i64 1))
  next := revArrNext (arrGet n g) (drNext (i64 1))
  isz := inner.isz
  iel := inner.iel
  elt := inner.elt
  len := inner.len
  size := inner.size
  lastv := firstOf inner.first

/-- A number (or character) as an iterator, base/number.jl:329-330. -/
def numIt (v : V) : It :=
  { first := .ok (some (v, .nothing)), next := fun _ => .ok none,
    isz := .hasShape 0, len := .ok (i64 1), size := .ok [], lastv := .ok v }

/-- A pair as an iterator, base/pair.jl:41. -/
def pairIt (a b : V) : It :=
  { first := pairNext a b (.int 1), next := pairNext a b, len := .ok (i64 2), lastv := .ok b }

/-- `lo:hi` as an iterator. -/
def urIt (lo hi : JInt64) : It :=
  { first := urFirst lo hi, next := urNext hi, isz := .hasShape 1, elt := .int,
    len := .ok (hi - lo + i64 1), size := .ok [hi - lo + i64 1], lastv := .ok (.int hi.val) }

/-- `hi:-1:lo` as an iterator. -/
def drIt (hi lo : JInt64) : It :=
  { first := drFirst hi lo, next := drNext lo, isz := .hasShape 1, elt := .int,
    len := .ok (hi - lo + i64 1), size := .ok [hi - lo + i64 1], lastv := .ok (.int lo.val) }

/-- A vector with `last(A) = A[end]`. -/
def vecObjIt (xs : List V) : It :=
  { vecIt .any xs with lastv := match xs.getLast? with
    | some x => .ok x
    | none => jthrow .boundsError }

/-- A tuple with `last(t) = t[end]`. -/
def tupObjIt (xs : List V) : It :=
  { tupIt [] xs with elt := .any, lastv := match xs.getLast? with
    | some x => .ok x
    | none => jthrow .boundsError }

/-- `Iterators.Reverse(t)` of a tuple: the wrapped type's traits, `last(r) =
first(r.itr)` and the tuple `iterate` method (base/iterators.jl:128-133, 162). -/
def revTupIt (xs : List V) : It :=
  let i := tupObjIt xs
  { first := revTupStep xs xs.length, next := revTupNext xs, isz := i.isz, iel := i.iel,
    elt := i.elt, len := i.len, size := i.size, lastv := firstOf i.first }

/-- The iterator of `Iterators.Reverse(o)`: the array methods for arrays, the
tuple method for tuples; any other wrapped object has no `eachindex`. -/
def revItOf : Obj → It
  | .vec xs => revArrIt (vecObjIt xs) xs.length (i64 xs.length) (fun i => getIdx xs i)
  | .urange lo hi => revArrIt (urIt lo hi) (urLen lo hi) (i64 (urLen lo hi)) (fun i => .int (lo.val + i - 1))
  | .drange hi lo => revArrIt (drIt hi lo) (urLen lo hi) (i64 (urLen lo hi)) (fun i => .int (hi.val - i + 1))
  | .tup xs => revTupIt xs
  | _ => { first := jthrow (.methodError "eachindex"), next := fun _ => jthrow (.methodError "iterate") }

/-- The iterator of an object. -/
def Obj.it : Obj → It
  | .num v => numIt v
  | .pair a b => pairIt a b
  | .urange lo hi => urIt lo hi
  | .drange hi lo => drIt hi lo
  | .vec xs => vecObjIt xs
  | .tup xs => tupObjIt xs
  | .rev o => revItOf o
  | .gen f o =>
    let i := o.it
    { first := genCont f i.first, next := fun s => genCont f (i.next s),
      isz := i.isz, iel := false, len := i.len, size := i.size, done0 := i.done0,
      doneS := i.doneS, lastv := i.lastv.map f }

/-- `Iterators.reverse(itr)`, base/iterators.jl:113, 156-160. -/
def itReverse : Obj → Obj
  | .urange lo hi => .drange hi lo        -- 156: Base.reverse(R) is hi:-1:lo
  | .drange hi lo => .urange lo hi        -- 156: Base.reverse(hi:-1:lo) is lo:1:hi
  | .gen f o => .gen f (itReverse o)      -- 157
  | .rev o => o                           -- 158
  | .num v => .num v                      -- 159
  | .pair a b => .pair b a                -- 160: Base.reverse(p::Pair) = p.second => p.first
  | o => .rev o                           -- 113

/-! ## Specification -/

/-- The values `lo, lo+1, ..., hi`. -/
def urVals (lo hi : JInt64) : List V := (List.range (urLen lo hi)).map fun (j : Nat) => .int (lo.val + j)

/-- The values `hi, hi-1, ..., lo`. -/
def drVals (hi lo : JInt64) : List V := (List.range (urLen lo hi)).map fun (j : Nat) => .int (hi.val - j)

/-- What iterating an object yields. -/
def Obj.elems : Obj → List V
  | .num v => [v]
  | .pair a b => [a, b]
  | .urange lo hi => urVals lo hi
  | .drange hi lo => drVals hi lo
  | .vec xs => xs
  | .tup xs => xs
  | .rev o => o.elems.reverse
  | .gen f o => o.elems.map f

/-- Arrays and tuples: the objects with `eachindex` and `getindex`. -/
def Obj.ArrayLike : Obj → Prop
  | .urange _ _ | .drange _ _ | .vec _ | .tup _ => True
  | _ => False

/-- Objects whose iteration the model covers: ranges are normalised, the
wrapped object of a `Reverse` is an array or tuple, and sizes fit in an `Int`. -/
def Obj.WF : Obj → Prop
  | .num _ | .pair _ _ => True
  | .urange lo hi => lo.val - 1 ≤ hi.val ∧ hi.val < 2 ^ 61 ∧ -(2 ^ 61) < lo.val
  | .drange hi lo => lo.val - 1 ≤ hi.val ∧ hi.val < 2 ^ 61 ∧ -(2 ^ 61) < lo.val
  | .vec xs | .tup xs => Fits xs
  | .rev o => o.ArrayLike ∧ o.WF
  | .gen _ o => o.WF

/-! ## Lemmas -/

theorem ur_YF (hi : JInt64) (hhi : hi.val < 2 ^ 62) : ∀ (k : Nat) (v : Int), hi.val - v = k →
    -(2 ^ 62) < v → YF (urNext hi) (.ok (some (.int v, .int v)))
      ((List.range (k + 1)).map fun (j : Nat) => .int (v + j)) := by
  intro k
  induction k with
  | zero =>
    intro v hv _
    have : v = hi.val := by omega
    rw [show (List.range (0 + 1)).map (fun (j : Nat) => V.int (v + j)) = [V.int v] by simp]
    refine .cons ?_
    show YF _ (if v = hi.val then _ else _) _
    rw [if_pos this]; exact .nil
  | succ k ih =>
    intro v hv hv0
    have e : (List.range (k + 1 + 1)).map (fun j : Nat => V.int (v + j)) =
        .int v :: (List.range (k + 1)).map fun j : Nat => V.int (v + 1 + j) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      rw [List.cons.injEq]
      refine ⟨by simp, ?_⟩
      apply List.map_congr_left
      intro j _
      try simp only [Function.comp]
      congr 1; omega
    rw [e]
    refine .cons ?_
    show YF _ (if v = hi.val then .ok none else
      .ok (some (.int (i64 v + i64 1).val, .int (i64 v + i64 1).val))) _
    rw [if_neg (by omega), i64_succ (k := v) (by omega) (by omega)]
    exact ih (v + 1) (by omega) (by omega)

theorem dr_YF (lo : JInt64) (hlo : -(2 ^ 62) < lo.val) : ∀ (k : Nat) (v : Int), v - lo.val = k →
    v < 2 ^ 62 → YF (drNext lo) (.ok (some (.int v, .int v)))
      ((List.range (k + 1)).map fun (j : Nat) => .int (v - j)) := by
  intro k
  induction k with
  | zero =>
    intro v hv _
    have : v = lo.val := by omega
    rw [show (List.range (0 + 1)).map (fun (j : Nat) => V.int (v - j)) = [V.int v] by simp]
    refine .cons ?_
    show YF _ (if v = lo.val then _ else _) _
    rw [if_pos this]; exact .nil
  | succ k ih =>
    intro v hv hv0
    have e : (List.range (k + 1 + 1)).map (fun j : Nat => V.int (v - j)) =
        .int v :: (List.range (k + 1)).map fun j : Nat => V.int (v - 1 - j) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      rw [List.cons.injEq]
      refine ⟨by simp, ?_⟩
      apply List.map_congr_left
      intro j _
      try simp only [Function.comp]
      congr 1; omega
    rw [e]
    refine .cons ?_
    show YF _ (if v = lo.val then .ok none else
      .ok (some (.int (i64 v - i64 1).val, .int (i64 v - i64 1).val))) _
    rw [if_neg (by omega), i64_pred (k := v)
      (by show -(2 ^ 63 : Int) < v; omega) (by omega)]
    exact ih (v - 1) (by omega) (by omega)

theorem urLen_eq (lo hi : JInt64) (h : lo.val - 1 ≤ hi.val) : (urLen lo hi : Int) = hi.val - lo.val + 1 := by
  unfold urLen; omega

theorem urIt_yields (lo hi : JInt64) (h : lo.val - 1 ≤ hi.val ∧ hi.val < 2 ^ 62 ∧ -(2 ^ 62) < lo.val) :
    (urIt lo hi).Yields (urVals lo hi) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold It.Yields urVals
  show YF (urNext hi) (urFirst lo hi) _
  unfold urFirst
  by_cases he : hi < lo
  · rw [if_pos he]
    have : urLen lo hi = 0 := by unfold urLen; change hi.val < lo.val at he; omega
    rw [this]; exact .nil
  · rw [if_neg he]
    change ¬ hi.val < lo.val at he
    have hl : urLen lo hi = (hi.val - lo.val).toNat + 1 := by unfold urLen; omega
    rw [hl]
    exact ur_YF hi h2 _ lo.val (by omega) h3

theorem drIt_yields (hi lo : JInt64) (h : lo.val - 1 ≤ hi.val ∧ hi.val < 2 ^ 62 ∧ -(2 ^ 62) < lo.val) :
    (drIt hi lo).Yields (drVals hi lo) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold It.Yields drVals
  show YF (drNext lo) (drFirst hi lo) _
  unfold drFirst
  by_cases he : hi < lo
  · rw [if_pos he]
    have : urLen lo hi = 0 := by unfold urLen; change hi.val < lo.val at he; omega
    rw [this]; exact .nil
  · rw [if_neg he]
    change ¬ hi.val < lo.val at he
    have hl : urLen lo hi = (hi.val - lo.val).toNat + 1 := by unfold urLen; omega
    rw [hl]
    exact dr_YF lo h3 _ hi.val (by omega) h2

theorem genCont_YF (f : V → V) (nx : V → Step) {y : Step} {xs : List V} (h : YF nx y xs) :
    YF (fun s => genCont f (nx s)) (genCont f y) (xs.map f) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem revArr_YF (get : V → R V) (g : V → V) (ix : V → Step) (r : V) {y : Step} {ks : List V}
    (h : YF ix y ks) (hg : ∀ k ∈ ks, get k = .ok (g k)) :
    YF (revArrNext get ix) (revArrCont get r y) (ks.map g) := by
  induction h with
  | nil => exact .nil
  | @cons k s ks _ ih =>
    show YF _ (do let v ← get k; pure (some (v, .tup [r, s]))) _
    rw [hg k (List.mem_cons_self ..)]
    exact .cons (ih (fun k hk => hg k (List.mem_cons_of_mem _ hk)))

theorem revTup_YF (xs : List V) : ∀ (i : Nat), i ≤ xs.length →
    YF (revTupNext xs) (revTupStep xs i) ((xs.take i).reverse) := by
  intro i
  induction i with
  | zero => intro _; simp [revTupStep]; exact .nil
  | succ i ih =>
    intro hi
    unfold revTupStep
    rw [if_neg (by omega), if_pos (by omega)]
    have e : (xs.take (i + 1)).reverse = getIdx xs ((i + 1 : Nat) : Int) :: (xs.take i).reverse := by
      rw [List.take_succ, List.reverse_append]
      have hlt : i < xs.length := by omega
      simp [List.getElem?_eq_getElem hlt, getIdx, List.getD_eq_getElem?_getD]
    rw [e]
    refine .cons ?_
    have : ((i + 1 : Nat) : Int) - 1 = (i : Int) := by omega
    rw [this]
    exact ih (by omega)

theorem map_range_rev_eq (xs : List V) :
    (List.range xs.length).map (fun j : Nat => getIdx xs ((xs.length : Int) - j)) = xs.reverse := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, getIdx]
    simp at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1; omega

theorem ur_rev_eq (lo hi : JInt64) (n : Nat) (hn : n = urLen lo hi) :
    (List.range n).map (fun j : Nat => V.int (lo.val + ((n : Int) - j) - 1)) = (urVals lo hi).reverse := by
  subst hn
  apply List.ext_getElem
  · simp [urVals]
  · intro j h1 h2
    simp only [urVals, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    simp [urVals] at h1
    congr 1; push_cast; omega

theorem dr_rev_eq (lo hi : JInt64) (n : Nat) (hn : n = urLen lo hi) :
    (List.range n).map (fun j : Nat => V.int (hi.val - ((n : Int) - j) + 1)) = (drVals hi lo).reverse := by
  subst hn
  apply List.ext_getElem
  · simp [drVals]
  · intro j h1 h2
    simp only [drVals, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    simp [drVals] at h1
    congr 1; push_cast; omega

theorem dr_vals_eq (lo hi : JInt64) (h : lo.val - 1 ≤ hi.val) : drVals hi lo = (urVals lo hi).reverse := by
  apply List.ext_getElem
  · simp [drVals, urVals]
  · intro j h1 h2
    simp only [drVals, urVals, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    simp [drVals] at h1
    congr 1
    have := urLen_eq lo hi h
    push_cast; omega

theorem i64_one_val : (i64 1).val = 1 := i64_val (by omega) (by omega)

/-- `A[i]` read through an index value. -/
def intApp (g : Int → V) : V → V
  | .int i => g i
  | _ => .nothing

/-- `n:-1:1` yields `n, ..., 1`; `Iterators.Reverse` of an array of `n`
elements with `A[i] = g i` yields `g n, ..., g 1`. -/
theorem revArrIt_yields (inner : It) (n : Nat) (N : JInt64) (g : Int → V)
    (hN : N.val = n) (hn : n < 2 ^ 62) :
    (revArrIt inner n N g).Yields ((List.range n).map fun j : Nat => g ((n : Int) - j)) := by
  have hw : (i64 1).val - 1 ≤ N.val ∧ N.val < 2 ^ 62 ∧
      -(2 ^ 62) < (i64 1).val := by
    rw [hN, i64_one_val]; omega
  have hix : YF (drNext (i64 1)) (drFirst N (i64 1)) (drVals N (i64 1)) :=
    drIt_yields N (i64 1) hw
  have hl : urLen (i64 1) N = n := by
    unfold urLen; rw [hN, i64_one_val]; omega
  have hmap : (List.range n).map (fun j : Nat => g ((n : Int) - j)) =
      (drVals N (i64 1)).map (intApp g) := by
    unfold drVals
    rw [hl, List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    rw [hN]
    try rfl
  show YF (revArrNext (arrGet n g) (drNext (i64 1)))
    (revArrCont (arrGet n g) (revIdxObj n) (drFirst N (i64 1))) _
  rw [hmap]
  refine revArr_YF (arrGet n g) (intApp g) (drNext (i64 1)) (revIdxObj n) hix ?_
  intro k hk
  unfold drVals at hk
  rw [hl] at hk
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
  simp only [List.mem_range] at hj
  rw [hN]
  show (if 1 ≤ (n : Int) - j ∧ (n : Int) - j ≤ n then _ else _) = _
  rw [if_pos (by omega)]
  try rfl

/-- Every covered object yields its elements. -/
theorem obj_yields : ∀ o : Obj, o.WF → o.it.Yields o.elems := by
  intro o
  induction o with
  | num v => intro _; exact .cons .nil
  | pair a b => intro _; exact .cons (.cons .nil)
  | urange lo hi =>
    intro h; obtain ⟨h1, h2, h3⟩ := h; exact urIt_yields lo hi ⟨h1, by omega, by omega⟩
  | drange hi lo =>
    intro h; obtain ⟨h1, h2, h3⟩ := h; exact drIt_yields hi lo ⟨h1, by omega, by omega⟩
  | vec xs => intro _; exact vecIt_yields .any xs
  | tup xs => intro _; exact tupIt_yields [] xs
  | rev o _ =>
    intro h
    obtain ⟨ha, hw⟩ := h
    cases o with
    | vec xs =>
      show (revArrIt (vecObjIt xs) xs.length (i64 xs.length) (fun i => getIdx xs i)).Yields xs.reverse
      have hw' : Fits xs := hw
      have := revArrIt_yields (vecObjIt xs) xs.length (i64 xs.length) (fun i => getIdx xs i)
        (i64_nat_val (by unfold Fits at hw'; omega)) (by unfold Fits at hw'; omega)
      rwa [map_range_rev_eq] at this
    | urange lo hi =>
      show (revArrIt (urIt lo hi) (urLen lo hi) (i64 (urLen lo hi)) _).Yields (urVals lo hi).reverse
      obtain ⟨h1, h2, h3⟩ := hw
      have hn : urLen lo hi < 2 ^ 62 := by unfold urLen; omega
      have := revArrIt_yields (urIt lo hi) (urLen lo hi) (i64 (urLen lo hi))
        (fun i => .int (lo.val + i - 1)) (i64_nat_val hn) hn
      rwa [ur_rev_eq lo hi _ rfl] at this
    | drange hi lo =>
      show (revArrIt (drIt hi lo) (urLen lo hi) (i64 (urLen lo hi)) _).Yields (drVals hi lo).reverse
      obtain ⟨h1, h2, h3⟩ := hw
      have hn : urLen lo hi < 2 ^ 62 := by unfold urLen; omega
      have := revArrIt_yields (drIt hi lo) (urLen lo hi) (i64 (urLen lo hi))
        (fun i => .int (hi.val - i + 1)) (i64_nat_val hn) hn
      rwa [dr_rev_eq lo hi _ rfl] at this
    | tup xs =>
      show YF (revTupNext xs) (revTupStep xs xs.length) xs.reverse
      have := revTup_YF xs xs.length (Nat.le_refl _)
      rwa [List.take_length] at this
    | num _ | pair _ _ | rev _ | gen _ _ => exact absurd ha id
  | gen f o ih =>
    intro h
    exact genCont_YF f o.it.next (ih h)

/-! ## Properties -/

/-- `Iterators.reverse(itr)` yields the elements of `itr` in reverse order for
numbers, characters, pairs, ranges, arrays, tuples, generators and
`Iterators.Reverse` objects, and reversing twice gives back the original
elements (base/iterators.jl:83-112: "Given an iterator `itr`, then
`reverse(itr)` is an iterator over the same collection but in the reverse
order"). -/
def ReverseYields : Prop :=
  ∀ o : Obj, o.WF →
    (itReverse o).it.Yields o.elems.reverse ∧ (itReverse (itReverse o)).it.Yields o.elems

theorem itReverse_wf : ∀ o : Obj, o.WF → (itReverse o).WF ∧ (itReverse o).elems = o.elems.reverse := by
  intro o
  induction o with
  | num v => intro _; exact ⟨trivial, rfl⟩
  | pair a b => intro _; exact ⟨trivial, rfl⟩
  | urange lo hi => intro h; exact ⟨h, dr_vals_eq lo hi h.1⟩
  | drange hi lo =>
    intro h
    refine ⟨h, ?_⟩
    show urVals lo hi = (drVals hi lo).reverse
    rw [dr_vals_eq lo hi h.1, List.reverse_reverse]
  | vec xs => intro h; exact ⟨⟨trivial, h⟩, rfl⟩
  | tup xs => intro h; exact ⟨⟨trivial, h⟩, rfl⟩
  | rev o _ => intro h; exact ⟨h.2, by simp [Obj.elems, itReverse]⟩
  | gen f o ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih h
    exact ⟨h1, by simp only [itReverse, Obj.elems, h2, List.map_reverse]⟩

theorem reverseYields : ReverseYields := by
  intro o h
  obtain ⟨w1, e1⟩ := itReverse_wf o h
  obtain ⟨w2, e2⟩ := itReverse_wf _ w1
  refine ⟨?_, ?_⟩
  · rw [← e1]; exact obj_yields _ w1
  · have := obj_yields _ w2
    rwa [e2, e1, List.reverse_reverse] at this

/-- `Iterators.Reverse(A)` of an array or tuple has the `eltype`,
`IteratorEltype`, `IteratorSize`, `length` and `size` of `A`
(base/iterators.jl:128-132), `last(Reverse(A))` is `first(A)` (133), and
iterating `Iterators.Reverse{Union{}}` throws `ArgumentError` (153-154). -/
def ReverseTraits : Prop :=
  (∀ o : Obj, o.ArrayLike →
    (Obj.rev o).it.isz = o.it.isz ∧ (Obj.rev o).it.iel = o.it.iel ∧
    (Obj.rev o).it.elt = o.it.elt ∧ (Obj.rev o).it.len = o.it.len ∧
    (Obj.rev o).it.size = o.it.size ∧ (Obj.rev o).it.lastv = firstOf o.it.first) ∧
  (∀ s, ∃ m, revBottomIt.first = jthrow (.argumentError m) ∧ revBottomIt.next s = jthrow (.argumentError m))

theorem revBottom_throws (s : V) :
    revBottomIt.first = jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}") ∧
    revBottomIt.next s = jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}") :=
  ⟨rfl, rfl⟩

theorem revArrIt_traits (inner : It) (n : Nat) (N : JInt64) (g : Int → V) :
    (revArrIt inner n N g).isz = inner.isz ∧ (revArrIt inner n N g).iel = inner.iel ∧
    (revArrIt inner n N g).elt = inner.elt ∧ (revArrIt inner n N g).len = inner.len ∧
    (revArrIt inner n N g).size = inner.size ∧ (revArrIt inner n N g).lastv = firstOf inner.first :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revTupIt_traits (xs : List V) :
    (revTupIt xs).isz = (tupObjIt xs).isz ∧ (revTupIt xs).iel = (tupObjIt xs).iel ∧
    (revTupIt xs).elt = (tupObjIt xs).elt ∧ (revTupIt xs).len = (tupObjIt xs).len ∧
    (revTupIt xs).size = (tupObjIt xs).size ∧ (revTupIt xs).lastv = firstOf (tupObjIt xs).first :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reverseTraits : ReverseTraits := by
  refine ⟨?_, fun s => ⟨_, revBottom_throws s⟩⟩
  intro o ho
  cases o with
  | vec xs => exact revArrIt_traits (vecObjIt xs) xs.length (i64 xs.length) _
  | urange lo hi => exact revArrIt_traits (urIt lo hi) (urLen lo hi) (i64 (urLen lo hi)) _
  | drange hi lo => exact revArrIt_traits (drIt hi lo) (urLen lo hi) (i64 (urLen lo hi)) _
  | tup xs => exact revTupIt_traits xs
  | num _ | pair _ _ | rev _ | gen _ _ => exact absurd ho id

end JuliaLean.IteratorsCov
