import JuliaLean.IteratorsCov.TakeDrop

/-!
# `Iterators.Enumerate` (base/iterators.jl:164-233)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `T === Union{}`. -/
def Ty.isBottom : Ty → Bool
  | .bottom => true
  | _ => false

/-- `TupleOrBottom(ts...)`: `Union{}` if a field type is `Union{}`, else `Tuple{ts...}`. -/
def tupleOrBottom (ts : List Ty) : Ty := if ts.any Ty.isBottom then .bottom else .tuple ts

/-- The tail of `iterate(e::Enumerate, state)`: `n === nothing && return n;
(i, n[1]), (i+1, n[2])`. -/
def enumCont (i : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => .ok (some (.tup [.int i, x], .tup [.int (i64 i + i64 1).val, s]))
  | .error e => .error e

/-- `iterate(e::Enumerate, state=(1,))`, base/iterators.jl:211-216:
`i, rest = state[1], tail(state); n = iterate(e.itr, rest...)`. -/
def enumNext (it : It) : V → Step
  | .tup (.int i :: rest) => enumCont i (innerIter it rest)
  | _ => jthrow (.methodError "iterate")

/-- The object `enumerate(itr) = Enumerate(itr)` (207) with `length` (209),
`size` (210), `iterate` (211-216), `last(e) = (length(e.itr), last(e.itr))`
(217), `eltype` `TupleOrBottom(Int, eltype(I))` (219), `IteratorSize` and
`IteratorEltype` of `I` (221-222). -/
def enumIt (it : It) : It where
  first := enumNext it (.tup [.int 1])
  next := enumNext it
  isz := it.isz
  iel := it.iel
  elt := tupleOrBottom [.int, it.elt]
  len := it.len
  size := it.size
  lastv := do
    let n ← it.len
    let l ← it.lastv
    pure (.tup [.int n.val, l])

/-- The tail of `iterate(r::Reverse{<:Enumerate}, state)`, base/iterators.jl:228-233:
`n = iterate(ri, rest...); (i, n[1]), (i-1, ri, n[2])`. -/
def revEnumCont (ri : V) (i : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => .ok (some (.tup [.int i, x], .tup [.int (i64 i - i64 1).val, ri, s]))
  | .error e => .error e

def revEnumNext (rit : It) : V → Step
  | .tup (.int i :: ri :: rest) => revEnumCont ri i (innerIter rit rest)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.Reverse(enumerate(itr))` given `ri = reverse(itr)` (the object
`riObj` with iterator `rit`): `iterate(r) = iterate(r, (length(ri), ri))`
(224-227) and `iterate(r, state)` (228-233). -/
def revEnumIt (rit : It) (riObj : V) : It where
  first := rit.len.bind fun n => revEnumNext rit (.tup [.int n.val, riObj])
  next := revEnumNext rit

/-- `(i, x₁), (i+1, x₂), ...` -/
def enumSpec : Int → List V → List V
  | _, [] => []
  | i, x :: xs => .tup [.int i, x] :: enumSpec (i + 1) xs

/-- `(i, y₁), (i-1, y₂), ...` -/
def revEnumSpec : Int → List V → List V
  | _, [] => []
  | i, y :: ys => .tup [.int i, y] :: revEnumSpec (i - 1) ys

/-! ## Lemmas -/

theorem enum_YF (it : It) {y : Step} {xs : List V} (h : YF it.next y xs) :
    ∀ i : Int, 0 ≤ i → i + xs.length ≤ 2 ^ 63 →
      YF (enumNext it) (enumCont i y) (enumSpec i xs) := by
  induction h with
  | nil => intro _ _ _; exact .nil
  | @cons x s xs h ih =>
    intro i h0 h1
    simp only [List.length_cons] at h1
    show YF _ (.ok (some (.tup [.int i, x], .tup [.int (i64 i + i64 1).val, s]))) _
    refine .cons ?_
    cases xs with
    | nil =>
      generalize hq : it.next s = q at h
      cases h
      show YF _ (enumCont _ (it.next s)) []
      rw [hq]; exact .nil
    | cons z zs =>
      simp only [List.length_cons] at h1
      rw [i64_succ (k := i) (by omega) (by omega)]
      exact ih (i + 1) (by omega) (by simp; omega)

/-- Counters wrap after `typemax(Int)` elements, so an endless prefix only
keeps its length. -/
theorem enum_PF (it : It) {y : Step} {xs : List V} (h : PF it.next y xs) :
    ∀ i : Int, ∃ zs, PF (enumNext it) (enumCont i y) zs ∧ zs.length = xs.length := by
  induction h with
  | nil => intro _; exact ⟨[], .nil, rfl⟩
  | @cons x s xs _ ih =>
    intro i
    obtain ⟨zs, hz, hl⟩ := ih (i64 i + i64 1).val
    exact ⟨_ :: zs, .cons hz, by simp [hl]⟩

theorem enum_PF_inner (it : It) : ∀ (zs : List V) (i : Int) (y : Step),
    PF (enumNext it) (enumCont i y) zs →
      ∃ xs, PF it.next y xs ∧ zs.length = xs.length ∧
        ∀ z ∈ zs, ∃ j x, z = .tup [.int j, x] ∧ x ∈ xs := by
  intro zs
  induction zs with
  | nil => intro _ _ _; exact ⟨[], .nil, rfl, by simp⟩
  | cons z zs ih =>
    intro i y h
    generalize hw : enumCont i y = w at h
    cases h with
    | @cons _ s' _ h' =>
      match y, hw with
      | .ok (some (a, s)), hw =>
        simp only [enumCont, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨xs, hp, hl, hm⟩ := ih _ _ h'
        refine ⟨a :: xs, .cons hp, by simp [hl], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨i, a, rfl, List.mem_cons_self ..⟩
        · obtain ⟨j, x, rfl, hx⟩ := hm _ hz
          exact ⟨j, x, rfl, List.mem_cons_of_mem _ hx⟩

theorem enumSpec_length : ∀ (i : Int) (xs : List V), (enumSpec i xs).length = xs.length
  | _, [] => rfl
  | i, _ :: xs => by simp [enumSpec, enumSpec_length (i + 1) xs]

theorem revEnum_YF (rit : It) (ri : V) {y : Step} {ys : List V} (h : YF rit.next y ys) :
    ∀ i : Int, i ≤ 2 ^ 62 → ys.length ≤ i →
      YF (revEnumNext rit) (revEnumCont ri i y) (revEnumSpec i ys) := by
  induction h with
  | nil => intro _ _ _; exact .nil
  | @cons x s xs _ ih =>
    intro i h0 h1
    simp only [List.length_cons] at h1
    show YF _ (.ok (some (.tup [.int i, x], .tup [.int (i64 i - i64 1).val, ri, s]))) _
    rw [i64_pred (k := i) (by omega) (by omega)]
    exact .cons (ih (i - 1) (by omega) (by omega))

theorem enumSpec_append (x : V) : ∀ (i : Int) (xs : List V),
    enumSpec i (xs ++ [x]) = enumSpec i xs ++ [.tup [.int (i + xs.length), x]]
  | i, [] => by simp [enumSpec]
  | i, y :: ys => by
    show .tup [.int i, y] :: enumSpec (i + 1) (ys ++ [x]) =
      (.tup [.int i, y] :: enumSpec (i + 1) ys) ++ [.tup [.int (i + ((y :: ys).length : Int)), x]]
    rw [enumSpec_append x (i + 1) ys, List.cons_append,
      show i + 1 + (ys.length : Int) = i + ((y :: ys).length : Int) by rw [List.length_cons]; omega]

theorem revEnumSpec_append (x : V) : ∀ (j : Int) (ys : List V),
    revEnumSpec j (ys ++ [x]) = revEnumSpec j ys ++ [.tup [.int (j - ys.length), x]]
  | j, [] => by simp [revEnumSpec]
  | j, y :: ys => by
    show .tup [.int j, y] :: revEnumSpec (j - 1) (ys ++ [x]) =
      (.tup [.int j, y] :: revEnumSpec (j - 1) ys) ++ [.tup [.int (j - ((y :: ys).length : Int)), x]]
    rw [revEnumSpec_append x (j - 1) ys, List.cons_append,
      show j - 1 - (ys.length : Int) = j - ((y :: ys).length : Int) by rw [List.length_cons]; omega]

theorem enumSpec_rev : ∀ (i : Int) (xs : List V),
    (enumSpec i xs).reverse = revEnumSpec (i + xs.length - 1) xs.reverse
  | _, [] => rfl
  | i, x :: xs => by
    show (.tup [.int i, x] :: enumSpec (i + 1) xs).reverse = _
    rw [List.reverse_cons, enumSpec_rev (i + 1) xs, List.reverse_cons, revEnumSpec_append,
      List.length_reverse]
    have e1 : i + ((x :: xs).length : Int) - 1 = i + 1 + xs.length - 1 := by
      rw [List.length_cons]; omega
    rw [e1, show i + 1 + (xs.length : Int) - 1 - xs.length = i by omega]

theorem revEnumSpec_rev (xs : List V) :
    revEnumSpec xs.length xs.reverse = (enumSpec 1 xs).reverse := by
  rw [enumSpec_rev]; congr 1; omega

/-! ## Properties -/

/-- `enumerate(itr)` yields `(i, x)` for the `i`-th element `x` of `itr`
(base/iterators.jl:171-206: "An iterator that yields `(i, x)` where `i` is a
counter starting at 1, and `x` is the `i`th value from the given iterator"),
stays infinite for an infinite `itr`, its `IteratorSize`, `length` and
`eltype` `Tuple{Int, eltype(itr)}` are truthful whenever `itr`'s are,
`last(enumerate(itr))` is `(length(itr), last(itr))`, and
`Iterators.reverse(enumerate(itr))` yields the pairs backwards whenever
`Iterators.reverse(itr)` yields `itr` backwards. -/
def EnumerateSound : Prop :=
  ∀ it : It,
    (∀ xs, it.Yields xs → xs.length < 2 ^ 62 → (enumIt it).Yields (enumSpec 1 xs)) ∧
    (it.Endless → (enumIt it).Endless) ∧
    (it.SizeSound → (enumIt it).SizeSound) ∧
    (it.EltSound → (enumIt it).EltSound) ∧
    (∀ (xs : List V) (x : V), xs.length < 2 ^ 62 → it.len = .ok (i64 xs.length) → it.lastv = .ok x →
      (enumIt it).lastv = .ok (.tup [.int xs.length, x])) ∧
    (∀ (rit : It) (ri : V) xs, it.Yields xs → xs.length < 2 ^ 62 → rit.Yields xs.reverse →
      rit.len = .ok (i64 xs.length) → (revEnumIt rit ri).Yields (enumSpec 1 xs).reverse)

theorem enumerateSound : EnumerateSound := by
  intro it
  have hy : ∀ xs, it.Yields xs → xs.length < 2 ^ 62 → (enumIt it).Yields (enumSpec 1 xs) :=
    fun xs h hl => enum_YF it h 1 (by omega) (by omega)
  refine ⟨hy, ?_, ?_, ?_, ?_, ?_⟩
  · intro hE n
    obtain ⟨xs, hl, hp⟩ := hE n
    obtain ⟨zs, hz, hzl⟩ := enum_PF it hp 1
    exact ⟨zs, by rw [hzl, hl], hz⟩
  · intro hS
    obtain ⟨hS1, hS2, hS3⟩ := hS
    refine ⟨?_, ?_, ?_⟩
    · intro hf
      obtain ⟨xs, hyx, hl, hlen⟩ := hS1 hf
      exact ⟨enumSpec 1 xs, enum_YF it hyx 1 (by omega) (by omega),
        by rw [enumSpec_length]; exact hl, by rw [enumSpec_length]; exact hlen⟩
    · intro m hm
      obtain ⟨ds, xs, hds, hdl, hyx, hp⟩ := hS2 m hm
      refine ⟨ds, enumSpec 1 xs, hds, hdl, ?_, by rw [enumSpec_length]; exact hp⟩
      obtain ⟨xs', hyx', hl', _⟩ := hS1 (by simp [show it.isz = .hasShape m from hm, Isz.finite])
      have := YF.unique hyx hyx'
      subst this
      exact enum_YF it hyx 1 (by omega) (by omega)
    · intro hi
      intro n
      obtain ⟨xs, hl, hp⟩ := hS3 hi n
      obtain ⟨zs, hz, hzl⟩ := enum_PF it hp 1
      exact ⟨zs, by rw [hzl, hl], hz⟩
  · intro hE hiel zs hp z hz
    obtain ⟨xs, hxs, _, hm⟩ := enum_PF_inner it zs 1 it.first hp
    obtain ⟨j, x, rfl, hx⟩ := hm z hz
    have hxm := hE hiel xs hxs x hx
    show (tupleOrBottom [.int, it.elt]).mem _
    unfold tupleOrBottom
    split
    · rename_i hb
      have : it.elt = .bottom := by
        cases h : it.elt <;> simp_all [Ty.isBottom]
      rw [this] at hxm; exact absurd hxm id
    · exact ⟨[.int j, x], rfl, ⟨j, rfl⟩, hxm, trivial⟩
  · intro xs x hsm hl hx
    show (do let n ← it.len; let l ← it.lastv; pure (V.tup [.int n.val, l])) = _
    rw [hl, hx]
    show Except.ok (V.tup [.int (i64 xs.length).val, x]) = _
    rw [i64_nat_val hsm]
  · intro rit ri xs _ hl hr hrl
    unfold It.Yields
    show YF _ (rit.len.bind fun n => revEnumNext rit (.tup [.int n.val, ri])) _
    rw [hrl]
    show YF _ (revEnumCont ri (i64 xs.length).val rit.first) _
    rw [i64_nat_val (by omega), ← revEnumSpec_rev]
    exact revEnum_YF rit ri hr _ (by omega) (by simp)

end JuliaLean.IteratorsCov
