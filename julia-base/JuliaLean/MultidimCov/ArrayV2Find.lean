import JuliaLean.MultidimCov.ArrayV2Core

/-!
`findnext`, `findfirst`, `findprev`, `findlast` and `findall` on vectors
(master `base/array.jl:2404-2858`).

A vector `A` with keys `1:length(A)` is its element list `xs`; `A[i]` is `vget`
(`BoundsError` outside `1:length(A)`, as `getindex` checks). A predicate is
`p : α → R Bool`, so a throwing predicate and the order of its calls are
observable: the first call that throws decides the error. `nextind(A, i) = i + 1`
and `prevind(A, i) = i - 1` for arrays.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `A[i]` for a vector with keys `1:length(A)`. -/
def vget (xs : List α) (i : Int) : R α :=
  if i < 1 then .error .bounds else
  match xs[(i - 1).toNat]? with
  | some x => .ok x
  | none => .error .bounds

/-- `pairs(A)` of a vector from index `k` on: `(k, xs[1]), (k+1, xs[2]), …`. -/
def idxFrom : Int → List α → List (Int × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: idxFrom (k + 1) xs

/-- `pairs(A)`: every `(i, A[i])` in index order. -/
def pairsV (xs : List α) : List (Int × α) := idxFrom 1 xs

/-- `for (i, a) in ps; testf(a) && return i; end; return nothing`. -/
def scanPairs (p : α → R Bool) : List (Int × α) → R (Option Int)
  | [] => .ok none
  | (i, x) :: rest => do
    let b ← p x
    if b then pure (some i) else scanPairs p rest

/-- The `while true` loop of `findnext` (`base/array.jl:2475`), with `fuel`
iterations left before `i == l`. -/
def fwdLoop (p : α → R Bool) (xs : List α) (l : Int) : Nat → Int → R (Option Int)
  | 0, _ => .ok none
  | fuel + 1, i => do
    let x ← vget xs i
    let b ← p x
    if b then pure (some i) else if i = l then pure none else fwdLoop p xs l fuel (i + 1)

/-- base/array.jl:2475 `findnext(testf::Function, A, start)`. -/
def m2475 (p : α → R Bool) (xs : List α) (start : Int) : R (Option Int) :=
  let l : Int := xs.length
  if start > l then .ok none else fwdLoop p xs l (l - start + 1).toNat start

/-- base/array.jl:2404 `findnext(A, start) = findnext(identity, A, start)`. -/
def m2404 (bs : List Bool) (start : Int) : R (Option Int) := m2475 (fun b => .ok b) bs start

/-- base/array.jl:2523 `findfirst(testf::Function, A)`: a scan of `pairs(A)`. -/
def m2523 (p : α → R Bool) (xs : List α) : R (Option Int) := scanPairs p (pairsV xs)

/-- base/array.jl:2531 `findfirst(testf, A::AbstractArray) = findnext(testf, A, first(keys(A)))`. -/
def m2531 (p : α → R Bool) (xs : List α) : R (Option Int) := m2475 p xs 1

/-- base/array.jl:2441 `findfirst(A) = findfirst(identity, A)`. -/
def m2441 (bs : List Bool) : R (Option Int) := m2523 (fun b => .ok b) bs

/-- base/array.jl:2444 `findfirst(A::AbstractArray) = findnext(A, first(keys(A)))`. -/
def m2444 (bs : List Bool) : R (Option Int) := m2404 bs 1

/-- The `while true` loop of `findprev` (`base/array.jl:2671`). -/
def bwdLoop (p : α → R Bool) (xs : List α) : Nat → Int → R (Option Int)
  | 0, _ => .ok none
  | fuel + 1, i => do
    let x ← vget xs i
    let b ← p x
    if b then pure (some i) else if i = 1 then pure none else bwdLoop p xs fuel (i - 1)

/-- base/array.jl:2671 `findprev(testf::Function, A, start)`. -/
def m2671 (p : α → R Bool) (xs : List α) (start : Int) : R (Option Int) :=
  if start < 1 then .ok none else bwdLoop p xs start.toNat start

/-- base/array.jl:2591 `findprev(A, start) = findprev(identity, A, start)`. -/
def m2591 (bs : List Bool) (start : Int) : R (Option Int) := m2671 (fun b => .ok b) bs start

/-- base/array.jl:2716 `findlast(testf::Function, A)`: a scan of `Iterators.reverse(pairs(A))`. -/
def m2716 (p : α → R Bool) (xs : List α) : R (Option Int) := scanPairs p (pairsV xs).reverse

/-- base/array.jl:2724 `findlast(testf, A::AbstractArray) = findprev(testf, A, last(keys(A)))`. -/
def m2724 (p : α → R Bool) (xs : List α) : R (Option Int) := m2671 p xs xs.length

/-- base/array.jl:2629 `findlast(A) = findlast(identity, A)`. -/
def m2629 (bs : List Bool) : R (Option Int) := m2716 (fun b => .ok b) bs

/-- base/array.jl:2632 `findlast(A::AbstractArray) = findprev(A, last(keys(A)))`. -/
def m2632 (bs : List Bool) : R (Option Int) := m2591 bs bs.length

/-- `collect(first(p) for p in ps if testf(last(p)))`: the generator calls `testf` in order. -/
def filterPairs (p : α → R Bool) : List (Int × α) → R (List Int)
  | [] => .ok []
  | (i, x) :: rest => do
    let b ← p x
    let r ← filterPairs p rest
    pure (if b then i :: r else r)

/-- base/array.jl:2789 `findall(testf::Function, A)`. -/
def m2789 (p : α → R Bool) (xs : List α) : R (List Int) := filterPairs p (pairsV xs)

/-- base/array.jl:2838 `findall(A) = collect(first(p) for p in pairs(A) if last(p))`. -/
def m2838 (bs : List Bool) : R (List Int) := filterPairs (fun b => .ok b) (pairsV bs)

/-- The loop of `findall(A::AbstractArray{Bool})` from slot counter `cnt`: `I[cnt] = i; cnt += 1`
for every true `a`; `I` is a function from 1-based slots. -/
def findallLoop : List (Int × Bool) → (Nat → Option Int) × Nat → (Nat → Option Int) × Nat
  | [], st => st
  | (i, a) :: rest, (I, cnt) =>
    findallLoop rest (if a then (fun k => if k = cnt then some i else I k, cnt + 1) else (I, cnt))

/-- base/array.jl:2843 `findall(A::AbstractArray{Bool})`: `n = count(A)`,
`I = Vector{Int}(undef, n)`, then the loop; `#undef` slots are `none`. -/
def m2843 (bs : List Bool) : List (Option Int) :=
  let n := bs.count true
  let I : Nat → Option Int := fun _ => none
  let I := (findallLoop (pairsV bs) (I, 1)).1
  (List.range n).map fun k => I (k + 1)

/-- `testf.(A)`: broadcasting calls `testf` on every element in index order. -/
def mapR (p : α → R β) : List α → R (List β)
  | [] => .ok []
  | x :: xs => do
    let y ← p x
    let ys ← mapR p xs
    pure (y :: ys)

/-- base/array.jl:2796 `findall(testf, A::AbstractArray) = findall(testf.(A))`. -/
def m2796 (p : α → R Bool) (xs : List α) : R (List (Option Int)) := do
  let bs ← mapR p xs
  pure (m2843 bs)

/-- base/array.jl:2856 `findall(x::Bool) = x ? [1] : Vector{Int}()`. -/
def m2856 (x : Bool) : List Int := if x then [1] else []

/-- base/array.jl:2857 `findall(testf::Function, x::Number) = testf(x) ? [1] : Vector{Int}()`. -/
def m2857 (p : α → R Bool) (x : α) : R (List Int) := do
  let b ← p x
  pure (if b then [1] else [])

/-- base/array.jl:2858 `findall(p::Fix2{typeof(in)}, x::Number) = x in p.x ? [1] : Vector{Int}()`,
with `inColl x` the call `x in p.x`. -/
def m2858 (inColl : α → R Bool) (x : α) : R (List Int) := do
  let b ← inColl x
  pure (if b then [1] else [])

/-! ## Lemmas -/

theorem idxFrom_append (k : Int) (as bs : List α) :
    idxFrom k (as ++ bs) = idxFrom k as ++ idxFrom (k + as.length) bs := by
  induction as generalizing k with
  | nil => simp [idxFrom]
  | cons x xs ih =>
    have h : k + ((x :: xs).length : Int) = k + 1 + xs.length := by simp; omega
    rw [h]; simp only [List.cons_append, idxFrom, ih]

theorem mem_idxFrom {k : Int} {xs : List α} {pr : Int × α} (h : pr ∈ idxFrom k xs) :
    k ≤ pr.1 ∧ pr.1 < k + xs.length ∧ pr.2 ∈ xs := by
  induction xs generalizing k with
  | nil => simp [idxFrom] at h
  | cons x xs ih =>
    simp only [idxFrom, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact ⟨Int.le_refl _, by simp only [List.length_cons]; omega, by simp⟩
    · have := ih h; simp only [List.length_cons, List.mem_cons]; refine ⟨by omega, by omega, Or.inr this.2.2⟩

theorem find?_congr {l : List β} {f g : β → Bool} (h : ∀ x ∈ l, f x = g x) : l.find? f = l.find? g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem filter_congr' {l : List β} {f g : β → Bool} (h : ∀ x ∈ l, f x = g x) : l.filter f = l.filter g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem scan_pure (q : α → Bool) (ps : List (Int × α)) :
    scanPairs (fun x => .ok (q x)) ps = .ok ((ps.find? fun pr => q pr.2).map Prod.fst) := by
  induction ps with
  | nil => rfl
  | cons pr rest ih =>
    obtain ⟨i, x⟩ := pr
    simp only [scanPairs, bind_ok, List.find?_cons]
    cases q x <;> simp [ih]

theorem scan_err {p : α → R Bool} {e : Err} (pre post : List (Int × α)) (i : Int) (x : α)
    (hpre : ∀ pr ∈ pre, p pr.2 = .ok false) (hx : p x = .error e) :
    scanPairs p (pre ++ (i, x) :: post) = .error e := by
  induction pre with
  | nil => simp [scanPairs, hx]
  | cons pr rest ih =>
    obtain ⟨j, y⟩ := pr
    simp only [List.cons_append, scanPairs, hpre (j, y) (by simp), bind_ok, Bool.false_eq_true, if_false]
    exact ih (fun q hq => hpre q (by simp [hq]))

theorem filter_pure (q : α → Bool) (ps : List (Int × α)) :
    filterPairs (fun x => .ok (q x)) ps = .ok ((ps.filter fun pr => q pr.2).map Prod.fst) := by
  induction ps with
  | nil => rfl
  | cons pr rest ih =>
    obtain ⟨i, x⟩ := pr
    simp only [filterPairs, bind_ok, ih, List.filter_cons]
    cases q x <;> simp

theorem filter_err {p : α → R Bool} {e : Err} (pre post : List (Int × α)) (i : Int) (x : α)
    (hpre : ∀ pr ∈ pre, ∃ b, p pr.2 = .ok b) (hx : p x = .error e) :
    filterPairs p (pre ++ (i, x) :: post) = .error e := by
  induction pre with
  | nil => simp [filterPairs, hx]
  | cons pr rest ih =>
    obtain ⟨j, y⟩ := pr
    obtain ⟨b, hb⟩ := hpre (j, y) (by simp)
    simp only [List.cons_append, filterPairs, hb, bind_ok]
    rw [ih (fun q hq => hpre q (by simp [hq])), bind_error]

theorem mapR_pure (q : α → β) (xs : List α) : mapR (fun x => .ok (q x)) xs = .ok (xs.map q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapR, ih]

theorem mapR_err {p : α → R β} {e : Err} (pre post : List α) (x : α)
    (hpre : ∀ y ∈ pre, ∃ b, p y = .ok b) (hx : p x = .error e) :
    mapR p (pre ++ x :: post) = .error e := by
  induction pre with
  | nil => simp [mapR, hx]
  | cons y rest ih =>
    obtain ⟨b, hb⟩ := hpre y (by simp)
    simp only [List.cons_append, mapR, hb, bind_ok]
    rw [ih (fun z hz => hpre z (by simp [hz])), bind_error]

theorem vget_ok {xs : List α} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ xs.length) :
    vget xs i = .ok (xs[(i - 1).toNat]'(by omega)) := by
  unfold vget
  rw [if_neg (by omega), List.getElem?_eq_getElem (by omega)]

theorem fwdLoop_eq (p : α → R Bool) (xs : List α) :
    ∀ (fuel : Nat) (i : Int), 1 ≤ i → i ≤ xs.length → i + fuel = xs.length + 1 →
      fwdLoop p xs xs.length fuel i = scanPairs p (idxFrom i (xs.drop (i - 1).toNat)) := by
  intro fuel
  induction fuel with
  | zero => intro i h1 h2 h3; omega
  | succ fuel ih =>
    intro i h1 h2 h3
    have hlt : (i - 1).toNat < xs.length := by omega
    rw [List.drop_eq_getElem_cons hlt]
    simp only [fwdLoop, idxFrom, scanPairs, vget_ok h1 h2, bind_ok]
    cases hp : p (xs[(i - 1).toNat]'hlt) with
    | error e => rfl
    | ok b =>
      simp only [bind_ok]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        by_cases hi : i = xs.length
        · rw [if_pos hi, List.drop_of_length_le (by omega)]; rfl
        · rw [if_neg hi, ih (i + 1) (by omega) (by omega) (by omega),
            show (i + 1 - 1).toNat = (i - 1).toNat + 1 by omega]
      · rfl

theorem bwdLoop_eq (p : α → R Bool) (xs : List α) :
    ∀ (fuel : Nat) (i : Int), 1 ≤ i → i ≤ xs.length → (fuel : Int) = i →
      bwdLoop p xs fuel i = scanPairs p (idxFrom 1 (xs.take i.toNat)).reverse := by
  intro fuel
  induction fuel with
  | zero => intro i h1 h2 h3; omega
  | succ fuel ih =>
    intro i h1 h2 h3
    have hlt : (i - 1).toNat < xs.length := by omega
    rw [show i.toNat = (i - 1).toNat + 1 by omega, List.take_succ_eq_append_getElem hlt,
      idxFrom_append, List.length_take, Nat.min_eq_left (by omega)]
    simp only [idxFrom, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, scanPairs, bwdLoop, vget_ok h1 h2, bind_ok,
      show (1 : Int) + ((i - 1).toNat : Nat) = i by omega]
    cases hp : p (xs[(i - 1).toNat]'hlt) with
    | error e => rfl
    | ok b =>
      simp only [bind_ok]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        by_cases hi : i = 1
        · subst hi; rfl
        · rw [if_neg hi, ih (i - 1) (by omega) (by omega) (by omega)]
      · rfl

theorem pairsV_split (xs : List α) (s : Nat) (hs : s ≤ xs.length) :
    pairsV xs = idxFrom 1 (xs.take s) ++ idxFrom (1 + s) (xs.drop s) := by
  unfold pairsV
  conv => lhs; rw [← List.take_append_drop s xs]
  rw [idxFrom_append, List.length_take, Nat.min_eq_left hs]

theorem m2475_pure_eq (q : α → Bool) (xs : List α) (start : Int) (h1 : 1 ≤ start) :
    m2475 (fun x => .ok (q x)) xs start =
      .ok (((pairsV xs).find? fun pr => decide (start ≤ pr.1) && q pr.2).map Prod.fst) := by
  unfold m2475
  by_cases hs : start > xs.length
  · rw [if_pos hs]
    rw [(List.find?_eq_none).mpr]; · rfl
    intro pr hpr
    have := mem_idxFrom hpr
    simp; omega
  · rw [if_neg hs, fwdLoop_eq _ xs _ start h1 (by omega) (by omega), scan_pure,
      pairsV_split xs (start - 1).toNat (by omega), List.find?_append]
    have hnone : (idxFrom 1 (xs.take (start - 1).toNat)).find?
        (fun pr => decide (start ≤ pr.1) && q pr.2) = none := by
      apply List.find?_eq_none.mpr
      intro pr hpr
      have := mem_idxFrom hpr
      simp only [List.length_take] at this
      simp; omega
    rw [hnone]
    simp only [Option.none_or]
    rw [show (1 : Int) + ((start - 1).toNat : Nat) = start by omega]
    congr 2
    apply find?_congr
    intro pr hpr
    have := mem_idxFrom hpr
    simp [show start ≤ pr.1 by omega]

theorem m2671_pure_eq (q : α → Bool) (xs : List α) (start : Int) (h2 : start ≤ xs.length) :
    m2671 (fun x => .ok (q x)) xs start =
      .ok (((pairsV xs).reverse.find? fun pr => decide (pr.1 ≤ start) && q pr.2).map Prod.fst) := by
  unfold m2671
  by_cases hs : start < 1
  · rw [if_pos hs, (List.find?_eq_none).mpr]; · rfl
    intro pr hpr
    have := mem_idxFrom (List.mem_reverse.mp hpr)
    simp; omega
  · rw [if_neg hs, bwdLoop_eq _ xs _ start (by omega) h2 (by omega), scan_pure,
      pairsV_split xs start.toNat (by omega), List.reverse_append, List.find?_append]
    have hnone : (idxFrom (1 + (start.toNat : Int)) (xs.drop start.toNat)).reverse.find?
        (fun pr => decide (pr.1 ≤ start) && q pr.2) = none := by
      apply List.find?_eq_none.mpr
      intro pr hpr
      have := mem_idxFrom (List.mem_reverse.mp hpr)
      simp; omega
    rw [hnone]
    simp only [Option.none_or]
    congr 2
    apply find?_congr
    intro pr hpr
    have := mem_idxFrom (List.mem_reverse.mp hpr)
    simp only [List.length_take] at this
    simp [show pr.1 ≤ start by omega]

/-- Slots of the `findall(A::AbstractArray{Bool})` loop: after a run from counter
`c`, slot `k` holds the `(k - c)`-th true index of the run, or its old value. -/
theorem findallLoop_spec : ∀ (ps : List (Int × Bool)) (I : Nat → Option Int) (c : Nat),
    let t := (ps.filter fun pr => pr.2).map Prod.fst
    (findallLoop ps (I, c)).2 = c + t.length ∧
    ∀ k, (findallLoop ps (I, c)).1 k = if c ≤ k ∧ k < c + t.length then t[k - c]? else I k := by
  intro ps
  induction ps with
  | nil =>
    intro I c
    refine ⟨by simp [findallLoop], fun k => ?_⟩
    simp only [findallLoop, List.filter_nil, List.map_nil, List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
  | cons pr rest ih =>
    intro I c
    obtain ⟨i, a⟩ := pr
    cases a
    · simp only [findallLoop, Bool.false_eq_true, if_false, List.filter_cons]
      exact ih I c
    · simp only [findallLoop, if_true, List.filter_cons, List.map_cons, List.length_cons]
      obtain ⟨h1, h2⟩ := ih (fun k => if k = c then some i else I k) (c + 1)
      refine ⟨by rw [h1]; omega, fun k => ?_⟩
      rw [h2 k]
      by_cases hk : k = c
      · rw [if_neg (by omega), if_pos hk, if_pos (by omega), hk, Nat.sub_self]; rfl
      · by_cases hr : c + 1 ≤ k ∧ k < c + 1 + ((rest.filter fun pr => pr.2).map Prod.fst).length
        · rw [if_pos hr, if_pos (by omega), show k - c = (k - (c + 1)) + 1 by omega]
          simp
        · rw [if_neg hr, if_neg hk, if_neg (by omega)]

theorem count_idxFrom (bs : List Bool) (k : Int) :
    ((idxFrom k bs).filter fun pr => pr.2).length = bs.count true := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [idxFrom, List.filter_cons, ih]

theorem m2843_eq (bs : List Bool) :
    m2843 bs = (((pairsV bs).filter fun pr => pr.2).map Prod.fst).map some := by
  unfold m2843
  obtain ⟨_, h2⟩ := findallLoop_spec (pairsV bs) (fun _ => none) 1
  apply List.ext_getElem
  · simp [pairsV, count_idxFrom]
  · intro k hk1 hk2
    have hn : ((pairsV bs).filter fun pr => pr.2).length = bs.count true := count_idxFrom bs 1
    simp only [List.length_map] at hk2
    simp only [List.getElem_map, List.getElem_range, h2]
    rw [if_pos (by simp only [List.length_map]; omega), show k + 1 - 1 = k by omega,
      List.getElem?_eq_getElem (by simp only [List.length_map]; omega)]
    simp

/-! ## Contracts -/

/-- `findnext`/`findfirst`/`findprev`/`findlast`/`findall` on a vector (docstrings
`base/array.jl:2447`, `2489`, `2635`, `2685`, `2739`). For a predicate that
returns normally (`q`), each result is the matching index of `pairs(v)`:
`findfirst` the first `i` with `q(v[i])`, `findnext(q, v, s)` the first with
`i ≥ s`, `findprev(q, v, s)` the last with `i ≤ s`, `findlast` the last, and
`findall` every such `i` in increasing order, for every start `s` that is an
index of `v`. (Starts outside the indices: the refuted entry
`arrayops-findnext-start-below`.) -/
def PFindPure : Prop := ∀ {α : Type} (q : α → Bool) (xs : List α),
    let p : α → R Bool := fun x => .ok (q x)
    let first := ((pairsV xs).find? fun pr => q pr.2).map Prod.fst
    let last := ((pairsV xs).reverse.find? fun pr => q pr.2).map Prod.fst
    let all := ((pairsV xs).filter fun pr => q pr.2).map Prod.fst
    m2523 p xs = .ok first ∧ m2531 p xs = .ok first ∧
    m2716 p xs = .ok last ∧ m2724 p xs = .ok last ∧
    m2789 p xs = .ok all ∧ m2796 p xs = .ok (all.map some) ∧
    (∀ s : Int, 1 ≤ s → s ≤ xs.length → m2475 p xs s = .ok (((pairsV xs).find? fun pr => decide (s ≤ pr.1) && q pr.2).map Prod.fst)) ∧
    (∀ s : Int, 1 ≤ s → s ≤ xs.length →
      m2671 p xs s = .ok (((pairsV xs).reverse.find? fun pr => decide (pr.1 ≤ s) && q pr.2).map Prod.fst))

theorem filter_map_some (q : α → Bool) (xs : List α) (k : Int) :
    ((idxFrom k (xs.map q)).filter fun pr => pr.2).map Prod.fst =
      ((idxFrom k xs).filter fun pr => q pr.2).map Prod.fst := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, idxFrom, List.filter_cons]; cases q x <;> simp [ih]

theorem pFindPure : PFindPure := by
  intro α q xs
  dsimp only
  have hf := m2475_pure_eq q xs 1 (by omega)
  have hl := m2671_pure_eq q xs xs.length (Int.le_refl _)
  have hcf : ((pairsV xs).find? fun pr => decide (1 ≤ pr.1) && q pr.2) = (pairsV xs).find? fun pr => q pr.2 :=
    find?_congr fun pr hpr => by have := mem_idxFrom hpr; simp [show 1 ≤ pr.1 by omega]
  have hcl : ((pairsV xs).reverse.find? fun pr => decide (pr.1 ≤ (xs.length : Int)) && q pr.2) =
      (pairsV xs).reverse.find? fun pr => q pr.2 :=
    find?_congr fun pr hpr => by
      have := mem_idxFrom (List.mem_reverse.mp hpr); simp [show pr.1 ≤ (xs.length : Int) by omega]
  refine ⟨scan_pure q _, ?_, scan_pure q _, ?_, filter_pure q _, ?_, fun s hs _ => m2475_pure_eq q xs s hs,
    fun s _ hs => m2671_pure_eq q xs s hs⟩
  · unfold m2531; rw [hf, hcf]
  · unfold m2724; rw [hl, hcl]
  · unfold m2796; rw [mapR_pure, bind_ok, pure_ok, m2843_eq]
    unfold pairsV; rw [filter_map_some]

/-- Call order of a throwing predicate. If `v = pre ++ [x] ++ post` and `p(x)`
throws `e`: `findfirst(p, v)` throws `e` when `p` is `false` on all of `pre`,
`findlast(p, v)` when `p` is `false` on all of `post`, and `findall(p, v)` when
`p` returns normally on all of `pre` (it calls `p` left to right). -/
def PFindErr : Prop := ∀ {α : Type} (p : α → R Bool) (pre post : List α) (x : α) (e : Err),
    p x = .error e →
    ((∀ y ∈ pre, p y = .ok false) → m2523 p (pre ++ x :: post) = .error e ∧ m2531 p (pre ++ x :: post) = .error e) ∧
    ((∀ y ∈ post, p y = .ok false) → m2716 p (pre ++ x :: post) = .error e ∧ m2724 p (pre ++ x :: post) = .error e) ∧
    ((∀ y ∈ pre, ∃ b, p y = .ok b) → m2789 p (pre ++ x :: post) = .error e ∧ m2796 p (pre ++ x :: post) = .error e)

theorem pairsV_mid (pre post : List α) (x : α) :
    pairsV (pre ++ x :: post) =
      idxFrom 1 pre ++ ((1 : Int) + pre.length, x) :: idxFrom ((1 : Int) + pre.length + 1) post := by
  unfold pairsV; rw [idxFrom_append]; rfl

theorem pFindErr : PFindErr := by
  intro α p pre post x e hx
  have hn : (1 : Int) ≤ (pre ++ x :: post).length := by simp; omega
  refine ⟨fun hpre => ?_, fun hpost => ?_, fun hpre => ?_⟩
  · have h : m2523 p (pre ++ x :: post) = .error e := by
      unfold m2523; rw [pairsV_mid]
      exact scan_err _ _ _ _ (fun pr hpr => hpre _ (mem_idxFrom hpr).2.2) hx
    refine ⟨h, ?_⟩
    unfold m2531 m2475
    rw [if_neg (by omega), fwdLoop_eq _ _ _ 1 (by omega) hn (by omega)]
    exact h
  · have h : m2716 p (pre ++ x :: post) = .error e := by
      unfold m2716; rw [pairsV_mid, List.reverse_append, List.reverse_cons, List.append_assoc]
      exact scan_err _ _ _ _ (fun pr hpr => hpost _ (mem_idxFrom (List.mem_reverse.mp hpr)).2.2) hx
    refine ⟨h, ?_⟩
    unfold m2724 m2671
    rw [if_neg (by omega), bwdLoop_eq _ _ _ _ (by omega) (Int.le_refl _) (by simp; omega),
      show ((pre ++ x :: post).length : Int).toNat = (pre ++ x :: post).length by omega, List.take_length]
    exact h
  · refine ⟨?_, ?_⟩
    · unfold m2789; rw [pairsV_mid]
      exact filter_err _ _ _ _ (fun pr hpr => hpre _ (mem_idxFrom hpr).2.2) hx
    · unfold m2796; rw [mapR_err pre post x hpre hx, bind_error]

/-- The `Bool`-array methods (docstrings `base/array.jl:2407`, `2558`, `2594`, `2799`):
`findfirst(A)`, `findnext(A, s)`, `findprev(A, s)`, `findlast(A)` and `findall(A)`
locate the `true` entries of `pairs(A)` exactly as the predicate forms with `identity`. -/
def PFindBool : Prop := ∀ (bs : List Bool),
    let first := ((pairsV bs).find? fun pr => pr.2).map Prod.fst
    let last := ((pairsV bs).reverse.find? fun pr => pr.2).map Prod.fst
    m2441 bs = .ok first ∧ m2444 bs = .ok first ∧ m2629 bs = .ok last ∧ m2632 bs = .ok last ∧
    m2838 bs = .ok (((pairsV bs).filter fun pr => pr.2).map Prod.fst) ∧
    m2843 bs = (((pairsV bs).filter fun pr => pr.2).map Prod.fst).map some ∧
    (∀ s : Int, 1 ≤ s → s ≤ bs.length → m2404 bs s = .ok (((pairsV bs).find? fun pr => decide (s ≤ pr.1) && pr.2).map Prod.fst)) ∧
    (∀ s : Int, 1 ≤ s → s ≤ bs.length → m2591 bs s = .ok (((pairsV bs).reverse.find? fun pr => decide (pr.1 ≤ s) && pr.2).map Prod.fst))

theorem pFindBool : PFindBool := by
  intro bs first last
  obtain ⟨h1, h2, h3, h4, _, _, h7, h8⟩ := pFindPure (fun b : Bool => b) bs
  exact ⟨h1, h2, h3, h4, filter_pure (fun b : Bool => b) _, m2843_eq bs, h7, h8⟩

/-- The scalar `findall` methods (`base/array.jl:2856-2858`) agree with `findall` on
the one-element vector `[x]` (`findall(x::Bool)` with `findall([x])`, the predicate
forms with `findall(p, [x])`), including a throwing predicate. -/
def PFindallScalar : Prop := ∀ {α : Type} (p : α → R Bool) (x : α) (b : Bool),
    (m2856 b).map some = m2843 [b] ∧
    (m2857 p x).map (List.map some) = m2796 p [x] ∧
    (m2858 p x).map (List.map some) = m2796 p [x]

theorem pFindallScalar : PFindallScalar := by
  intro α p x b
  refine ⟨by cases b <;> rfl, ?_, ?_⟩ <;>
  · simp only [m2857, m2858, m2796, mapR]
    cases hp : p x with
    | error e => rfl
    | ok c => cases c <;> rfl

end JuliaLean.MultidimCov.ArrayV2
