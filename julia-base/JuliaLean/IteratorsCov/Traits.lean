import JuliaLean.IteratorsCov.Base

/-!
# Iterator-size and eltype trait algebra of `base/iterators.jl`

The helpers combine the `IteratorSize` of the component iterators of `zip`
and `product`, and compute `length(take(..))`/`length(drop(..))`. Their
properties are stated against the true element count of an iterator, `Len`
(`fin n` elements, or `inf`inite): an `IteratorSize` value *agrees* with a
count when `HasLength`/`HasShape` go with finite counts and `IsInfinite` with
infinite ones (base/generator.jl:69-82).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- The true number of elements of an iterator. -/
inductive Len where
  | fin (n : Nat)
  | inf
  deriving Repr, DecidableEq, Inhabited

/-- `IteratorSize` value `a` is truthful for an iterator with `l` elements. -/
def Agree : Isz → Len → Prop
  | .hasLength, .fin _ => True
  | .hasShape _, .fin _ => True
  | .isInfinite, .inf => True
  | .sizeUnknown, _ => True
  | _, _ => False

theorem agree_fin {a : Isz} (h : a.finite = true) (n : Nat) : Agree a (.fin n) := by
  cases a <;> simp_all [Isz.finite, Agree]

theorem agree_su (l : Len) : Agree .sizeUnknown l := by cases l <;> trivial

/-- Element count of `zip`: the shortest component. -/
def Len.min : Len → Len → Len
  | .fin a, .fin b => .fin (Nat.min a b)
  | .fin a, .inf => .fin a
  | .inf, l => l

/-- Element count of `zip(is...)` (`inf` for no components). -/
def zipLen : List Len → Len
  | [] => .inf
  | l :: ls => Len.min l (zipLen ls)

/-- Element count of a product of two factors: empty as soon as one factor is. -/
def Len.mul : Len → Len → Len
  | .fin a, .fin b => .fin (a * b)
  | .fin a, .inf => if a = 0 then .fin 0 else .inf
  | .inf, .fin b => if b = 0 then .fin 0 else .inf
  | .inf, .inf => .inf

/-- Element count of `product(is...)`. -/
def prodLen : List Len → Len
  | [] => .fin 1
  | l :: ls => Len.mul l (prodLen ls)

/-- Pointwise agreement of component traits with component counts. -/
def AgreeAll : List Isz → List Len → Prop
  | [], [] => True
  | a :: as, l :: ls => Agree a l ∧ AgreeAll as ls
  | _, _ => False

/-! ## `and_iteratorsize`, `and_iteratoreltype` -/

/-- `and_iteratorsize`, base/iterators.jl:71-76: equal traits are returned
(`(isz::T, ::T)`, line 71, and `HasShape{N}`, line 74), mixed `HasLength` /
`HasShape` and `HasShape`s of different `N` give `HasLength` (72, 73, 75),
everything else `SizeUnknown()` (76). -/
def andIsz : Isz → Isz → Isz
  | .hasShape m, .hasShape n => if m = n then .hasShape n else .hasLength
  | .hasLength, .hasLength => .hasLength
  | .sizeUnknown, .sizeUnknown => .sizeUnknown
  | .isInfinite, .isInfinite => .isInfinite
  | .hasLength, .hasShape _ => .hasLength
  | .hasShape _, .hasLength => .hasLength
  | _, _ => .sizeUnknown

/-- `and_iteratoreltype`, base/iterators.jl:78-79 (`true` is `HasEltype()`). -/
def andIel (a b : Bool) : Bool := if a = b then a else false

/-- `and_iteratorsize(a, b)` promises a length exactly when both arguments
do, the shape `HasShape{N}` exactly when both have it, `IsInfinite` exactly
when both are, and is symmetric; `and_iteratoreltype` is `HasEltype` exactly
when both are. -/
def AndTraitsSpec : Prop :=
  (∀ a b : Isz, andIsz a b = andIsz b a) ∧
  (∀ a b : Isz, (andIsz a b).finite = (a.finite && b.finite)) ∧
  (∀ (a b : Isz) (n : Nat), andIsz a b = .hasShape n ↔ a = .hasShape n ∧ b = .hasShape n) ∧
  (∀ a b : Isz, andIsz a b = .isInfinite ↔ a = .isInfinite ∧ b = .isInfinite) ∧
  (∀ a b : Bool, andIel a b = (a && b))

theorem andIsz_shape (m n : Nat) :
    andIsz (.hasShape m) (.hasShape n) = if m = n then .hasShape n else .hasLength := rfl

theorem andTraitsSpec : AndTraitsSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> try rfl
    rename_i m n
    rw [andIsz_shape, andIsz_shape]
    by_cases h : m = n
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro a b
    cases a <;> cases b <;> try rfl
    rename_i m n
    rw [andIsz_shape]; split <;> rfl
  · intro a b n
    cases a <;> cases b <;> simp [andIsz]
    rename_i p q
    by_cases h : p = q
    · subst h; simp
    · simp [h]; omega
  · intro a b
    cases a <;> cases b <;> simp [andIsz]
    rename_i p q
    split <;> simp
  · intro a b
    cases a <;> cases b <;> rfl

/-! ## `zip_iteratorsize`, `zip_iteratoreltype` -/

/-- `zip_iteratorsize(a, b)`, base/iterators.jl:508-512. -/
def zipIsz2 : Isz → Isz → Isz
  | .isInfinite, .isInfinite => .isInfinite          -- 512
  | .hasLength, .isInfinite => .hasLength            -- 509
  | .hasShape _, .isInfinite => .hasLength           -- 510
  | .isInfinite, b =>                                -- 511: zip_iteratorsize(b, a)
    match b with
    | .hasLength => .hasLength
    | .hasShape _ => .hasLength
    | _ => andIsz b .isInfinite
  | a, b => andIsz a b                               -- 508

/-- `zip_iteratorsize(...)`, base/iterators.jl:506-507, 513. -/
def zipIsz : List Isz → Isz
  | [] => .isInfinite                                -- 506
  | [a] => a                                         -- 507
  | a :: b :: rest => zipIsz2 a (zipIsz (b :: rest)) -- 513

/-- `zip_iteratoreltype(...)`, base/iterators.jl:515-517. -/
def zipIel : List Bool → Bool
  | [] => true                                       -- 515
  | [a] => a                                         -- 516
  | a :: b :: rest => andIel a (zipIel (b :: rest))  -- 517

/-- `IteratorSize(Zip{Is})`, base/iterators.jl:503: `zip_iteratorsize` of the
component traits. -/
def zipTypeIsz (cs : List Isz) : Isz := zipIsz cs

/-- `IteratorEltype(Zip{Is})`, base/iterators.jl:504. -/
def zipTypeIel (cs : List Bool) : Bool := zipIel cs

/-- `IteratorSize(zip(is...))` agrees with the number of elements `zip`
yields, the shortest component's count, whenever the components' own
`IteratorSize` values agree with theirs; `IteratorEltype(zip(is...))` is
`HasEltype` exactly when every component's is. -/
def ZipTraitsSound : Prop :=
  (∀ (cs : List Isz) (ls : List Len), AgreeAll cs ls → Agree (zipTypeIsz cs) (zipLen ls)) ∧
  (∀ cs : List Bool, zipTypeIel cs = cs.all id)

theorem agree_of (c : Isz) (l : Len) (hf : c.finite = true → ∃ n, l = .fin n)
    (hi : c = .isInfinite → l = .inf) : Agree c l := by
  cases c <;> cases l <;> simp_all [Agree, Isz.finite]

theorem agree_fin_inv {a : Isz} {l : Len} (h : Agree a l) (hf : a.finite = true) : ∃ n, l = .fin n := by
  cases a <;> cases l <;> simp_all [Agree, Isz.finite]

theorem agree_inf_inv {l : Len} (h : Agree .isInfinite l) : l = .inf := by
  cases l <;> simp_all [Agree]

theorem agree_andIsz (a b : Isz) (la lb : Len) (ha : Agree a la) (hb : Agree b lb) :
    Agree (andIsz a b) (Len.min la lb) := by
  obtain ⟨_, hfin, _, hinf, _⟩ := andTraitsSpec
  apply agree_of
  · intro hf
    rw [hfin] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨m, rfl⟩ := agree_fin_inv ha hf.1
    obtain ⟨n, rfl⟩ := agree_fin_inv hb hf.2
    exact ⟨_, rfl⟩
  · intro hi
    obtain ⟨h1, h2⟩ := (hinf a b).mp hi
    subst h1; subst h2
    rw [agree_inf_inv ha, agree_inf_inv hb]; rfl

theorem agree_zipIsz2 (a b : Isz) (la lb : Len) (ha : Agree a la) (hb : Agree b lb) :
    Agree (zipIsz2 a b) (Len.min la lb) := by
  cases a <;> cases b
  all_goals first
    | exact agree_andIsz _ _ _ _ ha hb
    | (cases la <;> cases lb <;> simp_all [zipIsz2, Agree, Len.min, andIsz])

theorem zipTraitsSound : ZipTraitsSound := by
  constructor
  · intro cs
    induction cs with
    | nil => intro ls h; cases ls with
      | nil => trivial
      | cons => exact absurd h id
    | cons a as ih =>
      intro ls h
      cases ls with
      | nil => exact absurd h id
      | cons l ls =>
        obtain ⟨ha, hs⟩ := h
        cases as with
        | nil =>
          cases ls with
          | nil =>
            show Agree a (Len.min l .inf)
            cases l <;> exact ha
          | cons => exact absurd hs id
        | cons b bs =>
          exact agree_zipIsz2 a _ l _ ha (ih ls hs)
  · intro cs
    induction cs with
    | nil => rfl
    | cons a as ih =>
      cases as with
      | nil => cases a <;> rfl
      | cons b bs =>
        show andIel a (zipIel (b :: bs)) = (a && (b :: bs).all id)
        rw [show zipIel (b :: bs) = zipTypeIel (b :: bs) from rfl, ih]
        generalize (b :: bs).all id = r
        cases a <;> cases r <;> rfl

/-! ## `prod_iteratorsize` -/

/-- `prod_iteratorsize(a, b)`, base/iterators.jl:1157-1166. -/
def prodIsz2 : Isz → Isz → Isz
  | .hasLength, .hasLength => .hasShape 2            -- 1157
  | .hasLength, .hasShape n => .hasShape (n + 1)     -- 1158
  | .hasShape n, .hasLength => .hasShape (n + 1)     -- 1159
  | .hasShape m, .hasShape n => .hasShape (m + n)    -- 1160
  | .isInfinite, .isInfinite => .isInfinite          -- 1163
  | _, .isInfinite => .isInfinite                    -- 1164
  | .isInfinite, _ => .isInfinite                    -- 1165
  | _, _ => .sizeUnknown                             -- 1166

/-- `prod_iteratorsize(...)`, base/iterators.jl:1154-1155, 1167. -/
def prodIsz : List Isz → Isz
  | [] => .hasShape 0                                -- 1154
  | [a] => a                                         -- 1155
  | a :: b :: rest => prodIsz2 a (prodIsz (b :: rest)) -- 1167

/-- `IteratorSize(ProductIterator{T})`, base/iterators.jl:1150-1152:
`HasShape{0}()` for no factors, otherwise `prod_iteratorsize` of the factor
traits followed by `HasShape{0}()`. -/
def productIsz (cs : List Isz) : Isz :=
  match cs with
  | [] => .hasShape 0
  | _ => prodIsz (cs ++ [.hasShape 0])

/-- Number of dimensions an iterator contributes to a product: `N` for
`HasShape{N}`, one for `HasLength`. -/
def Isz.dims : Isz → Nat
  | .hasShape n => n
  | _ => 1

theorem prodIsz_cons (a : Isz) (l : List Isz) (h : l ≠ []) :
    prodIsz (a :: l) = prodIsz2 a (prodIsz l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons => rfl

theorem productIsz_cons (a : Isz) (l : List Isz) :
    productIsz (a :: l) = prodIsz (a :: l ++ [.hasShape 0]) := rfl

/-- `IteratorSize(product(is...))` agrees with the number of elements the
product yields (the product of the factor counts, zero as soon as a factor is
empty) whenever every factor's `IteratorSize` agrees with its count. -/
def ProductSizeSound : Prop :=
  ∀ (cs : List Isz) (ls : List Len), AgreeAll cs ls → Agree (productIsz cs) (prodLen ls)

/-- `Iterators.product(1:0, Iterators.countfrom())` is empty, yet its
`IteratorSize` is `IsInfinite()`. -/
theorem productSizeSound_refuted : ¬ ProductSizeSound := by
  intro h
  exact h [.hasShape 1, .isInfinite] [.fin 0, .inf] ⟨trivial, trivial, trivial⟩

/-- When no factor is infinite, `IteratorSize(product(is...))` agrees with the
product's element count, and when every factor promises a length it is
`HasShape{N}` with `N` the sum of the factors' dimensions. -/
def ProductShapeFinite : Prop :=
  (∀ (cs : List Isz) (ls : List Len), AgreeAll cs ls → (∀ c ∈ cs, c ≠ .isInfinite) →
    Agree (productIsz cs) (prodLen ls)) ∧
  (∀ cs : List Isz, (∀ c ∈ cs, c.finite = true) →
    productIsz cs = .hasShape (cs.map Isz.dims).sum)

theorem prodIsz_append_finite (cs : List Isz) (hc : ∀ c ∈ cs, c.finite = true) :
    prodIsz (cs ++ [.hasShape 0]) = .hasShape (cs.map Isz.dims).sum := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
    rw [List.cons_append, prodIsz_cons _ _ (by simp),
      ih (fun c h => hc c (List.mem_cons_of_mem _ h))]
    have ha := hc a (List.mem_cons_self ..)
    cases a <;> simp_all [Isz.finite, prodIsz2, Isz.dims] <;> omega

theorem agree_prodIsz2 (a p : Isz) (l q : Len) (ha : Agree a l) (hp : Agree p q)
    (ha' : a ≠ .isInfinite) (hp' : p ≠ .isInfinite) :
    Agree (prodIsz2 a p) (Len.mul l q) ∧ prodIsz2 a p ≠ .isInfinite := by
  cases a <;> cases p <;> cases l <;> cases q <;> simp_all [prodIsz2, Agree, Len.mul] <;>
    (split <;> trivial)

theorem prodIsz_append_noinf (cs : List Isz) (ls : List Len) (h : AgreeAll cs ls)
    (hc : ∀ c ∈ cs, c ≠ .isInfinite) :
    Agree (prodIsz (cs ++ [.hasShape 0])) (prodLen ls) ∧
      prodIsz (cs ++ [.hasShape 0]) ≠ .isInfinite := by
  induction cs generalizing ls with
  | nil => cases ls with
    | nil => exact ⟨trivial, by simp [prodIsz]⟩
    | cons => exact absurd h id
  | cons a as ih =>
    cases ls with
    | nil => exact absurd h id
    | cons l ls =>
      obtain ⟨ha, hs⟩ := h
      obtain ⟨ih1, ih2⟩ := ih ls hs (fun c h => hc c (List.mem_cons_of_mem _ h))
      rw [List.cons_append, prodIsz_cons _ _ (by simp)]
      exact agree_prodIsz2 a _ l _ ha ih1 (hc a (List.mem_cons_self ..)) ih2

theorem productShapeFinite : ProductShapeFinite := by
  constructor
  · intro cs ls h hc
    cases cs with
    | nil => cases ls with
      | nil => trivial
      | cons => exact absurd h id
    | cons a as =>
      rw [productIsz_cons]
      exact (prodIsz_append_noinf (a :: as) ls h hc).1
  · intro cs hc
    cases cs with
    | nil => rfl
    | cons a as => rw [productIsz_cons]; exact prodIsz_append_finite _ hc

/-! ## `IteratorEltype(ProductIterator)` -/

/-- `IteratorEltype(ProductIterator{T})`, base/iterators.jl:1188-1195:
`HasEltype` for no factors (1188), the factor's trait for one factor (1189),
otherwise `EltypeUnknown` if any factor's is, else the last factor's trait
(1191-1195). -/
def productIel (cs : List Bool) : Bool :=
  match cs with
  | [] => true
  | [c] => c
  | _ => if cs.contains false then false else cs.getLastD true

/-- `IteratorEltype(product(is...))` is `HasEltype` exactly when every
factor's is. -/
def ProductIelSpec : Prop := ∀ cs : List Bool, productIel cs = cs.all id

theorem productIelSpec : ProductIelSpec := by
  intro cs
  match cs with
  | [] => rfl
  | [c] => cases c <;> rfl
  | a :: b :: rest =>
    show (if (a :: b :: rest).contains false then false else (a :: b :: rest).getLastD true) = _
    by_cases h : (a :: b :: rest).contains false = true
    · rw [if_pos h]
      have hm : false ∈ a :: b :: rest := by simpa using h
      symm
      rw [List.all_eq_false]
      exact ⟨false, hm, by simp⟩
    · rw [if_neg h]
      have hall : ∀ x ∈ a :: b :: rest, x = true := by
        intro x hx
        cases x
        · exact absurd (by simpa using hx) h
        · rfl
      have hl : (a :: b :: rest).getLastD true = (a :: b :: rest).getLast (by simp) := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (by simp)]; rfl
      rw [hl, hall _ (List.getLast_mem _)]
      symm; exact List.all_eq_true.mpr (fun x hx => by simpa using hall x hx)

/-! ## `_min_length`, `_diff_length` -/

/-- `_min_length(a, b, A, B)`, base/iterators.jl:58-61, given the two
`length` calls and the two `IteratorSize` traits. -/
def minLength (la lb : R JInt64) : Isz → Isz → R JInt64
  | .isInfinite, .isInfinite => do let x ← la; let y ← lb; pure (jmin x y) -- 58
  | _, .isInfinite => la                                               -- 59
  | .isInfinite, _ => lb                                               -- 60
  | _, _ => do let x ← la; let y ← lb; pure (jmin x y)                  -- 61

/-- `_diff_length(a, b, A, B)`, base/iterators.jl:63-69. -/
def diffLength (la lb : R JInt64) : Isz → Isz → R JInt64
  | _, .isInfinite => pure (i64 0)                                     -- 63, 64
  | .isInfinite, _ => la                                               -- 65
  | _, _ => do                                                         -- 66-69
    let m ← la
    let n ← lb
    pure (if m > n then m - n else i64 0)

/-- An iterator with trait `A`, `length` result `la` and true count `l`:
the trait agrees with the count, and a promised length is the count. -/
def Counted (A : Isz) (la : R JInt64) (l : Len) : Prop :=
  Agree A l ∧ ∀ n, l = .fin n → A.finite = true → n < 2 ^ 62 ∧ la = .ok (i64 n)

/-- `_min_length(a, b, ...)` is the length of the shorter of `a` and `b`
(`zip`/`take` semantics), and `_diff_length(a, b, ...)` the number of
elements of `a` left after `b`'s count (`drop` semantics), whenever the
result is finite and the traits promise the lengths involved. -/
def LengthHelpersSpec : Prop :=
  ∀ (A B : Isz) (la lb : R JInt64) (a b : Len), Counted A la a → Counted B lb b →
    (∀ n, Len.min a b = .fin n → (A.finite = true ∨ A = .isInfinite) →
      (B.finite = true ∨ B = .isInfinite) → minLength la lb A B = .ok (i64 n)) ∧
    (∀ m n, a = .fin m → b = .fin n → A.finite = true → B.finite = true →
      diffLength la lb A B = .ok (i64 (m - n : Nat))) ∧
    (B = .isInfinite → diffLength la lb A B = .ok (i64 0))

theorem Counted.finLen {A : Isz} {la : R JInt64} {l : Len} (h : Counted A la l)
    (hA : A.finite = true) : ∃ n, l = .fin n ∧ n < 2 ^ 62 ∧ la = .ok (i64 n) := by
  obtain ⟨hag, hl⟩ := h
  cases l with
  | inf => cases A <;> simp_all [Agree, Isz.finite]
  | fin n => exact ⟨n, rfl, hl n rfl hA⟩

theorem Counted.infLen {A : Isz} {la : R JInt64} {l : Len} (h : Counted A la l)
    (hA : A = .isInfinite) : l = .inf := by
  obtain ⟨hag, _⟩ := h
  subst hA
  cases l with
  | inf => rfl
  | fin => exact absurd hag id

theorem minLength_ff {A B : Isz} (la lb : R JInt64) (hA : A.finite = true) (hB : B.finite = true) :
    minLength la lb A B = (do let x ← la; let y ← lb; pure (jmin x y)) := by
  cases A <;> cases B <;> simp_all [Isz.finite] <;> rfl

theorem minLength_fi {A : Isz} (la lb : R JInt64) (hA : A.finite = true) :
    minLength la lb A .isInfinite = la := by
  cases A <;> simp_all [Isz.finite] <;> rfl

theorem minLength_if {B : Isz} (la lb : R JInt64) (hB : B.finite = true) :
    minLength la lb .isInfinite B = lb := by
  cases B <;> simp_all [Isz.finite] <;> rfl

theorem diffLength_ff {A B : Isz} (la lb : R JInt64) (hA : A.finite = true) (hB : B.finite = true) :
    diffLength la lb A B = (do let m ← la; let n ← lb; pure (if m > n then m - n else i64 0)) := by
  cases A <;> cases B <;> simp_all [Isz.finite] <;> rfl

theorem lengthHelpersSpec : LengthHelpersSpec := by
  intro A B la lb a b hA hB
  refine ⟨?_, ?_, ?_⟩
  · intro n hmin hAf hBf
    rcases hAf with hAf | hAi <;> rcases hBf with hBf | hBi
    · obtain ⟨x, rfl, hx, rfl⟩ := hA.finLen hAf
      obtain ⟨y, rfl, hy, rfl⟩ := hB.finLen hBf
      rw [minLength_ff _ _ hAf hBf]
      simp only [Len.min, Len.fin.injEq] at hmin
      subst hmin
      show Except.ok (jmin (i64 x) (i64 y)) = _
      rw [jmin_i64 (by omega) (by omega)]
    · obtain ⟨x, rfl, hx, rfl⟩ := hA.finLen hAf
      rw [hB.infLen hBi] at hmin
      subst hBi
      rw [minLength_fi _ _ hAf]
      simp only [Len.min, Len.fin.injEq] at hmin
      rw [hmin]
    · obtain ⟨y, rfl, hy, rfl⟩ := hB.finLen hBf
      rw [hA.infLen hAi] at hmin
      subst hAi
      rw [minLength_if _ _ hBf]
      simp only [Len.min, Len.fin.injEq] at hmin
      rw [hmin]
    · rw [hA.infLen hAi, hB.infLen hBi] at hmin
      cases hmin
  · intro m n hm hn hAf hBf
    subst hm; subst hn
    obtain ⟨hx, hla⟩ := (hA.2 m rfl hAf)
    obtain ⟨hy, hlb⟩ := (hB.2 n rfl hBf)
    rw [diffLength_ff _ _ hAf hBf, hla, hlb]
    show Except.ok (if i64 n < i64 m then i64 m - i64 n else i64 0) = _
    have hlt := i64_lt (x := n) (y := m) (by omega) (by omega) (by omega) (by omega)
    split
    · rename_i h
      have : n < m := by exact_mod_cast hlt.mp h
      rw [i64_sub (by omega) (by omega) (by omega) (by omega)]
      congr 2
      omega
    · rename_i h
      have : ¬ n < m := fun hc => h (hlt.mpr (by exact_mod_cast hc))
      have : m - n = 0 := by omega
      rw [this]; rfl
  · intro hB
    subst hB
    cases A <;> rfl

end JuliaLean.IteratorsCov
