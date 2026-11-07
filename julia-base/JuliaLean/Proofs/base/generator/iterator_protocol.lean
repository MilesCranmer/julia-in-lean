import JuliaLean.base.generator

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Iterating from step result `y` with `iterate(itr, s) = nx s` produces
exactly `xs`, then `nothing`. -/
inductive YF (nx : V → Step) : Step → List V → Prop
  | nil : YF nx (.ok none) []
  | cons {x s : V} {xs : List V} : YF nx (nx s) xs → YF nx (.ok (some (x, s))) (x :: xs)

/-- Iterating from `y` produces at least the elements `xs` first, every step
succeeding. -/
inductive PF (nx : V → Step) : Step → List V → Prop
  | nil {y : Step} : PF nx y []
  | cons {x s : V} {xs : List V} : PF nx (nx s) xs → PF nx (.ok (some (x, s))) (x :: xs)

/-- `itr` yields exactly `xs`. -/
def It.Yields (it : It) (xs : List V) : Prop := YF it.next it.first xs

/-- `itr` yields at least `xs` first. -/
def It.Pre (it : It) (xs : List V) : Prop := PF it.next it.first xs

/-- `itr` yields values forever. -/
def It.Endless (it : It) : Prop := ∀ n, ∃ xs : List V, xs.length = n ∧ it.Pre xs

/-- Product of a list of `Int64`s as integers. -/
def prodVals : List JInt64 → Int
  | [] => 1
  | d :: ds => d.val * prodVals ds

/-- `IteratorSize` agrees with the iteration: `HasLength`/`HasShape` promise
a finite iteration whose element count `length` returns, `HasShape{N}`
promises an `N`-dimensional `size` with that many elements, and
`IsInfinite` promises that the iteration never ends (base/generator.jl:69-82). -/
def It.SizeSound (it : It) : Prop :=
  (it.isz.finite = true → ∃ xs, it.Yields xs ∧ xs.length < 2 ^ 63 ∧ it.len = .ok (i64 xs.length)) ∧
  (∀ n, it.isz = .hasShape n → ∃ ds xs, it.size = .ok ds ∧ ds.length = n ∧
    it.Yields xs ∧ prodVals ds = xs.length) ∧
  (it.isz = .isInfinite → it.Endless)

/-- `IteratorEltype` `HasEltype` promises that every element is an `eltype`
(base/generator.jl:110-117). -/
def It.EltSound (it : It) : Prop :=
  it.iel = true → ∀ xs, it.Pre xs → ∀ x ∈ xs, it.elt.mem x

/-- States reachable by iterating from step result `y`. -/
inductive RF (nx : V → Step) : Step → V → Prop
  | here {x s : V} : RF nx (.ok (some (x, s))) s
  | step {y : Step} {s x s' : V} : RF nx y s → nx s = .ok (some (x, s')) → RF nx y s'

/-- `isdone(itr)` agrees with `iterate(itr)` (base/essentials.jl:1574-1591):
`true` means there is no element, `false` that there is one; `missing`
promises nothing. -/
def It.Done0Sound (it : It) : Prop :=
  (it.done0 = .ok (some true) → it.first = .ok none) ∧
  (it.done0 = .ok (some false) → ∃ p, it.first = .ok (some p))

/-- `isdone(itr, s)` agrees with `iterate(itr, s)` on every reachable state. -/
def It.DoneSSound (it : It) : Prop :=
  ∀ s, RF it.next it.first s →
    (it.doneS s = .ok (some true) → it.next s = .ok none) ∧
    (it.doneS s = .ok (some false) → ∃ p, it.next s = .ok (some p))

/-- A vector whose element count fits comfortably in an `Int` (every array in
memory does: 8-byte slots for `2^59` elements exceed the address space). -/
def Fits {α : Type} (xs : List α) : Prop := xs.length < 2 ^ 59

/-! ## Basic lemmas -/

theorem YF.pre {nx : V → Step} {y : Step} {xs : List V} (h : YF nx y xs) :
    ∀ ys, ys <+: xs → PF nx y ys := by
  induction h with
  | nil => intro ys hy; rw [List.prefix_nil.mp hy]; exact .nil
  | @cons x s xs _ ih =>
    intro ys hy
    cases ys with
    | nil => exact .nil
    | cons z zs =>
      obtain ⟨t, ht⟩ := hy
      simp at ht
      obtain ⟨rfl, ht⟩ := ht
      exact .cons (ih zs ⟨t, ht⟩)

theorem YF.unique {nx : V → Step} {y : Step} {xs ys : List V} (h : YF nx y xs)
    (h' : YF nx y ys) : xs = ys := by
  induction h generalizing ys with
  | nil => cases h'; rfl
  | cons _ ih => cases h'; rename_i h''; rw [ih h'']

/-- A prefix of a finite iteration is a prefix of its element list. -/
theorem PF.prefix_of_YF {nx : V → Step} {y : Step} {xs ys : List V}
    (hp : PF nx y ys) (hy : YF nx y xs) : ys <+: xs := by
  induction hp generalizing xs with
  | nil => exact List.nil_prefix
  | cons _ ih =>
    cases hy with
    | cons h => exact List.cons_prefix_cons.mpr ⟨rfl, ih h⟩

theorem i64_val {x : Int} (h0 : -(2 ^ 63) ≤ x) (h1 : x ≤ 2 ^ 63 - 1) : (i64 x).val = x := by
  show wrapInt .i64 x = x
  exact wrapInt_of_inRange .i64 x ⟨by simpa [IntTy.min, IntTy.signed, IntTy.bits] using h0,
    by simpa [IntTy.max, IntTy.signed, IntTy.bits] using h1⟩

theorem i64_nat_val {n : Nat} (h : n < 2 ^ 62) : (i64 n).val = n := i64_val (by omega) (by omega)

/-- Subtraction of `Int64`s that cannot wrap. -/
theorem i64_sub {x y : Int} (hx0 : -(2 ^ 62) ≤ x) (hx1 : x < 2 ^ 62) (hy0 : -(2 ^ 62) ≤ y)
    (hy1 : y < 2 ^ 62) : i64 x - i64 y = i64 (x - y) := by
  apply Subtype.ext
  show wrapInt .i64 ((i64 x).val - (i64 y).val) = (i64 (x - y)).val
  rw [i64_val (by omega) (by omega), i64_val (by omega) (by omega), i64_val (by omega) (by omega)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

/-- Addition of `Int64`s that cannot wrap. -/
theorem i64_add {x y : Int} (hx0 : -(2 ^ 62) ≤ x) (hx1 : x < 2 ^ 62) (hy0 : -(2 ^ 62) ≤ y)
    (hy1 : y < 2 ^ 62) : i64 x + i64 y = i64 (x + y) := by
  apply Subtype.ext
  show wrapInt .i64 ((i64 x).val + (i64 y).val) = (i64 (x + y)).val
  rw [i64_val (by omega) (by omega), i64_val (by omega) (by omega), i64_val (by omega) (by omega)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

theorem i64_lt {x y : Int} (hx0 : -(2 ^ 63) ≤ x) (hx1 : x ≤ 2 ^ 63 - 1) (hy0 : -(2 ^ 63) ≤ y)
    (hy1 : y ≤ 2 ^ 63 - 1) : (i64 x < i64 y) ↔ x < y := by
  show (i64 x).val < (i64 y).val ↔ _
  rw [i64_val hx0 hx1, i64_val hy0 hy1]

theorem i64_le {x y : Int} (hx0 : -(2 ^ 63) ≤ x) (hx1 : x ≤ 2 ^ 63 - 1) (hy0 : -(2 ^ 63) ≤ y)
    (hy1 : y ≤ 2 ^ 63 - 1) : (i64 x ≤ i64 y) ↔ x ≤ y := by
  show (i64 x).val ≤ (i64 y).val ↔ _
  rw [i64_val hx0 hx1, i64_val hy0 hy1]


theorem jmin_i64 {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    jmin (i64 x) (i64 y) = i64 (Nat.min x y : Nat) := by
  unfold jmin
  have h := i64_lt (x := y) (y := x) (by omega) (by omega) (by omega) (by omega)
  split
  · rename_i hlt
    have : y < x := by exact_mod_cast h.mp hlt
    congr 2; simp only [Nat.min_def]; split <;> omega
  · rename_i hlt
    have : ¬ y < x := fun hc => hlt (h.mpr (by exact_mod_cast hc))
    congr 2; simp only [Nat.min_def]; split <;> omega

theorem i64_nat_val' {n : Nat} (h : n < 2 ^ 63) : (i64 n).val = n := i64_val (by omega) (by omega)

/-- `n - 1` on an `Int64` above `typemin`. -/
theorem i64_pred {k : Int} (h0 : -(2 ^ 63) < k) (h1 : k ≤ 2 ^ 63 - 1) : (i64 k - i64 1).val = k - 1 := by
  show wrapInt .i64 ((i64 k).val - (i64 1).val) = k - 1
  rw [i64_val (by omega) h1, i64_val (by omega) (by omega)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

/-- `i + 1` on an `Int64` below `typemax`. -/
theorem i64_succ {k : Int} (h0 : -(2 ^ 63) ≤ k) (h1 : k < 2 ^ 63 - 1) : (i64 k + i64 1).val = k + 1 := by
  show wrapInt .i64 ((i64 k).val + (i64 1).val) = k + 1
  rw [i64_val h0 (by omega), i64_val (by omega) (by omega)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

end JuliaLean.IteratorsCov
