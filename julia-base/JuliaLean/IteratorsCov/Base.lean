import JuliaLean.Core

/-!
# Shared model for the method coverage of `base/iterators.jl`,
`base/generator.jl`, `base/anyall.jl` and `base/simdloop.jl` (master `bbfa0ce4150`)

A Julia iterator is an `It`: the two `iterate` methods (`first` is
`iterate(itr)`, `next s` is `iterate(itr, s)`), the type-level traits
(`IteratorSize`, `IteratorEltype`, `eltype` of `typeof(itr)`), `length`,
`size` and the two `isdone` methods. Iteration states are Julia values (`V`),
exactly as Julia's states are ordinary objects such as `(n, inner_state)`.
Wrappers (`Take`, `Zip`, ...) are functions `It → It` whose fields mirror the
Julia methods of the wrapper type.

`Yields it xs`: iterating `it` produces exactly `xs` and then `nothing`.
`Pre it xs`: `xs` is a prefix of what `it` produces (all steps succeed).
`Endless it`: `it` produces arbitrarily many elements.

Julia exceptions are `E.jl`; `E.typeError` is `TypeError` (a non-`Bool` in a
boolean context or a failed type assertion), `E.eof` is `EOFError`, and
`E.fuel` is the model-only result of a loop bound being reached (never a
Julia result).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Julia values. Iteration states are values too. `vec` is a `Vector`,
`tup` a `Tuple`, `pair k v` is `k => v`, `str s` a `String` (as its
characters), `obj n` any other object. -/
inductive V where
  | int (x : Int)
  | bool (b : Bool)
  | missing
  | nothing
  | sym (s : String)
  | chr (c : Nat)
  | tup (vs : List V)
  | vec (vs : List V)
  | pair (k v : V)
  | obj (n : Nat)
  deriving Repr, Inhabited

/-- Julia exceptions, plus the model-only `fuel`. -/
inductive E where
  | jl (e : JlError)
  | typeError
  | eof
  | simdError (msg : String)
  | dimensionMismatch
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except E α

/-- `throw(e)` for a Julia exception. -/
def jthrow {α : Type} (e : JlError) : R α := .error (.jl e)

/-- The result of one `iterate` call: `nothing` or `(value, state)`. -/
abbrev Step := R (Option (V × V))

/-- `Int64` literal. -/
abbrev i64 (x : Int) : JInt64 := JInt.lit .i64 x

/-- `Base.IteratorSize` values, base/generator.jl:63-67. -/
inductive Isz where
  | sizeUnknown
  | hasLength
  | hasShape (n : Nat)
  | isInfinite
  deriving Repr, DecidableEq, Inhabited

/-- `HasLength` or `HasShape`: a length is promised. -/
def Isz.finite : Isz → Bool
  | .hasLength | .hasShape _ => true
  | _ => false

/-- The part of a Julia type the iterator methods inspect: `tuple ts` is
`Tuple{ts...}`, `vararg t` is `Tuple{Vararg{t}}`, `vector t` is `Vector{t}`,
`pair k v` is `Pair{k, v}`, `bottom` is `Union{}`, `union a b` is
`Union{a, b}`, `char` is `Char`. -/
inductive Ty where
  | any
  | bottom
  | int
  | bool
  | missing
  | nothing
  | sym
  | char
  | obj
  | tuple (ts : List Ty)
  | vararg (t : Ty)
  | vector (t : Ty)
  | pair (k v : Ty)
  | union (a b : Ty)
  deriving Repr, Inhabited

mutual
/-- `v isa T`. -/
def Ty.mem : Ty → V → Prop
  | .any, _ => True
  | .bottom, _ => False
  | .int, v => ∃ x, v = .int x
  | .bool, v => ∃ b, v = .bool b
  | .missing, v => v = .missing
  | .nothing, v => v = .nothing
  | .sym, v => ∃ s, v = .sym s
  | .char, v => ∃ c, v = .chr c
  | .obj, v => ∃ n, v = .obj n
  | .tuple ts, v => ∃ vs, v = .tup vs ∧ Ty.memList ts vs
  | .vararg t, v => ∃ vs, v = .tup vs ∧ ∀ x ∈ vs, t.mem x
  | .vector t, v => ∃ vs, v = .vec vs ∧ ∀ x ∈ vs, t.mem x
  | .pair k w, v => ∃ a b, v = .pair a b ∧ k.mem a ∧ w.mem b
  | .union a b, v => a.mem v ∨ b.mem v
/-- Componentwise `isa` for tuple fields. -/
def Ty.memList : List Ty → List V → Prop
  | [], [] => True
  | t :: ts, v :: vs => t.mem v ∧ Ty.memList ts vs
  | _, _ => False
end

/-- A Julia iterator object as seen through its methods. The defaults are
Julia's fallbacks: `IteratorSize` `HasLength()`, `IteratorEltype`
`HasEltype()`, `eltype` `Any`, `isdone` `missing` (base/essentials.jl), and a
`MethodError` for `length` and `size`. -/
structure It where
  /-- `iterate(itr)`. -/
  first : Step
  /-- `iterate(itr, s)`. -/
  next : V → Step
  /-- `IteratorSize(typeof(itr))`. -/
  isz : Isz := .hasLength
  /-- `IteratorEltype(typeof(itr)) === HasEltype()`. -/
  iel : Bool := true
  /-- `eltype(typeof(itr))`. -/
  elt : Ty := .any
  /-- `length(itr)`. -/
  len : R JInt64 := jthrow (.methodError "length")
  /-- `size(itr)`. -/
  size : R (List JInt64) := jthrow (.methodError "size")
  /-- `isdone(itr)`; `none` is `missing`. -/
  done0 : R (Option Bool) := .ok none
  /-- `isdone(itr, s)`; `none` is `missing`. -/
  doneS : V → R (Option Bool) := fun _ => .ok none
  /-- `last(itr)`. -/
  lastv : R V := jthrow (.methodError "last")

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

/-- `min(x, y)` on `Int`: `ifelse(y < x, y, x)` (base/promotion.jl). -/
def jmin (x y : JInt64) : JInt64 := if y < x then y else x

/-- `max(x, y)` on `Int`: `ifelse(y < x, x, y)` (base/promotion.jl). -/
def jmax (x y : JInt64) : JInt64 := if y < x then x else y

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
