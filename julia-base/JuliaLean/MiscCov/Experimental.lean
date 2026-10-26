import JuliaLean.MiscCov.Basic
import JuliaLean.IntArith.Checked

/-!
# `base/experimental.jl` (master `bbfa0ce4150`)

Macros are functions from their argument syntax (`Ex`) to the expansion or the
exception thrown during expansion. A macro defined only for an `n::Int` argument
throws `MethodError` for any other argument. Runtime state that the methods read or
write through `ccall`s is an explicit record.
-/

namespace JuliaLean.MiscCov.Experimental

open JuliaLean

/-! ## `Const` -/

/-- `Const(A::Array)`: the wrapped array, as its dimensions and column-major elements. -/
structure Const (V : Type) where
  dims : List Nat
  elems : List V

variable {V : Type}

/-- `Base.IndexStyle(::Type{<:Const}) = IndexLinear()`, `base/experimental.jl:29`. -/
def indexStyleLinear : Bool := true

/-- `Base.size(C::Const) = size(C.a)` and `Base.axes(C::Const) = axes(C.a)` (`:30-31`):
the sizes and the ranges `1:n`, here by their lengths. -/
def size (C : Const V) : List Nat := C.dims
def axes (C : Const V) : List (Nat × Nat) := C.dims.map (fun n => (1, n))

/-- `getindex(A::Const, i::Int)`, `base/experimental.jl:32-36`: `checkbounds(A.a, i)`
under `@boundscheck`, then the unchecked load of element `i`. -/
def getindex1 (A : Const V) (i : Int) : M V :=
  if 1 ≤ i ∧ i ≤ A.elems.length then
    match A.elems[(i - 1).toNat]? with
    | some v => .ok v
    | none => .error .boundsError
  else .error .boundsError

/-- `_to_linear_index(A.a, i1, i2, I...)`: the column-major linear index of `(i1, i2, I...)`
in an array of size `dims`,
`1 + Σ (i_k - 1) * prod(dims[1:k-1])`. -/
def linearIndex : List Nat → List Int → Int
  | _, [] => 1
  | [], i :: _ => i
  | d :: ds, i :: is => i + d * (linearIndex ds is - 1)

/-- `checkbounds(A.a, i1, i2, I...)`: every index within its dimension (trailing
dimensions are 1, trailing indices must be 1). -/
def inBounds : List Nat → List Int → Bool
  | _, [] => true
  | [], i :: is => i == 1 && inBounds [] is
  | d :: ds, i :: is => decide (1 ≤ i ∧ i ≤ d) && inBounds ds is

/-- `getindex(A::Const, i1::Int, i2::Int, I::Int...)`, `base/experimental.jl:37-41`:
bounds check, then `A[_to_linear_index(A.a, i1, i2, I...)]`. -/
def getindexN (A : Const V) (i1 i2 : Int) (I : List Int) : M V :=
  if inBounds A.dims (i1 :: i2 :: I) then getindex1 A (linearIndex A.dims (i1 :: i2 :: I))
  else .error .boundsError

/-- `Const` indexes like its array: linear indexing returns element `i` exactly when
`1 ≤ i ≤ length`, otherwise `BoundsError`; Cartesian indexing returns the
column-major element when every index is in its dimension and the array has
`prod(dims)` elements. -/
def ConstIndexing : Prop :=
  indexStyleLinear = true ∧
  (∀ (A : Const V), size A = A.dims ∧ (axes A).map (·.2) = A.dims) ∧
  (∀ (A : Const V) (i : Int), 1 ≤ i → i ≤ A.elems.length → ∃ v, getindex1 A i = .ok v ∧ A.elems[(i - 1).toNat]? = some v) ∧
  (∀ (A : Const V) (i : Int), (i < 1 ∨ A.elems.length < i) → getindex1 A i = .error .boundsError) ∧
  (∀ (A : Const V) (i j : Int) (m n : Nat), A.dims = [m, n] → A.elems.length = m * n →
    1 ≤ i → i ≤ m → 1 ≤ j → j ≤ n →
    getindexN A i j [] = getindex1 A (i + m * (j - 1))) ∧
  (∀ (A : Const V) (i1 i2 : Int) (I : List Int), inBounds A.dims (i1 :: i2 :: I) = false →
    getindexN A i1 i2 I = .error .boundsError)

theorem constIndexing_proven : @ConstIndexing V := by
  refine ⟨rfl, fun A => ⟨rfl, by simp [axes, Function.comp_def]⟩, ?_, ?_, ?_, ?_⟩
  · intro A i h1 h2
    have hlt : (i - 1).toNat < A.elems.length := by omega
    refine ⟨A.elems[(i - 1).toNat], ?_, by simp [hlt]⟩
    simp only [getindex1, h1, h2, and_self, ↓reduceIte]
    rw [List.getElem?_eq_getElem hlt]
  · intro A i h
    simp only [getindex1]
    rw [if_neg (by omega)]
  · intro A i j m n hd hl hi1 hi2 hj1 hj2
    simp only [getindexN, hd, inBounds, linearIndex]
    have : (decide (1 ≤ i ∧ i ≤ (m : Int)) && (decide (1 ≤ j ∧ j ≤ (n : Int)) && true)) = true := by
      simp [hi1, hi2, hj1, hj2]
    rw [if_pos this]
    congr 1
    simp
  · intro A i1 i2 I h
    simp [getindexN, h]

/-! ## Expression macros -/

/-- `@aliasscope body`, `base/experimental.jl:52-60`. -/
def aliasscope (body : Ex) : Ex :=
  .expr "block" [.expr "aliasscope" [], .expr "=" [.sym "aliasscope_result", Ex.esc body],
    .expr "popaliasscope" [], .sym "aliasscope_result"]

/-- `@optlevel n::Int`, `base/experimental.jl:158-160`: no range check. -/
def optlevel (n : Ex) : M Ex :=
  match n with
  | .int k => .ok (.expr "meta" [.sym "optlevel", .int k])
  | _ => .error .methodError

/-- `@max_methods n::Int`, `base/experimental.jl:180-183`. -/
def maxMethods1 (n : Ex) : M Ex :=
  match n with
  | .int k =>
    if 1 ≤ k ∧ k ≤ 4 then .ok (.expr "meta" [.sym "max_methods", .int k])
    else .error (.errorException "We must have that `1 <= max_methods <= 4`")
  | _ => .error .methodError

/-- `@max_methods n::Int fdef::Expr`, `base/experimental.jl:193-197`. -/
def maxMethods2 (n fdef : Ex) : M Ex :=
  match n, fdef with
  | .int k, .expr hd args =>
    if ¬ (1 ≤ k ∧ k ≤ 255) then .error (.errorException "We must have that `1 <= max_methods <= 255`")
    else if ¬ (hd = "function" ∧ args.length = 1) then
      .error (.errorException "Second argument must be a function forward declaration")
    else .ok (.expr "=" [.expr "." [.expr "." [.expr "call" [.sym "typeof", Ex.esc (.expr hd args)],
        .qn (.sym "name")], .qn (.sym "max_methods")], .val s!"UInt8({k})"])
  | _, _ => .error .methodError

/-- The value the docstring of `@max_methods n` promises for each supported value:
"Supported values are `1`, `2`, `3`, `4`, and `default` (currently equivalent to `3`)". -/
def supportedMaxMethods : List (Ex × Int) :=
  [(.int 1, 1), (.int 2, 2), (.int 3, 3), (.int 4, 4), (.sym "default", 3)]

/-- The docstring of `@max_methods n` (`base/experimental.jl:162-179`): every supported
value expands to `Expr(:meta, :max_methods, value)`. -/
def MaxMethodsDoc : Prop :=
  ∀ v k, (v, k) ∈ supportedMaxMethods → maxMethods1 v = .ok (.expr "meta" [.sym "max_methods", .int k])

theorem maxMethodsDoc_refuted : ¬ MaxMethodsDoc := by
  intro h
  have := h (.sym "default") 3 (by simp [supportedMaxMethods])
  simp [maxMethods1] at this

/-- `@compiler_options args...`, `base/experimental.jl:212-244`. -/
def compilerOption (ex : Ex) : M Ex :=
  match ex with
  | .expr "=" [.sym name, a] =>
    if name = "optimize" then
      match a with
      | .int k => .ok (.expr "meta" [.sym "optlevel", .int k])
      | _ => .error .typeError
    else if name = "compile" then
      if a.isSym "min" then .ok (.expr "meta" [.sym "compile", .int 3])
      else .error (.errorException "invalid argument to \"compile\" option")
    else if name = "infer" then
      match a with
      | .bool false => .ok (.expr "meta" [.sym "infer", .int 0])
      | .bool true => .ok (.expr "meta" [.sym "infer", .int 1])
      | .sym "no" => .ok (.expr "meta" [.sym "infer", .int 0])
      | .sym "yes" => .ok (.expr "meta" [.sym "infer", .int 1])
      | _ => .error (.errorException "invalid argument to \"infer\" option")
    else if name = "max_methods" then
      match a with
      | .sym "default" => .ok (.expr "meta" [.sym "max_methods", .int 3])
      | .int k =>
        if 1 ≤ k ∧ k ≤ 4 then .ok (.expr "meta" [.sym "max_methods", .int k])
        else .error (.errorException "We must have that `1 <= max_methods <= 4`")
      | _ => .error (.errorException "invalid argument to \"max_methods\" option")
    else .error (.errorException "unknown option")
  | .expr "=" [_, _] => .error (.errorException "unknown option")
  | _ => .error (.errorException "invalid option syntax")

def compilerOptions : List Ex → M (List Ex)
  | [] => .ok []
  | ex :: rest =>
    match compilerOption ex with
    | .error e => .error e
    | .ok m =>
      match compilerOptions rest with
      | .error e => .error e
      | .ok ms => .ok (m :: ms)

/-- `@force_compile`, `base/experimental.jl:268`. -/
def forceCompile : Ex := .expr "meta" [.sym "force_compile"]

/-- The option macros expand to the `:meta` expressions named by their docstrings:
`@optlevel n` for any `Int` (the docstring's 0-3 is not checked), `@max_methods n`
for 1-4 and `@max_methods n function f end` for 1-255 with the documented errors
otherwise, `@compiler_options` one `:meta` per option in order (with `default` as 3,
`yes`/`true` as 1) and an error for an unknown option, `@force_compile` and
`@aliasscope` their fixed forms. -/
def OptionMacros : Prop :=
  (∀ k : Int, optlevel (.int k) = .ok (.expr "meta" [.sym "optlevel", .int k])) ∧
  (∀ k : Int, 1 ≤ k → k ≤ 4 → maxMethods1 (.int k) = .ok (.expr "meta" [.sym "max_methods", .int k])) ∧
  (∀ k : Int, (k < 1 ∨ 4 < k) → maxMethods1 (.int k) = .error (.errorException "We must have that `1 <= max_methods <= 4`")) ∧
  (∀ (k : Int) (fname : Ex), 1 ≤ k → k ≤ 255 →
    ∃ e, maxMethods2 (.int k) (.expr "function" [fname]) = .ok e) ∧
  (∀ (k : Int) (hd : String) (args : List Ex), 1 ≤ k → k ≤ 255 → ¬ (hd = "function" ∧ args.length = 1) →
    maxMethods2 (.int k) (.expr hd args) = .error (.errorException "Second argument must be a function forward declaration")) ∧
  (∀ (k : Int), 1 ≤ k → k ≤ 4 →
    compilerOptions [.expr "=" [.sym "optimize", .int 2], .expr "=" [.sym "max_methods", .int k],
      .expr "=" [.sym "infer", .bool false], .expr "=" [.sym "compile", .sym "min"]] =
    .ok [.expr "meta" [.sym "optlevel", .int 2], .expr "meta" [.sym "max_methods", .int k],
      .expr "meta" [.sym "infer", .int 0], .expr "meta" [.sym "compile", .int 3]]) ∧
  (compilerOption (.expr "=" [.sym "max_methods", .sym "default"]) =
    .ok (.expr "meta" [.sym "max_methods", .int 3])) ∧
  (∀ (name : String) (a : Ex), name ∉ ["optimize", "compile", "infer", "max_methods"] →
    compilerOption (.expr "=" [.sym name, a]) = .error (.errorException "unknown option")) ∧
  forceCompile = .expr "meta" [.sym "force_compile"] ∧
  (∀ body, aliasscope body = .expr "block" [.expr "aliasscope" [], .expr "=" [.sym "aliasscope_result",
    Ex.esc body], .expr "popaliasscope" [], .sym "aliasscope_result"])

theorem optionMacros_proven : OptionMacros := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, fun _ => rfl⟩
  · intro k h1 h2; simp [maxMethods1, h1, h2]
  · intro k h; simp only [maxMethods1]; rw [if_neg (by omega)]
  · intro k fname h1 h2; simp [maxMethods2, h1, h2]
  · intro k hd args h1 h2 h3; simp only [maxMethods2]; rw [if_neg (by omega), if_pos h3]
  · intro k h1 h2
    simp [compilerOptions, compilerOption, Ex.isSym, h1, h2]
  · intro name a h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [compilerOption, h1, h2, h3, h4]

/-! ## `@make_all_arithmetic_checked` -/

open JuliaLean.IntArith.Checked in
/-- The six methods `@make_all_arithmetic_checked` defines, `base/experimental.jl:530-539`:
`-x`, `x - y` (for `Int` and for any same-type `BitInteger`), `x + y` (likewise) and
`x * y` call `checked_neg`, `checked_sub`, `checked_add`, `checked_mul`. -/
def checkedNegM {t : IntTy} (x : JInt t) : Jl (JInt t) := checkedNeg x
open JuliaLean.IntArith.Checked in
def checkedSubInt (x y : JInt .i64) : Jl (JInt .i64) := checkedSub x y
open JuliaLean.IntArith.Checked in
def checkedSubM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedSub x y
open JuliaLean.IntArith.Checked in
def checkedAddInt (x y : JInt .i64) : Jl (JInt .i64) := checkedAdd x y
open JuliaLean.IntArith.Checked in
def checkedAddM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedAdd x y
open JuliaLean.IntArith.Checked in
def checkedMulM {t : IntTy} (x y : JInt t) : Jl (JInt t) := checkedMul x y

open JuliaLean.IntArith.Checked in
/-- After `@make_all_arithmetic_checked`, `+`, `-` (binary and unary) and `*` return the
exact result when it fits the type and throw `OverflowError` otherwise (for `*`, at
every width but the 128-bit ones, whose `checked_mul` algorithm is not modelled here). -/
def CheckedArithmetic : Prop :=
  (∀ (t : IntTy) (x : JInt t), ExactOrOverflow (checkedNegM x) (-x.val)) ∧
  (∀ (x y : JInt .i64), ExactOrOverflow (checkedSubInt x y) (x.val - y.val) ∧
    ExactOrOverflow (checkedAddInt x y) (x.val + y.val)) ∧
  (∀ (t : IntTy) (x y : JInt t), ExactOrOverflow (checkedSubM x y) (x.val - y.val) ∧
    ExactOrOverflow (checkedAddM x y) (x.val + y.val)) ∧
  (∀ (t : IntTy) (x y : JInt t), t ≠ .i128 → t ≠ .u128 →
    ExactOrOverflow (checkedMulM x y) (x.val * y.val))

theorem checkedArithmetic_proven : CheckedArithmetic := by
  refine ⟨fun t x => JuliaLean.IntArith.Checked.negExact t x, fun x y => ?_, fun t x y => ?_,
    fun t x y h1 h2 => JuliaLean.IntArith.Checked.intrinsicMulExact t x y h1 h2⟩
  · have := JuliaLean.IntArith.Checked.addSubExact .i64 x y
    exact ⟨this.2, this.1⟩
  · have := JuliaLean.IntArith.Checked.addSubExact t x y
    exact ⟨this.2, this.1⟩

end JuliaLean.MiscCov.Experimental
