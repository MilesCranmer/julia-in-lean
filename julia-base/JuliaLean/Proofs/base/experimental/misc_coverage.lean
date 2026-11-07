import JuliaLean.base.experimental
import JuliaLean.Proofs.base.checked.IntArith

/-!
# `base/experimental.jl` (master `bbfa0ce4150`)

Macros are functions from their argument syntax (`Ex`) to the expansion or the
exception thrown during expansion. A macro defined only for an `n::Int` argument
throws `MethodError` for any other argument. Runtime state that the methods read or
write through `ccall`s is an explicit record.
-/

namespace JuliaLean.MiscCov.Experimental

open JuliaLean
variable {V : Type}

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

/-- Disabled caches perform no pruning or copying; an unsuccessful prune
never reaches compaction; a successful compaction returns the number removed. -/
def PruneObjcacheContract : Prop :=
  (∀ dir i, i.enabled = false → pruneObjcache dir i = (["enabled"], .ok none)) ∧
  (∀ dir i err, i.enabled = true → i.cutoff = .error err →
    pruneObjcache dir i = (["enabled"], .error err)) ∧
  (∀ dir i cutoff, i.enabled = true → i.cutoff = .ok cutoff → i.removed < 0 →
    pruneObjcache dir i = (["enabled", "prune:" ++ toString cutoff],
      .error (.errorException "could not prune the native code cache"))) ∧
  (∀ dir i cutoff err, i.enabled = true → i.cutoff = .ok cutoff → 0 ≤ i.removed →
    i.compactError = some err → pruneObjcache dir i =
      (["enabled", "prune:" ++ toString cutoff, "compact:" ++ dir],
        .error (.errorException ("could not copy the native code cache to " ++ dir ++ ": " ++ err)))) ∧
  (∀ dir i cutoff, i.enabled = true → i.cutoff = .ok cutoff → 0 ≤ i.removed →
    i.compactError = none → pruneObjcache dir i =
      (["enabled", "prune:" ++ toString cutoff, "compact:" ++ dir], .ok (some i.removed)))

theorem pruneObjcacheContract_proven : PruneObjcacheContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro dir i h
    simp [pruneObjcache, h]
  · intro dir i err he hc
    simp [pruneObjcache, he, hc]
  · intro dir i cutoff he hc hr
    simp [pruneObjcache, he, hc, hr]
  · intro dir i cutoff err he hc hr hcompact
    simp [pruneObjcache, he, hc, show ¬ i.removed < 0 by omega, hcompact]
  · intro dir i cutoff he hc hr hcompact
    simp [pruneObjcache, he, hc, show ¬ i.removed < 0 by omega, hcompact]

end JuliaLean.MiscCov.Experimental

namespace JuliaLean.MiscCov

def ExperimentalConstIndexingClosed : Prop := @Experimental.ConstIndexing Unit
theorem experimentalConstIndexingClosed_proven : ExperimentalConstIndexingClosed :=
  Experimental.constIndexing_proven

end JuliaLean.MiscCov
