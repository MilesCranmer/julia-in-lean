import JuliaLean.base.fastmath

namespace JuliaLean.NumMisc

/-- `hypot(x::Number)` and `hypot(x::Number, y::Number, xs::Number...)`,
`base/math.jl:729-731`. -/
def hypotSupportsArity (n : Nat) : Bool := n ≥ 1

/-- The only direct `hypot_fast` implementation takes two arguments,
`base/fastmath.jl:327`; the fallback loops at lines 371-395 add no other arity. -/
def hypotFastSupportsArity (n : Nat) : Bool := n == 2

/-- Rewriting `hypot` under `@fastmath` preserves every supported public arity. -/
def FastMathCoverage : Prop :=
  ∀ n : Nat, hypotSupportsArity n = true → hypotFastSupportsArity n = true

theorem fastMathCoverage_refuted : ¬ FastMathCoverage := by
  intro h
  have hs := h 3 (by decide)
  simp [hypotFastSupportsArity] at hs

end JuliaLean.NumMisc

namespace JuliaLean.NumMisc.Coverage

def FastRewriteBehavior : Prop :=
  (∀ symbol, makeFastSymbol symbol = lookupName symbol fastOpPairs) ∧
  (∀ id, makeFastMath (.opaque id) = .opaque id) ∧
  (∀ body, makeFastMath (.quote body) = .quote body) ∧
  (∀ base power, makeFastMath (.call "^" [base, .int power]) =
    .call "Base.FastMath.pow_fast" [makeFastMath base, .valInt power]) ∧
  (∀ name args, (name ≠ "^" ∨ ∀ base power, args ≠ [base, .int power]) →
    makeFastMath (.call name args) = .call (makeFastSymbol name) (makeFastList args)) ∧
  (∀ head name rhs, rewrittenAssignmentOp head = some name →
    makeFastMath (.node head [.symbol "x", rhs]) =
      .node "=" [.symbol "x", .call (makeFastSymbol name) [.symbol "x", makeFastMath rhs]]) ∧
  (∀ expression, fastmathMacro expression = makeFastMath (.node "escape" [expression]))

theorem fastRewriteBehavior : FastRewriteBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro name args h
    by_cases hn : name = "^"
    · subst name
      cases args with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail =>
          cases tail with
          | nil => cases b <;> simp_all [makeFastMath]
          | cons c more => simp only [makeFastMath]
    · simp [makeFastMath, hn]
  · intro head name rhs hop
    simp only [makeFastMath, hop]
  · intros; rfl
def ScalarFallbackBehavior : Prop :=
  (∀ base args, fallbackVarargsTerm base args = .call base args) ∧
  (∀ fast args, promoteVarargsTerm fast args =
    .call fast [.call "splat" [.call "promote" args]]) ∧
  (∀ fast x y, promoteBinaryTerm fast x y =
    .call fast [.call "splat" [.call "promote" [x, y]]]) ∧
  (∀ fast a b c rest, naryFoldTerm fast a b c rest =
    .call "afoldl" [.call "symbol" [.call fast []],
      ftCall2 fast (ftCall2 fast a b) c, .list rest]) ∧
  (∀ fast a b c rest, promoteNaryTerm fast a b c rest =
    .call fast [.call "splat" [.call "promote" (a :: b :: c :: rest)]])

theorem scalarFallbackBehavior : ScalarFallbackBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
def ScalarMethodBehavior : Prop :=
  (∀ x, subFastUnaryTerm x = ftCall1 "neg_float_fast" x) ∧
  (∀ x y, addFastTerm x y = ftCall2 "add_float_fast" x y) ∧
  (∀ x y, subFastTerm x y = ftCall2 "sub_float_fast" x y) ∧
  (∀ x y, mulFastTerm x y = ftCall2 "mul_float_fast" x y) ∧
  (∀ x y, divFastTerm x y = ftCall2 "div_float_fast" x y) ∧
  (∀ x y, maxFastTerm x y = ftCall2 "max_float_fast" x y) ∧
  (∀ x y, minFastTerm x y = ftCall2 "min_float_fast" x y) ∧
  (∀ x y, cmpFastTerm x y =
    .eagerIf (ftCall2 "Base.FastMath.eq_fast" x y) (.int 0)
      (.eagerIf (ftCall2 "Base.FastMath.lt_fast" x y) (.int (-1)) (.int 1))) ∧
  (∀ base x, logBaseFastTerm base x =
    ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.log_fast" x)
      (ftCall1 "Base.FastMath.log_fast" base)) ∧
  (∀ x y, eqFastTerm x y = ftCall2 "eq_float_fast" x y) ∧
  (∀ x y, neFastTerm x y = ftCall2 "ne_float_fast" x y) ∧
  (∀ x y, ltFastTerm x y = ftCall2 "lt_float_fast" x y) ∧
  (∀ x y, leFastTerm x y = ftCall2 "le_float_fast" x y) ∧
  (∀ x y, gtFastTerm x y = ftCall2 "Base.FastMath.lt_fast" y x) ∧
  (∀ x y, geFastTerm x y = ftCall2 "Base.FastMath.le_fast" y x) ∧
  (∀ x, isinfFastTerm x = .bool false) ∧
  (∀ x, isfiniteFastTerm x = .bool true) ∧
  (∀ x, isnanFastTerm x = .bool false) ∧
  (∀ x, issubnormalFastTerm x = .bool false) ∧
  (∀ x, exp2FastTerm x = ftCall1 "Base.Math.exp2_fast" x) ∧
  (∀ x, expFastTerm x = ftCall1 "Base.Math.exp_fast" x) ∧
  (∀ x, exp10FastTerm x = ftCall1 "Base.Math.exp10_fast" x) ∧
  (∀ x y, powiFastTerm "Float16" x y = .call "ccall:llvm.powi" [.call "Float16" [], x, y]) ∧
  (∀ x y, powiFastTerm "Float32" x y = .call "ccall:llvm.powi" [.call "Float32" [], x, y]) ∧
  (∀ x y, powiFastTerm "Float64" x y = .call "ccall:llvm.powi" [.call "Float64" [], x, y]) ∧
  (∀ x power, powValFastTerm x power = ftCall2 "Base.FastMath.pow_fast" x (.int power)) ∧
  (∀ x value, powLiteralFallbackTerm x value =
    .call "Base.literal_pow" [.call "Base.^" [], x, value]) ∧
  (∀ x, sqrtFastTerm x = ftCall1 "sqrt_llvm_fast" x) ∧
  (∀ x, sincosPrimitiveFastTerm x = ftCall1 "sincos" x) ∧
  (∀ x, sincosFloat16FastTerm x =
    let result := ftCall1 "Base.FastMath.sincos_fast" (ftCall1 "Float32" x)
    .pair (ftCall1 "Float16" (.call "first" [result]))
      (ftCall1 "Float16" (.call "second" [result]))) ∧
  (∀ x, sincosRealFastTerm x = ftCall1 "Base.FastMath.sincos_fast"
    (.call "typeassert:AbstractFloat" [ftCall1 "float" x])) ∧
  (∀ x y, remFastTerm x y = ftCall2 "copysign"
    (ftCall2 "Base.rem_internal" (ftCall1 "Base.FastMath.abs_fast" x)
      (ftCall1 "Base.FastMath.abs_fast" y)) x) ∧
  (∀ x y, hypotFastTerm x y = ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall2 "Base.FastMath.add_fast" (ftCall2 "Base.FastMath.mul_fast" x x)
      (ftCall2 "Base.FastMath.mul_fast" y y))) ∧
  (∀ x y, powIntegerFastTerm x y =
    let z := (JInt.wrap .i32 y).val
    if z == y then ftCall2 "Base.FastMath.pow_fast" x (.int z)
    else ftCall2 "Base.^" x (.int y))

theorem scalarMethodBehavior : ScalarMethodBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl
def ScalarFastBehavior : Prop :=
  (∀ ops x y, fastCmp ops x y = if ops.eq x y then 0 else if ops.lt x y then -1 else 1) ∧
  (∀ ops x y, fastMinmax ops x y = (ops.min x y, ops.max x y)) ∧
  (∀ promote op x y, promoteThen promote op x y =
    let pair := promote x y; op pair.1 pair.2) ∧
  (∀ op x xs, foldFast op x xs = xs.foldl op x) ∧
  (∀ fits fast normal, powFastPath fits fast normal = if fits then fast else normal) ∧
  (∀ sin cos x, sincosFast sin cos x = (sin x, cos x)) ∧
  (∀ n, hypotFastSupportsArity n = (n == 2)) ∧
  (∀ operation x, fastUnary operation x = operation x) ∧
  (∀ operation x y, fastBinary operation x y = operation x y) ∧
  (∀ kind x, fastClassification kind x = (kind == 1)) ∧
  (∀ abs rem copySign x y, fastRemainder abs rem copySign x y =
    copySign (rem (abs x 0) (abs y 0)) x) ∧
  (∀ mul add sqrt x y, fastHypot mul add sqrt x y =
    sqrt (add (mul x x) (mul y y)) 0)

theorem scalarFastBehavior : ScalarFastBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def ScalarCoverageBehavior : Prop :=
  ScalarFastBehavior ∧ ScalarMethodBehavior ∧ ScalarFallbackBehavior

theorem scalarCoverageBehavior : ScalarCoverageBehavior :=
  ⟨scalarFastBehavior, scalarMethodBehavior, scalarFallbackBehavior⟩
def ComplexFastBehavior : Prop :=
  (∀ o x y, complexAdd o x y = ⟨o.add x.re y.re, o.add x.im y.im⟩) ∧
  (∀ o x y, complexSub o x y = ⟨o.sub x.re y.re, o.sub x.im y.im⟩) ∧
  (∀ o x y, complexMul o x y =
    ⟨o.sub (o.mul x.re y.re) (o.mul x.im y.im),
     o.add (o.mul x.re y.im) (o.mul x.im y.re)⟩) ∧
  (∀ o x y, complexEq o x y = (o.eq x.re y.re && o.eq x.im y.im)) ∧
  (∀ neg x, complexConj neg x = ⟨x.re, neg x.im⟩) ∧
  (∀ mul add x, complexAbs2 mul add x = add (mul x.re x.re) (mul x.im x.im)) ∧
  (∀ o x y, complexDivNumerator o x y =
    ⟨o.add (o.mul x.re y.re) (o.mul x.im y.im),
     o.sub (o.mul x.im y.re) (o.mul x.re y.im)⟩) ∧
  (∀ tag, complexFormulaCode tag = match tag with
    | .pow => 1 | .acos => 2 | .acosh => 3 | .angle => 4 | .asin => 5 | .asinh => 6
    | .atan => 7 | .atanh => 8 | .cis => 9 | .cos => 10 | .cosh => 11 | .exp10 => 12
    | .exp2 => 13 | .exp => 14 | .expm1 => 15 | .log10 => 16 | .log1p => 17
    | .log2 => 18 | .log => 19 | .sin => 20 | .sinh => 21 | .sqrt => 22
    | .tan => 23 | .tanh => 24) ∧
  (∀ op values init, reduceFast op values init = values.foldl op init)

theorem complexFastBehavior : ComplexFastBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros <;> first | rfl | (rename_i tag; cases tag <;> rfl)
def ComplexMethodBehavior : Prop :=
  (∀ x, cAbsFast x = ftCall2 "Base.FastMath.hypot_fast" (cReal x) (cImag x)) ∧
  (∀ x, cInvFast x = ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.conj_fast" x) (ftCall1 "Base.FastMath.abs2_fast" x)) ∧
  (∀ x, cSignFast x = .ite (ftCall2 "Base.FastMath.eq_fast" x (.int 0))
    (.call "float" [.call "zero" [x]])
    (ftCall2 "Base.FastMath.div_fast" x (ftCall1 "Base.FastMath.abs_fast" x))) ∧
  (∀ x b, cAddScalarRight x b = cMake (ftCall2 "Base.FastMath.add_fast" (cReal x) b) (cImag x)) ∧
  (∀ a y, cAddScalarLeft a y = cMake (ftCall2 "Base.FastMath.add_fast" a (cReal y)) (cImag y)) ∧
  (∀ x b, cSubScalarRight x b = cMake (ftCall2 "Base.FastMath.sub_fast" (cReal x) b) (cImag x)) ∧
  (∀ a y, cSubScalarLeft a y = cMake (ftCall2 "Base.FastMath.sub_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (cImag y))) ∧
  (∀ x b, cMulScalarRight x b = cMake (ftCall2 "Base.FastMath.mul_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.mul_fast" (cImag x) b)) ∧
  (∀ a y, cMulScalarLeft a y = cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall2 "Base.FastMath.mul_fast" a (cImag y))) ∧
  (∀ x b, cDivScalarRight x b = cMake (ftCall2 "Base.FastMath.div_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.div_fast" (cImag x) b)) ∧
  (∀ x y, cDivFast x y =
    let numerator := cMake
      (ftCall2 "Base.FastMath.add_fast"
        (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cReal y))
        (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cImag y)))
      (ftCall2 "Base.FastMath.sub_fast"
        (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cReal y))
        (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cImag y)))
    ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)) ∧
  (∀ a y, cDivScalarLeft a y =
    let numerator := cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
      (ftCall1 "Base.FastMath.sub_fast" (ftCall2 "Base.FastMath.mul_fast" a (cImag y)))
    ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)) ∧
  (∀ x y, cEqFast x y = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (cImag y))) ∧
  (∀ x b, cEqScalarRight x b = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (.int 0))) ∧
  (∀ a y, cEqScalarLeft a y = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" a (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (.int 0) (cImag y))) ∧
  (∀ x y, cNeFast x y = ftCall1 "!" (ftCall2 "Base.FastMath.eq_fast" x y)) ∧
  (∀ x, cCisFastReal x =
    let sc := ftCall1 "Base.FastMath.sincos_fast" x
    cMake (.call "second" [sc]) (.call "first" [sc])) ∧
  (∀ x y, cPowFast x y = ftCall1 "Base.FastMath.exp_fast"
    (ftCall2 "Base.FastMath.mul_fast" y (ftCall1 "Base.FastMath.log_fast" x))) ∧
  (∀ x, cAcosFast x = ftCall2 "Base.FastMath.add_fast"
    (ftCall2 "Base.FastMath.div_fast" (.call "convertπ" [.call "typeof" [x]]) (.int 2))
    (ftCall2 "Base.FastMath.mul_fast" cIm
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast"
        (ftCall2 "Base.FastMath.mul_fast" cIm x)
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1)
          (ftCall2 "Base.FastMath.mul_fast" x x))))))) ∧
  (∀ x, cAcoshFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x (ftCall2 "Base.FastMath.mul_fast"
      (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.add_fast" x (.int 1)))
      (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" x (.int 1)))))) ∧
  (∀ x, cAngleFast x = .call "atan" [cImag x, cReal x]) ∧
  (∀ x, cAsinFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.asinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cAsinhFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x (ftCall1 "Base.FastMath.sqrt_fast"
      (ftCall2 "Base.FastMath.add_fast" (.int 1) (ftCall2 "Base.FastMath.mul_fast" x x))))) ∧
  (∀ x, cAtanFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.atanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cAtanhFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x))
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1) x)))) ∧
  (∀ x, cCisFastComplex x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" (cImag x)))
    (ftCall1 "Base.FastMath.cis_fast" (cReal x))) ∧
  (∀ x, cCosFast x = ftCall1 "Base.FastMath.cosh_fast"
    (ftCall2 "Base.FastMath.mul_fast" cIm x)) ∧
  (∀ x, cCoshFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.add_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))) ∧
  (∀ name base x, cExpBaseFast name base x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 name (cReal x)) (ftCall1 "Base.FastMath.cis_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x)
        (ftCall1 "Base.FastMath.log_fast" (cConst x base))))) ∧
  (∀ x, cExp10Fast x = cExpBaseFast "Base.FastMath.exp10_fast" 10 x) ∧
  (∀ x, cExp2Fast x = cExpBaseFast "Base.FastMath.exp2_fast" 2 x) ∧
  (∀ x, cExpFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.exp_fast" (cReal x)) (ftCall1 "Base.FastMath.cis_fast" (cImag x))) ∧
  (∀ x, cExpm1Fast x = ftCall2 "Base.FastMath.sub_fast"
    (ftCall1 "Base.FastMath.exp_fast" x) (.int 1)) ∧
  (∀ x, cLog1pFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" (.int 1) x)) ∧
  (∀ base x, cLogBaseFast base x = ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" (cConst x base))) ∧
  (∀ x, cLog10Fast x = cLogBaseFast 10 x) ∧
  (∀ x, cLog2Fast x = cLogBaseFast 2 x) ∧
  (∀ x, cLogFast x = cMake (ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" (ftCall1 "Base.FastMath.abs2_fast" x)) (.int 2))
    (ftCall1 "Base.FastMath.angle_fast" x)) ∧
  (∀ base x, cLogTwoFast base x = .call "Complex" [ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)]) ∧
  (∀ x, cSinFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.sinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cSinhFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))) ∧
  (∀ x, cSqrtFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.sqrt_fast" (ftCall1 "Base.FastMath.abs_fast" x))
    (ftCall1 "Base.FastMath.cis_fast" (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.angle_fast" x) (.int 2)))) ∧
  (∀ x, cTanFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.tanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cTanhFast x =
    let a := ftCall1 "Base.FastMath.exp_fast" x
    let b := ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)
    ftCall2 "Base.FastMath.div_fast" (ftCall2 "Base.FastMath.sub_fast" a b)
      (ftCall2 "Base.FastMath.add_fast" a b))

theorem complexMethodBehavior : ComplexMethodBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl
def FastFallbackReductionBehavior : Prop :=
  (∀ base x, unaryMathFallbackTerm base x = ftCall1 base x) ∧
  (∀ base x y, binaryMathFallbackTerm base x y = ftCall2 base x y) ∧
  (∀ fast x y, binaryMathPromoteTerm fast x y =
    .call fast [.call "splat" [.call "promote" [x, y]]]) ∧
  (∀ x y, powerNumberIntegerFallbackTerm x y = ftCall2 "Base.^" x y) ∧
  (∀ array kwargs, maximumFastTerm array kwargs =
    .call "Base.reduce" [.call "Base.FastMath.max_fast" [], array, kwargs]) ∧
  (∀ array kwargs, minimumFastTerm array kwargs =
    .call "Base.reduce" [.call "Base.FastMath.min_fast" [], array, kwargs]) ∧
  (∀ f array kwargs, maximumMapFastTerm f array kwargs =
    .call "Base.mapreduce" [f, .call "Base.FastMath.max_fast" [], array, kwargs]) ∧
  (∀ f array kwargs, minimumMapFastTerm f array kwargs =
    .call "Base.mapreduce" [f, .call "Base.FastMath.min_fast" [], array, kwargs]) ∧
  (∀ f reducer array region, reducedimInitFastTerm f reducer array region =
    .call "Base.reducedim_init" [f, reducer, array, region]) ∧
  (∀ f array region, maxReducedimInitFastTerm f array region =
    .call "Base.reducedim_init" [f, .call "max" [], array, region]) ∧
  (∀ f array region, minReducedimInitFastTerm f array region =
    .call "Base.reducedim_init" [f, .call "min" [], array, region]) ∧
  (∀ result array kwargs, maximumBangWrapperTerm result array kwargs =
    .call "Base.FastMath.maximum!_fast" [.call "identity" [], result, array, kwargs]) ∧
  (∀ result array kwargs, minimumBangWrapperTerm result array kwargs =
    .call "Base.FastMath.minimum!_fast" [.call "identity" [], result, array, kwargs]) ∧
  (∀ f result array init, maximumBangTerm f result array init =
    .call "Base.mapreducedim!" [f, .call "Base.FastMath.max_fast" [],
      .call "Base.initarray!" [result, f, .call "max" [], init, array], array]) ∧
  (∀ f result array init, minimumBangTerm f result array init =
    .call "Base.mapreducedim!" [f, .call "Base.FastMath.min_fast" [],
      .call "Base.initarray!" [result, f, .call "min" [], init, array], array])

theorem fastFallbackReductionBehavior : FastFallbackReductionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ComplexCoverageBehavior : Prop :=
  ComplexFastBehavior ∧ ComplexMethodBehavior ∧ FastFallbackReductionBehavior

theorem complexCoverageBehavior : ComplexCoverageBehavior :=
  ⟨complexFastBehavior, complexMethodBehavior, fastFallbackReductionBehavior⟩

end JuliaLean.NumMisc.Coverage
