import JuliaLean.base.traits

namespace JuliaLean.ReduceCov

open JuliaLean


/-- Types whose values `isless` totally orders: real numbers, strings, symbols,
concrete tuples and vectors of such values, and (vacuously) `Union{}`. -/
def totallyOrdered : JT → Bool
  | .bottom => true
  | .tuple fs => (JT.tuple fs).isConcrete && fs.attach.all fun ⟨f, _⟩ => totallyOrdered f
  | .vec t | .range t => totallyOrdered t
  | .int _ | .bool | .bigInt | .f64 | .f32 | .f16 | .bigFloat | .rational | .absInteger
  | .absFloat | .absReal | .string | .symbol => true
  | _ => false

/-- The `OrderStyle` trait, `base/traits.jl:4-20`: an instance has the style of its
type; a type is `Ordered` exactly when its values are totally ordered by `isless`
(real numbers, strings, symbols, and concrete tuples and vectors of those);
`OrderStyle(Union{}, x...)` throws `MethodError`. -/
def OrderStyleSpec : Prop :=
  (∀ t : JT, orderStyle (.inst t) = orderStyle (.ty t)) ∧
  (∀ t : JT, orderStyle (.ty t) = .ordered ↔ totallyOrdered t = true) ∧
  (∃ f, orderStyleBottomSlurp = .error (.methodError f))

/-- The comments at `base/traits.jl:24-26`: floating-point arithmetic rounds ("least
significant bits can be lost"), integer arithmetic wraps ("most significant bits
can be lost"), and every other type is unknown; instances follow their type. -/
def ArithmeticStyleSpec : Prop :=
  (∀ t : JT, arithmeticStyle (.inst t) = arithmeticStyle (.ty t)) ∧
  (∀ t : JT, arithmeticStyle (.ty t) =
    match t with
    | .bottom => .unknown
    | t => if t.isAbstractFloat then .rounds else if t.isInteger then .wraps else .unknown) ∧
  (∀ t, t.isInteger = true → arithmeticStyle (.inst t) = .wraps) ∧
  (∀ t, t.isAbstractFloat = true → arithmeticStyle (.inst t) = .rounds) ∧
  (∃ f, arithmeticStyleBottomSlurp = .error (.methodError f))

/-- The `RangeStepStyle` docstring, `base/traits.jl:35-65`: ranges with an integer
element type have regular steps, other ranges are irregular, and an instance
has the style of its type. -/
def RangeStepStyleRanges : Prop :=
  (∀ t : JT, rangeStepStyle 1 (.ty (.range t)) = some (if t.isInteger then .regular else .irregular)) ∧
  (∀ t : JT, rangeStepStyle 2 (.inst (.range t)) = rangeStepStyle 1 (.ty (.range t))) ∧
  rangeStepStyle 1 (.ty .bottom) = some .irregular ∧
  (∃ f, rangeStepStyleBottomSlurp = .error (.methodError f))

/-- A trait query terminates: every call `RangeStepStyle(x)` returns after
finitely many dispatch steps. -/
def RangeStepStyleTerminates : Prop :=
  ∀ a : TArg, ∃ n r, rangeStepStyle n a = some r

theorem orderStyleTy_eq : ∀ t : JT,
    orderStyleTy t = if totallyOrdered t then .ordered else .unordered
  | .bottom => by simp [orderStyleTy, totallyOrdered, orderStyleBottom]
  | .tuple fs => by
    have ih : ∀ f ∈ fs, (orderStyleTy f == .ordered) = totallyOrdered f := by
      intro f hf
      rw [orderStyleTy_eq f]
      cases totallyOrdered f <;> rfl
    have hall : ((fs.attach.map fun x => orderStyleTy x.1).all (· == .ordered)) =
        (fs.attach.all fun x => totallyOrdered x.1) := by
      rw [List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply]
      exact ⟨fun h x hx => (ih x.1 x.2) ▸ h x hx, fun h x hx => (ih x.1 x.2).symm ▸ h x hx⟩
    rw [orderStyleTy, totallyOrdered, orderStyleTuple]
    simp only [hall]
    cases (JT.tuple fs).isConcrete <;> cases (fs.attach.all fun x => totallyOrdered x.1) <;> rfl
  | .vtuple _ => by simp [orderStyleTy, totallyOrdered, orderStyleTuple]
  | .vec t => by rw [orderStyleTy, totallyOrdered, orderStyleTy_eq t]
  | .range t => by rw [orderStyleTy, totallyOrdered, orderStyleTy_eq t]
  | .int _ | .bool | .bigInt | .f64 | .f32 | .f16 | .bigFloat | .rational | .complex
  | .string | .symbol | .char | .missing | .nothing | .absInteger | .absFloat | .absReal
  | .number | .any | .dataType => by
    simp [orderStyleTy, totallyOrdered, JT.isReal, JT.isInteger, JT.isAbstractFloat, JT.isString,
      orderStyleReal, orderStyleString, orderStyleSymbol, orderStyleAny]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem ‹_ ∈ fs›)
  all_goals omega

theorem orderStyleSpec_proven : OrderStyleSpec := by
  refine ⟨fun _ => rfl, ?_, ⟨_, rfl⟩⟩
  intro t
  simp only [orderStyle]
  rw [orderStyleTy_eq t]
  cases totallyOrdered t <;> simp

theorem arithmeticStyleSpec_proven : ArithmeticStyleSpec := by
  refine ⟨fun _ => rfl, fun t => ?_, fun t h => ?_, fun t h => ?_, ⟨_, rfl⟩⟩
  · cases t <;> rfl
  · cases t <;> simp_all [arithmeticStyle, arithmeticStyleTy, JT.isInteger, JT.isAbstractFloat,
      arithmeticStyleInteger, arithmeticStyleFloat]
  · cases t <;> simp_all [arithmeticStyle, arithmeticStyleTy, JT.isInteger, JT.isAbstractFloat,
      arithmeticStyleInteger, arithmeticStyleFloat]

theorem rangeStepStyleRanges_proven : RangeStepStyleRanges :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, ⟨_, rfl⟩⟩

theorem rangeStepStyle_dataType : ∀ n, rangeStepStyle n (.ty .dataType) = none
  | 0 => rfl
  | n + 1 => by
    simp only [rangeStepStyle, rangeStepStyleStep]
    exact rangeStepStyle_dataType n

theorem rangeStepStyleTerminates_refuted : ¬ RangeStepStyleTerminates := by
  intro h
  obtain ⟨n, r, hn⟩ := h (.inst (.int .i64))
  match n, hn with
  | 0, hn => simp [rangeStepStyle] at hn
  | 1, hn => simp [rangeStepStyle, rangeStepStyleStep] at hn
  | n + 2, hn =>
    simp only [rangeStepStyle, rangeStepStyleStep] at hn
    rw [rangeStepStyle_dataType] at hn
    simp at hn

end JuliaLean.ReduceCov
