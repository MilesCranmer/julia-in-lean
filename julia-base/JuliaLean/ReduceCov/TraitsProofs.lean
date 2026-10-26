import JuliaLean.ReduceCov.Traits

namespace JuliaLean.ReduceCov

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

theorem indexStyleCombine_if (x : IndexStyleV) (c : Bool) :
    indexStyleCombine x (if c = true then .linear else .cartesian) =
      if (x == .linear && c) = true then .linear else .cartesian := by
  cases x <;> cases c <;> rfl

theorem indexStyleSpec_proven : IndexStyleSpec := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ⟨_, rfl⟩⟩
  intro a rest
  induction rest generalizing a with
  | nil =>
    simp only [indexStyleN, List.all_cons, List.all_nil, Bool.and_true]
    cases indexStyle1 a <;> rfl
  | cons b rest ih =>
    rw [indexStyleN, ih b]
    simp only [List.all_cons]
    exact indexStyleCombine_if _ _

end JuliaLean.ReduceCov
