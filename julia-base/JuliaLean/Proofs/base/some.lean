import JuliaLean.base.some
import JuliaLean.base.promotion
import JuliaLean.Registry.Types

/-!
# Properties of `base/some.jl`

The statements below cover the documented behavior of `Some`, `notnothing`, `isnothing`,
`something`, `@something`, and the wrapper's comparison and hash methods. Type-level operations
use the `PType` model imported with `base/promotion.jl`.
-/

namespace JuliaLean.Proofs.base.some

open JuliaLean
open JuliaLean.base.some
open JuliaLean.base.promotion
open JuliaLean.Registry

/-! ## Specification vocabulary -/

def containsNothing : PType → Bool
  | .union a b => containsNothing a || containsNothing b
  | ty => pEqual ty primitiveNothingType

def evalThunks {α : Type} (values : List (Value α)) : List (ValueThunk α) :=
  values.map fun value => fun state => (.ok value, state + 1)

def selectedEvalCount {α : Type} (values : List (Value α)) : Nat :=
  match values.findIdx? (fun value => !isnothing value) with
  | none => values.length
  | some index => index + 1

def macroEscapedArgs : JuliaExpr → List JuliaExpr
  | .block [.assign _ (.escape argument), .ifThenElse _ _ rest] =>
      argument :: macroEscapedArgs rest
  | _ => []

private def macroNode (val arg rest : JuliaExpr) : JuliaExpr :=
  .block [.assign val (.escape arg),
    .ifThenElse (.call (.symbol "!") [.call (.symbol "isnothing") [val]])
      (.call (.globalRef "Base" "something") [val]) rest]

/-- The macro expansion preserves source argument order. `reverse` is the other-file
`reverse(::OneTo)` call; `inlineanonymous` is the other-file macro helper. -/
def MacroExpansionOrderSpec : Prop :=
  ∀ (reverse : List Nat → List Nat) (inlineanonymous : String → Nat → JuliaExpr),
    (∀ args : List JuliaExpr, reverse (JuliaLean.base.tuple.keysTuple args) =
      (JuliaLean.base.tuple.keysTuple args).reverse) →
    ∀ args : List JuliaExpr, (args.length : Int) ≤ IntTy.i64.max →
      (macroSomething reverse inlineanonymous JuliaExpr.escape args).map macroEscapedArgs = .ok args

/-- Exact nested control flow: each next argument occurs only in the `nothing` branch. -/
inductive ShortCircuitExpansion : List JuliaExpr → JuliaExpr → Prop where
  | done : ShortCircuitExpansion []
      (.call (.globalRef "Base" "something") [.globalRef "Base" "nothing"])
  | next (val arg : JuliaExpr) {args : List JuliaExpr} {rest : JuliaExpr} :
      ShortCircuitExpansion args rest →
      ShortCircuitExpansion (arg :: args) (macroNode val arg rest)

def MacroShortCircuitShapeSpec : Prop :=
  ∀ (reverse : List Nat → List Nat) (inlineanonymous : String → Nat → JuliaExpr),
    (∀ args : List JuliaExpr, reverse (JuliaLean.base.tuple.keysTuple args) =
      (JuliaLean.base.tuple.keysTuple args).reverse) →
    ∀ args : List JuliaExpr, (args.length : Int) ≤ IntTy.i64.max →
      ∃ expr, macroSomething reverse inlineanonymous JuliaExpr.escape args = .ok expr ∧
        ShortCircuitExpansion args expr

/-! ## Documented behavior -/

def SomeTypeObjectSpec : Prop :=
  ∀ T : PType, someTypeOf (someTypeObject T) = someValueType (typeObjectType T) ∧
    (someTypeObject T).value = T

def NonNothingTypeSpec : Prop :=
  ∀ T : PType, containsNothing (nonnothingtype sourcePTypeOps T) = false

def NonNothingTypeCheckedSpec : Prop :=
  ∀ (error : String → SomeException),
    (∀ message, error message = .errorException message) →
    nonnothingtypeChecked sourcePTypeOps error primitiveNothingType =
        .error (.errorException "cannot convert a value to nothing for assignment") ∧
      nonnothingtypeChecked sourcePTypeOps error .any =
        .error (.errorException "could not compute non-nothing type")

def PromoteRuleNothingSpec : Prop :=
  ∀ S : PType, pUnionContains primitiveNothingType (promoteRuleNothing S)

def PromoteRuleWithNothingSpec : Prop :=
  ∀ (promoteRule : PType → PType → Option PType) T S R,
    pSubtype T (nonnothingtype sourcePTypeOps T) = false →
    promoteRuleWithNothing sourcePTypeOps promoteRule T S = some R →
    pUnionContains primitiveNothingType R

def ConvertNothingSpec : Prop :=
  (∀ {α : Type} ops T (acceptsNothing : ops.subtype primitiveNothingType T = true) (x : α),
      convertNothingSame ops T acceptsNothing x = x) ∧
    (∀ {ε α β : Type} ops (error : String → ε) (convert : PType → α → Except ε β)
        T (acceptsNothing : ops.subtype primitiveNothingType T = true) x,
      convertNothingOther ops error convert T acceptsNothing x = do
        let R ← nonnothingtypeChecked ops error T
        convert R x)

def ConvertSomeSpec : Prop :=
  (∀ {T : PType} {α : Type} (x : SomeValue T α),
      (convertSomeSame x).value = x.value) ∧
    (∀ {ε α β : Type} (convert : PType → α → Except ε β) T S (x : SomeValue S α),
      (convertSome convert T S x).map (fun result => result.value) = convert T x.value)

def ShowSomeSpec : Prop :=
  ∀ {T : PType} {α : Type} (ops : ShowOperations α) (io : ShowIO) (x : SomeValue T α),
    (pEqual (ops.get io ":typeinfo" .any) (someTypeOf x) = true →
      (showSome ops io x).output = (ops.showValue io x.value).output) ∧
    (pEqual (ops.get io ":typeinfo" .any) (someTypeOf x) = false →
      (showSome ops io x).output =
        (ops.printChar (ops.showValue (ops.printString io "Some(") x.value) ')').output)

def NotnothingSpec : Prop :=
  ∀ {α : Type} (x : Value α),
    (x = .nothing →
      notnothingNothing (α := α) () = .error (.argumentError "nothing passed to notnothing")) ∧
    (x ≠ .nothing → notnothingAny x = .ok x)

def IsnothingSpec : Prop :=
  ∀ {α : Type} (x : Value α), (isnothing x = true ↔ x = .nothing) ∧
    (isnothing x = false ↔ x ≠ .nothing)

def SomethingSpec : Prop :=
  ∀ {α : Type} (xs : List (Value α)),
    something xs = match xs.find? (fun x => !isnothing x) with
      | none => .error (.argumentError "No value arguments present")
      | some (.some value) => .ok value
      | some value => .ok value

def AtSomethingSpec : Prop :=
  ∀ {α : Type} (values : List (Value α)) (state : Nat),
    atSomething (evalThunks values) state =
      (something values, state + selectedEvalCount values)

def ShortCircuitSpec : Prop :=
  AtSomethingSpec ∧ MacroExpansionOrderSpec ∧ MacroShortCircuitShapeSpec

def EqSomeSpec : Prop :=
  ∀ {T : PType} {α : Type} (eq : α → α → Bool),
    (∀ a, eq a a = true) → ∀ a : SomeValue T α, eqSome eq a a = true

def IsequalSomeSpec : Prop :=
  ∀ {T : PType} {α : Type} (isequal : α → α → Bool),
    (∀ a, isequal a a = true) → ∀ a : SomeValue T α, isequalSome isequal a a = true

def HashSomeIsequal : Prop :=
  ∀ {T S : PType} {α : Type} (width : UIntWidth) (isequal : α → α → Bool)
    (hash : α → JInt width.intTy → JInt width.intTy),
    (∀ a b h, isequal a b = true → hash a h = hash b h) →
    ∀ (a : SomeValue T α) (b : SomeValue S α) h,
      isequalSome isequal a b = true → hashSome width hash a h = hashSome width hash b h

/-- Relevant documented interfaces of the other-file IO, vector printer and evaluator.
The evaluator law records the absent `convert(Some{Int64}, ::Int64)` method. -/
def SomeShowEval : Prop :=
  ∀ (ops : ShowOperations Int)
    (render : (ShowIO → SomeValue (primitivePType (.int .i64)) Int → ShowIO) →
      List (SomeValue (primitivePType (.int .i64)) Int) → String)
    (evaluate : String → Except String (List Int)),
    (∀ io, ops.get io ":typeinfo" .any = io.typeinfo.getD .any) →
    (∀ io n, (ops.showValue io n).output = io.output ++ toString n) →
    (∀ showElement values, render showElement values = "Some{Int64}[" ++
      String.intercalate ", " (values.map (fun value =>
        (showElement ⟨some (someValueType (primitivePType (.int .i64))), ""⟩ value).output)) ++ "]") →
    evaluate "Some{Int64}[1, 2]" = .error "convert(::Type{Some{Int64}}, ::Int64)" →
    evaluate "Some{Int64}[Some(1), Some(2)]" = .ok [1, 2] →
    ∀ values : List Int,
      evaluate (render (showSome ops)
        (values.map fun value => (⟨value⟩ : SomeValue (primitivePType (.int .i64)) Int))) = .ok values

/-! ## Proofs -/

theorem someTypeObject_proven : SomeTypeObjectSpec := by
  intro T
  exact ⟨rfl, rfl⟩

theorem nonNothingTypeChecked_proven : NonNothingTypeCheckedSpec := by
  intro error h
  simp [nonnothingtypeChecked, nonnothingtype, typesplit, sourcePTypeOps,
    primitiveNothingType, pSubtype, pEqual, pListEqual, h]
  exact ⟨rfl, rfl⟩

theorem promoteRuleNothing_proven : PromoteRuleNothingSpec := by
  intro S
  exact Or.inr rfl

theorem promoteRuleWithNothing_proven : PromoteRuleWithNothingSpec := by
  intro promoteRule T S R h hr
  unfold promoteRuleWithNothing at hr
  change (if pSubtype T (nonnothingtype sourcePTypeOps T) then some .any else
    (promoteType promoteRule (nonnothingtype sourcePTypeOps T) S).bind
      (fun result => some (.union result primitiveNothingType))) = some R at hr
  rw [h] at hr
  cases hp : promoteType promoteRule (nonnothingtype sourcePTypeOps T) S with
  | none => simp [hp] at hr
  | some result =>
    simp [hp] at hr
    subst R
    exact Or.inr rfl

theorem convertNothing_proven : ConvertNothingSpec := by
  constructor
  · intros; rfl
  · intros; rfl

theorem convertSome_proven : ConvertSomeSpec := by
  constructor
  · intros; rfl
  · intro ε α β convert T S x
    change Except.map (fun result : SomeValue T β => result.value)
      ((convert T x.value).bind (fun value => .ok ⟨value⟩)) = convert T x.value
    cases h : convert T x.value <;> rfl

theorem showSome_proven : ShowSomeSpec := by
  intro T α ops io x
  constructor <;> intro h <;> simp [showSome, h]

theorem notnothing_proven : NotnothingSpec := by
  intro α x
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem isnothing_proven : IsnothingSpec := by
  intro α x
  cases x <;> simp [isnothing, Value.isNothing]

theorem something_proven : SomethingSpec := by
  intro α xs
  induction xs with
  | nil => simp [something, somethingZero]
  | cons x xs ih =>
    cases x <;> simp [something, somethingNothing, somethingSome,
      somethingAny, Value.unwrap, isnothing, Value.isNothing, ih]

theorem eqSome_proven : EqSomeSpec := by
  intro T α eq h a
  exact h a.value

theorem isequalSome_proven : IsequalSomeSpec := by
  intro T α isequal h a
  exact h a.value

theorem hashSomeIsequal_proven : HashSomeIsequal := by
  intro T S α width isequal hash h a b seed heq
  exact h a.value b.value _ heq

private theorem nothingEqual_subtype (T : PType)
    (h : pEqual T primitiveNothingType = true) : pSubtype T primitiveNothingType = true := by
  cases T <;> simp [primitiveNothingType, pEqual] at h
  next name wrapper params super =>
    have hn : name = ⟨"Core", "Nothing"⟩ := by simpa using h.1.1.1
    simp [primitiveNothingType, pSubtype, hn, h.1.2]

private theorem typesplit_noNothing (T : PType) :
    containsNothing (typesplit sourcePTypeOps T primitiveNothingType) = false := by
  have hu : typesplit sourcePTypeOps T primitiveNothingType =
      (if pSubtype T primitiveNothingType then .bottom else
        match T with
        | .union a b => .union (typesplit sourcePTypeOps a primitiveNothingType)
            (typesplit sourcePTypeOps b primitiveNothingType)
        | _ => T) := by
    conv => lhs; rw [typesplit.eq_def]
    rfl
  rw [hu]
  by_cases h : pSubtype T primitiveNothingType = true
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    cases T with
    | union a b =>
      simp [containsNothing, typesplit_noNothing a, typesplit_noNothing b]
    | _ =>
      apply Bool.eq_false_iff.mpr
      intro he
      exact h (nothingEqual_subtype _ he)
termination_by sizeOf T

theorem nonNothingType_proven : NonNothingTypeSpec := typesplit_noNothing

private theorem evalCount_nothing {α : Type} (xs : List (Value α)) :
    selectedEvalCount (.nothing :: xs) = selectedEvalCount xs + 1 := by
  unfold selectedEvalCount
  rw [List.findIdx?_cons]
  change (match (List.findIdx? (fun value : Value α => !isnothing value) xs).map (· + 1) with
    | none => xs.length + 1
    | some i => i + 1) =
      (match List.findIdx? (fun value : Value α => !isnothing value) xs with
      | none => xs.length
      | some i => i + 1) + 1
  cases List.findIdx? (fun value : Value α => !isnothing value) xs <;> rfl

theorem atSomething_proven : AtSomethingSpec := by
  intro α values
  induction values with
  | nil =>
    intro state
    simp [evalThunks, atSomething, something, somethingNothing, somethingZero,
      selectedEvalCount]
  | cons x xs ih =>
    intro state
    simp only [evalThunks] at ih
    cases x with
    | nothing =>
      simp [evalThunks, atSomething, isnothing, Value.isNothing,
        something, somethingNothing, evalCount_nothing]
      rw [ih]
      congr 1
      omega
    | some value =>
      simp [evalThunks, atSomething, isnothing, Value.isNothing,
        something, somethingSome, Value.unwrap, selectedEvalCount, List.findIdx?_cons]
    | scalar value =>
      simp [evalThunks, atSomething, isnothing, Value.isNothing,
        something, somethingAny, selectedEvalCount, List.findIdx?_cons]


private theorem expansion_args {args : List JuliaExpr} {expr : JuliaExpr}
    (h : ShortCircuitExpansion args expr) : macroEscapedArgs expr = args := by
  induction h with
  | done => rfl
  | next val arg h ih => simp [macroNode, macroEscapedArgs, ih]

private theorem macroLoop_shape
    (get : Nat → JuliaLean.base.abstractarray.Result JuliaExpr)
    (inlineanonymous : String → Nat → JuliaExpr) (pairs : List (JuliaExpr × Nat))
    (hget : ∀ p ∈ pairs, get p.2 = .ok p.1)
    {initialArgs : List JuliaExpr} {initial : JuliaExpr}
    (hinit : ShortCircuitExpansion initialArgs initial) :
    ∃ expr, forIn (pairs.map Prod.snd) initial (fun i rest => do
      let arg ← get i
      pure (.yield (macroNode (inlineanonymous "val" i) arg rest))) = .ok expr ∧
      ShortCircuitExpansion (pairs.reverse.map Prod.fst ++ initialArgs) expr := by
  induction pairs generalizing initialArgs initial with
  | nil => exact ⟨initial, rfl, hinit⟩
  | cons p ps ih =>
    obtain ⟨expr, he, hs⟩ := ih (fun p hp => hget p (by simp [hp]))
      (ShortCircuitExpansion.next (inlineanonymous "val" p.2) p.1 hinit)
    refine ⟨expr, ?_, ?_⟩
    · simp only [List.map_cons, List.forIn_cons]
      rw [hget p (by simp)]
      exact he
    · simpa [List.reverse_cons, List.append_assoc] using hs

private theorem tuple_getindex {args : List JuliaExpr} {value : JuliaExpr} {i : Nat}
    (h : (value, i) ∈ args.zipIdx 1) (small : (args.length : Int) ≤ IntTy.i64.max) :
    JuliaLean.base.tuple.getindexInteger args (.big (Int.ofNat i)) = .ok value := by
  obtain ⟨hi, hb, hv⟩ := List.mem_zipIdx h
  have hr : IntTy.i64.min ≤ (i : Int) ∧ (i : Int) ≤ IntTy.i64.max := by
    constructor
    · have : IntTy.i64.min ≤ 0 := by decide
      omega
    · omega
  have hconv : JInt.convert .i64 (Int.ofNat i) = .ok ⟨(i : Int), hr⟩ := by
    unfold JInt.convert
    exact dite_eq_left hr
  simp only [JuliaLean.base.tuple.getindexInteger, JuliaLean.base.tuple.convertIndex,
    hconv, JuliaLean.base.tuple.liftJ]
  change JuliaLean.base.tuple.getfield args (i : Int) = .ok value
  unfold JuliaLean.base.tuple.getfield
  rw [ite_eq_left (by omega)]
  have hn : (((i : Int) - 1).toNat) = i - 1 := by omega
  rw [hn, List.getElem?_eq_getElem (by omega), ← hv]

theorem macroShortCircuitShape_proven : MacroShortCircuitShapeSpec := by
  intro reverse inlineanonymous hreverse args small
  have hk : JuliaLean.base.tuple.keysTuple args = (args.zipIdx 1).map Prod.snd := by
    rw [List.zipIdx_map_snd]
    unfold JuliaLean.base.tuple.keysTuple JuliaLean.base.tuple.oneTo
      JuliaLean.base.tuple.lengthTuple
    rw [List.range'_eq_map_range]
    congr 1
    funext x
    omega
  unfold macroSomething
  dsimp only
  simp only [JuliaLean.base.abstractarray.eachindexIterators]
  change ∃ expr : JuliaExpr, ((forIn (reverse (JuliaLean.base.tuple.keysTuple args))
    (JuliaExpr.call (.globalRef "Base" "something") [.globalRef "Base" "nothing"])
    (fun i rest => do
      let arg ← ((JuliaLean.base.tuple.getindexInteger args (.big (Int.ofNat i))).mapError _ :
        JuliaLean.base.abstractarray.Result JuliaExpr)
      pure (.yield (macroNode (inlineanonymous "val" i) arg rest))) :
        JuliaLean.base.abstractarray.Result JuliaExpr) >>= pure) = .ok expr ∧
          ShortCircuitExpansion args expr
  simp only [bind_pure]
  rw [hreverse args, hk, ← List.map_reverse]
  refine Exists.imp (p := fun expr : JuliaExpr => _ ∧
    ShortCircuitExpansion (((args.zipIdx 1).reverse).reverse.map Prod.fst ++ []) expr)
    (fun expr h => ⟨h.1, ?_⟩) ?_
  · simpa [List.zipIdx_map_fst] using h.2
  · apply macroLoop_shape
    · intro p hp
      exact congrArg (Except.mapError _) (tuple_getindex (List.mem_reverse.mp hp) small)
    · exact ShortCircuitExpansion.done

theorem macroExpansionOrder_proven : MacroExpansionOrderSpec := by
  intro reverse inlineanonymous hreverse args small
  obtain ⟨expr, he, hs⟩ := macroShortCircuitShape_proven reverse inlineanonymous hreverse args small
  rw [he]
  exact congrArg Except.ok (expansion_args hs)

theorem shortCircuit_proven : ShortCircuitSpec :=
  ⟨atSomething_proven, macroExpansionOrder_proven, macroShortCircuitShape_proven⟩

theorem someShowEval_refuted : ¬ SomeShowEval := by
  intro h
  let ops : ShowOperations Int := {
    get := fun io _ fallback => io.typeinfo.getD fallback
    showValue := fun io n => { io with output := io.output ++ toString n }
    printString := fun io s => { io with output := io.output ++ s }
    printChar := fun io c => { io with output := io.output.push c } }
  let render := fun
      (showElement : ShowIO → SomeValue (primitivePType (.int .i64)) Int → ShowIO)
      (values : List (SomeValue (primitivePType (.int .i64)) Int)) =>
    "Some{Int64}[" ++ String.intercalate ", " (values.map (fun value =>
      (showElement ⟨some (someValueType (primitivePType (.int .i64))), ""⟩ value).output)) ++ "]"
  let evaluate : String → Except String (List Int) := fun code =>
    if code = "Some{Int64}[Some(1), Some(2)]" then .ok [1, 2]
    else .error "convert(::Type{Some{Int64}}, ::Int64)"
  have he := h ops render evaluate
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by simp [evaluate]) (by simp [evaluate]) [1, 2]
  have hn : (evaluate (render (showSome ops)
      [(⟨1⟩ : SomeValue (primitivePType (.int .i64)) Int), ⟨2⟩])).isOk = false := by decide
  have hbad : true = false := (congrArg Except.isOk he).symm.trans hn
  contradiction

/-! ## Registry -/

def entries : List Entry := [
  { id := "some-type-construction", juliaFile := "base/some.jl",
    juliaFns := ["Some(::Type{T})"]
    statement := "Some(T) stores T as its payload and has wrapper type Some{Type{T}}.",
    source := "base/some.jl:15",
    status := .proven, prop := ``SomeTypeObjectSpec, thm := some ``someTypeObject_proven },
  { id := "some-type-promotion", juliaFile := "base/some.jl",
    juliaFns := ["nonnothingtype(::Type)"]
    statement := "Removing Nothing from a union type leaves no Nothing alternative.",
    source := "base/some.jl:17",
    status := .proven, prop := ``NonNothingTypeSpec, thm := some ``nonNothingType_proven },
  { id := "some-checked-type-removal", juliaFile := "base/some.jl",
    juliaFns := ["nonnothingtype_checked(::Type)"]
    statement := "Checked removal reports ErrorException when the type is Any or when removing Nothing leaves Bottom.",
    source := "base/some.jl:27-32",
    status := .proven, prop := ``NonNothingTypeCheckedSpec, thm := some ``nonNothingTypeChecked_proven },
  { id := "some-promote-rule-nothing", juliaFile := "base/some.jl",
    juliaFns := ["promote_rule(::Type{Nothing}, ::Type)"]
    statement := "Promotion of Nothing with any type retains Nothing in the promoted union type.",
    source := "base/some.jl:18",
    status := .proven, prop := ``PromoteRuleNothingSpec, thm := some ``promoteRuleNothing_proven },
  { id := "some-promote-rule-supertype", juliaFile := "base/some.jl",
    juliaFns := ["promote_rule(::Type{>:Nothing}, ::Type)"]
    statement := "The Nothing-bearing promotion rule includes Nothing in its result unless its source check returns Any.",
    source := "base/some.jl:19-25",
    status := .proven, prop := ``PromoteRuleWithNothingSpec, thm := some ``promoteRuleWithNothing_proven },
  { id := "some-convert-nothing-union", juliaFile := "base/some.jl",
    juliaFns := ["convert(::Type{T}, ::T) where T>:Nothing", "convert(::Type{T}, x) where T>:Nothing"]
    statement := "Conversion to a type admitting Nothing preserves same-typed values and otherwise converts to the non-Nothing portion of the target.",
    source := "base/some.jl:34-35",
    status := .proven, prop := ``ConvertNothingSpec, thm := some ``convertNothing_proven },
  { id := "some-convert-some", juliaFile := "base/some.jl",
    juliaFns := ["convert(::Type{Some{T}}, ::Some{T})", "convert(::Type{Some{T}}, ::Some)"]
    statement := "Conversion to Some{T} preserves an already matching wrapper's payload, and otherwise converts the payload to T before wrapping it.",
    source := "base/some.jl:36-37",
    status := .proven, prop := ``ConvertSomeSpec, thm := some ``convertSome_proven },
  { id := "some-show-typeinfo", juliaFile := "base/some.jl",
    juliaFns := ["show(::IO, ::Some)"]
    statement := "show uses the payload's representation when IOContext typeinfo equals typeof(x), and includes Some(...) otherwise.",
    source := "base/some.jl:39-47 (show method)",
    status := .proven, prop := ``ShowSomeSpec, thm := some ``showSome_proven },
  { id := "some-notnothing", juliaFile := "base/some.jl",
    juliaFns := ["notnothing(::Any)", "notnothing(::Nothing)"]
    statement := "notnothing(x) throws ArgumentError exactly when x is nothing, and returns every non-nothing value unchanged.",
    source := "base/some.jl:49-55 (notnothing docstring and methods)",
    status := .proven, prop := ``NotnothingSpec, thm := some ``notnothing_proven },
  { id := "some-isnothing", juliaFile := "base/some.jl",
    juliaFns := ["isnothing"]
    statement := "isnothing(x) is true exactly when x is nothing; it does not unwrap nested Some values.",
    source := "base/some.jl:57-67 (isnothing docstring and method)",
    status := .proven, prop := ``IsnothingSpec, thm := some ``isnothing_proven },
  { id := "some-something-first", juliaFile := "base/some.jl",
    juliaFns := ["something()", "something(::Nothing, ...)", "something(::Some, ...)", "something(::Any, ...)"]
    statement := "something returns the first non-nothing argument, unwraps one Some, and throws ArgumentError if no value exists.",
    source := "base/some.jl:70-102 (something docstring and methods)",
    status := .proven, prop := ``SomethingSpec, thm := some ``something_proven },
  { id := "some-something-short-circuit", juliaFile := "base/some.jl",
    juliaFns := ["@something"]
    statement := "@something preserves the arguments in left-to-right order and evaluates only through the first non-nothing value.",
    source := "base/some.jl:105-167 (@something docstring and macro)",
    status := .proven, prop := ``ShortCircuitSpec, thm := some ``shortCircuit_proven,
    notes := "Tuple lengths fit Int64. The proof checks the actual macro's complete conditional syntax, argument order and evaluation count." },
  { id := "some-eq", juliaFile := "base/some.jl",
    juliaFns := ["==(::Some, ::Some)"]
    statement := "Equality on Some wrappers is reflexive whenever equality on the wrapped values is reflexive.",
    source := "base/some.jl:169 (method); invariant (equality is reflexive)",
    status := .proven, prop := ``EqSomeSpec, thm := some ``eqSome_proven },
  { id := "some-isequal", juliaFile := "base/some.jl",
    juliaFns := ["isequal(::Some, ::Some)"]
    statement := "isequal on Some wrappers is reflexive whenever isequal on the wrapped values is reflexive.",
    source := "base/some.jl:170 (method); invariant (isequal is reflexive)",
    status := .proven, prop := ``IsequalSomeSpec, thm := some ``isequalSome_proven },
  { id := "missingchar-some-hash-isequal", juliaFile := "base/some.jl",
    juliaFns := ["isequal(::Some, ::Some)", "hash(::Some, ::UInt)"]
    statement := "isequal(Some(a), Some(b)) implies hash(Some(a), h) == hash(Some(b), h) whenever the hash contract holds for the wrapped values.",
    source := "invariant (hash docstring: isequal(x,y) implies hash(x)==hash(y))",
    status := .proven, prop := ``HashSomeIsequal, thm := some ``hashSomeIsequal_proven },
  { id := "missingchar-some-show-typeinfo", juliaFile := "base/some.jl",
    juliaFns := ["show(::IO, ::Some)"]
    statement := "Evaluating repr(v) for v::Vector{Some{Int64}} gives v back.",
    source := "base/show.jl (show docstring: parseable Julia code when possible)",
    status := .refuted, prop := ``SomeShowEval, thm := some ``someShowEval_refuted,
    issue := "none found (queries: Some show typeinfo, Some typeinfo, show Some array convert, repr Some)",
    notes := "repr([Some(1), Some(2)]) is Some{Int64}[1, 2]; evaluating it throws MethodError. External IO, vector rendering and evaluation are constrained by their documented interface laws." }
]

/-! ## Method to property coverage -/

/-! Nothing to promise: `Some{T}`@11: type declaration only; `SomeValue.value` represents its field. -/
/-! Nothing to promise: `hash_some_seed`@171: a fixed constant used by `hashSome`. -/

/-!
| Julia method | Property |
|---|---|
| `Some{T}` | representation declaration; no method behavior |
| `Some(::Type{T})` | `some-type-construction` |
| `nonnothingtype(::Type)` | `some-type-promotion` |
| `promote_rule(::Type{Nothing}, ::Type)` | `some-promote-rule-nothing` |
| `promote_rule(::Type{>:Nothing}, ::Type)` | `some-promote-rule-supertype` |
| `nonnothingtype_checked(::Type)` | `some-checked-type-removal` |
| `convert(::Type{T}, ::T) where T>:Nothing` | `some-convert-nothing-union` |
| `convert(::Type{T}, x) where T>:Nothing` | `some-convert-nothing-union` |
| `convert(::Type{Some{T}}, ::Some{T})` | `some-convert-some` |
| `convert(::Type{Some{T}}, ::Some)` | `some-convert-some` |
| `show(::IO, ::Some)` | `some-show-typeinfo`, `missingchar-some-show-typeinfo` |
| `notnothing(::Any)` | `some-notnothing` |
| `notnothing(::Nothing)` | `some-notnothing` |
| `isnothing` | `some-isnothing` |
| `something()` | `some-something-first` |
| `something(::Nothing, ...)` | `some-something-first` |
| `something(::Some, ...)` | `some-something-first` |
| `something(::Any, ...)` | `some-something-first` |
| `@something` | `some-something-short-circuit` |
| `==(::Some, ::Some)` | `some-eq` |
| `isequal(::Some, ::Some)` | `some-isequal`, `missingchar-some-hash-isequal` |
| `hash_some_seed` | representation constant; no method behavior |
| `hash(::Some, ::UInt)` | `missingchar-some-hash-isequal` |
-/

end JuliaLean.Proofs.base.some
