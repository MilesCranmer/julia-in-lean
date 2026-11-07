import JuliaLean.base.reflection
import JuliaLean.Proofs.base.reflection.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

def ReflectionRow19Property : Prop := ∀ methods generated ir worldMax debug,
  reflectionRow19 methods generated ir worldMax debug =
    match normalizeReflectionDebug ir debug with
    | .error error => .error error
    | .ok normalized => if worldMax then .error (.argumentError "reflection from generated function")
      else methods.mapM fun method => do
        let code ← lowerOne generated method
        return if normalized == "none" && !(generated && method.generated) then "remove_linenums:" ++ code else code

theorem reflectionRow19_proven : ReflectionRow19Property := by
  unfold ReflectionRow19Property
  intros; rfl

/-- Object-form `code_lowered`; `base/reflection.jl:49-52`. -/

def ReflectionRow49Property : Prop := ∀ signature function types query,
  reflectionRow49 signature function types query = query (signature function types)

theorem reflectionRow49_proven : ReflectionRow49Property := by unfold ReflectionRow49Property; intros; rfl

/-- `method_instances(argtypes, world)`; `base/reflection.jl:58-68`. -/

def ReflectionRow58Property : Prop := ∀ world candidates,
  reflectionRow58 world candidates = if world then .error (.argumentError "reflection from generated function")
    else .ok (candidates.map ("specialize:" ++ ·.name))

theorem reflectionRow58_proven : ReflectionRow58Property := by unfold ReflectionRow58Property; intros; rfl

/-- Object-form `method_instances`; `base/reflection.jl:70-73`. -/

def ReflectionRow70Property : Prop := ∀ signature function types lookup,
  reflectionRow70 signature function types lookup = lookup (signature function types)

theorem reflectionRow70_proven : ReflectionRow70Property := by unfold ReflectionRow70Property; intros; rfl

/-- `method_instance(argtypes; world, method_table)`; `base/reflection.jl:75-82`. -/

def ReflectionRow75Property : Prop := ∀ tuple world table,
  reflectionRow75 tuple world table = (table.find? (·.1 == tuple)).map (·.2)

theorem reflectionRow75_proven : ReflectionRow75Property := by unfold ReflectionRow75Property; intros; rfl

/-- Object-form `method_instance`; `base/reflection.jl:84-88`. -/

def ReflectionRow84Property : Prop := ∀ signature function types lookup,
  reflectionRow84 signature function types lookup = lookup (signature function types)

theorem reflectionRow84_proven : ReflectionRow84Property := by unfold ReflectionRow84Property; intros; rfl

/-- `default_debug_info_kind`; `base/reflection.jl:90`. -/

def ReflectionRow90Property : Prop := ∀ runtimeGlobal, reflectionRow90 runtimeGlobal = runtimeGlobal

theorem reflectionRow90_proven : ReflectionRow90Property := by unfold ReflectionRow90Property; intro; rfl

def ReflectionRow201Property : Prop := ∀ flags, (reflectionRow201 flags).length = 15

theorem reflectionRow201_proven : ReflectionRow201Property := by unfold ReflectionRow201Property; intro; rfl

/-- `EmissionParams` keyword constructor; `base/reflection.jl:224-226`. -/

def ReflectionRow224Property : Prop := ∀ value, reflectionRow224 value = 0 ∨ reflectionRow224 value = 1

theorem reflectionRow224_proven : ReflectionRow224Property := by intro value; cases value <;> simp [reflectionRow224, boolToCint]

def ReflectionRow288Property : Prop := ∀ name types opaqueQuery regular,
  (reflectionRow288 (.opaque name) types opaqueQuery regular = opaqueQuery name types) ∧
  (reflectionRow288 (.ordinary name) types opaqueQuery regular = regular name types) ∧
  (reflectionRow288 (.builtin name) types opaqueQuery regular = regular name types)

theorem reflectionRow288_proven : ReflectionRow288Property := by unfold ReflectionRow288Property; intros; exact ⟨rfl,rfl,rfl⟩

/-- Signature-form `code_typed`; `base/reflection.jl:299-302`. -/

def ReflectionRow299Property : Prop := ∀ convert query arguments,
  reflectionRow299 convert query arguments = query (convert arguments)

theorem reflectionRow299_proven : ReflectionRow299Property := by unfold ReflectionRow299Property; intros; rfl

/-- `default_tt`; `base/reflection.jl:307-314`. -/

def ReflectionRow307Property : Prop :=
  (∀ signature, reflectionRow307 [signature] = "tail:" ++ signature) ∧ reflectionRow307 [] = "Tuple"

theorem reflectionRow307_proven : ReflectionRow307Property := by exact ⟨fun _ => rfl, rfl⟩

/-- `raise_match_failure`; `base/reflection.jl:316-320`. -/

def ReflectionRow316Property : Prop := ∀ name signature,
  reflectionRow316 name signature = .error (.argumentError (name ++ ": unanalyzable call given " ++ signature))

theorem reflectionRow316_proven : ReflectionRow316Property := by unfold ReflectionRow316Property; intros; rfl

/-- `invoke_in_typeinf_world`; `base/reflection.jl:324-327`. -/

def ReflectionRow324Property : Prop := ∀ call arguments, reflectionRow324 call arguments = call arguments

theorem reflectionRow324_proven : ReflectionRow324Property := by unfold ReflectionRow324Property; intros; rfl

/-- `invoke_default_compiler`; `base/reflection.jl:329-335`. -/

def ReflectionRow329Property : Prop := ∀ defaultCompiler name arguments,
  reflectionRow329 none defaultCompiler name arguments = defaultCompiler name arguments

theorem reflectionRow329_proven : ReflectionRow329Property := by unfold ReflectionRow329Property; intros; rfl

def ReflectionRow337Property : Prop := ∀ defaultCall moduleCall,
  reflectionRow337 none defaultCall moduleCall = .ok defaultCall

theorem reflectionRow337_proven : ReflectionRow337Property := by unfold ReflectionRow337Property; intros; rfl

/-- `invoke_mt_compiler`; `base/reflection.jl:352-365`. -/

def ReflectionRow352Property : Prop := ∀ defaultCall moduleCall,
  reflectionRow352 none defaultCall moduleCall = .ok defaultCall

theorem reflectionRow352_proven : ReflectionRow352Property := by unfold ReflectionRow352Property; intros; rfl

def ReflectionRow373Property : Prop := ∀ pure worldMax debug candidates,
  reflectionRow373 pure worldMax debug candidates =
    if pure || worldMax then .error (.argumentError "reflection from generated function")
    else match debug with
      | .error error => .error error
      | .ok _ => match candidates with
        | none => .error (.argumentError "unanalyzable call")
        | some values => .ok (shapeInferenceRows values)

theorem reflectionRow373_proven : ReflectionRow373Property := by unfold ReflectionRow373Property; intros; rfl

def ReflectionRow407Property : Prop := ∀ pure optimize source,
  reflectionRow407 pure optimize source =
    if pure then .error (.argumentError "reflection from generated function")
    else match source with
      | .methodSource true true => if optimize then .ok "typeinf_code=>rettype" else .ok "uncompressed_ir=>declaredtype"
      | .methodSource true false => .ok "uncompressed_ir=>declaredtype"
      | .methodSource false _ | .optimizedIR => .ok "cached_inferred=>rettype"
      | .invalid => .error (.argumentError "invalid OpaqueClosure")

theorem reflectionRow407_proven : ReflectionRow407Property := by unfold ReflectionRow407Property; intros; rfl

/-- `code_typed_opaque_closure`; `base/reflection.jl:438-447`. -/

def ReflectionRow438Property : Prop := ∀ code,
  reflectionRow438 (.ok code) false = .ok [code] ∧
  reflectionRow438 (.ok code) true = .ok ["remove_linenums:" ++ code]

theorem reflectionRow438_proven : ReflectionRow438Property := by unfold ReflectionRow438Property; intros; exact ⟨rfl,rfl⟩

/-- Object-form `code_ircode`; `base/reflection.jl:492-498`. -/

def ReflectionRow492Property : Prop := ∀ name query,
  reflectionRow492 (.opaque name) query = .error (.argumentError "OpaqueClosure not supported") ∧
  reflectionRow492 (.ordinary name) query = .ok (query name) ∧
  reflectionRow492 (.builtin name) query = .ok (query name)

theorem reflectionRow492_proven : ReflectionRow492Property := by unfold ReflectionRow492Property; intros; exact ⟨rfl,rfl,rfl⟩

/-- Signature-form `code_ircode`; `base/reflection.jl:500-503`. -/

def ReflectionRow500Property : Prop := ∀ convert query arguments,
  reflectionRow500 convert query arguments = query (convert arguments)

theorem reflectionRow500_proven : ReflectionRow500Property := by unfold ReflectionRow500Property; intros; rfl

/-- `code_ircode_by_type`; `base/reflection.jl:511-535`. -/

def ReflectionRow511Property : Prop := ∀ pure worldMax candidates,
  reflectionRow511 pure worldMax candidates =
    if pure || worldMax then .error (.argumentError "reflection from generated function")
    else match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (shapeInferenceRows values)

theorem reflectionRow511_proven : ReflectionRow511Property := by unfold ReflectionRow511Property; intros; rfl

/-- `_builtin_return_type`; `base/reflection.jl:537-542`. -/

def ReflectionRow537Property : Prop := ∀ builtin widen arguments,
  reflectionRow537 builtin widen arguments = widen (builtin arguments)

theorem reflectionRow537_proven : ReflectionRow537Property := by unfold ReflectionRow537Property; intros; rfl

/-- `_builtin_effects`; `base/reflection.jl:544-551`. -/

def ReflectionRow544Property : Prop := ∀ typeFunction lattice effects arguments,
  reflectionRow544 typeFunction lattice effects arguments = effects (lattice (typeFunction arguments))

theorem reflectionRow544_proven : ReflectionRow544Property := by unfold ReflectionRow544Property; intros; rfl

/-- `_builtin_exception_type`; `base/reflection.jl:553-557`. -/

def ReflectionRow553Property : Prop := ∀ isNothrow,
  reflectionRow553 isNothrow = if isNothrow then "Union{}" else "Any"

theorem reflectionRow553_proven : ReflectionRow553Property := by unfold ReflectionRow553Property; intro; rfl

/-- `check_generated_context`; `base/reflection.jl:559-561`. -/

def ReflectionRow559Property : Prop := ∀ pure worldMax,
  reflectionRow559 pure worldMax = .ok () ↔ pure = false ∧ worldMax = false

theorem reflectionRow559_proven : ReflectionRow559Property := by
  intros pure worldMax; cases pure <;> cases worldMax <;> simp [reflectionRow559]

/-- `return_types`; `base/reflection.jl:610-631`. -/

def ReflectionRow610Property : Prop := ∀ generated functionClass candidates,
  reflectionRow610 generated functionClass candidates =
    if generated then .error (.argumentError "reflection from generated function")
    else match functionClass with
      | .opaque _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
      | .builtin _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
      | .ordinary _ => match candidates with
        | none => .error (.argumentError "unanalyzable call")
        | some values => .ok (values.map (·.getD "Any"))

theorem reflectionRow610_proven : ReflectionRow610Property := by unfold ReflectionRow610Property; intros; rfl

/-- `infer_return_type`; `base/reflection.jl:680-700`. -/

def ReflectionRow680Property : Prop := ∀ generated functionClass types,
  reflectionRow680 generated functionClass types =
    if generated then .error (.argumentError "reflection from generated function")
    else match functionClass with
      | .opaque _ | .builtin _ => .ok ((types.bind fun values => values.head?).getD "Any")
      | .ordinary _ => match types with
        | none => .error (.argumentError "unanalyzable call")
        | some values => .ok (String.intercalate "∪" values)

theorem reflectionRow680_proven : ReflectionRow680Property := by unfold ReflectionRow680Property; intros; rfl

/-- `infer_exception_types`; `base/reflection.jl:752-777`. -/

def ReflectionRow752Property : Prop := ∀ generated functionClass frames,
  reflectionRow752 generated functionClass frames =
    if generated then .error (.argumentError "reflection from generated function")
    else match functionClass with
      | .opaque _ => .ok ["Any"]
      | .builtin _ => .ok [((frames.bind fun values => values.head?).join).getD "Any"]
      | .ordinary _ => match frames with
        | none => .error (.argumentError "unanalyzable call")
        | some values => .ok (values.map (·.getD "Any"))

theorem reflectionRow752_proven : ReflectionRow752Property := by unfold ReflectionRow752Property; intros; rfl

/-- `infer_exception_type`; `base/reflection.jl:830-845`. -/

def ReflectionRow830Property : Prop := ∀ generated functionClass inferred,
  reflectionRow830 generated functionClass inferred =
    if generated then .error (.argumentError "reflection from generated function")
    else match functionClass with
      | .opaque _ => .ok "Any"
      | .builtin _ => .ok (inferred.getD "Any")
      | .ordinary _ => match inferred with
        | some value => .ok value
        | none => .error (.argumentError "unanalyzable call")

theorem reflectionRow830_proven : ReflectionRow830Property := by unfold ReflectionRow830Property; intros; rfl

/-- `infer_effects`; `base/reflection.jl:908-922`. -/

def ReflectionRow908Property : Prop := ∀ generated functionClass inferred,
  reflectionRow908 generated functionClass inferred =
    if generated then .error (.argumentError "reflection from generated function")
    else match functionClass with
      | .builtin _ => .ok (inferred.getD "unknown-effects")
      | _ => match inferred with
        | some value => .ok value
        | none => .error (.argumentError "unanalyzable call")

theorem reflectionRow908_proven : ReflectionRow908Property := by unfold ReflectionRow908Property; intros; rfl

/-- Object-form `print_statement_costs`; `base/reflection.jl:930-933`. -/

def ReflectionRow930Property : Prop := ∀ signature function types printer,
  reflectionRow930 signature function types printer = printer (signature function types)

theorem reflectionRow930_proven : ReflectionRow930Property := by unfold ReflectionRow930Property; intros; rfl

/-- Signature-form `print_statement_costs`; `base/reflection.jl:935-964`. -/

def ReflectionRow935Property : Prop := ∀ candidates,
  (reflectionRow935 candidates).length = candidates.length

theorem reflectionRow935_proven : ReflectionRow935Property := by unfold ReflectionRow935Property; intros; simp [reflectionRow935]

/-- Stdout wrapper `print_statement_costs`; `base/reflection.jl:966`. -/

def ReflectionRow966Property : Prop := ∀ printer argument, reflectionRow966 printer argument = printer argument

theorem reflectionRow966_proven : ReflectionRow966Property := by unfold ReflectionRow966Property; intros; rfl

def ReflectionRow968Property : Prop :=
  (∀ raise candidate, reflectionRow968 true raise candidate = .generatedFunctionError) ∧
  (∀ raise, reflectionRow968 false raise .missing = if raise then .noMatchError else .none) ∧
  (∀ raise method, reflectionRow968 false raise (.methodMatch method) = .matchFound method) ∧
  (∀ raise, reflectionRow968 false raise .other = .typeError)

theorem reflectionRow968_proven : ReflectionRow968Property := by
  simp [ReflectionRow968Property, reflectionRow968]

/-- `which(f,t)`; `base/reflection.jl:990-1003`. -/

def ReflectionRow990Property : Prop := ∀ candidate,
  reflectionRow990 candidate = match candidate with
    | some method => .ok method
    | none => .error (.argumentError "invoke would throw")

theorem reflectionRow990_proven : ReflectionRow990Property := by unfold ReflectionRow990Property; intro; rfl

/-- `which(tt)`; `base/reflection.jl:1010-1012`. -/

def ReflectionRow1010Property : Prop := ∀ lookup,
  reflectionRow1010 lookup = match lookup with
    | .error error => .error error
    | .ok (some method) => .ok method
    | .ok none => .error (.argumentError "no unique match")

theorem reflectionRow1010_proven : ReflectionRow1010Property := by
  unfold ReflectionRow1010Property
  intro lookup; cases lookup <;> rfl

/-- Tuple wrapper `which`; `base/reflection.jl:1013`. -/

def ReflectionRow1013Property : Prop := ∀ convert query arguments,
  reflectionRow1013 convert query arguments = query (convert arguments)

theorem reflectionRow1013_proven : ReflectionRow1013Property := by unfold ReflectionRow1013Property; intros; rfl

/-- `which(module,symbol)` checks `isdefinedglobal`, then looks up the
binding owner, or throws an `ErrorException`; `base/reflection.jl:1020-1025`.
The module and symbol strings are their Julia interpolation results. -/

def ReflectionRow1020Property : Prop :=
  (∀ moduleText symbolText owner, reflectionRow1020 true moduleText symbolText owner = .ok owner) ∧
  (∀ moduleText symbolText owner, reflectionRow1020 false moduleText symbolText owner =
    .error ("\"" ++ symbolText ++ "\" is not defined in module " ++ moduleText))

theorem reflectionRow1020_proven : ReflectionRow1020Property := by
  simp [ReflectionRow1020Property, reflectionRow1020]

/-- `nameof(::Function)`; `base/reflection.jl:1036-1038`. -/

def ReflectionRow1036Property : Prop := ∀ name, reflectionRow1036 name = name

theorem reflectionRow1036_proven : ReflectionRow1036Property := by unfold ReflectionRow1036Property; intro; rfl

/-- `nameof(::IntrinsicFunction)`; `base/reflection.jl:1040-1043`. -/

def ReflectionRow1040Property : Prop := ∀ names index,
  reflectionRow1040 names index = names[index]?

theorem reflectionRow1040_proven : ReflectionRow1040Property := by
  unfold ReflectionRow1040Property
  intros; rfl

/-- `parentmodule(::Function)`; `base/reflection.jl:1051`. -/

def ReflectionRow1051Property : Prop := ∀ moduleName, reflectionRow1051 moduleName = moduleName

theorem reflectionRow1051_proven : ReflectionRow1051Property := by unfold ReflectionRow1051Property; intro; rfl

/-- `parentmodule(f,types)`; `base/reflection.jl:1059-1065`. -/

def ReflectionRow1059Property : Prop := ∀ methods,
  reflectionRow1059 methods = match methods with
    | [] => .error (.argumentError "no matching methods")
    | method :: _ => .ok method.moduleName

theorem reflectionRow1059_proven : ReflectionRow1059Property := by unfold ReflectionRow1059Property; intro methods; cases methods <;> rfl

/-- `parentmodule(::Method)`; `base/reflection.jl:1075`. -/

def ReflectionRow1075Property : Prop := ∀ method, reflectionRow1075 method = method.moduleName

theorem reflectionRow1075_proven : ReflectionRow1075Property := by unfold ReflectionRow1075Property; intro; rfl

/-- Positional `hasmethod`; `base/reflection.jl:1113-1115`. -/

def ReflectionRow1113Property : Prop := ∀ result, reflectionRow1113 result = result

theorem reflectionRow1113_proven : ReflectionRow1113Property := by unfold ReflectionRow1113Property; intro; rfl

/-- World-age keyword wrapper for `hasmethod`; `base/reflection.jl:1117-1120`. -/

def ReflectionRow1117Property : Prop := ∀ lookup world, reflectionRow1117 lookup world = lookup world

theorem reflectionRow1117_proven : ReflectionRow1117Property := by unfold ReflectionRow1117Property; intros; rfl

/-- Keyword-name `hasmethod`; `base/reflection.jl:1122-1139`. -/

def ReflectionRow1122Property : Prop := ∀ worldMax positional requested method,
  reflectionRow1122 worldMax positional requested method =
    if worldMax then .error (.argumentError "reflection from generated function")
    else if requested.isEmpty then .ok positional
    else match method with
      | none => .ok false
      | some method =>
        .ok (method.keywordNames.isEmpty || method.forwardsKeywords || requested.all method.keywordNames.contains)

theorem reflectionRow1122_proven : ReflectionRow1122Property := by unfold ReflectionRow1122Property; intros; rfl

def ReflectionRow1155Property : Prop := ∀ fuel reference,
  reflectionRow1155 fuel reference = match fuel, reference with
    | 0, _ => none
    | _, .symbol moduleName name | _, .global moduleName name => some (moduleName,name)
    | remaining+1, .apply next | remaining+1, .applyIterate next => reflectionRow1155 remaining next
    | remaining+1, .ssa (some next) => reflectionRow1155 remaining next
    | _, _ => none

theorem reflectionRow1155_proven : ReflectionRow1155Property := by
  unfold ReflectionRow1155Property
  intro fuel reference
  cases fuel with
  | zero => rfl
  | succ remaining =>
    cases reference <;> try rfl
    case ssa next => cases next <;> rfl

def ReflectionRow1229Property : Prop := ∀ input flag,
  reflectionRow1229 input flag = if input.sameMethod then false
    else if input.reverseIntersectionWorks then ambiguityInner input flag else false

theorem reflectionRow1229_proven : ReflectionRow1229Property := by unfold ReflectionRow1229Property; intros; rfl

/-- Nested `inner`; `base/reflection.jl:1233-1277`. -/

def ReflectionRow1233Property : Prop := ∀ input flag,
  reflectionRow1233 input flag = ambiguityInner input flag

theorem reflectionRow1233_proven : ReflectionRow1233Property := by unfold ReflectionRow1233Property; intros; rfl

/-- Nested `involves_both`; `base/reflection.jl:1249-1257`. -/

def ReflectionRow1249Property : Prop := ∀ input,
  reflectionRow1249 input = (input.involvesFirst && input.involvesSecond)

theorem reflectionRow1249_proven : ReflectionRow1249Property := by unfold ReflectionRow1249Property; intros; rfl

def ReflectionRow1345Property : Prop := ∀ function arguments keywords,
  (reflectionRow1345 function arguments keywords).take keywords.length = keywords

theorem reflectionRow1345_proven : ReflectionRow1345Property := by unfold ReflectionRow1345Property; intros; simp [reflectionRow1345]

/-- `getglobalref`; `base/reflection.jl:1365`. -/

def ReflectionRow1365Property : Prop := ∀ globals moduleName name,
  reflectionRow1365 globals moduleName name = (globals.find? (·.1 == (moduleName,name))).map (·.2)

theorem reflectionRow1365_proven : ReflectionRow1365Property := by unfold ReflectionRow1365Property; intros; rfl

/-- `invokelatest_gr`; `base/reflection.jl:1367-1376`. -/

def ReflectionRow1367Property : Prop := ∀ keywords,
  reflectionRow1367 keywords = if keywords.isEmpty then "invoke_in_world" else "invoke_in_world:kwcall"

theorem reflectionRow1367_proven : ReflectionRow1367Property := by unfold ReflectionRow1367Property; intros; rfl

def ReflectionRow1406Property : Prop := ∀ target isGlobal,
  reflectionRow1406 target isGlobal = match target with
    | .literalGlobal => "invokelatest_gr"
    | .dottedGlobal | .symbolGlobal => if isGlobal then "invokelatest_gr" else "invokelatest"
    | .expression => "invokelatest"

theorem reflectionRow1406_proven : ReflectionRow1406Property := by unfold ReflectionRow1406Property; intros; rfl

def ReflectionRow1450Property : Prop := ∀ expression,
  reflectionRow1450 expression = match expression with
    | .call function arguments keywords => .ok (function,arguments,keywords)
    | .property object field => .ok ("getproperty",[object,field],[])
    | .index object indices => .ok ("getindex",object::indices,[])
    | .setProperty object field value => .ok ("setproperty!",[object,field,value],[])
    | .setIndex object value indices => .ok ("setindex!",object::value::indices,[])
    | .invalid => .error (.argumentError "expected call expression")

theorem reflectionRow1450_proven : ReflectionRow1450Property := by unfold ReflectionRow1450Property; intros; rfl

/-- Nested `flatten`; `base/reflection.jl:1451-1461`. -/

def ReflectionRow1451Property : Prop := ∀ values,
  (reflectionRow1451 values).length = (values.map List.length).sum

theorem reflectionRow1451_proven : ReflectionRow1451Property := by unfold ReflectionRow1451Property; intros; simp [reflectionRow1451, flattenArguments]

def ReflectionRow1506Property : Prop := ∀ state,
  let output := reflectionRow1506 state
  output.runtimeDropped = true ∧ output.requireWorldIsMax = true ∧ output.compilerActive = true

theorem reflectionRow1506_proven : ReflectionRow1506Property := by intro; exact ⟨rfl,rfl,rfl⟩

end JuliaLean.ExprReflect
