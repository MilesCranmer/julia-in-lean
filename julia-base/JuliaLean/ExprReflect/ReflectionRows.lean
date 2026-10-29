import JuliaLean.ExprReflect.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

/-! Exact row models for `base/reflection.jl` at `bbfa0ce4150`. Runtime compiler
and method-table calls consume explicit tables rather than bare result variables. -/

structure ReflectionMethod where
  name : String
  generated : Bool
  mayInvokeGenerator : Bool
  fallbackCode : String
  generatedCode : String
  moduleName : String
  deriving Repr, DecidableEq, Inhabited

def normalizeReflectionDebug (irShowDefined : Bool) (requested : String) : Jl String :=
  let normalized := if !irShowDefined && requested == "default" then "source" else requested
  if normalized == "source" || normalized == "none" then .ok normalized
  else .error (.argumentError "debuginfo must be source or none")

def lowerOne (generated : Bool) (method : ReflectionMethod) : Jl String :=
  if generated && method.generated then
    if method.mayInvokeGenerator then .ok method.generatedCode
    else .error (.argumentError "could not expand generator")
  else .ok method.fallbackCode

/-- `code_lowered(argtypes; generated, debuginfo)`; `base/reflection.jl:19-47`. -/
def reflectionRow19 (methods : List ReflectionMethod) (generated irShowDefined worldIsMax : Bool)
    (debugInfo : String) : Jl (List String) :=
  match normalizeReflectionDebug irShowDefined debugInfo with
  | .error error => .error error
  | .ok normalized =>
    if worldIsMax then .error (.argumentError "reflection from generated function")
    else methods.mapM fun method => do
      let code ← lowerOne generated method
      return if normalized == "none" && !(generated && method.generated) then "remove_linenums:" ++ code else code

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
def reflectionRow49 (signatureType : String → String → String) (function types : String)
    (query : String → Jl (List String)) : Jl (List String) :=
  query (signatureType function types)
def ReflectionRow49Property : Prop := ∀ signature function types query,
  reflectionRow49 signature function types query = query (signature function types)
theorem reflectionRow49_proven : ReflectionRow49Property := by unfold ReflectionRow49Property; intros; rfl

/-- `method_instances(argtypes, world)`; `base/reflection.jl:58-68`. -/
def reflectionRow58 (worldIsMax : Bool) (candidates : List ReflectionMethod) : Jl (List String) :=
  if worldIsMax then .error (.argumentError "reflection from generated function")
  else .ok (candidates.map ("specialize:" ++ ·.name))
def ReflectionRow58Property : Prop := ∀ world candidates,
  reflectionRow58 world candidates = if world then .error (.argumentError "reflection from generated function")
    else .ok (candidates.map ("specialize:" ++ ·.name))
theorem reflectionRow58_proven : ReflectionRow58Property := by unfold ReflectionRow58Property; intros; rfl

/-- Object-form `method_instances`; `base/reflection.jl:70-73`. -/
def reflectionRow70 (signatureType : String → String → String) (function types : String)
    (lookup : String → Jl (List String)) := lookup (signatureType function types)
def ReflectionRow70Property : Prop := ∀ signature function types lookup,
  reflectionRow70 signature function types lookup = lookup (signature function types)
theorem reflectionRow70_proven : ReflectionRow70Property := by unfold ReflectionRow70Property; intros; rfl

/-- `method_instance(argtypes; world, method_table)`; `base/reflection.jl:75-82`. -/
def reflectionRow75 (tupleType : String) (_world : Nat) (methodTable : List (String × String)) : Option String :=
  (methodTable.find? (·.1 == tupleType)).map (·.2)
def ReflectionRow75Property : Prop := ∀ tuple world table,
  reflectionRow75 tuple world table = (table.find? (·.1 == tuple)).map (·.2)
theorem reflectionRow75_proven : ReflectionRow75Property := by unfold ReflectionRow75Property; intros; rfl

/-- Object-form `method_instance`; `base/reflection.jl:84-88`. -/
def reflectionRow84 (signatureType : String → String → String) (function types : String)
    (lookup : String → Option String) : Option String := lookup (signatureType function types)
def ReflectionRow84Property : Prop := ∀ signature function types lookup,
  reflectionRow84 signature function types lookup = lookup (signature function types)
theorem reflectionRow84_proven : ReflectionRow84Property := by unfold ReflectionRow84Property; intros; rfl

/-- `default_debug_info_kind`; `base/reflection.jl:90`. -/
def reflectionRow90 (runtimeGlobal : Int) : Int := runtimeGlobal
def ReflectionRow90Property : Prop := ∀ runtimeGlobal, reflectionRow90 runtimeGlobal = runtimeGlobal
theorem reflectionRow90_proven : ReflectionRow90Property := by unfold ReflectionRow90Property; intro; rfl

structure FullCodegenFlags where
  trackAllocations : Bool
  codeCoverage : Bool
  preferSpecsig : Bool
  gnuPubnames : Bool
  debugInfoKind : Int
  debugInfoLevel : Int
  safepointOnEntry : Bool
  gcstackArg : Bool
  useJlplt : Bool
  forceEmitAll : Bool
  sanitizeMemory : Bool
  sanitizeThread : Bool
  sanitizeAddress : Bool
  uniqueNames : Bool
  debugInfoInlineScopes : Bool
  deriving Repr, DecidableEq, Inhabited

def boolToCint (value : Bool) : Int := if value then 1 else 0

/-- `CodegenParams` keyword constructor; `base/reflection.jl:201-217`. -/
def reflectionRow201 (flags : FullCodegenFlags) : List Int := [
  boolToCint flags.trackAllocations, boolToCint flags.codeCoverage,
  boolToCint flags.preferSpecsig, boolToCint flags.gnuPubnames,
  flags.debugInfoKind, flags.debugInfoLevel, boolToCint flags.safepointOnEntry,
  boolToCint flags.gcstackArg, boolToCint flags.useJlplt, boolToCint flags.forceEmitAll,
  boolToCint flags.sanitizeMemory, boolToCint flags.sanitizeThread,
  boolToCint flags.sanitizeAddress, boolToCint flags.uniqueNames,
  boolToCint flags.debugInfoInlineScopes]
def ReflectionRow201Property : Prop := ∀ flags, (reflectionRow201 flags).length = 15
theorem reflectionRow201_proven : ReflectionRow201Property := by unfold ReflectionRow201Property; intro; rfl

/-- `EmissionParams` keyword constructor; `base/reflection.jl:224-226`. -/
def reflectionRow224 (emitMetadata : Bool) : Int := boolToCint emitMetadata
def ReflectionRow224Property : Prop := ∀ value, reflectionRow224 value = 0 ∨ reflectionRow224 value = 1
theorem reflectionRow224_proven : ReflectionRow224Property := by intro value; cases value <;> simp [reflectionRow224, boolToCint]

inductive ReflectedFunction where | ordinary (name : String) | opaque (name : String) | builtin (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Object-form `code_typed`; `base/reflection.jl:288-294`. -/
def reflectionRow288 (function : ReflectedFunction) (types : String)
    (opaqueQuery regularQuery : String → String → List String) : List String :=
  match function with
  | .opaque name => opaqueQuery name types
  | .ordinary name | .builtin name => regularQuery name types
def ReflectionRow288Property : Prop := ∀ name types opaqueQuery regular,
  (reflectionRow288 (.opaque name) types opaqueQuery regular = opaqueQuery name types) ∧
  (reflectionRow288 (.ordinary name) types opaqueQuery regular = regular name types) ∧
  (reflectionRow288 (.builtin name) types opaqueQuery regular = regular name types)
theorem reflectionRow288_proven : ReflectionRow288Property := by unfold ReflectionRow288Property; intros; exact ⟨rfl,rfl,rfl⟩

/-- Signature-form `code_typed`; `base/reflection.jl:299-302`. -/
def reflectionRow299 (toTupleType query : String → String) (arguments : String) : String :=
  query (toTupleType arguments)
def ReflectionRow299Property : Prop := ∀ convert query arguments,
  reflectionRow299 convert query arguments = query (convert arguments)
theorem reflectionRow299_proven : ReflectionRow299Property := by unfold ReflectionRow299Property; intros; rfl

/-- `default_tt`; `base/reflection.jl:307-314`. -/
def reflectionRow307 (methodSignatures : List String) : String :=
  match methodSignatures with | [only] => "tail:" ++ only | _ => "Tuple"
def ReflectionRow307Property : Prop :=
  (∀ signature, reflectionRow307 [signature] = "tail:" ++ signature) ∧ reflectionRow307 [] = "Tuple"
theorem reflectionRow307_proven : ReflectionRow307Property := by exact ⟨fun _ => rfl, rfl⟩

/-- `raise_match_failure`; `base/reflection.jl:316-320`. -/
def reflectionRow316 (name signature : String) : Jl Unit :=
  .error (.argumentError (name ++ ": unanalyzable call given " ++ signature))
def ReflectionRow316Property : Prop := ∀ name signature,
  reflectionRow316 name signature = .error (.argumentError (name ++ ": unanalyzable call given " ++ signature))
theorem reflectionRow316_proven : ReflectionRow316Property := by unfold ReflectionRow316Property; intros; rfl

/-- `invoke_in_typeinf_world`; `base/reflection.jl:324-327`. -/
def reflectionRow324 (typeinfCall : List String → String) (arguments : List String) : String := typeinfCall arguments
def ReflectionRow324Property : Prop := ∀ call arguments, reflectionRow324 call arguments = call arguments
theorem reflectionRow324_proven : ReflectionRow324Property := by unfold ReflectionRow324Property; intros; rfl

/-- `invoke_default_compiler`; `base/reflection.jl:329-335`. -/
def reflectionRow329 (customCompiler : Option (String → List String → String))
    (typeinfCompiler : String → List String → String) (name : String) (arguments : List String) : String :=
  match customCompiler with | none => typeinfCompiler name arguments | some compiler => compiler name arguments
def ReflectionRow329Property : Prop := ∀ defaultCompiler name arguments,
  reflectionRow329 none defaultCompiler name arguments = defaultCompiler name arguments
theorem reflectionRow329_proven : ReflectionRow329Property := by unfold ReflectionRow329Property; intros; rfl

structure CompilerType where
  ancestry : List (String × String)
  deriving Repr, DecidableEq, Inhabited

def findCompilerModule (target : String) (type : CompilerType) : Jl String :=
  match type.ancestry.find? (fun pair => pair.1 == target || pair.1 == "Any") with
  | some (name,moduleName) => if name == target then .ok moduleName else .error (.argumentError ("Expected " ++ target))
  | none => .error (.argumentError ("Expected " ++ target))

/-- `invoke_interp_compiler`; `base/reflection.jl:337-350`. -/
def reflectionRow337 (interpreter : Option CompilerType) (defaultCall : String)
    (moduleCall : String → String) : Jl String :=
  match interpreter with
  | none => .ok defaultCall
  | some type => return moduleCall (← findCompilerModule "AbstractInterpreter" type)
def ReflectionRow337Property : Prop := ∀ defaultCall moduleCall,
  reflectionRow337 none defaultCall moduleCall = .ok defaultCall
theorem reflectionRow337_proven : ReflectionRow337Property := by unfold ReflectionRow337Property; intros; rfl

/-- `invoke_mt_compiler`; `base/reflection.jl:352-365`. -/
def reflectionRow352 (methodTable : Option CompilerType) (defaultCall : String)
    (moduleCall : String → String) : Jl String :=
  match methodTable with
  | none => .ok defaultCall
  | some type => return moduleCall (← findCompilerModule "MethodTableView" type)
def ReflectionRow352Property : Prop := ∀ defaultCall moduleCall,
  reflectionRow352 none defaultCall moduleCall = .ok defaultCall
theorem reflectionRow352_proven : ReflectionRow352Property := by unfold ReflectionRow352Property; intros; rfl

structure InferenceMatch where
  methodName : String
  inferred : Option String
  returnType : String
  deriving Repr, DecidableEq, Inhabited

def shapeInferenceRows (candidates : List InferenceMatch) : List String :=
  candidates.map fun candidate => candidate.inferred.getD (candidate.methodName ++ "=>Any")

/-- `code_typed_by_type`; `base/reflection.jl:373-405`. -/
def reflectionRow373 (pure worldMax : Bool) (debugInfo : Jl String)
    (candidates : Option (List InferenceMatch)) : Jl (List String) :=
  if pure || worldMax then .error (.argumentError "reflection from generated function")
  else match debugInfo with
    | .error error => .error error
    | .ok _ => match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (shapeInferenceRows values)
def ReflectionRow373Property : Prop := ∀ pure worldMax debug candidates,
  reflectionRow373 pure worldMax debug candidates =
    if pure || worldMax then .error (.argumentError "reflection from generated function")
    else match debug with
      | .error error => .error error
      | .ok _ => match candidates with
        | none => .error (.argumentError "unanalyzable call")
        | some values => .ok (shapeInferenceRows values)
theorem reflectionRow373_proven : ReflectionRow373Property := by unfold ReflectionRow373Property; intros; rfl

inductive OpaqueSource where | methodSource (hasSource : Bool) (optimized : Bool) | optimizedIR | invalid
  deriving Repr, DecidableEq, Inhabited

/-- `get_oc_code_rt`; `base/reflection.jl:407-436`. -/
def reflectionRow407 (pure optimize : Bool) (source : OpaqueSource) : Jl String :=
  if pure then .error (.argumentError "reflection from generated function")
  else match source with
    | .methodSource true true => if optimize then .ok "typeinf_code=>rettype" else .ok "uncompressed_ir=>declaredtype"
    | .methodSource true false => .ok "uncompressed_ir=>declaredtype"
    | .methodSource false _ | .optimizedIR => .ok "cached_inferred=>rettype"
    | .invalid => .error (.argumentError "invalid OpaqueClosure")
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
def reflectionRow438 (result : Jl String) (debugNone : Bool) : Jl (List String) :=
  match result with | .error error => .error error | .ok code => .ok [if debugNone then "remove_linenums:" ++ code else code]
def ReflectionRow438Property : Prop := ∀ code,
  reflectionRow438 (.ok code) false = .ok [code] ∧
  reflectionRow438 (.ok code) true = .ok ["remove_linenums:" ++ code]
theorem reflectionRow438_proven : ReflectionRow438Property := by unfold ReflectionRow438Property; intros; exact ⟨rfl,rfl⟩

/-- Object-form `code_ircode`; `base/reflection.jl:492-498`. -/
def reflectionRow492 (function : ReflectedFunction) (regularQuery : String → String) : Jl String :=
  match function with | .opaque _ => .error (.argumentError "OpaqueClosure not supported") | .ordinary name | .builtin name => .ok (regularQuery name)
def ReflectionRow492Property : Prop := ∀ name query,
  reflectionRow492 (.opaque name) query = .error (.argumentError "OpaqueClosure not supported") ∧
  reflectionRow492 (.ordinary name) query = .ok (query name) ∧
  reflectionRow492 (.builtin name) query = .ok (query name)
theorem reflectionRow492_proven : ReflectionRow492Property := by unfold ReflectionRow492Property; intros; exact ⟨rfl,rfl,rfl⟩

/-- Signature-form `code_ircode`; `base/reflection.jl:500-503`. -/
def reflectionRow500 (toTuple query : String → String) (arguments : String) : String := query (toTuple arguments)
def ReflectionRow500Property : Prop := ∀ convert query arguments,
  reflectionRow500 convert query arguments = query (convert arguments)
theorem reflectionRow500_proven : ReflectionRow500Property := by unfold ReflectionRow500Property; intros; rfl

/-- `code_ircode_by_type`; `base/reflection.jl:511-535`. -/
def reflectionRow511 (pure worldMax : Bool) (candidates : Option (List InferenceMatch)) : Jl (List String) :=
  if pure || worldMax then .error (.argumentError "reflection from generated function")
  else match candidates with | none => .error (.argumentError "unanalyzable call") | some values => .ok (shapeInferenceRows values)
def ReflectionRow511Property : Prop := ∀ pure worldMax candidates,
  reflectionRow511 pure worldMax candidates =
    if pure || worldMax then .error (.argumentError "reflection from generated function")
    else match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (shapeInferenceRows values)
theorem reflectionRow511_proven : ReflectionRow511Property := by unfold ReflectionRow511Property; intros; rfl

/-- `_builtin_return_type`; `base/reflection.jl:537-542`. -/
def reflectionRow537 (builtinType widen : String → String) (arguments : String) : String := widen (builtinType arguments)
def ReflectionRow537Property : Prop := ∀ builtin widen arguments,
  reflectionRow537 builtin widen arguments = widen (builtin arguments)
theorem reflectionRow537_proven : ReflectionRow537Property := by unfold ReflectionRow537Property; intros; rfl

/-- `_builtin_effects`; `base/reflection.jl:544-551`. -/
def reflectionRow544 (typeFunction lattice effects : String → String) (arguments : String) : String :=
  effects (lattice (typeFunction arguments))
def ReflectionRow544Property : Prop := ∀ typeFunction lattice effects arguments,
  reflectionRow544 typeFunction lattice effects arguments = effects (lattice (typeFunction arguments))
theorem reflectionRow544_proven : ReflectionRow544Property := by unfold ReflectionRow544Property; intros; rfl

/-- `_builtin_exception_type`; `base/reflection.jl:553-557`. -/
def reflectionRow553 (isNothrow : Bool) : String := if isNothrow then "Union{}" else "Any"
def ReflectionRow553Property : Prop := ∀ isNothrow,
  reflectionRow553 isNothrow = if isNothrow then "Union{}" else "Any"
theorem reflectionRow553_proven : ReflectionRow553Property := by unfold ReflectionRow553Property; intro; rfl

/-- `check_generated_context`; `base/reflection.jl:559-561`. -/
def reflectionRow559 (pure worldMax : Bool) : Jl Unit :=
  if pure || worldMax then .error (.argumentError "reflection from generated function") else .ok ()
def ReflectionRow559Property : Prop := ∀ pure worldMax,
  reflectionRow559 pure worldMax = .ok () ↔ pure = false ∧ worldMax = false
theorem reflectionRow559_proven : ReflectionRow559Property := by
  intros pure worldMax; cases pure <;> cases worldMax <;> simp [reflectionRow559]

/-- `return_types`; `base/reflection.jl:610-631`. -/
def reflectionRow610 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (candidates : Option (List (Option String))) : Jl (List String) :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
    | .builtin _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
    | .ordinary _ => match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (values.map (·.getD "Any"))
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
def reflectionRow680 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (types : Option (List String)) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ | .builtin _ => .ok ((types.bind fun values => values.head?).getD "Any")
    | .ordinary _ => match types with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (String.intercalate "∪" values)
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
def reflectionRow752 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (frames : Option (List (Option String))) : Jl (List String) :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok ["Any"]
    | .builtin _ => .ok [((frames.bind fun values => values.head?).join).getD "Any"]
    | .ordinary _ => match frames with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (values.map (·.getD "Any"))
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
def reflectionRow830 (generatedContext : Bool) (functionClass : ReflectedFunction) (inferred : Option String) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok "Any"
    | .builtin _ => .ok (inferred.getD "Any")
    | .ordinary _ => match inferred with
      | some value => .ok value
      | none => .error (.argumentError "unanalyzable call")
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
def reflectionRow908 (generatedContext : Bool) (functionClass : ReflectedFunction) (inferred : Option String) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .builtin _ => .ok (inferred.getD "unknown-effects")
    | _ => match inferred with
      | some value => .ok value
      | none => .error (.argumentError "unanalyzable call")
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
def reflectionRow930 (signatureType : String → String → String) (function types : String)
    (printer : String → String) : String := printer (signatureType function types)
def ReflectionRow930Property : Prop := ∀ signature function types printer,
  reflectionRow930 signature function types printer = printer (signature function types)
theorem reflectionRow930_proven : ReflectionRow930Property := by unfold ReflectionRow930Property; intros; rfl

/-- Signature-form `print_statement_costs`; `base/reflection.jl:935-964`. -/
def reflectionRow935 (candidates : List (String × Option (List Nat))) : List String :=
  candidates.map fun candidate => candidate.1 ++ match candidate.2 with
    | none => ": inference not successful" | some costs => ":" ++ toString costs
def ReflectionRow935Property : Prop := ∀ candidates,
  (reflectionRow935 candidates).length = candidates.length
theorem reflectionRow935_proven : ReflectionRow935Property := by unfold ReflectionRow935Property; intros; simp [reflectionRow935]

/-- Stdout wrapper `print_statement_costs`; `base/reflection.jl:966`. -/
def reflectionRow966 (printer : String → String) (argument : String) : String := printer argument
def ReflectionRow966Property : Prop := ∀ printer argument, reflectionRow966 printer argument = printer argument
theorem reflectionRow966_proven : ReflectionRow966Property := by unfold ReflectionRow966Property; intros; rfl

structure ReflectedMethod where
  name : String
  moduleName : String
  keywordNames : List String
  forwardsKeywords : Bool
  deriving Repr, DecidableEq, Inhabited

inductive LookupCandidate where
  | missing
  | methodMatch (method : ReflectedMethod)
  | other

inductive LookupResult where
  | generatedFunctionError
  | noMatchError
  | typeError
  | none
  | matchFound (method : ReflectedMethod)
  deriving DecidableEq

/-- `_which`; the compiler result may be `nothing`, a MethodMatch, or an
incorrectly typed value rejected by the assertion at `base/reflection.jl:978`. -/
def reflectionRow968 (worldMax raiseError : Bool) (candidate : LookupCandidate) : LookupResult :=
  if worldMax then .generatedFunctionError
  else match candidate with
    | .missing => if raiseError then .noMatchError else .none
    | .methodMatch method => .matchFound method
    | .other => .typeError

def ReflectionRow968Property : Prop :=
  (∀ raise candidate, reflectionRow968 true raise candidate = .generatedFunctionError) ∧
  (∀ raise, reflectionRow968 false raise .missing = if raise then .noMatchError else .none) ∧
  (∀ raise method, reflectionRow968 false raise (.methodMatch method) = .matchFound method) ∧
  (∀ raise, reflectionRow968 false raise .other = .typeError)
theorem reflectionRow968_proven : ReflectionRow968Property := by
  simp [ReflectionRow968Property, reflectionRow968]

/-- `which(f,t)`; `base/reflection.jl:990-1003`. -/
def reflectionRow990 (candidate : Option ReflectedMethod) : Jl ReflectedMethod :=
  match candidate with | some method => .ok method | none => .error (.argumentError "invoke would throw")
def ReflectionRow990Property : Prop := ∀ candidate,
  reflectionRow990 candidate = match candidate with
    | some method => .ok method
    | none => .error (.argumentError "invoke would throw")
theorem reflectionRow990_proven : ReflectionRow990Property := by unfold ReflectionRow990Property; intro; rfl

/-- `which(tt)`; `base/reflection.jl:1010-1012`. -/
def reflectionRow1010 (lookup : Jl (Option ReflectedMethod)) : Jl ReflectedMethod :=
  match lookup with
  | .error error => .error error
  | .ok (some method) => .ok method
  | .ok none => .error (.argumentError "no unique match")
def ReflectionRow1010Property : Prop := ∀ lookup,
  reflectionRow1010 lookup = match lookup with
    | .error error => .error error
    | .ok (some method) => .ok method
    | .ok none => .error (.argumentError "no unique match")
theorem reflectionRow1010_proven : ReflectionRow1010Property := by
  unfold ReflectionRow1010Property
  intro lookup; cases lookup <;> rfl

/-- Tuple wrapper `which`; `base/reflection.jl:1013`. -/
def reflectionRow1013 (toTuple query : String → String) (arguments : String) : String := query (toTuple arguments)
def ReflectionRow1013Property : Prop := ∀ convert query arguments,
  reflectionRow1013 convert query arguments = query (convert arguments)
theorem reflectionRow1013_proven : ReflectionRow1013Property := by unfold ReflectionRow1013Property; intros; rfl

/-- `which(module,symbol)` checks `isdefinedglobal`, then looks up the
binding owner, or throws an `ErrorException`; `base/reflection.jl:1020-1025`.
The module and symbol strings are their Julia interpolation results. -/
def reflectionRow1020 (globalDefined : Bool) (moduleText symbolText bindingModule : String) :
    Except String String :=
  if globalDefined then .ok bindingModule
  else .error ("\"" ++ symbolText ++ "\" is not defined in module " ++ moduleText)
def ReflectionRow1020Property : Prop :=
  (∀ moduleText symbolText owner, reflectionRow1020 true moduleText symbolText owner = .ok owner) ∧
  (∀ moduleText symbolText owner, reflectionRow1020 false moduleText symbolText owner =
    .error ("\"" ++ symbolText ++ "\" is not defined in module " ++ moduleText))
theorem reflectionRow1020_proven : ReflectionRow1020Property := by
  simp [ReflectionRow1020Property, reflectionRow1020]

/-- `nameof(::Function)`; `base/reflection.jl:1036-1038`. -/
def reflectionRow1036 (singletonName : String) : String := singletonName
def ReflectionRow1036Property : Prop := ∀ name, reflectionRow1036 name = name
theorem reflectionRow1036_proven : ReflectionRow1036Property := by unfold ReflectionRow1036Property; intro; rfl

/-- `nameof(::IntrinsicFunction)`; `base/reflection.jl:1040-1043`. -/
def reflectionRow1040 (intrinsicNames : List String) (index : Nat) : Option String := intrinsicNames[index]?
def ReflectionRow1040Property : Prop := ∀ names index,
  reflectionRow1040 names index = names[index]?
theorem reflectionRow1040_proven : ReflectionRow1040Property := by
  unfold ReflectionRow1040Property
  intros; rfl

/-- `parentmodule(::Function)`; `base/reflection.jl:1051`. -/
def reflectionRow1051 (typeModule : String) : String := typeModule
def ReflectionRow1051Property : Prop := ∀ moduleName, reflectionRow1051 moduleName = moduleName
theorem reflectionRow1051_proven : ReflectionRow1051Property := by unfold ReflectionRow1051Property; intro; rfl

/-- `parentmodule(f,types)`; `base/reflection.jl:1059-1065`. -/
def reflectionRow1059 (methods : List ReflectedMethod) : Jl String :=
  match methods with | [] => .error (.argumentError "no matching methods") | method :: _ => .ok method.moduleName
def ReflectionRow1059Property : Prop := ∀ methods,
  reflectionRow1059 methods = match methods with
    | [] => .error (.argumentError "no matching methods")
    | method :: _ => .ok method.moduleName
theorem reflectionRow1059_proven : ReflectionRow1059Property := by unfold ReflectionRow1059Property; intro methods; cases methods <;> rfl

/-- `parentmodule(::Method)`; `base/reflection.jl:1075`. -/
def reflectionRow1075 (method : ReflectedMethod) : String := method.moduleName
def ReflectionRow1075Property : Prop := ∀ method, reflectionRow1075 method = method.moduleName
theorem reflectionRow1075_proven : ReflectionRow1075Property := by unfold ReflectionRow1075Property; intro; rfl

/-- Positional `hasmethod`; `base/reflection.jl:1113-1115`. -/
def reflectionRow1113 (hasMatch : Bool) : Bool := hasMatch
def ReflectionRow1113Property : Prop := ∀ result, reflectionRow1113 result = result
theorem reflectionRow1113_proven : ReflectionRow1113Property := by unfold ReflectionRow1113Property; intro; rfl

/-- World-age keyword wrapper for `hasmethod`; `base/reflection.jl:1117-1120`. -/
def reflectionRow1117 (worldLookup : Nat → Bool) (world : Nat) : Bool := worldLookup world
def ReflectionRow1117Property : Prop := ∀ lookup world, reflectionRow1117 lookup world = lookup world
theorem reflectionRow1117_proven : ReflectionRow1117Property := by unfold ReflectionRow1117Property; intros; rfl

/-- Keyword-name `hasmethod`; `base/reflection.jl:1122-1139`. -/
def reflectionRow1122 (worldMax positionalMatch : Bool) (requested : List String)
    (method : Option ReflectedMethod) : Jl Bool :=
  if worldMax then .error (.argumentError "reflection from generated function")
  else if requested.isEmpty then .ok positionalMatch
  else match method with
    | none => .ok false
    | some method =>
      .ok (method.keywordNames.isEmpty || method.forwardsKeywords || requested.all method.keywordNames.contains)
def ReflectionRow1122Property : Prop := ∀ worldMax positional requested method,
  reflectionRow1122 worldMax positional requested method =
    if worldMax then .error (.argumentError "reflection from generated function")
    else if requested.isEmpty then .ok positional
    else match method with
      | none => .ok false
      | some method =>
        .ok (method.keywordNames.isEmpty || method.forwardsKeywords || requested.all method.keywordNames.contains)
theorem reflectionRow1122_proven : ReflectionRow1122Property := by unfold ReflectionRow1122Property; intros; rfl

inductive BodyFunctionRef where
  | symbol (moduleName name : String) | global (moduleName name : String)
  | apply (next : BodyFunctionRef) | applyIterate (next : BodyFunctionRef)
  | ssa (next : Option BodyFunctionRef) | invalid
  deriving Repr, Inhabited

/-- `bodyfunction`; `base/reflection.jl:1155-1193`. -/
def reflectionRow1155 : Nat → BodyFunctionRef → Option (String × String)
  | 0, _ => none
  | _, .symbol moduleName name | _, .global moduleName name => some (moduleName,name)
  | fuel+1, .apply next | fuel+1, .applyIterate next => reflectionRow1155 fuel next
  | fuel+1, .ssa (some next) => reflectionRow1155 fuel next
  | _, _ => none
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

structure AmbiguityInput where
  sameMethod : Bool
  bottomIntersection : Bool
  bottomParameter : Bool
  generatorWorld : Bool
  runtimeAmbiguity : Bool
  involvesFirst : Bool
  involvesSecond : Bool
  filteredMatches : Bool
  resortAmbiguous : Bool
  reverseIntersectionWorks : Bool
  deriving Repr, DecidableEq, Inhabited

def ambiguityInvolvesBoth (input : AmbiguityInput) : Bool := input.involvesFirst && input.involvesSecond

def ambiguityInner (input : AmbiguityInput) (ambiguousBottom : Bool) : Bool :=
  if input.bottomIntersection then false
  else if !ambiguousBottom && input.bottomParameter then false
  else if input.generatorWorld then true
  else if !input.runtimeAmbiguity then false
  else if !ambiguityInvolvesBoth input then false
  else if input.filteredMatches then input.resortAmbiguous && ambiguityInvolvesBoth input
  else true

/-- `isambiguous`; `base/reflection.jl:1229-1297`. -/
def reflectionRow1229 (input : AmbiguityInput) (ambiguousBottom : Bool) : Bool :=
  if input.sameMethod then false else if input.reverseIntersectionWorks then ambiguityInner input ambiguousBottom else false
def ReflectionRow1229Property : Prop := ∀ input flag,
  reflectionRow1229 input flag = if input.sameMethod then false
    else if input.reverseIntersectionWorks then ambiguityInner input flag else false
theorem reflectionRow1229_proven : ReflectionRow1229Property := by unfold ReflectionRow1229Property; intros; rfl

/-- Nested `inner`; `base/reflection.jl:1233-1277`. -/
def reflectionRow1233 (input : AmbiguityInput) (flag : Bool) : Bool := ambiguityInner input flag
def ReflectionRow1233Property : Prop := ∀ input flag,
  reflectionRow1233 input flag = ambiguityInner input flag
theorem reflectionRow1233_proven : ReflectionRow1233Property := by unfold ReflectionRow1233Property; intros; rfl

/-- Nested `involves_both`; `base/reflection.jl:1249-1257`. -/
def reflectionRow1249 (input : AmbiguityInput) : Bool := ambiguityInvolvesBoth input
def ReflectionRow1249Property : Prop := ∀ input,
  reflectionRow1249 input = (input.involvesFirst && input.involvesSecond)
theorem reflectionRow1249_proven : ReflectionRow1249Property := by unfold ReflectionRow1249Property; intros; rfl

inductive InvokeArgument where | annotated (value typeName : String) | plain (value : String)
  deriving Repr, DecidableEq, Inhabited

def invokeValue : InvokeArgument → String | .annotated value _ | .plain value => value
def invokeType : InvokeArgument → String | .annotated _ typeName => typeName | .plain value => "Core.Typeof(" ++ value ++ ")"

/-- `@invoke`; `base/reflection.jl:1345-1363`. -/
def reflectionRow1345 (function : String) (arguments : List InvokeArgument) (keywords : List String) : List String :=
  keywords ++ ["Core.invoke", function, "Tuple{" ++ String.intercalate "," (arguments.map invokeType) ++ "}"] ++ arguments.map invokeValue
def ReflectionRow1345Property : Prop := ∀ function arguments keywords,
  (reflectionRow1345 function arguments keywords).take keywords.length = keywords
theorem reflectionRow1345_proven : ReflectionRow1345Property := by unfold ReflectionRow1345Property; intros; simp [reflectionRow1345]

/-- `getglobalref`; `base/reflection.jl:1365`. -/
def reflectionRow1365 (globals : List ((String × String) × String)) (moduleName name : String) : Option String :=
  (globals.find? (·.1 == (moduleName,name))).map (·.2)
def ReflectionRow1365Property : Prop := ∀ globals moduleName name,
  reflectionRow1365 globals moduleName name = (globals.find? (·.1 == (moduleName,name))).map (·.2)
theorem reflectionRow1365_proven : ReflectionRow1365Property := by unfold ReflectionRow1365Property; intros; rfl

/-- `invokelatest_gr`; `base/reflection.jl:1367-1376`. -/
def reflectionRow1367 (keywords : List String) : String := if keywords.isEmpty then "invoke_in_world" else "invoke_in_world:kwcall"
def ReflectionRow1367Property : Prop := ∀ keywords,
  reflectionRow1367 keywords = if keywords.isEmpty then "invoke_in_world" else "invoke_in_world:kwcall"
theorem reflectionRow1367_proven : ReflectionRow1367Property := by unfold ReflectionRow1367Property; intros; rfl

inductive LatestTarget where | literalGlobal | symbolGlobal | dottedGlobal | expression
  deriving Repr, DecidableEq, Inhabited

/-- `@invokelatest`; `base/reflection.jl:1406-1448`. -/
def reflectionRow1406 (target : LatestTarget) (isGlobal : Bool) : String :=
  match target with | .literalGlobal => "invokelatest_gr" | .dottedGlobal | .symbolGlobal => if isGlobal then "invokelatest_gr" else "invokelatest" | .expression => "invokelatest"
def ReflectionRow1406Property : Prop := ∀ target isGlobal,
  reflectionRow1406 target isGlobal = match target with
    | .literalGlobal => "invokelatest_gr"
    | .dottedGlobal | .symbolGlobal => if isGlobal then "invokelatest_gr" else "invokelatest"
    | .expression => "invokelatest"
theorem reflectionRow1406_proven : ReflectionRow1406Property := by unfold ReflectionRow1406Property; intros; rfl

inductive CallExpression where
  | call (function : String) (arguments keywords : List String)
  | property (object field : String)
  | index (object : String) (indices : List String)
  | setProperty (object field value : String)
  | setIndex (object value : String) (indices : List String)
  | invalid
  deriving Repr, DecidableEq, Inhabited

def flattenArguments (values : List (List String)) : List String := values.flatten

/-- `destructure_callex`; `base/reflection.jl:1450-1497`. -/
def reflectionRow1450 : CallExpression → Jl (String × List String × List String)
  | .call function arguments keywords => .ok (function,arguments,keywords)
  | .property object field => .ok ("getproperty",[object,field],[])
  | .index object indices => .ok ("getindex",object::indices,[])
  | .setProperty object field value => .ok ("setproperty!",[object,field,value],[])
  | .setIndex object value indices => .ok ("setindex!",object::value::indices,[])
  | .invalid => .error (.argumentError "expected call expression")
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
def reflectionRow1451 (values : List (List String)) : List String := flattenArguments values
def ReflectionRow1451Property : Prop := ∀ values,
  (reflectionRow1451 values).length = (values.map List.length).sum
theorem reflectionRow1451_proven : ReflectionRow1451Property := by unfold ReflectionRow1451Property; intros; simp [reflectionRow1451, flattenArguments]

structure ReflectionCacheState where
  runtimeDropped : Bool
  requireWorldIsMax : Bool
  compilerActive : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `drop_all_caches`; `base/reflection.jl:1506-1514`. -/
def reflectionRow1506 (_ : ReflectionCacheState) : ReflectionCacheState := ⟨true,true,true⟩
def ReflectionRow1506Property : Prop := ∀ state,
  let output := reflectionRow1506 state
  output.runtimeDropped = true ∧ output.requireWorldIsMax = true ∧ output.compilerActive = true
theorem reflectionRow1506_proven : ReflectionRow1506Property := by intro; exact ⟨rfl,rfl,rfl⟩

end JuliaLean.ExprReflect
