import JuliaLean.Proofs.base.methodshow.retainedCoverage

/-! Method-specific models for `base/methodshow.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.MethodshowFaithful

open JuliaLean.ErrorShow.Coverage


def StripGensymExact : Prop := ∀ symbol, stripGensym symbol = match symbol with
  | .self | .unused => "" | .generated base | .plain base => base
theorem stripGensymExact : StripGensymExact := by unfold StripGensymExact; intro symbol; cases symbol <;> rfl

def ArgtypeDeclExact : Prop := ∀ name argType, argtypeDecl name argType = match argType with
  | .any => (stripGensym name, "")
  | .ordinary text => (stripGensym name, text)
  | .unboundedVararg "Any" => (stripGensym name ++ "...", "")
  | .unboundedVararg text => (stripGensym name, text ++ "...")
  | .fixedVararg text count => (stripGensym name, "Vararg{" ++ text ++ ", " ++ toString count ++ "}")
theorem argtypeDeclExact : ArgtypeDeclExact := by
  unfold ArgtypeDeclExact
  intro name argType
  cases argType <;> rfl

def MethodArgnamesExact : Prop := ∀ names nargs,
  methodArgnames names nargs = if names.isEmpty then [] else names.take nargs
theorem methodArgnamesExact : MethodArgnamesExact := by unfold MethodArgnamesExact; intros; rfl

def ArgDeclPartsExact : Prop := ∀ typevars argnames argtypes file line,
  (argDeclParts typevars argnames argtypes file line).declarations =
    if argnames.length < argtypes.length then List.replicate argtypes.length ("", "")
    else (argnames.zip argtypes).map fun (name, type) => argtypeDecl name type
theorem argDeclPartsExact : ArgDeclPartsExact := by unfold ArgDeclPartsExact; intros; rfl

def KwargDeclExact : Prop := ∀ eligible found slotnames, kwargDecl eligible found slotnames =
  if !eligible || !found then [] else
    let filtered := slotnames.filter fun name => !name.isEmpty && !name.contains '#'
    let moved := match filtered.find? (·.endsWith "...") with | none => filtered | some splat => filtered.erase splat ++ [splat]
    if moved.isEmpty then ["..."] else moved
theorem kwargDeclExact : KwargDeclExact := by unfold KwargDeclExact; intros; rfl

def ShowMethodParamsExact : Prop := ∀ parameters, showMethodParams parameters = match parameters with
  | [] => "" | [parameter] => " where " ++ parameter
  | parameters => " where {" ++ String.intercalate ", " parameters ++ "}"
theorem showMethodParamsExact : ShowMethodParamsExact := by
  unfold ShowMethodParamsExact
  intro parameters
  cases parameters with
  | nil => rfl
  | cons head tail => cases tail <;> rfl

def FixupStdlibPathExact : Prop := ∀ stdlibDiff compilerSource stdlib compiler original,
  fixupStdlibPath stdlibDiff compilerSource stdlib compiler original =
    if compilerSource then compiler else if stdlibDiff then stdlib else original
theorem fixupStdlibPathExact : FixupStdlibPathExact := by unfold FixupStdlibPathExact; intros; rfl

def UpdatedMethodlocExact : Prop := ∀ original callback,
  updatedMethodloc original callback = callback.orElse fun _ => original
theorem updatedMethodlocExact : UpdatedMethodlocExact := by unfold UpdatedMethodlocExact; intros; rfl

def FunctionlocMethodExact : Prop := ∀ file line, functionlocMethod file line =
  if line ≤ 0 then .error "could not determine location of method definition" else .ok (file, line)
theorem functionlocMethodExact : FunctionlocMethodExact := by unfold FunctionlocMethodExact; intros; rfl

def FunctionlocMethodInstanceExact : Prop := ∀ file line,
  functionlocMethodInstance file line = functionlocMethod file line
theorem functionlocMethodInstanceExact : FunctionlocMethodInstanceExact := by unfold FunctionlocMethodInstanceExact; intros; rfl

def FunctionlocFunctionTypesExact : Prop := ∀ selectedFile selectedLine,
  functionlocFunctionTypes selectedFile selectedLine = functionlocMethod selectedFile selectedLine
theorem functionlocFunctionTypesExact : FunctionlocFunctionTypesExact := by unfold FunctionlocFunctionTypesExact; intros; rfl

def FunctionlocArgtypesExact : Prop := ∀ selectedFile selectedLine,
  functionlocArgtypes selectedFile selectedLine = functionlocMethod selectedFile selectedLine
theorem functionlocArgtypesExact : FunctionlocArgtypesExact := by unfold FunctionlocArgtypesExact; intros; rfl

def FunctionlocSingleExact : Prop := ∀ callable methods, functionlocSingle callable methods = match methods with
  | [] => .error (if callable then "function has no definitions" else "object is not callable")
  | [method] => .ok method
  | _ => .error "function has multiple methods; please specify a type signature"
theorem functionlocSingleExact : FunctionlocSingleExact := by
  unfold FunctionlocSingleExact
  intro callable methods
  cases methods with
  | nil => rfl
  | cons head tail => cases tail <;> rfl

def SymToStringExact : Prop := ∀ symbol, symToString symbol = match symbol with
  | .ellipsis => "..." | .trailingDots base => base ++ "..." | .ordinary shown => shown
theorem symToStringExact : SymToStringExact := by unfold SymToStringExact; intro symbol; cases symbol <;> rfl

def ShowMethodCompactExact : Prop := ∀ rendered, showMethodCompact rendered = rendered
theorem showMethodCompactExact : ShowMethodCompactExact := by unfold ShowMethodCompactExact; intros; rfl

def ShowMethodPlainExact : Prop := ∀ rendered, showMethodPlain rendered = rendered
theorem showMethodPlainExact : ShowMethodPlainExact := by unfold ShowMethodPlainExact; intros; rfl

def ShowMethodExact : Prop := ∀ method compact signatureOnly, showMethod method compact signatureOnly =
  let args := method.args.map fun (name, type) => name ++ if type.isEmpty then "" else "::" ++ type
  let keywords := if method.keywords.isEmpty then "" else "; " ++ String.intercalate ", " method.keywords
  let signature := method.functionName ++ "(" ++ String.intercalate ", " args ++ keywords ++ ")" ++ showMethodParams method.typevars
  if signatureOnly then signature else signature ++ (if compact then " " else "\n") ++ method.location
theorem showMethodExact : ShowMethodExact := by unfold ShowMethodExact; intros; rfl

def ShowMethodCompactFaithfulExact : Prop := ∀ method,
  showMethodCompactFaithful method = showMethod method true false
theorem showMethodCompactFaithfulExact : ShowMethodCompactFaithfulExact := by unfold ShowMethodCompactFaithfulExact; intros; rfl

def ShowMethodPlainFaithfulExact : Prop := ∀ method,
  showMethodPlainFaithful method = showMethod method false false
theorem showMethodPlainFaithfulExact : ShowMethodPlainFaithfulExact := by unfold ShowMethodPlainFaithfulExact; intros; rfl

def MethodListHeaderExact : Prop := ∀ count kind name moduleName, methodListHeader count kind name moduleName =
  "# " ++ toString count ++ " " ++ (if count = 1 then "method" else "methods") ++
    " for " ++ kind ++ " " ++ name ++ " from " ++ moduleName ++ if count = 0 then "" else ":"
theorem methodListHeaderExact : MethodListHeaderExact := by unfold MethodListHeaderExact; intros; rfl

def ModuleColorExact : Prop := ∀ method, moduleColor method = none
theorem moduleColorExact : ModuleColorExact := by unfold ModuleColorExact; intros; rfl

def ShowMethodTableExact : Prop := ∀ header methods maximum,
  showMethodTable header methods maximum =
    let shown := if maximum < 0 then methods else methods.take maximum.toNat
    let rest := methods.length - shown.length
    header.getD "" ++ String.intercalate "\n" (shown.zipIdx.map fun (method, i) => s!" [{i+1}] {method}") ++
      (if rest = 0 then "" else "\n... " ++ toString rest ++ " methods not shown")
theorem showMethodTableExact : ShowMethodTableExact := by unfold ShowMethodTableExact; intros; rfl

def ShowMethodListExact : Prop := ∀ table, showMethodList table = table
theorem showMethodListExact : ShowMethodListExact := by unfold ShowMethodListExact; intros; rfl

def ShowMethodListPlainExact : Prop := ∀ table, showMethodListPlain table = table
theorem showMethodListPlainExact : ShowMethodListPlainExact := by unfold ShowMethodListPlainExact; intros; rfl

def ShowCoreMethodTableExact : Prop := ∀ moduleName methodName count,
  showCoreMethodTable moduleName methodName count = moduleName ++ "." ++ methodName ++
    " is a Core.MethodTable with " ++ toString count ++ " methods."
theorem showCoreMethodTableExact : ShowCoreMethodTableExact := by unfold ShowCoreMethodTableExact; intros; rfl

def InBaseExact : Prop := ∀ modules, inBase modules = match modules with
  | [] => false
  | moduleName :: parents => "Base" == moduleName || inBase parents
theorem inBaseExact : InBaseExact := by
  unfold InBaseExact
  intro modules
  cases modules <;> rfl

def FileUrlExact : Prop := ∀ resolved, fileUrl resolved = resolved.getD ""
theorem fileUrlExact : FileUrlExact := by unfold FileUrlExact; intros; rfl

def MethodUrlExact : Prop := ∀ input, methodUrl input = match input with
  | .invalid => "" | .baseTagged version file line => s!"https://github.com/JuliaLang/julia/tree/v{version}/base/{file}#L{line}"
  | .baseCommit commit file line => s!"https://github.com/JuliaLang/julia/tree/{commit}/base/{file}#L{line}"
  | .package url => url | .local file => "file://" ++ file
theorem methodUrlExact : MethodUrlExact := by unfold MethodUrlExact; intro input; cases input <;> rfl

def ShowMethodHtmlExact : Prop := ∀ signature moduleName location url, showMethodHtml signature moduleName location url =
  signature ++ " in " ++ moduleName ++ match url with | none => location | some href => " at <a href=\"" ++ href ++ "\" target=\"_blank\">" ++ location ++ "</a>"
theorem showMethodHtmlExact : ShowMethodHtmlExact := by unfold ShowMethodHtmlExact; intros; rfl

def ShowMethodListHtmlExact : Prop := ∀ header methods, showMethodListHtml header methods =
  header ++ "<ul>" ++ String.intercalate "" (methods.map fun method => "<li> " ++ method ++ "</li> ") ++ "</ul>"
theorem showMethodListHtmlExact : ShowMethodListHtmlExact := by unfold ShowMethodListHtmlExact; intros; rfl

def ShowMethodVectorPlainExact : Prop := ∀ summary methods,
  showMethodVectorPlain summary methods =
    if methods.isEmpty then summary
    else String.intercalate "\n" (methods.zipIdx.map fun (method, i) => s!"[{i+1}] {method}")
theorem showMethodVectorPlainExact : ShowMethodVectorPlainExact := by unfold ShowMethodVectorPlainExact; intros; rfl

def ShowMethodVectorHtmlExact : Prop := ∀ summary methods,
  showMethodVectorHtml summary methods = summary ++ if methods.isEmpty then ""
    else ":<ul>" ++ String.intercalate "" (methods.map fun method => "<li> " ++ method ++ "</li>") ++ "</ul>"
theorem showMethodVectorHtmlExact : ShowMethodVectorHtmlExact := by unfold ShowMethodVectorHtmlExact; intros; rfl

end JuliaLean.ErrorShow.MethodshowFaithful
