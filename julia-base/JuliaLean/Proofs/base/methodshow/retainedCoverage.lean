import JuliaLean.base.methodshow


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

def MethodSignatureHelpersExact : Prop :=
  (∀ form, stripGensym form = match form with
    | .self | .unused => ""
    | .generated base | .plain base => base) ∧
  (∀ name typeText isAny vararg,
    argumentDeclaration name typeText isAny vararg =
      let stripped := stripGensym (.plain name)
      match vararg with
      | .ordinary => if isAny then (stripped, "") else (stripped, typeText)
      | .unbounded => if isAny then (stripped ++ "...", "") else (stripped, typeText ++ "...")
      | .fixed count => (stripped, "Vararg{" ++ typeText ++ ", " ++ toString count ++ "}")) ∧
  (∀ slotNames argumentCount,
    methodArgumentNames slotNames argumentCount =
      if slotNames.isEmpty then [] else slotNames.take argumentCount) ∧
  (∀ arguments, argumentDeclarationParts arguments = arguments) ∧
  (∀ slots, keywordDeclarations slots =
    let filtered := slots.filter fun name => !name.isEmpty && !name.contains '#'
    if filtered.isEmpty then ["..."] else moveSplatLast filtered) ∧
  (∀ parameters, showWhereParameters parameters = match parameters with
    | [] => ""
    | [parameter] => " where " ++ parameter
    | parameters => " where {" ++ String.intercalate ", " parameters ++ "}") ∧
  (∀ empty generated shown,
    symbolToString empty generated shown =
      if empty then "..." else if generated then shown ++ "..." else shown)

theorem methodSignatureHelpersExact : MethodSignatureHelpersExact := by
  constructor
  · intro form; cases form <;> rfl
  repeat' apply And.intro
  all_goals intros <;> rfl

def MethodLocationDisplayExact : Prop :=
  (∀ buildPathDiff compilerSource stdlibPath compilerPath path,
    fixupStdlibPath buildPathDiff compilerSource stdlibPath compilerPath path =
      if compilerSource then compilerPath else if buildPathDiff then stdlibPath else path) ∧
  (∀ original callback,
    updatedMethodLocation original callback = callback.getD original) ∧
  (∀ callable locations,
    singleFunctionLocation callable locations = match locations with
    | [] => if callable then .noDefinitions else .notCallable
    | [(file, line)] => .location file line
    | _ => .multipleDefinitions) ∧
  (∀ count kind name moduleName,
    methodListHeader count kind name moduleName =
      s!"# {count} {if count = 1 then "method" else "methods"} for {kind} {name} from {moduleName}" ++
        (if count = 0 then "" else ":")) ∧
  moduleColor = none ∧
  (∀ rows maximum,
    methodTableRows rows maximum = if maximum < 0 then rows else rows.take maximum.toNat) ∧
  (∀ parents, inBase parents = parents.contains "Base") ∧
  (∀ header rows html,
    renderMethodContainer header rows html =
      if html then header ++ "<ul>" ++
        String.intercalate "" (rows.map fun row => "<li> " ++ row ++ "</li> ") ++ "</ul>"
      else header ++ String.intercalate "\n" rows) ∧
  (∀ valid inBaseModule hasCommit commit file line,
    methodUrl valid inBaseModule hasCommit commit file line =
      if !valid then .none
      else if inBaseModule then .github (if hasCommit then commit else "tag") file line
      else .localFile file line)

theorem methodLocationDisplayExact : MethodLocationDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.ErrorShow.Coverage
