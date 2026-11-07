import JuliaLean.base.reflection
import JuliaLean.Proofs.base.reflection.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean

def ReflectionLoweredBodies : Prop := ∀ candidate,
  loweredCandidate false candidate = .ok candidate.fallback ∧
  (candidate.generated = false → loweredCandidate true candidate = .ok candidate.fallback) ∧
  (∀ candidates, (methodInstancesModel candidates).length = candidates.length) ∧
  normalizeDebugInfo false "default" = .ok "source" ∧
  reflectionWorldAllowed false false = true

theorem reflectionLoweredBodies_proven : ReflectionLoweredBodies := by
  intro candidate
  constructor
  · simp [loweredCandidate]
  constructor
  · intro h
    simp [loweredCandidate, h]
  constructor
  · intro candidates; simp [methodInstancesModel]
  exact ⟨rfl, rfl⟩

def ReflectionParamBodies : Prop := ∀ flags,
  (codegenParamsModel flags).length = 4 ∧
  (codegenParamsModel flags).all (fun value => value = 0 || value = 1) ∧
  (emissionParamsModel flags.emitMetadata = 0 ∨ emissionParamsModel flags.emitMetadata = 1)

theorem reflectionParamBodies_proven : ReflectionParamBodies := by
  intro flags
  rcases flags with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def ReflectionCompilerBodies : Prop := ∀ reflection interp table,
  compilerRoute reflection interp table =
    if interp then .interpreterModule
    else if table then .methodTableModule
    else if reflection then .reflectionModule else .typeinfWorld

theorem reflectionCompilerBodies_proven : ReflectionCompilerBodies := by
  unfold ReflectionCompilerBodies
  intros
  rfl

/-! ## base/reflection.jl: query result shaping -/

def ReflectionQueryBodies : Prop := ∀ results,
  (codeQueryRows results).length = results.length ∧
  (returnTypeRows .ordinary results).length = results.length ∧
  (exceptionTypeRows .ordinary results).length = results.length ∧
  (irCodeQueryRows (results.map (·.map fun value => (value, value)))).length = results.length ∧
  checkGeneratedContext false false = .ok ()

theorem reflectionQueryBodies_proven : ReflectionQueryBodies := by
  intro results
  simp [codeQueryRows, returnTypeRows, exceptionTypeRows, irCodeQueryRows,
    checkGeneratedContext]

/-! ## base/reflection.jl: public method APIs and ambiguity -/

def ReflectionApiBodies : Prop :=
  (∀ method, hasKeywordMethod method [] = method.positionalMatch) ∧
  (∀ moduleName rest, parentModuleModel (moduleName :: rest) = .ok moduleName) ∧
  (∀ table modules method, whichMethod table modules = some method → hasMethod table modules = true) ∧
  (∀ moduleName name, bodyFunctionModel (.globalRef moduleName name) = some (moduleName, name))

theorem reflectionApiBodies_proven : ReflectionApiBodies := by
  constructor
  · intro method
    simp [hasKeywordMethod]
  constructor
  · intros; rfl
  constructor
  · exact whichHasMethod_proven
  · intros; rfl

def ReflectionAmbiguityBodies : Prop := ∀ facts flag,
  isAmbiguousModel facts flag = true → facts.sameMethod = false ∧ facts.bottomIntersection = false

theorem reflectionAmbiguityBodies_proven : ReflectionAmbiguityBodies := by
  intro facts flag h
  simp [isAmbiguousModel] at h
  exact h.1

/-! ## base/reflection.jl: invoke macros and cache reset -/

def ReflectionInvokeBodies : Prop :=
  (∀ form target, callTarget form = .ok target → form ≠ .invalid) ∧
  invokeTypeSource true = "annotation" ∧ invokeTypeSource false = "Core.Typeof" ∧
  invokeLatestRoute true false = "invokelatest_gr:invoke_in_world" ∧
  (∀ arguments, (flattenTupleArgs arguments).length = (arguments.map List.length).sum)

theorem reflectionInvokeBodies_proven : ReflectionInvokeBodies := by
  constructor
  · intro form target h
    cases form <;> simp [callTarget] at h ⊢
  exact ⟨rfl, rfl, rfl, fun arguments => by simp [flattenTupleArgs]⟩

def ReflectionCacheBodies : Prop := ∀ state,
  (dropCachesModel state).requireWorldIsMax = true ∧
  (dropCachesModel state).compilerActive = true

theorem reflectionCacheBodies_proven : ReflectionCacheBodies := by
  intro state
  exact ⟨rfl, rfl⟩

end JuliaLean.ExprReflect
