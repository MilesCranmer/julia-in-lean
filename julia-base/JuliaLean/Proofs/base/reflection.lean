import JuliaLean.base.reflection
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.reflection

open JuliaLean JuliaLean.base.reflection JuliaLean.base.runtime_internals JuliaLean.Registry
open JuliaLean.base.io (M Error)

/-- Reflection from generated-function execution is explicitly rejected. -/
def GeneratedContextContract : Prop :=
  ∀ (World : Type) (query : M World Bool) (world : U) (before after : World) (pureContext : Bool),
    query before = some (.ok (pureContext, after)) →
    (pureContext = true ∨ world = JInt.typemax .u64) →
    checkGeneratedContext query world before =
      some (.error (.errorException "code reflection cannot be used from generated functions", after))

theorem generatedContextContract_proven : GeneratedContextContract := by
  intro World query world before after pureContext run forbidden
  rcases forbidden with hpure | hworld
  · subst pureContext
    simp [checkGeneratedContext, bind, pure, run, throw, throwThe, MonadExceptOf.throw]
  · subst world
    cases pureContext <;> simp [checkGeneratedContext, bind, pure, run, throw, throwThe, MonadExceptOf.throw]

/-- The default argument signature is deliberately general unless there is a unique method. -/
def DefaultTupleContract : Prop :=
  ∀ (World V Method Name : Type) (methods : V → M World (MethodList Method Name))
    (signature : Method → V) (tail : V → M World V) (tupleType f : V)
    (ms : MethodList Method Name) (before after : World),
    methods f before = some (.ok (ms, after)) → ms.ms.length ≠ 1 →
    defaultTupleType methods signature tail tupleType f before = some (.ok (tupleType, after))

theorem defaultTupleContract_proven : DefaultTupleContract := by
  intro World V Method Name methods signature tail tupleType f ms before after run many
  simp [defaultTupleType, bind, pure, run, many]

/-- Boolean code-emission controls have C integer values zero and one. -/
def EmissionContract : Prop :=
  ∀ flag, (newEmissionParams flag).emit_metadata.val = 0 ∨
    (newEmissionParams flag).emit_metadata.val = 1

theorem emissionContract_proven : EmissionContract := by
  intro flag
  cases flag <;> decide

/-- A method is never ambiguous with itself. -/
def SelfAmbiguityContract : Prop :=
  ∀ (World V D N Mod P Sym Method Match Ref Table : Type)
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref P Match)
    (ambiguity : AmbiguityOps World V Method Match P) (counter : M World U)
    (method : Method) (ambiguousBottom : Bool),
    ambiguity.egalMethod method method = true →
    isambiguous types lookup ambiguity counter method method ambiguousBottom = pure false

theorem selfAmbiguityContract_proven : SelfAmbiguityContract := by
  intro World V D N Mod P Sym Method Match Ref Table types lookup ambiguity counter method ambiguousBottom same
  simp [isambiguous, same]

/-- Function ownership is the module stored on the method definition. -/
def MethodModuleContract : Prop :=
  ∀ (Method Module : Type) (module : Method → Module) (method : Method),
    parentmoduleMethod module method = module method

theorem methodModuleContract_proven : MethodModuleContract := by
  intro Method Module module method
  rfl

/-- An unanalyzable call identifies both the query and the rendered call signature. -/
def MatchFailureContract : Prop :=
  ∀ (World Sym V Result : Type) (render : Sym → V → M World String)
    (empty : Sym) (text : Sym → String) (name : Sym) (types : V)
    (before after : World) (signature : String),
    render empty types before = some (.ok (signature, after)) →
    raiseMatchFailure (Result := Result) render empty text name types before =
      some (.error (.errorException (text name ++ ": unanalyzable call given " ++ signature), after))

theorem matchFailureContract_proven : MatchFailureContract := by
  intro World Sym V Result render empty text name types before after signature run
  simp [raiseMatchFailure, bind, pure, run, throw, throwThe, MonadExceptOf.throw]

def entries : List Entry := [
  { id := "reflection-generated-context", juliaFile := "base/reflection.jl"
    juliaFns := ["check_generated_context"]
    statement := "Reflection rejects generated-function execution with its documented error, preserving the state after the runtime context query."
    source := "base/reflection.jl:559-561", status := .proven
    prop := ``GeneratedContextContract, thm := some ``generatedContextContract_proven },
  { id := "reflection-default-signature", juliaFile := "base/reflection.jl"
    juliaFns := ["default_tt"]
    statement := "Functions without exactly one method use the general Tuple argument signature by default."
    source := "base/reflection.jl:307-314", status := .proven
    prop := ``DefaultTupleContract, thm := some ``defaultTupleContract_proven },
  { id := "reflection-emission-boolean", juliaFile := "base/reflection.jl"
    juliaFns := ["EmissionParams"]
    statement := "Boolean emission controls are represented as C integer zero or one."
    source := "base/reflection.jl:224-226", status := .proven
    prop := ``EmissionContract, thm := some ``emissionContract_proven },
  { id := "reflection-self-unambiguous", juliaFile := "base/reflection.jl"
    juliaFns := ["isambiguous"]
    statement := "A method cannot be ambiguous with itself, for either ambiguous_bottom setting."
    source := "base/reflection.jl:1229-1230", status := .proven
    prop := ``SelfAmbiguityContract, thm := some ``selfAmbiguityContract_proven },
  { id := "reflection-method-module", juliaFile := "base/reflection.jl"
    juliaFns := ["parentmodule(::Method)"]
    statement := "A method belongs to the module recorded on its definition."
    source := "base/reflection.jl:1075", status := .proven
    prop := ``MethodModuleContract, thm := some ``methodModuleContract_proven },
  { id := "reflection-match-failure-diagnostic", juliaFile := "base/reflection.jl"
    juliaFns := ["raise_match_failure"]
    statement := "Unanalyzable reflection calls report the query name and the rendered call signature."
    source := "base/reflection.jl:316-320", status := .proven
    prop := ``MatchFailureContract, thm := some ``matchFailureContract_proven }
]

end JuliaLean.Proofs.base.reflection
