import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.BootCov.Basic

/-!
# Typed model of `base/essentials.jl`

Julia method source is pinned to `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Each translated
method is preceded by its exact source lines. The file keeps untranslated method bodies visible.
-/

namespace JuliaLean.base.essentials

open JuliaLean JuliaLean.BootCov

def prodDims : List (JInt .i64) → JInt .i64
  | [] => JInt.wrap .i64 1
  | d :: ds => d * prodDims ds

abbrev SimpleVectorModel := List (Option JVal)

structure PairsModel (K V I A : Type) where
  data : A
  itr : I

inductive ColonModel where
  | mk

inductive ValValue {α : Type} (value : α) where
  | mk : ValValue value

def isUnionAll : JType → Bool
  | .unionAll _ _ => true
  | _ => false

structure EffectFlags where
  consistent : Bool
  effectFree : Bool
  nothrow : Bool
  terminatesGlobally : Bool
  terminatesLocally : Bool
  notaskstate : Bool
  inaccessiblememonly : Bool
  noub : Bool
  noubIfNoinbounds : Bool
  consistentOverlay : Bool
  nortcall : Bool

def EffectFlags.toList (f : EffectFlags) : List JVal :=
  [f.consistent, f.effectFree, f.nothrow, f.terminatesGlobally, f.terminatesLocally,
    f.notaskstate, f.inaccessiblememonly, f.noub, f.noubIfNoinbounds, f.consistentOverlay,
    f.nortcall].map JVal.bool

def effectMeta (internal : Bool) (flags : EffectFlags) : JVal :=
  if internal then .expr "meta" [.expr "purity" flags.toList] else .bool false

def cvtTupleElement {T X Y A : Type} (fieldtype : T → Nat → Y) (getfield : X → Nat → A)
    (isa : Y → A → Bool) (convert : Y → A → Except Exc A) (t : T) (x : X) (n : Nat) : Except Exc A := do
  let Tn := fieldtype t n
  let xn := getfield x n
  if isa Tn xn then pure xn else convert Tn xn

def svecEqLoop (eq : Option JVal → Option JVal → Bool) : List (Option JVal) → List (Option JVal) → Bool
  | a :: as, b :: bs => if eq a b then svecEqLoop eq as bs else false
  | _, _ => true


def anyTy : JType := .dt "Any" true []
def isAnyTy : JType → Bool
  | .dt "Any" _ [] => true
  | _ => false
def typeKind (t : JType) : JType := .dt "Type" true [t]
def argument (i : Nat) : JVal := .obj "Argument" [some (.int i)]
def ssa (i : Nat) : JVal := .expr "ssavalue" [.int i]
def undefArr (n : Nat) : List (Option JVal) := List.replicate n none
def setAt (a : List (Option JVal)) (i : Nat) (x : JVal) : List (Option JVal) := a.set (i - 1) (some x)
def setChecked (a : List (Option JVal)) (i : Nat) (x : JVal) : Except Exc (List (Option JVal)) :=
  if 1 ≤ i ∧ i ≤ a.length then .ok (setAt a i x) else .error .bounds
def splat : List (Option JVal) → Except Exc (List JVal)
  | [] => .ok []
  | none :: _ => .error .undefRef
  | some x :: xs => do
    let rest ← splat xs
    pure (x :: rest)
def asSymbol : JVal → Except Exc JVal
  | value@(.sym _) => .ok value
  | _ => .error (.typeError "typeassert")

structure MethodDef where
  atypes : List JVal
  tvars : List JVal
  lambda : JVal

structure DefaultCtorOps where
  getFieldtypes : JType → List JType
  getNames : JType → List JVal
  ccallHasTypevar : JType → JType → Int32
  isTypevar : JType → Bool
  upperBound : JType → JType
  sameType : JType → JType → Bool
  typeKind : JType → JType
  unionAll : JType → JType → Except Exc JType
  sourceLine : JVal → Except Exc Nat
  recordMethod : MethodDef → Except Exc Unit

def argnamesLoop : Nat → List JVal → List JType → List (Option JVal) → Nat →
    Except Exc (List (Option JVal) × Nat)
  | _, _, [], a, nany => .ok (a, nany)
  | i, name :: names, fieldType :: fieldTypes, a, nany => do
    let symbol ← asSymbol name
    let a := setAt a (i + 1) symbol
    let nany := if isAnyTy fieldType then nany + 1 else nany
    argnamesLoop (i + 1) names fieldTypes a nany
  | _, [], _ :: _, _, _ => .error .bounds

def curlyLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => curlyLoop (i + 1) k (setAt a (i + 1) (.expr "static_parameter" [.int i]))

def newArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => newArgsLoop (i + 1) k (setAt a (i + 1) (argument (i + 1)))

def atypesLoop : Nat → List JType → List (Option JVal) → List (Option JVal)
  | _, [], a => a
  | i, fieldType :: fieldTypes, a => atypesLoop (i + 1) fieldTypes (setAt a (i + 1) (.ty fieldType))

def allAnyLoop : List JType → Bool
  | [] => true
  | fieldType :: rest => isAnyTy fieldType && allAnyLoop rest

def ftStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa bidx, .expr "call" [.globalRef "Core" "fieldtype", argument 1, .int i]]
def cnvtStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa (bidx + 1), .expr "if"
    [.expr "call" [.globalRef "Core" "isa", argument (i + 1), ssa bidx], argument (i + 1),
     .expr "call" [.globalRef "Base" "convert", ssa bidx, argument (i + 1)]]]

def innerLoop : Nat → Nat → List JType → List (Option JVal) → List (Option JVal) →
    List (Option JVal) × List (Option JVal)
  | _, _, [], body, args => (body, args)
  | i, bidx, fieldType :: fieldTypes, body, args =>
    if isAnyTy fieldType then
      innerLoop (i + 1) bidx fieldTypes body (setAt args i (argument (i + 1)))
    else
      let body := setAt body bidx (ftStmt i bidx)
      let body := setAt body (bidx + 1) (cnvtStmt i bidx)
      innerLoop (i + 1) (bidx + 2) fieldTypes body (setAt args i (ssa (bidx + 1)))

def wrapLoop (ops : DefaultCtorOps) (tvars : List JType) : Nat → JType → Except Exc JType
  | 0, t => .ok t
  | i + 1, t => do
    let wrapped ← ops.unionAll (tvars.getD i .bottom) t
    wrapLoop ops tvars i wrapped

def anyArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => anyArgsLoop (i + 1) k (setAt a (i + 1) (.ty anyTy))

def srcLine : JVal → Except Exc Nat
  | .lineNode line _ => if line < 0 then .error (.inexact "convert" "UInt64") else .ok line.toNat
  | _ => .error (.typeError "getfield")

def outerCtor (ops : DefaultCtorOps) (ty : JType) (tvars fieldTypes : List JType)
    (argnames functionloc : JVal) : Except Exc MethodDef := do
  let nparams := tvars.length
  let n := fieldTypes.length
  let newTarget ← if nparams != 0 then do
      let curlyArgs := curlyLoop 1 nparams (setAt (undefArr (nparams + 1)) 1 (.ty ty))
      let args ← splat curlyArgs
      pure (.expr "curly" args)
    else pure (argument 1)
  let newArgs := newArgsLoop 1 n (setAt (undefArr (n + 1)) 1 newTarget)
  let args ← splat newArgs
  let lambda := .expr "lambda" [argnames, .expr "block" [functionloc, .expr "return" [.expr "new" args]]]
  let atypesArr := atypesLoop 1 fieldTypes (setAt (undefArr (n + 1)) 1 (.ty (ops.typeKind ty)))
  let atypes ← splat atypesArr
  pure ⟨atypes, tvars.map JVal.ty, lambda⟩

def innerCtor (ops : DefaultCtorOps) (dt : JType) (tvars fieldTypes : List JType)
    (nany : Nat) (argnames functionloc : JVal) : Except Exc MethodDef := do
  let nparams := tvars.length
  let n := fieldTypes.length
  let nstmts := (n - nany) + (n - nany) + 1
  let (bodyArgs, newArgs) := innerLoop 1 1 fieldTypes (undefArr nstmts) (undefArr n)
  let args ← splat newArgs
  let bodyArgs ← setChecked bodyArgs nstmts (.expr "return" [.expr "new" (argument 1 :: args)])
  let statements ← splat bodyArgs
  let lambda := .expr "lambda" [argnames, .expr "block" (functionloc :: statements)]
  let typedt ← wrapLoop ops tvars nparams (ops.typeKind dt)
  let atypesArr := anyArgsLoop 1 n (setAt (undefArr (n + 1)) 1 (.ty typedt))
  let atypes ← splat atypesArr
  pure ⟨atypes, [], lambda⟩
/--
Julia source: base/essentials.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
blackbox(x) = compilerbarrier(:blackbox, x)
```
-/
def blackbox {α : Type} (compilerbarrier : String → α → α) (x : α) : α := compilerbarrier "blackbox" x

/--
Julia source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::Array) = getfield(a, :size)
```
-/
def sizeArray {A D : Type} (getfield : A → String → D) (a : A) : D := getfield a "size"

/--
Julia source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::AbstractArray) = (@inline; prod(size(t)))
```
-/
def lengthAbstract {A D : Type} (size : A → D) (prod : D → JInt .i64) (t : A) : JInt .i64 := prod (size t)

/--
Julia source: base/essentials.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::GenericMemory) = (getfield(a, :length),)
```
-/
def sizeGenericMemory {A N : Type} (getfield : A → String → N) (a : A) : N := getfield a "length"

/--
Julia source: base/essentials.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserror {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) : Except Exc R := throwBounds a []

/--
Julia source: base/essentials.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, I) = (@noinline; throw(BoundsError(A, I)))
```
-/
def throwBoundserrorIndices {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (indices : List I) : Except Exc R := throwBounds a indices

/--
Julia source: base/essentials.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, i1, i2, I...) = (@noinline; throw(BoundsError(A, (i1, i2, I...))))
```
-/
def throwBoundserrorMany {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (i1 i2 : I) (rest : List I) : Except Exc R := throwBounds a (i1 :: i2 :: rest)

/--
Julia source: base/essentials.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserrorIndicesEmpty {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) : Except Exc R := throwBounds a []

/--
Julia source: base/essentials.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
```
-/
def throwBoundserrorIndicesMany {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (i1 : I) (rest : List I) : Except Exc R := throwBounds a (i1 :: rest)

/--
Julia source: base/essentials.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name
```
-/
def globalRefEq (a b : String × String) : Bool := a.1 == b.1 && a.2 == b.2

/--
Julia source: base/essentials.jl:46-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _gc_preserve_begin(arg1)
    Expr(:gc_preserve_begin, esc(arg1))
end
```
-/
def gcPreserveBegin (arg1 : JVal) : JVal := .expr "gc_preserve_begin" [esc arg1]

/--
Julia source: base/essentials.jl:50-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _gc_preserve_end(token)
    Expr(:gc_preserve_end, esc(token))
end
```
-/
def gcPreserveEnd (token : JVal) : JVal := .expr "gc_preserve_end" [esc token]

/--
Julia source: base/essentials.jl:125-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro nospecialize(vars...)
    if nfields(vars) === 1
        # in argument position, need to fix `@nospecialize x=v` to `@nospecialize (kw x v)`
        var = getfield(vars, 1)
        if isa(var, Expr) && var.head === :(=)
            var.head = :kw
        end
    end
    return Expr(:escape, Expr(:meta, :nospecialize, vars...))
end
```
-/
def nospecialize (vars : List JVal) : JVal :=
  let vars := match vars with
    | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
    | _ => vars
  .expr "escape" [.expr "meta" (.sym "nospecialize" :: vars)]

/--
Julia source: base/essentials.jl:142-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro specialize(vars...)
    if nfields(vars) === 1
        # in argument position, need to fix `@specialize x=v` to `@specialize (kw x v)`
        var = getfield(vars, 1)
        if isa(var, Expr) && var.head === :(=)
            var.head = :kw
        end
    end
    return Expr(:escape, Expr(:meta, :specialize, vars...))
end
```
-/
def specialize (vars : List JVal) : JVal :=
  let vars := match vars with
    | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
    | _ => vars
  .expr "escape" [.expr "meta" (.sym "specialize" :: vars)]

/--
Julia source: base/essentials.jl:184-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro isdefined(s::Symbol)
    return Expr(:escape, Expr(:isdefined, s))
end
```
-/
def isdefinedMacro (sym : String) : JVal := .expr "escape" [.expr "isdefined" [.sym sym]]

/--
Julia source: base/essentials.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nameof(m::Module) = ccall(:jl_module_name, Ref{Symbol}, (Any,), m)
```
-/
def nameofModule (moduleName : JVal → String) (m : JVal) : String := moduleName m

/--
Julia source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _is_internal(__module__)
    return _nameof(__module__) === :Base ||
      _nameof(ccall(:jl_base_relative_to, Any, (Any,), __module__)::Module) === :Compiler
end
```
-/
def isInternal (moduleName : JVal → String) (baseRelative : JVal → JVal) (m : JVal) : Bool :=
  nameofModule moduleName m == "Base" || nameofModule moduleName (baseRelative m) == "Compiler"

/--
Julia source: base/essentials.jl:196-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _total_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#true,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end
```
-/
def totalMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨true, true, true, true, false, true, true, true, false, false, true⟩

/--
Julia source: base/essentials.jl:211-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _foldable_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end
```
-/
def foldableMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨true, true, false, true, false, true, true, true, false, false, true⟩

/--
Julia source: base/essentials.jl:226-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_locally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesLocallyMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, false, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:241-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, true, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:256-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_notaskstate_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyNotaskstateMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, true, true, true, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:271-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyNoubMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, true, true, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:286-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _effect_free_terminates_locally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#true,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def effectFreeTerminatesLocallyMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, true, false, false, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:301-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nothrow_noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#true,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def nothrowNoubMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, true, false, false, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:316-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nothrow_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#true,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def nothrowMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, true, false, false, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:331-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def noubMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, false, false, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:346-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _notaskstate_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def notaskstateMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, false, false, true, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:361-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _noub_if_noinbounds_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#true,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def noubIfNoinboundsMeta (moduleName : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal) : JVal :=
  effectMeta (isInternal moduleName baseRelative module_) ⟨false, false, false, false, false, false, false, false, true, false, false⟩

/--
Julia source: base/essentials.jl:377-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _propagate_inbounds_meta()
    return Expr(:meta, :inline, :propagate_inbounds)
end
```
-/
def propagateInboundsMeta : JVal := .expr "meta" [.sym "inline", .sym "propagate_inbounds"]

/--
Julia source: base/essentials.jl:380-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nospecializeinfer_meta()
    return Expr(:meta, :nospecializeinfer)
end
```
-/
def nospecializeinferMeta : JVal := .expr "meta" [.sym "nospecializeinfer"]

/--
Julia source: base/essentials.jl:385-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
    @inline
    ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
end
```
-/
def checkboundsBool (len i : JInt .i64) : Bool :=
  JuliaLean.base.int.ult_int
    (JuliaLean.base.int.bitcast .u64
      (JuliaLean.base.int.sub_int i (JuliaLean.base.int.lit .i64 1)) rfl)
    (JuliaLean.base.int.bitcast .u64 len rfl)

/--
Julia source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(A::AbstractArray, I...)
    @inline
    checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
    nothing
end
```
-/
def checkboundsGeneric {A I : Type} (check : A → List I → Bool)
    (throwBounds : A → List I → Except Exc Unit) (a : A) (indices : List I) : Except Exc Unit :=
  if check a indices then .ok () else throwBounds a indices

/--
Julia source: base/essentials.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemory{:not_atomic}) = :not_atomic
```
-/
def defaultAccessOrder (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemory{:atomic}) = :monotonic
```
-/
def defaultAccessOrderMemory (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemoryRef{:not_atomic}) = :not_atomic
```
-/
def defaultAccessOrderRef (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemoryRef{:atomic}) = :monotonic
```
-/
def defaultAccessOrderMemoryRef (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:400-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::GenericMemory, i::Int)
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i)
    memoryrefget(memoryrefnew(A, i, false), default_access_order(A), false)
end
```
-/
def getindexGenericMemory {M I R V : Type} (boundscheck : Bool)
    (check : M → List I → Bool) (throwBounds : M → List I → Except Exc Unit)
    (memoryrefnew : M → I → Bool → R) (isAtomic : M → Bool)
    (memoryrefget : R → String → Bool → Except Exc V) (memory : M) (i : I) : Except Exc V := do
  if boundscheck then checkboundsGeneric check throwBounds memory [i]
  memoryrefget (memoryrefnew memory i false) (defaultAccessOrderMemory (isAtomic memory)) false

/--
Julia source: base/essentials.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(A::GenericMemoryRef) = memoryrefget(A, default_access_order(A), @_boundscheck)
```
-/
def getindexGenericMemoryRef {R V : Type} (boundscheck : Bool)
    (isAtomic : R → Bool) (memoryrefget : R → String → Bool → Except Exc V)
    (ref : R) : Except Exc V := memoryrefget ref (defaultAccessOrderMemoryRef (isAtomic ref)) boundscheck

/--
Julia source: base/essentials.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nameof(m::Module) = (@_total_meta; ccall(:jl_module_name, Ref{Symbol}, (Any,), m))
```
-/
def nameof (moduleName : JVal → String) (m : JVal) : String := moduleName m

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert end
```
-/

/--
Julia source: base/essentials.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Union{}}, _...) = throw(ArgumentError("cannot convert a value to Union{} for assignment"))
```
-/
def convertUnionBottom {α R : Type} (_ : List α) : Except Exc R :=
  .error (.argument "cannot convert a value to Union{} for assignment")

/--
Julia source: base/essentials.jl:476-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Type}, x::Type) = x # the ssair optimizer is strongly dependent on this method existing to avoid over-specialization
```
-/
def convertTypeIdentity {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{String}, x::String) = x
```
-/
def convertStringIdentity (x : String) : String := x

/--
Julia source: base/essentials.jl:488-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro eval(ex)
    return Expr(:let, Expr(:(=), :eval_local_result,
            Expr(:escape, Expr(:call, GlobalRef(Core, :eval), __module__, Expr(:quote, ex)))),
        Expr(:block,
            Expr(:var"latestworld-if-toplevel"),
            :eval_local_result))
end
```
-/
def evalMacro1 (esc : JVal → JVal) (module_ ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
    esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]

/--
Julia source: base/essentials.jl:495-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro eval(mod, ex)
    return Expr(:let, Expr(:(=), :eval_local_result,
            Expr(:escape, Expr(:call, GlobalRef(Core, :eval), mod, Expr(:quote, ex)))),
        Expr(:block,
            Expr(:var"latestworld-if-toplevel"),
            :eval_local_result))
end
```
-/
def evalMacro2 (esc : JVal → JVal) (mod ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
    esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]

/--
Julia source: base/essentials.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K, V, I, A}(data, itr) where {K, V, I, A} = $(Expr(:new, :(Pairs{K, V, I, A}), :(data isa A ? data : convert(A, data)), :(itr isa I ? itr : convert(I, itr))))
```
-/
def pairsCtorFull {K V I A D J : Type}
    (isData : D → Bool) (asData : D → A) (convertData : D → Except Exc A)
    (isIter : J → Bool) (asIter : J → I) (convertIter : J → Except Exc I)
    (data : D) (iter : J) : Except Exc (PairsModel K V I A) := do
  let data ← if isData data then pure (asData data) else convertData data
  let iter ← if isIter iter then pure (asIter iter) else convertIter iter
  pure ⟨data, iter⟩

/--
Julia source: base/essentials.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K, V}(data::A, itr::I) where {K, V, I, A} = $(Expr(:new, :(Pairs{K, V, I, A}), :data, :itr))
```
-/
def pairsCtorKV {K V I A : Type} (data : A) (iter : I) : PairsModel K V I A := ⟨data, iter⟩

/--
Julia source: base/essentials.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K}(data::A, itr::I) where {K, I, A} = $(Expr(:new, :(Pairs{K, eltype(A), I, A}), :data, :itr))
```
-/
def pairsCtorK {K I A : Type} (eltype : Type → Type)
    (data : A) (iter : I) : PairsModel K (eltype A) I A := ⟨data, iter⟩

/--
Julia source: base/essentials.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs(data::A, itr::I) where {I, A} = $(Expr(:new, :(Pairs{I !== Nothing ? eltype(I) : keytype(A), eltype(A), I, A}), :data, :itr))
```
-/
def pairsCtor {A I : Type} (isNothingI : Bool) (eltype keytype : Type → Type)
    (data : A) (iter : I) : PairsModel (if isNothingI then keytype A else eltype I) (eltype A) I A :=
  ⟨data, iter⟩

/--
Julia source: base/essentials.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(::Type{NamedTuple}) = Pairs{Symbol, V, Nothing, NT} where {V, NT <: NamedTuple}
```
-/
def pairsNamedTupleType : JType :=
  let any := JType.dt "Any" true []
  let bot := JType.bottom
  let namedTuple := JType.dt "NamedTuple" true []
  let V := JType.tvar 0 "V" bot any
  let NT := JType.tvar 1 "NT" bot namedTuple
  JType.unionAll V (JType.unionAll NT
    (JType.dt "Pairs" false [JType.dt "Symbol" false [], V, JType.dt "Nothing" false [], NT]))

/--
Julia source: base/essentials.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argtail(_, rest...) = rest
```
-/
def argtail {α : Type} (_ : α) (rest : List α) : List α := rest

/--
Julia source: base/essentials.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(x::Tuple) = argtail(x...)
```
-/
def tail {α : Type} : List α → Except Exc (List α)
  | first :: rest => .ok (argtail first rest)
  | [] => .error (.argument "Cannot call tail on an empty tuple.")

/--
Julia source: base/essentials.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(::Tuple{}) = throw(ArgumentError("Cannot call tail on an empty tuple."))
```
-/
def tailEmpty {α : Type} : Except Exc (List α) := .error (.argument "Cannot call tail on an empty tuple.")

/--
Julia source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrap_unionall(@nospecialize(a))
    @_foldable_meta
    while isa(a,UnionAll)
        a = a.body
    end
    return a
end
```
-/
def unwrapUnionall : JType → JType
  | .unionAll _ body => unwrapUnionall body
  | t => t

/--
Julia source: base/essentials.jl:552-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rewrap_unionall(@nospecialize(t), @nospecialize(u))
    @_foldable_meta
    if !isa(u, UnionAll)
        return t
    end
    return UnionAll(u.var, rewrap_unionall(t, u.body))
end
```
-/
def rewrapUnionall (unionAll : JType → JType → Except Exc JType) (t : JType) : JType → Except Exc JType
  | .unionAll var body => do
    let inner ← rewrapUnionall unionAll t body
    unionAll var inner
  | _ => .ok t

/--
Julia source: base/essentials.jl:560-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rewrap_unionall(t::Core.TypeofVararg, @nospecialize(u))
    @_foldable_meta
    isdefined(t, :T) || return t
    if !isa(u, UnionAll)
        return t
    end
    T = rewrap_unionall(t.T, u)
    if !isdefined(t, :N) || t.N === u.var
        return Vararg{T}
    end
    return Vararg{T, t.N}
end
```
-/
def rewrapUnionallVararg (isDefined : JType → String → Bool)
    (getField : JType → String → Except Exc JType)
    (eqType : JType → JType → Bool)
    (unionAll : JType → JType → Except Exc JType)
    (vararg : JType → Option JType → JType) (t u : JType) : Except Exc JType := do
  if !isDefined t "T" then pure t else
    match u with
    | .unionAll v _ => do
      let elementType ← getField t "T"
      let T ← rewrapUnionall unionAll elementType u
      if !isDefined t "N" then pure (vararg T none) else
        let N ← getField t "N"
        if eqType N v then pure (vararg T none) else pure (vararg T (some N))
    | _ => pure t

/--
Julia source: base/essentials.jl:574-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_unionall(@nospecialize(u))
    if !isa(u, UnionAll)
        return u
    end
    var = u.var::TypeVar
    body = UnionAll(var, rename_unionall(u.body))
    nv = TypeVar(var.name, var.lb, var.ub)
    return UnionAll(nv, body{nv})
end
```
-/
def renameUnionall (typevarInfo : JType → Except Exc (String × JType × JType))
    (unionAll : JType → JType → Except Exc JType)
    (typevar : String → JType → JType → JType)
    (instantiate : JType → JType → Except Exc JType) : JType → Except Exc JType
  | .unionAll var body => do
    let (name, lb, ub) ← typevarInfo var
    let body ← renameUnionall typevarInfo unionAll typevar instantiate body
    let body ← unionAll var body
    let nv := typevar name lb ub
    let body ← instantiate body nv
    let body ← unionAll nv body
    pure body
  | u => .ok u

/--
Julia source: base/essentials.jl:585-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function widen_diagonal(@nospecialize(t), troot::UnionAll)
    return ccall(:jl_widen_diagonal, Any, (Any, Any), t, troot)
end
```
-/
def widenDiagonal (widen : JType → JType → JType) (t root : JType) : JType := widen t root

/--
Julia source: base/essentials.jl:589-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isvarargtype(@nospecialize(t))
    return isa(t, Core.TypeofVararg)
end
```
-/
def isvarargtype : JType → Bool
  | .vararg _ _ => true
  | _ => false

/--
Julia source: base/essentials.jl:593-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isvatuple(@nospecialize(t))
    @_foldable_meta
    t = unwrap_unionall(t)
    if isa(t, DataType)
        n = length(t.parameters)
        return n > 0 && isvarargtype(t.parameters[n])
    end
    return false
end
```
-/
def isvatuple (t : JType) : Bool :=
  match unwrapUnionall t with
  | .dt _ _ params => match params.getLast? with | some p => isvarargtype p | none => false
  | _ => false

/--
Julia source: base/essentials.jl:603-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrapva(@nospecialize(t))
    isa(t, Core.TypeofVararg) || return t
    return isdefined(t, :T) ? t.T : Any
end
```
-/
def unwrapva (any : JType) : JType → JType
  | .vararg (some t) _ => t
  | .vararg none _ => any
  | t => t

/--
Julia source: base/essentials.jl:608-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unconstrain_vararg_length(va::Core.TypeofVararg)
    # construct a new Vararg type where its length is unconstrained,
    # but its element type still captures any dependencies the input
    # element type may have had on the input length
    return Vararg{unwrapva(va)}
end
```
-/
def unconstrainVarargLength (va : JType) : JType :=
  .vararg (some (unwrapva (.dt "Any" true []) va)) none

/--
Julia source: base/essentials.jl:617-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function datatype_min_ninitialized(@nospecialize t0)
    t = unwrap_unionall(t0)
    t isa DataType || return 0
    isabstracttype(t) && return 0
    if t.name === _NAMEDTUPLE_NAME
        names, types = t.parameters[1], t.parameters[2]
        if names isa Tuple
            return length(names)
        end
        t = unwrap_unionall(types)
        t isa DataType || return 0
        t.name === Tuple.name || return 0
    end
    if t.name === Tuple.name
        n = length(t.parameters)
        n == 0 && return 0
        va = t.parameters[n]
        if isvarargtype(va)
            n -= 1
            if isdefined(va, :N)
                va = va.N
                if va isa Int
                    n += va
                end
            end
        end
        return n
    end
    return length(t.name.names) - t.name.n_uninitialized
end
```
-/
def datatypeMinNinitialized (isabstract : JType → Bool)
    (fieldCount uninitialized : JType → Nat) (t0 : JType) : Int :=
  let t := unwrapUnionall t0
  match t with
  | .dt name _ params =>
    if isabstract t then 0
    else if name == "NamedTuple" then
      match params with
      | .names names :: _ => names.length
      | _ :: types :: _ =>
        match unwrapUnionall types with
        | .dt "Tuple" _ tupleParams => tupleMinInitialized tupleParams
        | _ => 0
      | _ => 0
    else if name == "Tuple" then tupleMinInitialized params
    else (fieldCount t : Int) - uninitialized t
  | _ => 0
where
  tupleMinInitialized (params : List JType) : Int :=
    let n : Int := params.length
    if params.isEmpty then 0
    else match params.getLast? with
      | some va =>
        if isvarargtype va then match va with
          | .vararg _ (some (.intParam k)) => n - 1 + k
          | .vararg _ _ => n - 1
          | _ => n
        else n
      | _ => n

/--
Julia source: base/essentials.jl:650-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tuple_error(T::Type, x) = (@noinline; throw(MethodError(convert, (T, x))))
```
-/
def tupleError {T X R : Type} (_ : T) (_ : X) : Except Exc R := .error (.method "convert")

/--
Julia source: base/essentials.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T<:Tuple} = x
```
-/
def convertTupleIdentity {T : Type} (x : T) : T := x

/--
Julia source: base/essentials.jl:653-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
    # First see if there could be any conversion of the input type that'd be a subtype of the output.
    # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
    if typeintersect(NTuple{N,Any}, T) === Union{}
        _tuple_error(T, x)
    end
    function cvt1(n)
        @inline
        Tn = fieldtype(T, n)
        xn = getfield(x, n, #=boundscheck=#false)
        xn isa Tn && return xn
        return convert(Tn, xn)
    end
    return ntuple(cvt1, Val(N))::NTuple{N,Any}
end
```
-/
def convertTuple {T X Y A : Type} (disjoint : Nat → T → Bool)
    (fieldtype : T → Nat → Y) (getfield : X → Nat → A) (isa : Y → A → Bool)
    (convert : Y → A → Except Exc A)
    (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A))
    (target : T) (x : X) (n : Nat) : Except Exc (List A) :=
  if disjoint n target then tupleError target x
  else ntuple n (fun i => cvtTupleElement fieldtype getfield isa convert target x i)

/--
Julia source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
```
-/
def oftype {α : Type} (isa : α → α → Bool) (convert : α → α → Except Exc α)
    (x y : α) : Except Exc α := if isa x y then .ok y else convert x y

/--
Julia source: base/essentials.jl:720-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::Int) = reinterpret(UInt, x)
```
-/
def unsignedInt (x : JInt .i64) : JInt .u64 := JInt.wrap .u64 x.val

/--
Julia source: base/essentials.jl:721-721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x::UInt) = reinterpret(Int, x)
```
-/
def signedUInt (x : JInt .u64) : JInt .i64 := JInt.wrap .i64 x.val

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert end
```
-/

/--
Julia source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
```
-/
def cconvert {T X : Type} (isa : X → Bool) (assert : X → T)
    (convert : X → Except Exc T) (x : X) : Except Exc T :=
  if isa x then .ok (assert x) else convert x

/--
Julia source: base/essentials.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Union{}}, x...) = convert(Union{}, x...)
```
-/
def cconvertUnionBottom {α R : Type} (convert : List α → Except Exc R) (xs : List α) : Except Exc R := convert xs

/--
Julia source: base/essentials.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{<:Ptr}, x) = x # but defer the conversion to Ptr to unsafe_convert
```
-/
def cconvertPointer {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{T}, x::T) where {T} = x # unsafe_convert (like convert) defaults to assuming the convert occurred
```
-/
def unsafeConvertIdentity {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:743-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{T}, x::T) where {T<:Ptr} = x  # to resolve ambiguity with the next method
```
-/
def unsafeConvertPointerIdentity {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:744-744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{P}, x::Ptr) where {P<:Ptr} = convert(P, x)
```
-/
def unsafeConvertPointer {P Ptr R : Type} (convert : P → Ptr → R) (target : P) (ptr : Ptr) : R := convert target ptr

/--
Julia source: base/essentials.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
```
-/
def unsafeConvertStringUInt8 {R : Type} (stringPointer : String → R) (s : String) : R := stringPointer s

/--
Julia source: base/essentials.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
```
-/
def unsafeConvertStringInt8 {R : Type} (stringPointer : String → R) (s : String) : R := stringPointer s

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reinterpret end
```
-/

/--
Julia source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reinterpret(::Type{Out}, x) where {Out}
    @inline
    if isprimitivetype(Out) && isprimitivetype(typeof(x))
        return bitcast(Out, x)
    end
    # only available when Base is fully loaded.
    return _reinterpret(Out, x)
end
```
-/
def reinterpret {O X R : Type} (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X) : R :=
  if isPrimitiveOut out && isPrimitiveValue x then bitcast out x else full out x

/--
Julia source: base/essentials.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(x) = Core.sizeof(x)
```
-/
def sizeof {X N : Type} (coreSizeof : X → N) (x : X) : N := coreSizeof x

/--
Julia source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
```
-/
def ifelse {α : Type} (condition : Bool) (x y : α) : α := if condition then x else y

/--
Julia source: base/essentials.jl:903-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
esc(@nospecialize(e)) = Expr(:escape, e)
```
-/
def esc (e : JVal) : JVal := .expr "escape" [e]

/--
Julia source: base/essentials.jl:949-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro boundscheck(blk)
    return Expr(:if, Expr(:boundscheck), esc(blk))
end
```
-/
def boundscheckMacro (block : JVal) : JVal := .expr "if" [.expr "boundscheck" [], esc block]

/--
Julia source: base/essentials.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro inbounds(blk)
    return Expr(:block,
        Expr(:inbounds, true),
        Expr(:local, Expr(:(=), :val, esc(blk))),
        Expr(:inbounds, :pop),
        :val)
end
```
-/
def inboundsMacro (block : JVal) : JVal :=
  .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", esc block]],
    .expr "inbounds" [.sym "pop"], .sym "val"]

/--
Julia source: base/essentials.jl:1030-1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(name::Symbol)
    name === :_ && error("use `@label expr` for anonymous blocks; `@label _` is not allowed")
    return esc(Expr(:symboliclabel, name))
end
```
-/
def label1 (name : String) : Except Exc JVal :=
  if name == "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (esc (.expr "symboliclabel" [.sym name]))

/--
Julia source: base/essentials.jl:1035-1052 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(name::Symbol, body)
    name === :_ && error("use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
    # If body is a syntactic loop, wrap its body in a continue block
    # This allows `continue name` to work by breaking to `name#cont`
    if body isa Expr && (body.head === :for || body.head === :while)
        cont_name = Symbol(string(name, "#cont"))
        if body.head === :for
            loop_body = body.args[2]
            wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
            body = Expr(:for, body.args[1], wrapped_body)
        else  # while
            loop_body = body.args[2]
            wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
            body = Expr(:while, body.args[1], wrapped_body)
        end
    end
    return esc(Expr(:symbolicblock, name, body))
end
```
-/
def label2 (name : String) (body : JVal) : Except Exc JVal :=
  if name == "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (esc (.expr "symbolicblock" [.sym name, body]))

/--
Julia source: base/essentials.jl:1054-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(body)
    # 1-arg form: create anonymous block that participates in the default break scope.
    # Uses `loop-exit` as the internal label so that `break` and `break _` both target it.
    return esc(Expr(:symbolicblock, Symbol("loop-exit"), body))
end
```
-/
def label0 (body : JVal) : JVal := esc (.expr "symbolicblock" [.sym "loop-exit", body])

/--
Julia source: base/essentials.jl:1068-1070 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro goto(name::Symbol)
    return esc(Expr(:symbolicgoto, name))
end
```
-/
def gotoMacro (name : String) : JVal := esc (.expr "symbolicgoto" [.sym name])

/--
Julia source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, i::Int)
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
end
```
-/
def getindexArray {A I P R V : Type} (boundscheck : Bool)
    (check : A → List I → Bool) (throwBounds : A → List I → Except Exc Unit)
    (getfield : A → String → P) (memoryrefnew : P → I → Bool → R)
    (memoryrefget : R → String → Bool → Except Exc V) (a : A) (i : I) : Except Exc V := do
  if boundscheck then checkboundsGeneric check throwBounds a [i]
  memoryrefget (memoryrefnew (getfield a "ref") i false) "not_atomic" false

/--
Julia source: base/essentials.jl:1079-1084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{Any}, @nospecialize(x), i::Int)
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefset!(memoryrefnew(getfield(A, :ref), i, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexArrayAny {A I P R X : Type} (boundscheck : Bool)
    (check : A → List I → Bool) (throwBounds : A → List I → Except Exc Unit)
    (getfield : A → String → P) (memoryrefnew : P → I → Bool → R)
    (memoryrefset : R → X → String → Bool → Except Exc Unit)
    (a : A) (x : X) (i : I) : Except Exc A := do
  if boundscheck then checkboundsGeneric check throwBounds a [i]
  memoryrefset (memoryrefnew (getfield a "ref") i false) x "not_atomic" false
  pure a

/--
Julia source: base/essentials.jl:1085-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{Any}, @nospecialize(x), i::Int)
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i)
    memoryrefset!(memoryrefnew(A, i, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexMemoryAny {A I R X : Type} (boundscheck : Bool)
    (check : A → List I → Bool) (throwBounds : A → List I → Except Exc Unit)
    (memoryrefnew : A → I → Bool → R)
    (memoryrefset : R → X → String → Bool → Except Exc Unit)
    (a : A) (x : X) (i : I) : Except Exc A := do
  if boundscheck then checkboundsGeneric check throwBounds a [i]
  memoryrefset (memoryrefnew a i false) x "not_atomic" false
  pure a

/--
Julia source: base/essentials.jl:1091-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::MemoryRef{T}, x) where {T} = (memoryrefset!(A, convert(T, x), :not_atomic, @_boundscheck); A)
```
-/
def setindexMemoryRef {A T X : Type} (convert : X → Except Exc T)
    (memoryrefset : A → T → String → Bool → Except Exc Unit)
    (ref : A) (x : X) : Except Exc A := do
  let value ← convert x
  memoryrefset ref value "not_atomic" false
  pure ref

/--
Julia source: base/essentials.jl:1092-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::MemoryRef{Any}, @nospecialize(x)) = (memoryrefset!(A, x, :not_atomic, @_boundscheck); A)
```
-/
def setindexMemoryRefAny {A X : Type}
    (memoryrefset : A → X → String → Bool → Except Exc Unit)
    (ref : A) (x : X) : Except Exc A := do
  memoryrefset ref x "not_atomic" false
  pure ref

/--
Julia source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::SimpleVector, i::Int) = (@_foldable_meta; Core._svec_ref(v, i))
```
-/
def getindexSVec (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
    (v : SimpleVectorModel) (i : Int) : Except Exc (Option JVal) := svecRef v i

/--
Julia source: base/essentials.jl:1097-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(v::SimpleVector)
    Core._svec_len(v)
end
```
-/
def lengthSVec (svecLength : SimpleVectorModel → Nat) (v : SimpleVectorModel) : Nat := svecLength v

/--
Julia source: base/essentials.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(::SimpleVector) = 1
```
-/
def firstindexSVec (_ : SimpleVectorModel) : Nat := 1

/--
Julia source: base/essentials.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(v::SimpleVector) = length(v)
```
-/
def lastindexSVec (svecLength : SimpleVectorModel → Nat) (v : SimpleVectorModel) : Nat := lengthSVec svecLength v

/--
Julia source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
```
-/
def iterateSVec (svecLength : SimpleVectorModel → Nat)
    (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
    (v : SimpleVectorModel) (i : Nat := 1) : Except Exc (Option (Option JVal × Nat)) :=
  if lengthSVec svecLength v < i then .ok none
  else do
    let x ← getindexSVec svecRef v i
    pure (some (x, i + 1))

/--
Julia source: base/essentials.jl:1103-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{SimpleVector}) = Any
```
-/
def eltypeSVec : String := "Any"

/--
Julia source: base/essentials.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(v::SimpleVector) = OneTo(length(v))
```
-/
def keysSVec (svecLength : SimpleVectorModel → Nat) (v : SimpleVectorModel) : Nat := lengthSVec svecLength v

/--
Julia source: base/essentials.jl:1105-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(v::SimpleVector) = (length(v) == 0)
```
-/
def isemptySVec (svecLength : SimpleVectorModel → Nat) (v : SimpleVectorModel) : Bool := lengthSVec svecLength v == 0

/--
Julia source: base/essentials.jl:1106-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(v::SimpleVector) = (OneTo(length(v)),)
```
-/
def axesSVec (svecLength : SimpleVectorModel → Nat) (v : SimpleVectorModel) : List Nat := [lengthSVec svecLength v]

/--
Julia source: base/essentials.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(v::SimpleVector, d::Integer) = d <= 1 ? axes(v)[d] : OneTo(1)
```
-/
def axesSVecDim (svecLength : SimpleVectorModel → Nat)
    (v : SimpleVectorModel) (d : Int) : Except Exc Nat :=
  if d ≤ 1 then if d = 1 then .ok (axesSVec svecLength v)[0]! else .error .bounds else .ok 1

/--
Julia source: base/essentials.jl:1109-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(v1::SimpleVector, v2::SimpleVector)
    length(v1)==length(v2) || return false
    for i = 1:length(v1)
        v1[i] == v2[i] || return false
    end
    return true
end
```
-/
def equalSVec (svecLength : SimpleVectorModel → Nat)
    (eq : Option JVal → Option JVal → Bool) (v1 v2 : SimpleVectorModel) : Bool :=
  if lengthSVec svecLength v1 != lengthSVec svecLength v2 then false
  else svecEqLoop eq v1 v2

/--
Julia source: base/essentials.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, v::SimpleVector) = Any[ f(v[i]) for i = 1:length(v) ]
```
-/
def mapSVec {α : Type} (svecLength : SimpleVectorModel → Nat)
    (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
    (f : Option JVal → α) (v : SimpleVectorModel) : Except Exc (List α) :=
  (List.range (lengthSVec svecLength v)).mapM fun (i : Nat) => do
    let value ← getindexSVec svecRef v ((i : Int) + 1)
    pure (f value)

/--
Julia source: base/essentials.jl:1119-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::SimpleVector, I::AbstractArray) = Core.svec(Any[ v[i] for i in I ]...)
```
-/
def getindexSVecArray {α : Type} (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
    (svecCtor : List (Option JVal) → α) (v : SimpleVectorModel) (indices : List Int) : Except Exc α := do
  let values ← indices.mapM (fun i => getindexSVec svecRef v i)
  pure (svecCtor values)

/--
Julia source: base/essentials.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Any}}, sv::SimpleVector) = convert(Ptr{Any},pointer_from_objref(sv)) + sizeof(Ptr)
```
-/
def unsafeConvertSVec {P Q : Type}
    (pointerFromObjref : SimpleVectorModel → P) (convert : P → Q)
    (pointerAdd : Q → Nat → Q) (sizeofPtr : Nat) (v : SimpleVectorModel) : Q :=
  pointerAdd (convert (pointerFromObjref v)) sizeofPtr

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1149-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned end
```
-/

/--
Julia source: base/essentials.jl:1151-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(v::SimpleVector, i::Int)
    @boundscheck 1 <= i <= length(v) || return false
    return true
end
```
-/
def isassignedSVec (svecLength : SimpleVectorModel → Nat)
    (v : SimpleVectorModel) (i : Int) : Bool :=
  if 1 ≤ i && i ≤ (lengthSVec svecLength v : Int) then true else false

/--
Julia source: base/essentials.jl:1170-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Colon() = new()
```
-/
def colonCtor : ColonModel := ⟨⟩

/--
Julia source: base/essentials.jl:1174-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::Colon)
    show_type_name(io, Colon.name)
    print(io, "()")
end
```
-/
def showColon {IO : Type} (colonName : JVal)
    (showTypeName : IO → JVal → Except Exc Unit)
    (print : IO → String → Except Exc Unit) (io : IO) : Except Exc Unit := do
  showTypeName io colonName
  print io "()"

/--
Julia source: base/essentials.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Val{x}() where {x} = new()
```
-/
def valValueDefault {α : Type} (x : α) : ValValue x := .mk

/--
Julia source: base/essentials.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Val(x) = Val{x}()
```
-/
def valCtor {α : Type} (x : α) : ValValue x := valValueDefault x

/--
Julia source: base/essentials.jl:1211-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inferencebarrier(@nospecialize(x)) = compilerbarrier(:type, x)
```
-/
def inferencebarrier {α : Type} (compilerbarrier : String → α → α) (x : α) : α := compilerbarrier "type" x

/--
Julia source: base/essentials.jl:1235-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isempty(itr)
    d = isdone(itr)
    d !== missing && return d
    iterate(itr) === nothing
end
```
-/
def isempty {I S : Type} (isdone : I → List S → Option Bool)
    (iterate : I → List S → Option (S × List S)) (itr : I) (state : List S := []) : Bool :=
  match isdone itr state with
  | some done_ => done_
  | none => (iterate itr state).isNone

/--
Julia source: base/essentials.jl:1263-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(itr) = itr
```
-/
def values {α : Type} (iterator : α) : α := iterator

/--
Julia source: base/essentials.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::Int, y::Int) = add_int(x, y)
```
-/
def addInt (x y : JInt .i64) : JInt .i64 := JuliaLean.base.int.add_int x y

/--
Julia source: base/essentials.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::Int, y::Int) = sub_int(x, y)
```
-/
def subInt (x y : JInt .i64) : JInt .i64 := JuliaLean.base.int.sub_int x y

/--
Julia source: base/essentials.jl:1294-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(x::Bool) = not_int(x)
```
-/
def notBool (notInt : Bool → Bool) (x : Bool) : Bool := notInt x

/--
Julia source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
```
-/
def lengthArray1 {A S N : Type} (getfield : A → String → S) (getindex : S → Nat → N) (a : A) : N := getindex (getfield a "size") 1

/--
Julia source: base/essentials.jl:1298-1298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_typevar(@nospecialize(t), v::TypeVar) = ccall(:jl_has_typevar, Int32, (Any, Any), t, v) !== Int32(0)
```
-/
def hasTypevar (ccall : JType → JType → Int32) (t v : JType) : Bool := ccall t v != 0

/--
Julia source: base/essentials.jl:1302-1339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldtypes_constrain_typevars(tvars::Array{Any,1}, fts::Core.SimpleVector)
    nparams = length(tvars)
    n = length(fts)
    i = nparams
    while i !== 0
        @inbounds tv = tvars[i]::TypeVar
        constrained = false
        j = 1
        while j !== n + 1
            ft = fts[j]
            if has_typevar(ft, tv)
                constrained = true
                break
            end
            j += 1
        end
        if !constrained
            j = i + 1
            remaining = nparams - i
            while remaining !== 0
                @inbounds tv2 = tvars[j]::TypeVar
                if has_typevar(tv2.ub, tv)
                    constrained = true
                    break
                end
                if tv2 === tv
                    constrained = false
                    break
                end
                j += 1
                remaining = remaining - 1
            end
        end
        constrained || return false
        i -= 1
    end
    return true
end
```
-/
def fieldtypesConstrainTypevars (ccall : JType → JType → Int32)
    (isTypevar : JType → Bool) (upperBound : JType → JType)
    (sameType : JType → JType → Bool) (tvars fts : List JType) : Except Exc Bool :=
  outer ccall isTypevar upperBound sameType fts tvars.reverse []
where
  inner (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
      (upperBound : JType → JType) (sameType : JType → JType → Bool)
      (later : List JType) (tv : JType) : Except Exc Bool := do
    match later with
    | [] => pure false
    | tv2 :: rest =>
      if !isTypevar tv2 then .error (.typeError "typeassert")
      else if hasTypevar ccall (upperBound tv2) tv then pure true
      else if sameType tv2 tv then pure false
      else inner ccall isTypevar upperBound sameType rest tv
  outer (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
      (upperBound : JType → JType) (sameType : JType → JType → Bool)
      (fts : List JType) : List JType → List JType → Except Exc Bool
    | [], _ => pure true
    | tv :: rest, later => do
      if !isTypevar tv then .error (.typeError "typeassert") else
        let constrained := fts.any fun ft => hasTypevar ccall ft tv
        if constrained then outer ccall isTypevar upperBound sameType fts rest (later ++ [tv])
        else do
          let linked ← inner ccall isTypevar upperBound sameType later.reverse tv
          if linked then outer ccall isTypevar upperBound sameType fts rest (later ++ [tv])
          else pure false

/--
Julia source: base/essentials.jl:1342-1360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _defaultctor_typeinfo(@nospecialize(ty::Type))
    nparams = 0
    ua = ty
    while isa(ua, UnionAll)
        nparams = nparams + 1
        ua = ua.body
    end
    dt = ua::DataType
    tvars = Array{Any,1}(Core.undef, nparams)
    ua = ty
    i = 1
    while i !== nparams + 1
        @inbounds tvars[i] = (ua::UnionAll).var
        ua = (ua::UnionAll).body
        i = i + 1
    end
    fts = ccall(:jl_get_fieldtypes, Any, (Any,), dt)::Core.SimpleVector
    return dt, tvars, fts
end
```
-/
def defaultctorTypeinfo (fieldtypes : JType → List JType)
    (ty : JType) : Except Exc (JType × List JType × List JType) :=
  let (_, dt) := peelUnionalls ty
  match dt with
  | .dt _ _ _ => .ok (dt, unionallVars ty, fieldtypes dt)
  | _ => .error (.typeError "typeassert")
where
  peelUnionalls : JType → Nat × JType
    | .unionAll _ body => let (n, t) := peelUnionalls body; (n + 1, t)
    | t => (0, t)
  unionallVars : JType → List JType
    | .unionAll var body => var :: unionallVars body
    | _ => []

/--
Julia source: base/essentials.jl:1365-1514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _defaultctors(@nospecialize(ty), functionloc)
    typeinfo = _defaultctor_typeinfo(ty)
    dt = getfield(typeinfo, 1)
    tvars = getfield(typeinfo, 2)
    fts = getfield(typeinfo, 3)
    nparams = length(tvars)

    mod = dt.name.module
    n = length(fts)
    names = dt.name.names::Core.SimpleVector
    src_file = ccall(:jl_symbol_name, Ptr{UInt8}, (Any,), functionloc.file)
    src_line = UInt(functionloc.line)

    is_parametric = nparams !== 0

    # Build argument names using actual field names for slot names (better debugging).
    # The body references arguments via Core.Argument(N) to avoid issues with
    # all-underscore field names being write-only in lowering.
    self = Symbol("#ctor-self#")
    argnames = Array{Any,1}(Core.undef, n + 1)
    @inbounds argnames[1] = self
    i = 1
    nany = 0
    while i !== n + 1
        @inbounds argnames[i + 1] = names[i]::Symbol
        if fts[i] === Any
            nany = nany + 1
        end
        i = i + 1
    end

    if _fieldtypes_constrain_typevars(tvars, fts)
        # Outer constructor: T(x::FT1, y::FT2, ...) = new{A,B,...}(x, y, ...)
        # Build lambda body with direct `new`, no convert calls
        if is_parametric
            # new(apply_type(ty, static_parameter(1), ...), args...)
            curly_args = Array{Any,1}(Core.undef, nparams + 1)
            @inbounds curly_args[1] = ty
            i = 1
            while i !== nparams + 1
                @inbounds curly_args[i + 1] = Expr(:static_parameter, i)
                i = i + 1
            end
            new_target = Expr(:curly, curly_args...)
        else
            new_target = Core.Argument(1)
        end
        new_args = Array{Any,1}(Core.undef, n + 1)
        @inbounds new_args[1] = new_target
        i = 1
        while i !== n + 1
            @inbounds new_args[i + 1] = Core.Argument(i + 1)
            i = i + 1
        end
        new_expr = Expr(:new, new_args...)
        lambda = Expr(:lambda, argnames,
            Expr(:block, functionloc, Expr(:return, new_expr)))
        ci = ccall(:jl_lower, Any, (Any, Any, Ptr{UInt8}, UInt, UInt, Int32),
                   lambda, mod, src_file, src_line, sub_int(UInt(0), UInt(1)), Int32(0))[1]

        # Build argdata: svec(svec(Type{ty}, ft1, ft2, ...), svec(tvars...), functionloc)
        atypes_arr = Array{Any,1}(Core.undef, n + 1)
        @inbounds atypes_arr[1] = Core.apply_type(Type, ty)
        i = 1
        while i !== n + 1
            @inbounds atypes_arr[i + 1] = fts[i]
            i = i + 1
        end
        outer_atypes = Core.svec(atypes_arr...)
        outer_tvars = Core.svec(tvars...)
        argdata = Core.svec(outer_atypes, outer_tvars, functionloc)
        ccall(:jl_method_def, Any, (Any, Ptr{Nothing}, Any, Any),
              argdata, C_NULL, ci, mod)

        # For non-parametric types where all fields are Any, outer constructor suffices
        if nparams === 0
            all_any = true
            i = 1
            while i !== n + 1
                if fts[i] !== Any
                    all_any = false
                    break
                end
                i = i + 1
            end
            if all_any
                return
            end
        end
    end

    # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
    # Build lambda body using Core.Argument references
    nstmts = ((n - nany) + (n - nany)) + 1
    body_args = Array{Any,1}(Core.undef, nstmts)
    new_args = Array{Any,1}(Core.undef, n)
    i = 1
    bidx = 1
    while i !== n + 1
        ft = fts[i]
        if ft === Any
            @inbounds new_args[i] = Core.Argument(i + 1)
        else
            # Use an isa check to avoid depending on convert inlining.
            # This matches the old convert-for-type-decl pattern:
            #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
            # The isa check is important because user code may define ambiguous
            # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
            # optimizer from inlining convert(fieldtype(self, i), arg) when the
            # field type is Any after specialization.
            ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
            ft_ssa = Expr(:ssavalue, bidx)
            cnvt_ssa = Expr(:ssavalue, bidx + 1)
            isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
            convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
            @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
            @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
                                               Core.Argument(i + 1), convert_expr))
            @inbounds new_args[i] = cnvt_ssa
            bidx = bidx + 2
        end
        i = i + 1
    end
    body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
    lambda = Expr(:lambda, argnames,
        Expr(:block, functionloc, body_args...))
    ci = ccall(:jl_lower, Any, (Any, Any, Ptr{UInt8}, UInt, UInt, Int32),
               lambda, mod, src_file, src_line, sub_int(UInt(0), UInt(1)), Int32(0))[1]

    # Build argdata: svec(svec(UnionAll...Type{dt}..., Any, Any, ...), svec(), functionloc)
    inner_atypes_arr = Array{Any,1}(Core.undef, n + 1)
    typedt = Core.apply_type(Type, dt)
    i = nparams
    while i !== 0
        @inbounds typedt = UnionAll(tvars[i], typedt)
        i = i - 1
    end
    @inbounds inner_atypes_arr[1] = typedt
    i = 1
    while i !== n + 1
        @inbounds inner_atypes_arr[i + 1] = Any
        i = i + 1
    end
    inner_atypes = Core.svec(inner_atypes_arr...)
    inner_tvars = Core.svec()
    argdata = Core.svec(inner_atypes, inner_tvars, functionloc)
    ccall(:jl_method_def, Any, (Any, Ptr{Nothing}, Any, Any),
          argdata, C_NULL, ci, mod)
    return
end
```
-/
def defaultctors (ops : DefaultCtorOps) (ty functionloc : JVal) : Except Exc (List MethodDef) := do
  let ty ← match ty with | .ty t => pure t | _ => .error (.typeError "typeassert")
  let (dt, tvars, fieldTypes) ← defaultctorTypeinfo ops.getFieldtypes ty
  let nparams := tvars.length
  let n := fieldTypes.length
  let names := ops.getNames dt
  let _ ← srcLine functionloc
  let self := .sym "#ctor-self#"
  let (argnames, nany) ← argnamesLoop 1 names fieldTypes (setAt (undefArr (n + 1)) 1 self) 0
  let argnames := .obj "Array{Any,1}" argnames
  let constrained ← fieldtypesConstrainTypevars ops.ccallHasTypevar ops.isTypevar ops.upperBound ops.sameType tvars fieldTypes
  if constrained then do
    let outer ← outerCtor ops ty tvars fieldTypes argnames functionloc
    ops.recordMethod outer
    if nparams == 0 && allAnyLoop fieldTypes then pure [outer]
    else do
      let inner ← innerCtor ops dt tvars fieldTypes nany argnames functionloc
      ops.recordMethod inner
      pure [outer, inner]
  else do
    let inner ← innerCtor ops dt tvars fieldTypes nany argnames functionloc
    ops.recordMethod inner
    pure [inner]

/--
Julia source: base/essentials.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismissing(x) = x === missing
```
-/
def ismissing {α : Type} (isMissing : α → Bool) (x : α) : Bool := isMissing x

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1544-1544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst! end
```
-/

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1570-1570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek end
```
-/

/--
Julia source: base/essentials.jl:1578-1580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro __LINE__()
    return __source__.line
end
```
-/
def lineMacro (lineNumber : JVal → Except Exc JVal) (source : JVal) : Except Exc JVal := lineNumber source

/--
Julia source: base/essentials.jl:1601-1601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(_, _...) = missing
```
-/
def isdoneDefault {α : Type} (_ : α) (_ : List α) : Option Bool := none

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1610-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate end
```
-/

/--
Julia source: base/essentials.jl:1618-1620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isiterable(T)::Bool
    return hasmethod(iterate, Tuple{T})
end
```
-/
def isiterable {T : Type} (hasmethod : T → Bool) (t : T) : Bool := hasmethod t

/--
Julia source: base/essentials.jl:1656-1670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro world(sym, world)
    if world == :∞
        world = Expr(:call, get_world_counter)
    end
    if isa(sym, Symbol)
        return :($(_resolve_in_world)($(esc(world)), $(QuoteNode(GlobalRef(__module__, sym)))))
    elseif isa(sym, GlobalRef)
        return :($(_resolve_in_world)($(esc(world)), $(QuoteNode(sym))))
    elseif isa(sym, Expr) && sym.head === :(.) &&
            length(sym.args) == 2 && isa(sym.args[2], QuoteNode) && isa(sym.args[2].value, Symbol)
        return :($(_resolve_in_world)($(esc(world)), $(GlobalRef)($(esc(sym.args[1])), $(sym.args[2]))))
    else
        error("`@world` requires a symbol or GlobalRef")
    end
end
```
-/
def worldMacro (moduleName : JVal → String) (getWorldCounter : JVal)
    (module_ sym world : JVal) : Except Exc JVal :=
  let world := match world with
    | .sym "∞" => .expr "call" [getWorldCounter]
    | other => other
  let resolver := .globalRef "Base" "_resolve_in_world"
  match sym with
  | .sym name => .ok (.expr "call" [resolver, esc world, .quoteNode (.globalRef (moduleName module_) name)])
  | .globalRef m name => .ok (.expr "call" [resolver, esc world, .quoteNode (.globalRef m name)])
  | .expr "." [a, .quoteNode (.sym name)] =>
    .ok (.expr "call" [resolver, esc world, .expr "globalref" [esc a, .quoteNode (.sym name)]])
  | _ => .error (.error "`@world` requires a symbol or GlobalRef")

/--
Julia source: base/essentials.jl:1672-1673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_resolve_in_world(world::Integer, gr::GlobalRef) =
    invoke_in_world(UInt(world), Core.getglobal, gr.mod, gr.name)
```
-/
def resolveInWorld {W G R : Type} (toUInt : W → Except Exc G)
    (invokeInWorld : G → String → String → R) (world : W) (gr : String × String) : Except Exc R := do
  let unsignedWorld ← toUInt world
  pure (invokeInWorld unsignedWorld gr.1 gr.2)

end JuliaLean.base.essentials
