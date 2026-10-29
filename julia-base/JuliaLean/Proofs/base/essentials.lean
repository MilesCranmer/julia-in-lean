import JuliaLean.base.essentials
import JuliaLean.base.int
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.essentials

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials JuliaLean.Registry

def productValue (dims : List (JInt .i64)) : Int :=
  dims.foldl (fun acc d => acc * d.val) 1

def CartesianIsEmpty : Prop :=
  ∀ dims : List (JInt .i64), (∀ d ∈ dims, 0 ≤ d.val) →
    ((prodDims dims).val = 0 ↔ ∃ d, d ∈ dims ∧ d.val = 0)

def DefaultCtorAccessesInBounds : Prop :=
  (∀ (names : List JVal) (fieldTypes : List JType),
    names.length = fieldTypes.length →
    (∀ name, name ∈ names → ∃ symbol, name = .sym symbol) →
    ∃ argnames nany,
      argnamesLoop 1 names fieldTypes (setAt (undefArr (fieldTypes.length + 1)) 1 (.sym "#ctor-self#")) 0 =
        .ok (argnames, nany) ∧ argnames.length = fieldTypes.length + 1) ∧
  (∀ n, (curlyLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ n, (newArgsLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ fieldTypes, (atypesLoop 1 fieldTypes (undefArr (fieldTypes.length + 1))).length = fieldTypes.length + 1) ∧
  (∀ n, (anyArgsLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ fieldTypes (nany : Nat), nany ≤ fieldTypes.length →
    let (body, args) := innerLoop 1 1 fieldTypes
      (undefArr ((fieldTypes.length - nany) * 2 + 1)) (undefArr fieldTypes.length)
    body.length = (fieldTypes.length - nany) * 2 + 1 ∧ args.length = fieldTypes.length)

def expectedEffectMeta (internal : Bool) (flags : List Bool) : JVal :=
  if internal then .expr "meta" [.expr "purity" (flags.map JVal.bool)] else .bool false

def BaseEffectMetasMatchAssume : Prop :=
  ∀ (nameof : JVal → String) (baseRelative : JVal → JVal) (module_ : JVal),
    (nameofModule nameof module_ = nameof module_) ∧
    (isInternal nameof baseRelative module_ =
      (nameof module_ == "Base" || nameof (baseRelative module_) == "Compiler")) ∧
    totalMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [true, true, true, true, false, true, true, true, false, false, true] ∧
    foldableMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [true, true, false, true, false, true, true, true, false, false, true] ∧
    terminatesLocallyMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, false, true, false, false, false, false, false, false] ∧
    terminatesGloballyMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, true, true, false, false, false, false, false, false] ∧
    terminatesGloballyNotaskstateMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, true, true, true, false, false, false, false, false] ∧
    terminatesGloballyNoubMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, true, true, false, false, true, false, false, false] ∧
    effectFreeTerminatesLocallyMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, true, false, false, true, false, false, false, false, false, false] ∧
    nothrowNoubMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, true, false, false, false, false, true, false, false, false] ∧
    nothrowMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, true, false, false, false, false, false, false, false, false] ∧
    noubMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, false, false, false, false, true, false, false, false] ∧
    notaskstateMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, false, false, true, false, false, false, false, false] ∧
    noubIfNoinboundsMeta nameof baseRelative module_ = expectedEffectMeta (isInternal nameof baseRelative module_)
      [false, false, false, false, false, false, false, false, true, false, false]

def CheckboundsBoolCorrect : Prop :=
  ∀ (len i : JInt .i64), 0 ≤ len.val →
    (checkboundsBool len i = true ↔ 1 ≤ i.val ∧ i.val ≤ len.val)

def AccessSemantics : Prop :=
  (∀ {M I R V : Type} (check : M → List I → Bool)
      (throwBounds : M → List I → Except Exc Unit)
      (memoryrefnew : M → I → Bool → R) (isAtomic : M → Bool)
      (memoryrefget : R → String → Bool → Except Exc V)
      (memory : M) (i : I) e,
    throwBounds memory [i] = .error e →
      getindexGenericMemory true check throwBounds memoryrefnew isAtomic memoryrefget memory i = .error e) ∧
  (∀ (atomic : Bool), defaultAccessOrder atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderMemory atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderRef atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderMemoryRef atomic = (if atomic then "monotonic" else "not_atomic")) ∧
  (∀ {A D : Type} (getfield : A → String → D) a, sizeArray getfield a = getfield a "size") ∧
  (∀ {A N : Type} (getfield : A → String → N) a,
    sizeGenericMemory getfield a = getfield a "length") ∧
  (∀ {A I : Type} (check : A → List I → Bool)
      (throwBounds : A → List I → Except Exc Unit) a indices,
    check a indices = true → checkboundsGeneric check throwBounds a indices = .ok ()) ∧
  (∀ {R V : Type} (isAtomic : R → Bool)
      (memoryrefget : R → String → Bool → Except Exc V) ref,
    getindexGenericMemoryRef false isAtomic memoryrefget ref =
      memoryrefget ref (defaultAccessOrderMemoryRef (isAtomic ref)) false)

def SvecSemantics : Prop :=
  (∀ (svecLength : SimpleVectorModel → Nat) v,
    lengthSVec svecLength v = svecLength v ∧ firstindexSVec v = 1 ∧
      lastindexSVec svecLength v = svecLength v ∧ keysSVec svecLength v = svecLength v ∧
      eltypeSVec = "Any" ∧ axesSVec svecLength v = [svecLength v] ∧
      isemptySVec svecLength v = decide (svecLength v = 0)) ∧
  (∀ (svecLength : SimpleVectorModel → Nat)
      (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal)) v i,
    (svecLength v : Nat) < i → iterateSVec svecLength svecRef v i = .ok none) ∧
  (∀ (svecLength : SimpleVectorModel → Nat)
      (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
      (v : SimpleVectorModel) (i : Nat) (value : Option JVal),
    svecRef v (i : Int) = .ok value → i ≤ svecLength v →
      iterateSVec svecLength svecRef v i = .ok (some (value, i + 1))) ∧
  (∀ (eq : Option JVal → Option JVal → Bool) (v : SimpleVectorModel),
    (∀ x, eq x x = true) → equalSVec List.length eq v v = true) ∧
  (∀ {α : Type} (svecLength : SimpleVectorModel → Nat)
      (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
      (f : Option JVal → α) v result,
    mapSVec svecLength svecRef f v = .ok result →
      result.length = svecLength v ∧
      ∀ i value, i < svecLength v → svecRef v ((i : Int) + 1) = .ok value →
        result[i]? = some (f value)) ∧
  (∀ {α : Type} (svecRef : SimpleVectorModel → Int → Except Exc (Option JVal))
      (makeSVec : List (Option JVal) → α) v indices values,
    indices.mapM (fun i => getindexSVec svecRef v i) = .ok values →
      getindexSVecArray svecRef makeSVec v indices = .ok (makeSVec values))

def SvecIsassignedCorrect : Prop :=
  ∀ (v : SimpleVectorModel) (i : Int),
    isassignedSVec List.length v i = true ↔
      1 ≤ i ∧ i ≤ (v.length : Int) ∧ ∃ x, v[(i - 1).toNat]? = some (some x)

def UnwrapRewrap : Prop :=
  (∀ u, isUnionAll u = false → unwrapUnionall u = u) ∧
  (∀ (unionAll : JType → JType → Except Exc JType) t u,
    isUnionAll u = false → rewrapUnionall unionAll t u = .ok t) ∧
  (∀ (isDefined : JType → String → Bool) (getField : JType → String → Except Exc JType)
      (eqType : JType → JType → Bool) (unionAll : JType → JType → Except Exc JType)
      (vararg : JType → Option JType → JType) t u,
    isDefined t "T" = false → rewrapUnionallVararg isDefined getField eqType unionAll vararg t u = .ok t) ∧
  (∀ widen t root, widenDiagonal widen t root = widen t root)

def RenameUnionall : Prop :=
  (∀ (typevarInfo : JType → Except Exc (String × JType × JType))
    (unionAll : JType → JType → Except Exc JType)
    (typevar : String → JType → JType → JType)
    (instantiate : JType → JType → Except Exc JType) u,
    isUnionAll u = false → renameUnionall typevarInfo unionAll typevar instantiate u = .ok u) ∧
  (∀ widen t root, widenDiagonal widen t root = widen t root)

def VarargHelpers : Prop :=
  (∀ t, isvarargtype t = true ↔ ∃ T N, t = .vararg T N) ∧
  (∀ t, isvatuple t = true ↔
    ∃ name abs params va, unwrapUnionall t = .dt name abs params ∧
      params.getLast? = some va ∧ isvarargtype va = true) ∧
  (∀ (any : JType) T N, unwrapva any (.vararg (some T) N) = T) ∧
  (∀ any N, unwrapva any (.vararg none N) = any) ∧
  (∀ va, unconstrainVarargLength va = .vararg (some (unwrapva (.dt "Any" true []) va)) none)

def MinNinitialized : Prop :=
  (∀ (isabstract : JType → Bool) fields uninitialized t,
    isabstract (unwrapUnionall t) = true →
      datatypeMinNinitialized isabstract fields uninitialized t = 0) ∧
  (∀ (isabstract : JType → Bool) fields uninitialized params,
    isabstract (.dt "Tuple" false params) = false →
      datatypeMinNinitialized isabstract fields uninitialized (.dt "Tuple" false params) =
        if params.isEmpty then 0 else match params.getLast? with
          | some (.vararg _ (some (.intParam n))) => (params.length : Int) - 1 + n
          | some (.vararg _ _) => (params.length : Int) - 1
          | _ => params.length)

def HasTypevarBehaviour : Prop :=
  (∀ (ccall : JType → JType → Int32) id name lb ub,
    ccall (.tvar id name lb ub) (.tvar id name lb ub) != 0 →
      hasTypevar ccall (.tvar id name lb ub) (.tvar id name lb ub) = true) ∧
  (∀ (ccall : JType → JType → Int32) t v,
    ccall t v != 0 → hasTypevar ccall t v = true) ∧
  (∀ (ccall : JType → JType → Int32) id name lb ub body,
    ccall (.unionAll (.tvar id name lb ub) body) (.tvar id name lb ub) = 0 →
      hasTypevar ccall (.unionAll (.tvar id name lb ub) body) (.tvar id name lb ub) = false)

def TupleHelpers : Prop :=
  (∀ {α : Type} (x : α) xs, tail (α := α) (x :: xs) = .ok (argtail x xs)) ∧
  (∀ {α : Type}, ∃ message, tailEmpty (α := α) = .error (.argument message)) ∧
  (∀ {T X Y A : Type} (disjoint : Nat → T → Bool) (fieldtype : T → Nat → Y)
      (getfield : X → Nat → A) (isa : Y → A → Bool) (convert : Y → A → Except Exc A)
      (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A)) target x n,
    disjoint n target = true →
      convertTuple disjoint fieldtype getfield isa convert ntuple target x n = tupleError target x) ∧
  (∀ {T X Y A : Type} (disjoint : Nat → T → Bool) (fieldtype : T → Nat → Y)
      (getfield : X → Nat → A) (isa : Y → A → Bool) (convert : Y → A → Except Exc A)
      (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A)) target x n result,
    convertTuple disjoint fieldtype getfield isa convert ntuple target x n = .ok result → result.length = n)

def ThrowBoundserrorForms : Prop :=
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a,
    throwBoundserror throwBounds a = throwBounds a []) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a I,
    throwBoundserrorIndices throwBounds a I = throwBounds a I) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a i1 i2 I,
    throwBoundserrorMany throwBounds a i1 i2 I = throwBounds a (i1 :: i2 :: I)) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a,
    throwBoundserrorIndicesEmpty throwBounds a = throwBounds a []) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a i1 I,
    throwBoundserrorIndicesMany throwBounds a i1 I = throwBounds a (i1 :: I))

def GlobalRefEq : Prop :=
  ∀ a b : String × String, globalRefEq a b = true ↔ a = b

def OftypeSpec : Prop :=
  (∀ {α : Type} (isa : α → α → Bool) (convert : α → α → Except Exc α) x y,
    isa x y = true → oftype isa convert x y = .ok y) ∧
  (∀ {α : Type} (isa : α → α → Bool) (convert : α → α → Except Exc α) x y result,
    isa x y = false → convert x y = .ok result → oftype isa convert x y = .ok result)

def SignedUnsignedInt : Prop :=
  (∀ x : JInt .i64, (unsignedInt x).val = wrapInt .u64 x.val) ∧
  (∀ x : JInt .u64, (signedUInt x).val = wrapInt .i64 x.val)

def ReinterpretSpec : Prop :=
  ∀ {O X R : Type} (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) out x,
    isPrimitiveOut out = true → isPrimitiveValue x = true →
      reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = bitcast out x

def SizeofSpec : Prop :=
  ∀ {X N : Type} (coreSizeof : X → N) x, sizeof coreSizeof x = coreSizeof x

def IsemptySpec : Prop :=
  (∀ {I S : Type} (isdone : I → List S → Option Bool)
      (iterate : I → List S → Option (S × List S)) itr state done_,
    isdone itr state = some done_ → isempty isdone iterate itr state = done_) ∧
  (∀ {I S : Type} (isdone : I → List S → Option Bool)
      (iterate : I → List S → Option (S × List S)) itr state,
    isdone itr state = none → isempty isdone iterate itr state = (iterate itr state).isNone)

def IntAddSub : Prop :=
  ∀ x y : JInt .i64,
    (JuliaLean.base.essentials.addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (JuliaLean.base.essentials.subInt x y).val = wrapInt .i64 (x.val - y.val)

def IsmissingSpec : Prop :=
  ∀ {α : Type} (isMissing : α → Bool) x, ismissing isMissing x = isMissing x

def ResolveInWorld : Prop :=
  (∀ {W G R : Type} (toUInt : W → Except Exc G)
      (invokeInWorld : G → String → String → R) world gr unsignedWorld,
    toUInt world = .ok unsignedWorld →
      resolveInWorld toUInt invokeInWorld world gr = .ok (invokeInWorld unsignedWorld gr.1 gr.2)) ∧
  (∀ {W G R : Type} (toUInt : W → Except Exc G)
      (invokeInWorld : G → String → String → R) world gr e,
    toUInt world = .error e → resolveInWorld toUInt invokeInWorld world gr = .error e)

def LengthAbstractSpec : Prop :=
  ∀ dims : List (JInt .i64),
    (lengthAbstract (fun (_ : Unit) => dims) prodDims ()).val =
      wrapInt .i64 (productValue dims)

def hasConvertStmt : JVal → Bool
  | .expr "=" [_, .expr "if" [_, _, .expr "call" (.globalRef "Base" "convert" :: _)]] => true
  | _ => false

def lambdaHasConvert : JVal → Bool
  | .expr "lambda" (_ :: .expr "block" body :: _) => body.any hasConvertStmt
  | _ => false

def DefaultctorsSpec : Prop :=
  ∀ (ops : DefaultCtorOps) (ty : JType) (location : JVal)
    (dt : JType) (tvars fields : List JType) (methods : List MethodDef),
    defaultctorTypeinfo ops.getFieldtypes ty = .ok (dt, tvars, fields) →
    defaultctors ops (.ty ty) location = .ok methods →
    let constrained := fieldtypesConstrainTypevars ops.ccallHasTypevar ops.isTypevar ops.upperBound ops.sameType tvars fields
    methods.length = (match constrained with
      | .ok true => if tvars.isEmpty && allAnyLoop fields then 1 else 2
      | _ => 1) ∧
    (constrained = .ok true →
      (if tvars.isEmpty && allAnyLoop fields then methods.length = 1
       else ∃ outer inner, methods = [outer, inner] ∧
         (fields.any (fun ft => !isAnyTy ft) = true → lambdaHasConvert inner.lambda = true))) ∧
    (constrained ≠ .ok true →
      ∃ inner, methods = [inner] ∧
        (fields.any (fun ft => !isAnyTy ft) = true → lambdaHasConvert inner.lambda = true))

def BaseMarkerMacros : Prop :=
  (∀ args, nospecialize [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "nospecialize", .expr "kw" args]]) ∧
  (∀ args, specialize [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "specialize", .expr "kw" args]]) ∧
  (∀ x, gcPreserveBegin x = .expr "gc_preserve_begin" [JuliaLean.base.essentials.esc x] ∧
    gcPreserveEnd x = .expr "gc_preserve_end" [JuliaLean.base.essentials.esc x]) ∧
  (∀ s, isdefinedMacro s = .expr "escape" [.expr "isdefined" [.sym s]]) ∧
  (∀ block, boundscheckMacro block = .expr "if" [.expr "boundscheck" [], JuliaLean.base.essentials.esc block]) ∧
  (∀ block, inboundsMacro block = .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", JuliaLean.base.essentials.esc block]],
    .expr "inbounds" [.sym "pop"], .sym "val"]) ∧
  propagateInboundsMeta = .expr "meta" [.sym "inline", .sym "propagate_inbounds"] ∧
  nospecializeinferMeta = .expr "meta" [.sym "nospecializeinfer"] ∧
  (∀ (esc : JVal → JVal) module_ ex,
    evalMacro1 esc module_ ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ (esc : JVal → JVal) mod ex,
    evalMacro2 esc mod ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ x, JuliaLean.base.essentials.esc x = .expr "escape" [x]) ∧
  (∃ message, label1 "_" = .error (.error message)) ∧
  (∀ name, name ≠ "_" → label1 name = .ok (JuliaLean.base.essentials.esc (.expr "symboliclabel" [.sym name]))) ∧
  (∀ body, ∃ message, label2 "_" body = .error (.error message)) ∧
  (∀ name body, name ≠ "_" →
    (∀ args, body ≠ .expr "for" args) → (∀ args, body ≠ .expr "while" args) →
    label2 name body = .ok (JuliaLean.base.essentials.esc (.expr "symbolicblock" [.sym name, body]))) ∧
  (∀ name iter loopBody, name ≠ "_" →
    label2 name (.expr "for" [iter, loopBody]) = .ok (JuliaLean.base.essentials.esc
      (.expr "symbolicblock" [.sym name, .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ name condition loopBody, name ≠ "_" →
    label2 name (.expr "while" [condition, loopBody]) = .ok (JuliaLean.base.essentials.esc
      (.expr "symbolicblock" [.sym name, .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ body, label0 body = JuliaLean.base.essentials.esc (.expr "symbolicblock" [.sym "loop-exit", body])) ∧
  (∀ name, gotoMacro name = JuliaLean.base.essentials.esc (.expr "symbolicgoto" [.sym name])) ∧
  (∀ (lineNumber : JVal → Except Exc JVal) source,
    lineMacro lineNumber source = lineNumber source) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ name world,
    world ≠ .sym "∞" → worldMacro moduleName getWorldCounter module_ (.sym name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        JuliaLean.base.essentials.esc world,
        .quoteNode (.globalRef (moduleName module_) name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ m name world,
    world ≠ .sym "∞" → worldMacro moduleName getWorldCounter module_ (.globalRef m name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        JuliaLean.base.essentials.esc world, .quoteNode (.globalRef m name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ value name world,
    world ≠ .sym "∞" →
      worldMacro moduleName getWorldCounter module_ (.expr "." [value, .quoteNode (.sym name)]) world =
        .ok (.expr "call" [.globalRef "Base" "_resolve_in_world", JuliaLean.base.essentials.esc world,
          .expr "globalref" [JuliaLean.base.essentials.esc value, .quoteNode (.sym name)]])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ world,
    ∃ message, worldMacro moduleName getWorldCounter module_ (.bool true) world = .error (.error message))

def Barriers : Prop :=
  (∀ {α : Type} (compilerbarrier : String → α → α) x,
    (∀ tag, compilerbarrier tag x = x) → blackbox compilerbarrier x = x ∧ inferencebarrier compilerbarrier x = x) ∧
  (∀ {α : Type} (iterator : α), values iterator = iterator)

def ConversionSpec : Prop :=
  (∀ {α : Type} (x : α), convertTypeIdentity x = x ∧ unsafeConvertIdentity x = x) ∧
  (∀ {T X : Type} (isa : X → Bool) (assert : X → T) (convert : X → Except Exc T) x,
    isa x = true → cconvert isa assert convert x = .ok (assert x)) ∧
  (∀ {T X : Type} (isa : X → Bool) (assert : X → T) (convert : X → Except Exc T) x,
    isa x = false → cconvert isa assert convert x = convert x) ∧
  (∀ {X R : Type} (convert : List X → Except Exc R) xs,
    cconvertUnionBottom convert xs = convert xs) ∧
  (∀ {α : Type} (x : α), cconvertPointer x = x) ∧
  (∀ {P Ptr R : Type} (convert : P → Ptr → R) p ptr,
    unsafeConvertPointer convert p ptr = convert p ptr) ∧
  (∀ {R : Type} (stringPointer : String → R) s,
    unsafeConvertStringUInt8 stringPointer s = stringPointer s ∧
    unsafeConvertStringInt8 stringPointer s = stringPointer s) ∧
  (∀ {α R : Type} (xs : List α), convertUnionBottom (R := R) xs =
    .error (.argument "cannot convert a value to Union{} for assignment"))

def IfelseSpec : Prop :=
  ∀ {α : Type} (x y : α), JuliaLean.base.essentials.ifelse true x y = x ∧ JuliaLean.base.essentials.ifelse false x y = y

def NotBool : Prop :=
  ∀ (notInt : Bool → Bool), notInt true = false → notInt false = true →
    notBool notInt true = false ∧ notBool notInt false = true

def IsdoneDefault : Prop :=
  ∀ {α : Type} (x : α) (state : List α), JuliaLean.base.essentials.isdoneDefault x state = none

def IsiterableSpec : Prop :=
  ∀ {T : Type} (hasmethod : T → Bool) t, isiterable hasmethod t = hasmethod t


def ArrayAccessSpec : Prop :=
  (∀ {A I P R V : Type} (getfield : A → String → P)
      (memoryrefnew : P → I → Bool → R)
      (memoryrefget : R → String → Bool → Except Exc V) a i r v,
    memoryrefnew (getfield a "ref") i false = r →
    memoryrefget r "not_atomic" false = .ok v →
      getindexArray false (fun _ _ => true) (fun _ _ => .ok ())
        getfield memoryrefnew memoryrefget a i = .ok v) ∧
  (∀ {A I R X : Type} (memoryrefnew : A → I → Bool → R)
      (memoryrefset : R → X → String → Bool → Except Exc Unit) a i x r,
    memoryrefnew a i false = r → memoryrefset r x "not_atomic" false = .ok () →
      setindexMemoryAny false (fun _ _ => true) (fun _ _ => .ok ())
        memoryrefnew memoryrefset a x i = .ok a) ∧
  (∀ {A T X : Type} (convert : X → Except Exc T)
      (memoryrefset : A → T → String → Bool → Except Exc Unit) ref x e,
    convert x = .error e →
      setindexMemoryRef convert memoryrefset ref x = .error e) ∧
  (∀ {A X : Type} (memoryrefset : A → X → String → Bool → Except Exc Unit)
      ref x,
    memoryrefset ref x "not_atomic" false = .ok () →
      setindexMemoryRefAny memoryrefset ref x = .ok ref)

def FieldtypesConstrainSpec : Prop :=
  ∀ (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
    (upperBound : JType → JType) (sameType : JType → JType → Bool)
    (tvars fields : List JType),
    (∀ tv, tv ∈ tvars → isTypevar tv = true) →
    (∀ tv, tv ∈ tvars → fields.any (fun ft => hasTypevar ccall ft tv) = true) →
      fieldtypesConstrainTypevars ccall isTypevar upperBound sameType tvars fields = .ok true

def unionallVars : JType → List JType
  | .unionAll var body => var :: unionallVars body
  | _ => []

def isDataType : JType → Bool
  | .dt _ _ _ => true
  | _ => false

def TypeinfoSpec : Prop :=
  ∀ (fieldtypes : JType → List JType) (ty : JType),
    if isDataType (unwrapUnionall ty) then
      defaultctorTypeinfo fieldtypes ty =
        .ok (unwrapUnionall ty, unionallVars ty, fieldtypes (unwrapUnionall ty))
    else defaultctorTypeinfo fieldtypes ty = .error (.typeError "typeassert")

def PairsAndColonVal : Prop :=
  (∀ {K V I A : Type} (data : A) (iter : I),
    pairsCtorKV data iter = (⟨data, iter⟩ : PairsModel K V I A)) ∧
  (∀ {K I A : Type} (eltype : Type → Type) (data : A) (iter : I),
    pairsCtorK eltype data iter = (⟨data, iter⟩ : PairsModel K (eltype A) I A)) ∧
  (∀ {A I : Type} (isNothingI : Bool) (eltype keytype : Type → Type) (data : A) (iter : I),
    pairsCtor isNothingI eltype keytype data iter =
      (⟨data, iter⟩ : PairsModel (if isNothingI then keytype A else eltype I) (eltype A) I A)) ∧
  (∀ {K V I A D J : Type} (isData : D → Bool) (asData : D → A)
      (convertData : D → Except Exc A) (isIter : J → Bool) (asIter : J → I)
      (convertIter : J → Except Exc I) data iter e,
    isData data = false → convertData data = .error e →
      pairsCtorFull (K := K) (V := V) isData asData convertData isIter asIter convertIter data iter = .error e) ∧
  colonCtor = ColonModel.mk ∧
  (∀ {α : Type} (x : α), valCtor x = ValValue.mk) ∧
  (∃ v nt, pairsNamedTupleType =
    .unionAll v (.unionAll nt (.dt "Pairs" false
      [.dt "Symbol" false [], v, .dt "Nothing" false [], nt])))

/-! Nothing to promise:
- convert@471: this is a generic-function declaration with no method body in this source file.
- cconvert@737: this is a generic-function declaration with no method body in this source file.
- _reinterpret@751: this is a generic-function declaration with no method body in this source file.
- isassigned@1149: this is a generic-function declaration with no method body in this source file.
- popfirst!@1544: this is a generic-function declaration with no method body in this source file.
- peek@1570: this is a generic-function declaration with no method body in this source file.
- iterate@1610: this is a generic-function declaration with no method body in this source file.
-/

/-! Method -> property table:
  blackbox@9 -> essentials-barriers
  size@12 -> bootcov-ess-access
  length@13 -> bootcov-ess-length-abstract
  size@14 -> bootcov-ess-access
  throw_boundserror@15 -> bootcov-ess-throw-boundserror
  throw_boundserror@16 -> bootcov-ess-throw-boundserror
  throw_boundserror@17 -> bootcov-ess-throw-boundserror
  _throw_boundserror_indices@18 -> bootcov-ess-throw-boundserror
  _throw_boundserror_indices@19 -> bootcov-ess-throw-boundserror
  ==@23 -> bootcov-ess-globalref-eq
  _gc_preserve_begin@46 -> essentials-marker-macros
  _gc_preserve_end@50 -> essentials-marker-macros
  nospecialize@125 -> essentials-marker-macros
  specialize@142 -> essentials-marker-macros
  isdefined@184 -> essentials-marker-macros
  _nameof@188 -> bootcov-foldable-meta-effects
  _is_internal@190 -> bootcov-foldable-meta-effects
  _total_meta@196 -> bootcov-foldable-meta-effects
  _foldable_meta@211 -> bootcov-foldable-meta-effects
  _terminates_locally_meta@226 -> bootcov-foldable-meta-effects
  _terminates_globally_meta@241 -> bootcov-foldable-meta-effects
  _terminates_globally_notaskstate_meta@256 -> bootcov-foldable-meta-effects
  _terminates_globally_noub_meta@271 -> bootcov-foldable-meta-effects
  _effect_free_terminates_locally_meta@286 -> bootcov-foldable-meta-effects
  _nothrow_noub_meta@301 -> bootcov-foldable-meta-effects
  _nothrow_meta@316 -> bootcov-foldable-meta-effects
  _noub_meta@331 -> bootcov-foldable-meta-effects
  _notaskstate_meta@346 -> bootcov-foldable-meta-effects
  _noub_if_noinbounds_meta@361 -> bootcov-foldable-meta-effects
  _propagate_inbounds_meta@377 -> essentials-marker-macros
  _nospecializeinfer_meta@380 -> essentials-marker-macros
  checkbounds@385 -> bootcov-ess-checkbounds
  checkbounds@389 -> bootcov-ess-checkbounds
  default_access_order@395 -> bootcov-ess-access
  default_access_order@396 -> bootcov-ess-access
  default_access_order@397 -> bootcov-ess-access
  default_access_order@398 -> bootcov-ess-access
  getindex@400 -> bootcov-ess-access
  getindex@406 -> bootcov-ess-access
  nameof@419 -> bootcov-foldable-meta-effects
  convert end@471 -> Nothing to promise: generic declaration only
  convert@474 -> essentials-conversions
  convert@476 -> essentials-conversions
  convert@480 -> essentials-conversions
  eval@488 -> essentials-marker-macros
  eval@495 -> essentials-marker-macros
  Pairs{K, V, I, A}@508 -> essentials-pairs-colon-val
  Pairs{K, V}@509 -> essentials-pairs-colon-val
  Pairs{K}@510 -> essentials-pairs-colon-val
  Pairs@511 -> essentials-pairs-colon-val
  pairs@513 -> essentials-pairs-colon-val
  argtail@523 -> bootcov-ess-tuples
  tail@541 -> bootcov-ess-tuples
  tail@542 -> bootcov-ess-tuples
  unwrap_unionall@544 -> bootcov-ess-unwrap-rewrap
  rewrap_unionall@552 -> bootcov-ess-unwrap-rewrap
  rewrap_unionall@560 -> bootcov-ess-unwrap-rewrap
  rename_unionall@574 -> bootcov-ess-rename
  widen_diagonal@585 -> bootcov-ess-rename
  isvarargtype@589 -> bootcov-ess-vararg
  isvatuple@593 -> bootcov-ess-vararg
  unwrapva@603 -> bootcov-ess-vararg
  unconstrain_vararg_length@608 -> bootcov-ess-vararg
  datatype_min_ninitialized@617 -> bootcov-ess-min-ninit
  _tuple_error@650 -> bootcov-ess-tuples
  convert@652 -> bootcov-ess-tuples
  convert@653 -> bootcov-ess-tuples
  oftype@718 -> bootcov-ess-oftype
  unsigned@720 -> bootcov-ess-signed-unsigned
  signed@721 -> bootcov-ess-signed-unsigned
  cconvert end@737 -> Nothing to promise: generic declaration only
  cconvert@739 -> essentials-conversions
  cconvert@740 -> essentials-conversions
  cconvert@741 -> essentials-conversions
  unsafe_convert@742 -> essentials-conversions
  unsafe_convert@743 -> essentials-conversions
  unsafe_convert@744 -> essentials-conversions
  unsafe_convert@745 -> essentials-conversions
  unsafe_convert@746 -> essentials-conversions
  _reinterpret end@751 -> Nothing to promise: generic declaration only
  reinterpret@787 -> essentials-conversions
  sizeof@841 -> essentials-conversions
  ifelse@894 -> essentials-control
  esc@903 -> essentials-marker-macros
  boundscheck@949 -> essentials-marker-macros
  inbounds@981 -> essentials-marker-macros
  label@1030 -> essentials-marker-macros
  label@1035 -> essentials-marker-macros
  label@1054 -> essentials-marker-macros
  goto@1068 -> essentials-marker-macros
  getindex@1073 -> essentials-array-access
  setindex!@1079 -> essentials-array-access
  setindex!@1085 -> essentials-array-access
  setindex!@1091 -> essentials-array-access
  setindex!@1092 -> essentials-array-access
  getindex@1096 -> bootcov-ess-svec
  length@1097 -> bootcov-ess-svec
  firstindex@1100 -> bootcov-ess-svec
  lastindex@1101 -> bootcov-ess-svec
  iterate@1102 -> bootcov-ess-svec
  eltype@1103 -> bootcov-ess-svec
  keys@1104 -> bootcov-ess-svec
  isempty@1105 -> bootcov-ess-svec
  axes@1106 -> bootcov-ess-svec
  axes@1107 -> bootcov-ess-svec
  ==@1109 -> bootcov-ess-svec
  map@1117 -> bootcov-ess-svec
  getindex@1119 -> bootcov-ess-svec
  unsafe_convert@1121 -> bootcov-ess-svec
  isassigned end@1149 -> Nothing to promise: generic declaration only
  isassigned@1151 -> bootcov-svec-isassigned-undef
  Colon@1170 -> essentials-pairs-colon-val
  show@1174 -> essentials-pairs-colon-val
  Val{x}@1200 -> essentials-pairs-colon-val
  Val@1203 -> essentials-pairs-colon-val
  inferencebarrier@1211 -> essentials-barriers
  isempty@1235 -> bootcov-ess-isempty
  values@1263 -> essentials-barriers
  method@1267 -> bootcov-ess-int-add-sub
  method@1268 -> bootcov-ess-int-add-sub
  !@1294 -> essentials-bool-not
  length@1296 -> bootcov-ess-length-abstract
  has_typevar@1298 -> bootcov-ess-has-typevar
  _fieldtypes_constrain_typevars@1302 -> essentials-fieldtypes-constrain
  _defaultctor_typeinfo@1342 -> essentials-defaultctor-typeinfo
  _defaultctors@1365 -> bootcov-ess-defaultctors
  ismissing@1542 -> bootcov-ess-ismissing
  popfirst! end@1544 -> Nothing to promise: generic declaration only
  peek end@1570 -> Nothing to promise: generic declaration only
  __LINE__@1578 -> essentials-marker-macros
  isdone@1601 -> essentials-iterator-defaults
  iterate end@1610 -> Nothing to promise: generic declaration only
  isiterable@1618 -> essentials-isiterable
  world@1656 -> essentials-marker-macros
  _resolve_in_world@1672 -> bootcov-ess-resolve-in-world
-/

def entries : List Entry := [
  { id := "multidim-cartesianindices-length-overflow", juliaFile := "base/essentials.jl",
    juliaFns := ["length(t::AbstractArray)", "isempty(a::AbstractArray)", "size(iter::CartesianIndices)", "getindex(::CartesianIndices, ::Int)"],
    statement := "isempty(R) for CartesianIndices is true exactly when one component range is empty.", source := "isempty and length semantics; base/abstractarray.jl length contract",
    status := .todo, prop := ``CartesianIsEmpty },
  { id := "memsafety-essentials-defaultctors", juliaFile := "base/essentials.jl",
    juliaFns := ["_fieldtypes_constrain_typevars", "_defaultctor_typeinfo", "_defaultctors"],
    statement := "Every unchecked access computed by default-constructor generation is within its source vector or generated allocation.", source := "base/essentials.jl:1290-1503; type representation invariant",
    status := .todo, prop := ``DefaultCtorAccessesInBounds },
  { id := "bootcov-foldable-meta-effects", juliaFile := "base/essentials.jl",
    juliaFns := ["@_total_meta", "@_foldable_meta", "@_terminates_locally_meta", "@_terminates_globally_meta", "@_terminates_globally_notaskstate_meta", "@_terminates_globally_noub_meta", "@_effect_free_terminates_locally_meta", "@_nothrow_noub_meta", "@_nothrow_meta", "@_noub_meta", "@_notaskstate_meta", "@_noub_if_noinbounds_meta", "_is_internal", "_nameof", "nameof(::Module)"],
    statement := "Each Base effect macro emits its documented effect settings inside Base or Compiler and false elsewhere.", source := "base/essentials.jl:188-419; effect macro comments",
    status := .todo, prop := ``BaseEffectMetasMatchAssume },
  { id := "bootcov-ess-checkbounds", juliaFile := "base/essentials.jl",
    juliaFns := ["checkbounds(::Type{Bool}, ::Union{Array,Memory}, ::Int)"],
    statement := "checkbounds(Bool,A,i) is true exactly for 1 ≤ i ≤ length(A), for every Int index.", source := "checkbounds contract; base/essentials.jl:385-388",
    status := .todo, prop := ``CheckboundsBoolCorrect },
  { id := "bootcov-ess-access", juliaFile := "base/essentials.jl",
    juliaFns := ["checkbounds(A,I...)", "default_access_order (4)", "getindex(::GenericMemory,::Int)", "getindex(::GenericMemoryRef)", "getindex(::Array,::Int)", "setindex! (4)", "size(::Array)", "size(::GenericMemory)", "length(::Vector)"],
    statement := "Access methods check bounds, use the documented memory order, and read or write the requested slot.", source := "indexing docstrings; base/essentials.jl:12-14,389-406,1063-1092,1296",
    status := .todo, prop := ``AccessSemantics },
  { id := "bootcov-ess-svec", juliaFile := "base/essentials.jl",
    juliaFns := ["getindex(::SimpleVector,::Int)", "length", "firstindex", "lastindex", "iterate", "eltype", "keys", "isempty", "axes (2)", "==", "map", "getindex(::SimpleVector,::AbstractArray)", "unsafe_convert(::Type{Ptr{Any}},::SimpleVector)"],
    statement := "SimpleVector indexing, iteration, axes, emptiness, equality and mapping agree with its stored elements.", source := "SimpleVector interface; base/essentials.jl:1096-1121",
    status := .todo, prop := ``SvecSemantics },
  { id := "bootcov-svec-isassigned-undef", juliaFile := "base/essentials.jl",
    juliaFns := ["isassigned(::SimpleVector,::Int)"],
    statement := "isassigned(v,i) is true exactly when i is in bounds and its slot is assigned.", source := "isassigned docstring; base/essentials.jl:1123-1153",
    status := .todo, prop := ``SvecIsassignedCorrect },
  { id := "bootcov-ess-unwrap-rewrap", juliaFile := "base/essentials.jl",
    juliaFns := ["unwrap_unionall", "rewrap_unionall", "rewrap_unionall(::TypeofVararg,u)"],
    statement := "unwrap_unionall strips every UnionAll and rewrap restores the enclosing UnionAlls.", source := "invariant; base/essentials.jl:544-571",
    status := .todo, prop := ``UnwrapRewrap },
  { id := "bootcov-ess-rename", juliaFile := "base/essentials.jl",
    juliaFns := ["rename_unionall", "widen_diagonal"],
    statement := "rename_unionall preserves a non-UnionAll type and gives each enclosing UnionAll a fresh variable with the same bounds.", source := "invariant; base/essentials.jl:574-587",
    status := .todo, prop := ``RenameUnionall },
  { id := "bootcov-ess-vararg", juliaFile := "base/essentials.jl",
    juliaFns := ["isvarargtype", "isvatuple", "unwrapva", "unconstrain_vararg_length"],
    statement := "Vararg helpers recognize Vararg types, preserve element types, and drop only the length parameter.", source := "base/essentials.jl:589-613",
    status := .todo, prop := ``VarargHelpers },
  { id := "bootcov-ess-min-ninit", juliaFile := "base/essentials.jl",
    juliaFns := ["datatype_min_ninitialized"],
    statement := "datatype_min_ninitialized returns the minimum number of fields guaranteed initialized by the type.", source := "comment and invariant; base/essentials.jl:615-646",
    status := .todo, prop := ``MinNinitialized },
  { id := "bootcov-ess-has-typevar", juliaFile := "base/essentials.jl",
    juliaFns := ["has_typevar"],
    statement := "has_typevar finds free type variables in types and ignores variables bound by their own UnionAll.", source := "base/essentials.jl:1288; jl_has_typevar interface",
    status := .todo, prop := ``HasTypevarBehaviour },
  { id := "bootcov-ess-tuples", juliaFile := "base/essentials.jl",
    juliaFns := ["argtail", "tail (2)", "_tuple_error", "convert(::Type{T},::NTuple{N,Any})", "cvt1"],
    statement := "tail removes the first tuple element and errors on an empty tuple; tuple conversion preserves length and converts fields.", source := "tail and convert docstrings; base/essentials.jl:523-668",
    status := .todo, prop := ``TupleHelpers },
  { id := "bootcov-ess-throw-boundserror", juliaFile := "base/essentials.jl",
    juliaFns := ["throw_boundserror (3)", "_throw_boundserror_indices (2)"],
    statement := "Every throw_boundserror form raises BoundsError with the given index tuple.", source := "BoundsError contract; base/essentials.jl:15-19",
    status := .todo, prop := ``ThrowBoundserrorForms },
  { id := "bootcov-ess-globalref-eq", juliaFile := "base/essentials.jl",
    juliaFns := ["==(::GlobalRef,::GlobalRef)"],
    statement := "Two GlobalRefs compare equal exactly when their modules and names match.", source := "invariant; base/essentials.jl:23",
    status := .todo, prop := ``GlobalRefEq },
  { id := "bootcov-ess-oftype", juliaFile := "base/essentials.jl",
    juliaFns := ["oftype"],
    statement := "oftype returns y when y has x’s type and otherwise converts y to x’s type.", source := "oftype docstring; base/essentials.jl:700-718",
    status := .todo, prop := ``OftypeSpec },
  { id := "bootcov-ess-signed-unsigned", juliaFile := "base/essentials.jl",
    juliaFns := ["unsigned(::Int)", "signed(::UInt)"],
    statement := "unsigned and signed reinterpret the bit pattern and invert each other.", source := "signed and unsigned conversion contract; base/essentials.jl:720-721",
    status := .todo, prop := ``SignedUnsignedInt },
  { id := "bootcov-ess-resolve-in-world", juliaFile := "base/essentials.jl",
    juliaFns := ["_resolve_in_world"],
    statement := "_resolve_in_world converts the world to UInt and resolves the GlobalRef in that world.", source := "invariant; base/essentials.jl:1672-1673",
    status := .todo, prop := ``ResolveInWorld },
  { id := "bootcov-ess-int-add-sub", juliaFile := "base/essentials.jl",
    juliaFns := ["+(::Int,::Int)", "-(::Int,::Int)"],
    statement := "Bootstrap Int addition and subtraction wrap modulo 2^64.", source := "integer overflow manual; base/essentials.jl:1267-1268",
    status := .todo, prop := ``IntAddSub },
  { id := "bootcov-ess-isempty", juliaFile := "base/essentials.jl",
    juliaFns := ["isempty(itr)"],
    statement := "isempty returns isdone when known, otherwise it checks whether iteration yields nothing.", source := "isempty docstring; base/essentials.jl:1203-1238",
    status := .todo, prop := ``IsemptySpec },
  { id := "bootcov-ess-ismissing", juliaFile := "base/essentials.jl",
    juliaFns := ["ismissing"],
    statement := "ismissing is true exactly for the missing singleton.", source := "ismissing docstring; base/essentials.jl:1525-1542",
    status := .todo, prop := ``IsmissingSpec },
  { id := "bootcov-ess-length-abstract", juliaFile := "base/essentials.jl",
    juliaFns := ["length(::AbstractArray)"],
    statement := "length(AbstractArray) multiplies its dimensions with Int wrapping.", source := "length docstring; base/abstractarray.jl:305-308",
    status := .todo, prop := ``LengthAbstractSpec },
  { id := "bootcov-ess-defaultctors", juliaFile := "base/essentials.jl",
    juliaFns := ["_defaultctors"],
    statement := "Default constructors create the documented outer and inner constructors and convert non-Any fields.", source := "constructor manual; base/essentials.jl:1290-1503",
    status := .todo, prop := ``DefaultctorsSpec },
  { id := "essentials-marker-macros", juliaFile := "base/essentials.jl",
    juliaFns := ["@_gc_preserve_begin", "@_gc_preserve_end", "@nospecialize", "@specialize", "@isdefined", "@_propagate_inbounds_meta", "@_nospecializeinfer_meta", "@eval (2)", "@boundscheck", "@inbounds", "@label (3)", "@goto", "@__LINE__", "@world"],
    statement := "The marker macros expand to the documented syntax and preserve their argument expressions.", source := "macro docstrings; base/essentials.jl:46-50,125-382,488-501,949-1069",
    status := .todo, prop := ``BaseMarkerMacros },
  { id := "essentials-barriers", juliaFile := "base/essentials.jl",
    juliaFns := ["blackbox", "inferencebarrier", "values"],
    statement := "blackbox and inferencebarrier pass their value through the named compiler barrier; values returns its input.", source := "inferencebarrier and values docstrings; base/essentials.jl:9,1211-1263",
    status := .todo, prop := ``Barriers },
  { id := "essentials-conversions", juliaFile := "base/essentials.jl",
    juliaFns := ["convert(::Type{Union{}},...)", "convert(::Type{Type},::Type)", "convert(::Type{String},::String)", "cconvert (3)", "unsafe_convert (5)", "reinterpret", "sizeof"],
    statement := "Identity conversions preserve their argument, cconvert performs or defers conversion as documented, and reinterpret selects the primitive bitcast path.", source := "convert, cconvert and reinterpret docstrings; base/essentials.jl:423-480,723-841",
    status := .todo, prop := ``ConversionSpec },
  { id := "essentials-control", juliaFile := "base/essentials.jl",
    juliaFns := ["ifelse"],
    statement := "ifelse returns the selected value after both arguments have been evaluated.", source := "ifelse docstring; base/essentials.jl:870-894",
    status := .todo, prop := ``IfelseSpec },
  { id := "essentials-bool-not", juliaFile := "base/essentials.jl",
    juliaFns := ["!(::Bool)"],
    statement := "Boolean negation swaps true and false.", source := "! docstring; base/essentials.jl:1260-1294",
    status := .todo, prop := ``NotBool },
  { id := "essentials-iterator-defaults", juliaFile := "base/essentials.jl",
    juliaFns := ["isdone(_, _...)"],
    statement := "The fallback isdone method returns missing.", source := "isdone docstring; base/essentials.jl:1573-1601",
    status := .todo, prop := ``IsdoneDefault },
  { id := "essentials-isiterable", juliaFile := "base/essentials.jl",
    juliaFns := ["isiterable"],
    statement := "isiterable(T) reports whether iterate has a method for T.", source := "isiterable docstring; base/essentials.jl:1612-1620",
    status := .todo, prop := ``IsiterableSpec },
  { id := "essentials-array-access", juliaFile := "base/essentials.jl",
    juliaFns := ["getindex(::Array,::Int)", "setindex!(::Array{Any},...)", "setindex!(::Memory{Any},...)", "setindex!(::MemoryRef{T},...)", "setindex!(::MemoryRef{Any},...)"],
    statement := "Bootstrap array indexing reads the selected slot, stores the requested value, and returns the array.", source := "base/essentials.jl:1063-1092; index and setindex! contracts",
    status := .todo, prop := ``ArrayAccessSpec },
  { id := "essentials-fieldtypes-constrain", juliaFile := "base/essentials.jl",
    juliaFns := ["_fieldtypes_constrain_typevars"],
    statement := "A type parameter is constrained when it occurs in a field or the upper bound of a later constrained type variable.", source := "comment at base/essentials.jl:1290-1329",
    status := .todo, prop := ``FieldtypesConstrainSpec },
  { id := "essentials-defaultctor-typeinfo", juliaFile := "base/essentials.jl",
    juliaFns := ["_defaultctor_typeinfo"],
    statement := "_defaultctor_typeinfo returns the DataType, outer-to-inner UnionAll variables, and field types.", source := "comment at base/essentials.jl:1331-1350",
    status := .todo, prop := ``TypeinfoSpec },
  { id := "essentials-pairs-colon-val", juliaFile := "base/essentials.jl",
    juliaFns := ["Pairs{K,V,I,A}", "Pairs{K,V}", "Pairs{K}", "Pairs", "pairs(::Type{NamedTuple})", "Colon()", "show(::IO,::Colon)", "Val{x}()", "Val(x)"],
    statement := "Pairs constructors retain their declared type parameters, Colon prints as Colon(), and Val(x) creates a Val{x} value.", source := "base/essentials.jl:502-513,1160-1203",
    status := .todo, prop := ``PairsAndColonVal }
]

end JuliaLean.Proofs.base.essentials
