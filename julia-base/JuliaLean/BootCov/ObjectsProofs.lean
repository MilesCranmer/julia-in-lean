import JuliaLean.BootCov.Objects

/-!
Properties of the Core struct constructors (`base/boot.jl`).
-/

namespace JuliaLean.BootCov.Objects

open JuliaLean
open JuliaLean.BootCov

/-- Exception constructors store their arguments in field order, leave omitted
fields undefined, and fill the documented defaults: `DomainError(val).msg == ""`,
`AssertionError().msg == ""`, `MethodError(f, args).world == typemax(UInt)`,
`TypeError(where, T, got)` has `func == Symbol(where)` and `context == ""`, and
`UndefVarError(var)` records the current world age with `scope` undefined. -/
def ExceptionFields : Prop :=
  (∀ m, getfieldObj (errorException m) 1 = .ok (.str m)) ∧
  (isdefinedObj boundsError0 1 = false ∧ isdefinedObj boundsError0 2 = false) ∧
  (∀ a, getfieldObj (boundsError1 a) 1 = .ok a ∧ isdefinedObj (boundsError1 a) 2 = false) ∧
  (∀ a i, getfieldObj (boundsError2 a i) 1 = .ok a ∧ getfieldObj (boundsError2 a i) 2 = .ok i) ∧
  (∀ n k, isdefinedObj (fieldless n) k = false) ∧
  (∀ w v, getfieldObj (undefVarError1 w v) 1 = .ok (.sym v) ∧
    getfieldObj (undefVarError1 w v) 2 = .ok (.int w) ∧ isdefinedObj (undefVarError1 w v) 3 = false) ∧
  (∀ w v s, getfieldObj (undefVarError2 w v s) 3 = .ok s) ∧
  (∀ m, getfieldObj (concurrencyViolationError m) 1 = .ok (.str m)) ∧
  (∀ mi, getfieldObj (missingCodeError mi) 1 = .ok mi) ∧
  (∀ v, getfieldObj (domainError1 v) 1 = .ok v ∧ getfieldObj (domainError1 v) 2 = .ok (.str "")) ∧
  (∀ v m, domainError2 v (.str m) = .ok (.obj "DomainError" [some v, some (.str m)])) ∧
  (∀ v m, (∀ s, m ≠ .str s) → domainError2 v m = .error (.method "convert")) ∧
  (∀ f c e g, typeError4 (.sym f) (.sym c) e g =
    .ok (.obj "TypeError" [some (.sym f), some (.sym c), some e, some g])) ∧
  (∀ str w e g, typeError3 str w e g =
    .ok (.obj "TypeError" [some (symbolOf str w), some (.str ""), some e, some g])) ∧
  (∀ f as, getfieldObj (inexactError f as) 2 = .ok (.tuple as)) ∧
  (∀ m, getfieldObj (overflowError m) 1 = .ok (.str m) ∧ getfieldObj (argumentError m) 1 = .ok (.str m)) ∧
  (∀ v, getfieldObj (undefKeywordError v) 1 = .ok (.sym v)) ∧
  (∀ f a w, getfieldObj (methodError3 f a w) 3 = .ok (.int w)) ∧
  (∀ f a, getfieldObj (methodError2 f a) 3 = .ok (.int (2 ^ 64 - 1))) ∧
  (∀ m, getfieldObj (assertionError1 m) 1 = .ok (.str m)) ∧
  getfieldObj assertionError0 1 = .ok (.str "") ∧
  (∀ t f, getfieldObj (fieldError t f) 2 = .ok (.sym f)) ∧
  (∀ f l e, getfieldObj (loadError f l e) 2 = .ok (.int l) ∧ getfieldObj (loadError f l e) 3 = .ok e) ∧
  (∀ m e, getfieldObj (initError m e) 1 = .ok (.sym m) ∧ getfieldObj (initError m e) 2 = .ok e) ∧
  (∀ a d, getfieldObj (abiOverride a d) 2 = .ok d) ∧
  (∀ a, getfieldObj (typeNameError a) 1 = .ok a)

theorem exceptionFields : ExceptionFields := by
  refine ⟨fun _ => rfl, ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, ?_,
    fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, ?_, fun _ _ _ _ => rfl, ?_,
    fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun _ _ => rfl, fun _ => rfl⟩
  · intro n k
    simp [isdefinedObj, fieldless]
  · intro v m h
    cases m <;> simp_all [domainError2, toAbstractString, bind, Except.bind]
  · intro str w e g
    cases w <;> rfl

/-- Wrapper and lattice-element constructors store their arguments; `Box()` and
`ReturnNode()`/`UpsilonNode()` leave their single field undefined; `WeakRef()` refers to
`nothing`; `VecElement(x)` is `VecElement{typeof(x)}(x)`; and `Pair(a, b)` stores both
arguments. -/
def WrapperFields : Prop :=
  (∀ s, stringOfString s = s) ∧ nothingCtor = .nothing ∧ emptyTuple = .tuple [] ∧
  (∀ m, getfieldObj (evalInto m) 1 = .ok (.module_ m)) ∧
  (∀ x, getfieldObj (box1 x) 1 = .ok x) ∧ getfieldObj box0 1 = .error .undefRef ∧
  (∀ v, getfieldObj (weakRef1 v) 1 = .ok v) ∧ getfieldObj weakRef0 1 = .ok .nothing ∧
  (∀ x, vecElement x = vecElementT x ∧ getfieldObj (vecElementT x) 1 = .ok x) ∧
  (∀ v, getfieldObj (const_ v) 1 = .ok v) ∧
  (∀ t u f, getfieldObj (partialStruct t u f) 3 = .ok f) ∧
  (∀ s a b, getfieldObj (interConditional s a b) 1 = .ok (.int s) ∧
    getfieldObj (interConditional s a b) 3 = .ok b) ∧
  (∀ s v i f, getfieldObj (interMustAlias s v i f) 3 = .ok (.int i)) ∧
  (∀ t e p s, getfieldObj (partialOpaque t e p s) 4 = .ok s) ∧
  (∀ f, getfieldObj (partialTask f) 1 = .ok f) ∧
  (∀ g a s, getfieldObj (generatedFunctionStub g a s) 1 = .ok g) ∧
  (∀ l v, getfieldObj (macroSource l v) 2 = .ok v) ∧
  (∀ a b, getfieldObj (pair a b) 1 = .ok a ∧ getfieldObj (pair a b) 2 = .ok b)

theorem wrapperFields : WrapperFields := by
  refine ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩

/-- IR node constructors store their arguments; `ReturnNode()`, `UpsilonNode()` and
`EnterNode(dest)` leave the optional field undefined; `LineNumberNode(l)` and
`DebugInfo(def)` fill `nothing`/`svec()`/`""`; `LineNumberNode(l, f)` turns a `String`
file into a `Symbol`, keeps `nothing` or a `Symbol`, and throws `TypeError` otherwise;
and `EnterNode(old, d)` retargets to `d`, keeping `old.scope` exactly when it is defined. -/
def IRNodeFields : Prop :=
  (∀ l, getfieldObj (gotoNode l) 1 = .ok (.int l)) ∧
  (∀ s, getfieldObj (newvarNode s) 1 = .ok s) ∧
  (∀ v, quoteNode v = .quoteNode v) ∧
  (∀ i, getfieldObj (ssaValue i) 1 = .ok (.int i) ∧ getfieldObj (argument i) 1 = .ok (.int i) ∧
    getfieldObj (slotNumber i) 1 = .ok (.int i)) ∧
  (∀ v, getfieldObj (returnNode1 v) 1 = .ok v) ∧ isdefinedObj returnNode0 1 = false ∧
  (∀ c d, getfieldObj (gotoIfNot c d) 2 = .ok (.int d)) ∧
  (∀ d, isdefinedObj (enterNode1 d) 2 = false) ∧
  (∀ d s, getfieldObj (enterNode2 d s) 2 = .ok s) ∧
  (∀ l, lineNumberNode1 l = .lineNode l .nothing) ∧
  (∀ l s, lineNumberNode2 l (.str s) = .ok (.lineNode l (.sym s)) ∧
    lineNumberNode2 l (.sym s) = .ok (.lineNode l (.sym s))) ∧
  (∀ l, lineNumberNode2 l .nothing = .ok (.lineNode l .nothing)) ∧
  (∀ l n, lineNumberNode2 l (.int n) = .error (.typeError "new")) ∧
  (∀ d, debugInfo1 d = debugInfo4 d .nothing (.tuple []) (.str "")) ∧
  (∀ d a b c, getfieldObj (debugInfo4 d a b c) 4 = .ok c) ∧
  (∀ e v, getfieldObj (phiNode e v) 2 = .ok v) ∧
  (∀ v t, getfieldObj (piNode v t) 2 = .ok t) ∧
  (∀ v, getfieldObj (phiCNode v) 1 = .ok v) ∧
  (∀ v, getfieldObj (upsilonNode1 v) 1 = .ok v) ∧ isdefinedObj upsilonNode0 1 = false ∧
  (∀ s p m b, getfieldObj (methodMatch s p m b) 4 = .ok (.bool b)) ∧
  (∀ m me f l i, getfieldObj (lineInfoNode m me f l i) 4 = .ok (.int l)) ∧
  (∀ d d' s, enterNodeRetarget (enterNode2 d s) d' = .ok (enterNode2 d' s)) ∧
  (∀ d d', enterNodeRetarget (enterNode1 d) d' = .ok (enterNode1 d'))

theorem irNodeFields : IRNodeFields := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- The `NamedTuple` constructors (`base/boot.jl:1022-1030`) pair the names with the
arguments in order; `NamedTuple{names}(args)` throws exactly when the counts differ, and
`NamedTuple()` is empty. -/
def NamedTupleCtors : Prop :=
  (∀ names args, names.length = args.length → namedTupleNames names args = .ok (names.zip args)) ∧
  (∀ names args, names.length ≠ args.length → ∃ m, namedTupleNames names args = .error (.error m)) ∧
  (∀ names args (h : names.length = args.length), namedTupleNT names args h = names.zip args) ∧
  namedTupleEmpty = []

theorem namedTupleCtors : NamedTupleCtors := by
  refine ⟨?_, ?_, fun _ _ _ => rfl, rfl⟩
  · intro names args h; simp [namedTupleNames, h]
  · intro names args h
    exact ⟨"NamedTuple names and field types must have matching lengths", by simp [namedTupleNames, h]⟩

/-- The handle constructors pass their arguments to the runtime in order:
`GlobalRef(m, s)` refers to binding `s` of `m`; `Module()` defaults to the name
`:anonymous` with standard imports and default names; `CodeInstance`, `getptls`,
`include`, `eval` and calling an `EvalInto` return what the runtime call returns. -/
def HandleCtors : Prop :=
  (∀ m s, globalRef m s = .globalRef m s) ∧
  moduleCtor = ⟨"anonymous", true, true⟩ ∧
  (∀ n a b, moduleCtor n a b = ⟨n, a, b⟩) ∧
  (∀ (f : List JVal → JVal) as, codeInstance f as = f as) ∧
  (∀ p, getptls p = p) ∧
  (∀ (ld : String → String → R JVal) m f, include_ ld m f = ld m f) ∧
  (∀ (ev : String → JVal → R JVal) m e, eval_ ev m e = ev m e ∧
    evalIntoCall ev (evalInto m) e = ev m e)

theorem handleCtors : HandleCtors :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => ⟨rfl, rfl⟩⟩

end JuliaLean.BootCov.Objects
