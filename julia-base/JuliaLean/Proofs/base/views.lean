import JuliaLean.base.views
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.views

open JuliaLean.base.views JuliaLean.Registry


theorem bindSerial {α β : Type} (action : ViewResult α)
    (next : α → ViewResult β) (serial : Nat) :
    (action >>= next) serial =
      match action serial with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (value, after)) => next value after := by
  simp only [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.mk, Option.bind]
  cases action serial with
  | none => rfl
  | some outcome => cases outcome <;> rfl

@[simp] theorem runBindThrow {α β : Type} (error : ViewError) (next : α → ViewResult β) (serial : Nat) :
    ((throw error : ViewResult α) >>= next) serial = some (.error error) := rfl

@[simp] theorem runBindPure {α β : Type} (value : α) (next : α → ViewResult β) (serial : Nat) :
    ((pure value : ViewResult α) >>= next) serial = next value serial := rfl

@[simp] theorem runMapThrow {α β : Type} (error : ViewError) (f : α → β) (serial : Nat) :
    ((f <$> (throw error : ViewResult α)) serial) = some (.error error) := rfl

@[simp] theorem runMapPure {α β : Type} (value : α) (f : α → β) (serial : Nat) :
    ((f <$> (pure value : ViewResult α)) serial) = some (.ok (f value, serial)) := rfl

@[simp] theorem runBindFresh {Module : Type} {α : Type} (hooks : ReplaceHooks Module) (tag : String)
    (next : ViewSyntax → ViewResult α) (serial : Nat) :
    ((freshSyntax hooks tag) >>= next) serial =
      next (.generated tag serial) (serial + 1) := rfl

@[simp] theorem runFresh {Module : Type} (hooks : ReplaceHooks Module)
    (tag : String) (serial : Nat) :
    freshSyntax hooks tag serial =
      some (.ok (.generated tag serial, serial + 1)) := rfl

@[simp] theorem viewsSymbol (hooks : ViewsHooks) (name : String) :
    viewsAny hooks (.symbol name) = pure (.symbol name) := by
  rw [viewsAny.eq_def]
  rfl

@[simp] theorem viewsGenerated (hooks : ViewsHooks) (tag : String) (serial : Nat) :
    viewsAny hooks (.generated tag serial) = pure (.generated tag serial) := by
  rw [viewsAny.eq_def]
  rfl

@[simp] theorem viewsInteger (hooks : ViewsHooks) (value : Nat) :
    viewsAny hooks (.integer value) = pure (.integer value) := by
  rw [viewsAny.eq_def]
  rfl

@[simp] theorem viewsGlobal (hooks : ViewsHooks) (name : String) :
    viewsAny hooks (.global name) = pure (.global name) := by
  rw [viewsAny.eq_def]
  rfl

@[simp] theorem viewsOpaque (hooks : ViewsHooks) (name : String) :
    viewsAny hooks (.opaque name) = pure (.opaque name) := by
  rw [viewsAny.eq_def]
  rfl

theorem successfulBind {α β : Type} (action : ViewResult α)
    (next : α → ViewResult β) (serial final : Nat) (result : β)
    (h : (action >>= next) serial = some (.ok (result, final))) :
    ∃ value after, action serial = some (.ok (value, after)) ∧
      next value after = some (.ok (result, final)) := by
  rw [bindSerial] at h
  cases ha : action serial with
  | none => simp only [ha, reduceCtorEq] at h
  | some outcome =>
    cases outcome with
    | error error =>
      simp only [ha] at h
      have impossible := Option.some.inj h
      cases impossible
    | ok pair =>
      obtain ⟨value, after⟩ := pair
      refine ⟨value, after, ?_, ?_⟩
      · first | rfl | exact ha
      · simpa only [ha] using h

theorem mapSerial {α β : Type} (f : α → β) (action : ViewResult α) (serial : Nat) :
    (f <$> action) serial =
      match action serial with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (value, after)) => some (.ok (f value, after)) := by
  simp only [Functor.map, StateT.map, ExceptT.map, ExceptT.mk, Option.map]
  cases action serial with
  | none => rfl
  | some outcome => cases outcome <;> rfl

@[simp] theorem runGet (serial : Nat) :
    (get : ViewResult Nat) serial = some (.ok (serial, serial)) := rfl

@[simp] theorem runSet (next serial : Nat) :
    (set next : ViewResult Unit) serial = some (.ok ((), next)) := rfl

attribute [local simp] bindSerial mapSerial ExceptT.mk syntaxArg
  List.mapM_cons List.mapM_nil



@[simp] theorem runPure {α : Type} (value : α) (serial : Nat) :
    (pure value : ViewResult α) serial = some (.ok (value, serial)) := rfl

@[simp] theorem runThrow {α : Type} (error : ViewError) (serial : Nat) :
    (throw error : ViewResult α) serial = some (.error error) := rfl



/-- Separate Core.gensym allocations have distinct identities, disjoint from source spellings. -/
def FreshNameSupply : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) p q m n first second afterFirst afterSecond,
    freshSyntax hooks p m = some (.ok (first, afterFirst)) →
    freshSyntax hooks q n = some (.ok (second, afterSecond)) →
    (m ≠ n → first ≠ second) ∧ (∀ user, first ≠ ViewSyntax.symbol user) ∧
      afterFirst = m + 1 ∧ afterSecond = n + 1

/-- A boundary inside a reference uses that reference, never its surrounding endpoints. -/
def NestedBoundaryScope : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (moduleValue : Module)
    (name : String) (outerFirst outerLast : ViewSyntax) (serial : Nat),
    name ≠ "begin" → name ≠ "end" →
    let array := ViewSyntax.symbol name
    let temporary := ViewSyntax.generated "S" serial
    replace_ref_begin_end_! hooks
      { owner := moduleValue, withex := some (outerFirst, outerLast),
        inQuoteContext := false, escapeDepth := 0 }
      (.expr "ref" [array, .symbol "end"]) serial =
      some (.ok ((.expr "block"
        [.expr "local" [.expr "=" [temporary, array]],
         .expr "ref" [temporary, lastIndexExpr temporary]], false), serial + 1))

/-- A one-index reference uses its own axis endpoints. Boundary symbols cannot name the array. -/
def BeginEndUseReferenceAxes : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (moduleValue : Module) (arrayName : String) (serial : Nat),
    let array := ViewSyntax.symbol arrayName
    let temporary := ViewSyntax.generated "S" serial
    let invalid := if arrayName = "begin" then some (ViewError.errorException "Invalid use of begin outside []")
      else if arrayName = "end" then some (.errorException "Invalid use of end outside []") else none
    (replace_ref_begin_end! hooks moduleValue (.expr "ref" [array, .symbol "begin"]) serial =
      match invalid with
      | some error => some (.error error)
      | none => some (.ok (.expr "block"
          [.expr "local" [.expr "=" [temporary, array]],
           .expr "ref" [temporary, firstIndexExpr temporary]], serial + 1))) ∧
    (replace_ref_begin_end! hooks moduleValue (.expr "ref" [array, .symbol "end"]) serial =
      match invalid with
      | some error => some (.error error)
      | none => some (.ok (.expr "block"
          [.expr "local" [.expr "=" [temporary, array]],
           .expr "ref" [temporary, lastIndexExpr temporary]], serial + 1))) ∧
    replace_ref_begin_end! hooks moduleValue (.symbol "begin") serial =
      some (.error (.errorException "Invalid use of begin outside []")) ∧
    replace_ref_begin_end! hooks moduleValue (.symbol "end") serial =
      some (.error (.errorException "Invalid use of end outside []"))

/-- `@view` rejects non-reference syntax; indexing a normal name becomes a view call. -/
def ViewMacroContract : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (moduleValue : Module),
    (∀ (expression : ViewSyntax) serial, isExpr expression "ref" = false →
      viewMacro hooks moduleValue expression serial =
        some (.error (.argumentError "Invalid use of @view macro: argument must be a reference expression A[...]."))) ∧
    (∀ (name : String) (index serial : Nat),
      viewMacro hooks moduleValue (.expr "ref" [.symbol name, .integer index]) serial =
        if name = "begin" then some (.error (.errorException "Invalid use of begin outside []"))
        else if name = "end" then some (.error (.errorException "Invalid use of end outside []"))
        else some (.ok (.expr "escape"
          [.expr "call" [.global "Base.view", .symbol name, .integer index]], serial + 1)))

namespace Heap
open JuliaLean JuliaLean.base.array

@[simp] theorem runGet {α : Type} (heap : VectorHeap α) :
    (get : VectorM α (VectorHeap α)) heap = .ok (heap, heap) := rfl
@[simp] theorem runPure {α β : Type} (value : β) (heap : VectorHeap α) :
    (pure value : VectorM α β) heap = .ok (value, heap) := rfl
@[simp] theorem runThrow {α β : Type} (error : Error) (heap : VectorHeap α) :
    (throw error : VectorM α β) heap = .error error := rfl
@[simp] theorem runModify {α : Type} (f : VectorHeap α → VectorHeap α) (heap : VectorHeap α) :
    (modify f : VectorM α Unit) heap = .ok ((), f heap) := rfl
@[simp] theorem runLift {α β : Type} (action : Except Error β) (heap : VectorHeap α) :
    (liftM action : VectorM α β) heap = action.map (fun value => (value, heap)) := by
  cases action <;> rfl
@[simp] theorem runBind {α β γ : Type} (action : VectorM α β)
    (next : β → VectorM α γ) (heap : VectorHeap α) :
    (action >>= next) heap =
      match action heap with
      | .error error => .error error
      | .ok (value, after) => next value after := by
  simp only [Bind.bind, StateT.bind, Except.bind]
  cases action heap <;> rfl

theorem writeVisible {α : Type} (heap after : VectorHeap α) (handle : Nat)
    (i : I) (value : α)
    (h : heapSet handle value i heap = .ok ((), after)) :
    heapGet handle i after = .ok (value, after) := by
  cases hs : heap[handle]? with
  | none => simp [heapSet, heapSlots, hs] at h
  | some slots =>
    by_cases hb : 1 ≤ i.val ∧ i.val ≤ slots.length
    · have hi : i.val.toNat - 1 < slots.length := by omega
      have hslot : slots[i.val.toNat - 1]? = some slots[i.val.toNat - 1] :=
        List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      have hh : handle < heap.length := List.getElem?_eq_some_iff.mp hs |>.1
      simp [heapSet, heapSlots, vectorGet, hs, hb, hslot, Except.map] at h
      cases h
      simp [heapGet, heapSlots, vectorGet, hb, hi, hh, Except.map]
    · simp [heapSet, heapSlots, vectorGet, hs, hb, Except.map] at h
end Heap

theorem heapViewParent {Tag T : Type} (ops : HeapViewOps Tag)
    (array : JuliaLean.base.array.HeapArray Tag) (indices : List JuliaLean.base.subarray.Index)
    (view : JuliaLean.base.subarray.SubArray (JuliaLean.base.array.HeapArray Tag) T)
    (h : heapView ops array indices = .ok view) : view.parent = array := by
  unfold heapView JuliaLean.base.subarray.viewArray at h
  cases hb : ops.checkBounds array ((ops.normalize array indices).map (ops.unalias array)) with
  | error error => simp [hb, Bind.bind, Except.bind] at h
  | ok unit =>
    simp [hb, Except.bind, JuliaLean.base.subarray.maybeReshapeParentSameRank,
      JuliaLean.base.subarray.unsafeViewArray, JuliaLean.base.subarray.subarrayCartesian,
      JuliaLean.base.subarray.subarrayInner, JuliaLean.base.subarray.checkParentIndexMatchArray] at h
    cases h
    rfl

def MaybeViewHeapAliases : Prop :=
  ∀ {Tag T : Type} (ops : HeapViewOps Tag) (array : JuliaLean.base.array.HeapArray Tag)
    (indices : List JuliaLean.base.subarray.Index)
    (view : JuliaLean.base.subarray.SubArray (JuliaLean.base.array.HeapArray Tag) T),
    maybeviewArray (heapView ops) array indices = .ok view →
    view.parent.handle = array.handle ∧
      ∀ (heap after : JuliaLean.base.array.VectorHeap T)
        (mappedIndex : JuliaLean.base.array.I) (value : T),
        JuliaLean.base.array.heapSet view.parent.handle value mappedIndex heap = .ok ((), after) →
        JuliaLean.base.array.heapGet array.handle mappedIndex after = .ok (value, after)

def MaybeViewBehavior : Prop :=
  (∀ {A Args R E : Type} (getindex : A → Args → Except E R) (array : A) (args : Args),
    maybeviewGeneric getindex array args = getindex array args) ∧
  (∀ {A N C R E : Type} [AbstractArrayType A] [NumberType N] [AbstractCartesianIndexType C]
    (getindex : A → List (ScalarViewIndex N C) → Except E R) (array : A)
    (args : List (ScalarViewIndex N C)),
    maybeviewArrayScalarIndices getindex array args = getindex array args) ∧
  (∀ {A R E : Type} (getindex : A → Except E R) (array : A),
    maybeviewGenericZero getindex array = getindex array) ∧
  (∀ {A R E : Type} [AbstractArrayType A] (getindex : A → Except E R) (array : A),
    maybeviewArrayZero getindex array = getindex array) ∧
  MaybeViewHeapAliases

theorem MaybeViewBehavior_proven : MaybeViewBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro Tag T ops array indices view hview
    have hparent := heapViewParent ops array indices view hview
    refine ⟨congrArg JuliaLean.base.array.HeapArray.handle hparent, ?_⟩
    intro heap after mappedIndex value hwrite
    rw [hparent] at hwrite
    exact Heap.writeVisible heap after array.handle mappedIndex value hwrite

/-- The external `exprarray` helper constructs the supplied head and arguments. -/
def ExprarrayLaw (hooks : ViewsHooks) : Prop :=
  ∀ head args, hooks.exprarray head args = .expr head args

/-- Extract initializers by their binding positions, preserving repetitions in user code. -/
def bindingInitializer : ViewSyntax → Option ViewSyntax
  | .expr "=" [_, value] => some value
  | .expr "local" [.expr "=" [_, value]] => some value
  | _ => none

def bindingTarget : ViewSyntax → Option ViewSyntax
  | .expr "=" [target, _] => some target
  | .expr "local" [.expr "=" [target, _]] => some target
  | _ => none

/-- Expr values are AST nodes according to Base.isa_ast_node. -/
def AstExprLaw {Module : Type} (hooks : ReplaceHooks Module) : Prop :=
  ∀ head args, hooks.isAstNode (.expr head args) = true

def AstSymbolLaw {Module : Type} (hooks : ReplaceHooks Module) : Prop :=
  ∀ name, hooks.isAstNode (.symbol name) = true

/-- An index's own boundaries never escape as a use of the enclosing reference. -/
def ReferenceBoundaryIsolation : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (context : ReplaceCtx Module)
    (head : String) (array : ViewSyntax) (indices : List ViewSyntax)
    (main : ViewSyntax) (path : List Nat) (serial : Nat)
    (result : ViewSyntax) (used : Bool) (final : Nat),
    handle_refexpr! hooks context (.expr head (array :: indices)) main path serial =
      some (.ok ((result, used), final)) →
    ∃ rewrittenArray usedArray afterArray,
      replace_ref_begin_end_! hooks context array serial =
        some (.ok ((rewrittenArray, usedArray), afterArray)) ∧ used = usedArray

/--
Cache initializers preserve the source positions, including repeated equal
expressions. The reference target subsequently uses the allocated temporaries.
Own-index boundaries do not mark the enclosing reference as used.
-/
def ReferenceEvaluationPreserved : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (moduleValue : Module),
    AstExprLaw hooks → ∀ (array index : ViewSyntax) (serial : Nat),
      let context : ReplaceCtx Module :=
        { owner := moduleValue, withex := none, inQuoteContext := false, escapeDepth := 0 }
      let indexed := ViewSyntax.expr "ref" [array, .symbol "begin", .expr "..." [index]]
      let actual := handle_refexpr! hooks context indexed indexed [] serial
      match replace_ref_begin_end_! hooks context array serial with
      | none => actual = none
      | some (.error error) => actual = some (.error error)
      | some (.ok ((rewrittenArray, usedArray), afterArray)) =>
        let arrayTemp := ViewSyntax.generated "S" afterArray
        let firstTemp := ViewSyntax.generated "arg" (afterArray + 1)
        let first := firstIndexExpr arrayTemp (some (.integer 1))
        let boundaries :=
          (firstIndexExpr arrayTemp (some (.integer 2)), lastIndexExpr arrayTemp (some (.integer 2)))
        match replace_ref_begin_end_! hooks
            { context with withex := some boundaries } index (afterArray + 2) with
        | none => actual = none
        | some (.error error) => actual = some (.error error)
        | some (.ok ((rewrittenIndex, _), afterIndex)) =>
          let indexTemp := ViewSyntax.generated "arg" afterIndex
          let cached := hooks.isAstNode rewrittenIndex
          let stored := ViewSyntax.expr "..." [if cached then indexTemp else rewrittenIndex]
          match actual with
          | some (.ok ((.expr "block" children, used), final)) =>
            used = usedArray ∧
            final = (if cached then afterIndex + 1 else afterIndex) ∧
            children.dropLast.map bindingInitializer =
              [some rewrittenArray, some first] ++ (if cached then [some rewrittenIndex] else []) ∧
            children.dropLast.map bindingTarget =
              [some arrayTemp, some firstTemp] ++ (if cached then [some indexTemp] else []) ∧
            children.getLast? = some (.expr "ref"
              [arrayTemp, firstTemp, stored])
          | _ => False

def ReferenceHandlerContract : Prop :=
  ReferenceBoundaryIsolation ∧ ReferenceEvaluationPreserved

/-- Generated cache names are distinct and cannot capture existing source names. -/
def CachedTemporaryHygiene : Prop :=
  ∀ {Module : Type} (hooks : ReplaceHooks Module) (moduleValue : Module) (users : List String),
    AstExprLaw hooks → AstSymbolLaw hooks →
    ∀ arrayName indexName serial result used final,
      let context : ReplaceCtx Module :=
        { owner := moduleValue, withex := none, inQuoteContext := false, escapeDepth := 0 }
      let indexed := ViewSyntax.expr "ref" [.symbol arrayName, .symbol "begin", .expr "..." [.symbol indexName]]
      handle_refexpr! hooks context indexed indexed [] serial =
        some (.ok ((result, used), final)) →
      match result with
      | .expr "block" children =>
        let names := children.dropLast.filterMap bindingTarget
        names.length = 3 ∧ List.Pairwise (· ≠ ·) names ∧
          ∀ user ∈ users, ViewSyntax.symbol user ∉ names
      | _ => False

def TemporaryHygiene : Prop := FreshNameSupply ∧ CachedTemporaryHygiene

/-- Each successful rewrite preserves its operands in their source positions. -/
def ViewsReadAssignmentContract : Prop :=
  ∀ (hooks : ViewsHooks), ExprarrayLaw hooks →
    (∀ args serial result final,
      viewsExpr hooks "ref" args serial = some (.ok (result, final)) →
      ∃ rewritten, args.mapM (viewsAny hooks) serial = some (.ok (rewritten, final)) ∧
        result = syntaxCall (.global "Base.maybeview") rewritten) ∧
    (∀ args rhs serial result final,
      viewsExpr hooks "=" [.expr "ref" args, rhs] serial = some (.ok (result, final)) →
      ∃ rewritten rewrittenRhs after,
        args.mapM (viewsAny hooks) serial = some (.ok (rewritten, after)) ∧
        viewsAny hooks rhs after = some (.ok (rewrittenRhs, final)) ∧
        result = .expr "=" [.expr "ref" rewritten, rewrittenRhs]) ∧
    (∀ args serial result final,
      viewsExpr hooks "call" (.global "Base.getindex" :: args) serial = some (.ok (result, final)) →
      ∃ rewritten, args.mapM (viewsAny hooks) serial = some (.ok (rewritten, final)) ∧
        result = .expr "call" (.global "Base.getindex" :: rewritten)) ∧
    (∀ head args serial result final, head ≠ "=" → head ≠ ".=" → head ≠ "ref" →
      (endsInEquals head = false ∨ !isExpr (args.headD (.opaque "missing-left-hand-side")) "ref") →
      viewsExpr hooks head args serial = some (.ok (result, final)) →
      ∃ rewritten, args.mapM (viewsAny hooks) serial = some (.ok (rewritten, final)) ∧
        result = .expr head rewritten)

def IndexedOperatorCache : Prop :=
  ∀ (hooks : ViewsHooks) (head : String) (array : ViewSyntax)
    (indices rhs : List ViewSyntax) serial result final,
    head ≠ "=" → head ≠ ".=" → head ≠ "ref" → head ≠ "" →
    endsInEquals head = true →
    viewsExpr hooks head (.expr "ref" (array :: indices) :: rhs) serial =
      some (.ok (result, final)) →
    ∃ (cached : List ViewSyntax) (bindings escapedRhs : List ViewSyntax),
      cached.length = indices.length ∧
      bindings.length = indices.length + 1 ∧
      escapedRhs.length = rhs.length ∧
      result = .expr "hygienic-scope"
        [.expr "let" [.expr "block" bindings,
          .expr (if startsInDot head then ".=" else "=")
            [.expr "ref" (.symbol "a" :: cached),
             syntaxCall (escapeSyntax (.symbol (dropLastChar head)))
               (syntaxCall (.global "Base.maybeview") (.symbol "a" :: cached) :: escapedRhs)]],
         .global "Base"]

/-- Cache slots, rather than occurrences anywhere in the RHS, record target evaluations. -/
def SingleOperatorAssignmentCache : Prop :=
  ∀ (hooks : ViewsHooks), ExprarrayLaw hooks → ∀ arrayName indexName rhs serial,
    match viewsAny hooks rhs serial with
    | none => viewsExpr hooks "+=" [.expr "ref" [.symbol arrayName, .symbol indexName], rhs] serial = none
    | some (.error error) =>
        viewsExpr hooks "+=" [.expr "ref" [.symbol arrayName, .symbol indexName], rhs] serial = some (.error error)
    | some (.ok (rewrittenRhs, final)) =>
      match viewsExpr hooks "+=" [.expr "ref" [.symbol arrayName, .symbol indexName], rhs] serial with
      | some (.ok (.expr "hygienic-scope"
          [.expr "let" [.expr "block" bindings, .expr "=" [target, operation]], .global "Base"], final')) =>
          final' = final ∧
          bindings.map bindingInitializer =
            [some (escapeSyntax (.symbol arrayName)), some (escapeSyntax (.symbol indexName))] ∧
          bindings.map bindingTarget = [some (.symbol "a"), some (.symbol "i1")] ∧
          target = .expr "ref" [.symbol "a", .symbol "i1"] ∧
          operation = syntaxCall (escapeSyntax (.symbol "+"))
            [syntaxCall (.global "Base.maybeview") [.symbol "a", .symbol "i1"], escapeSyntax rewrittenRhs]
      | _ => False

def OperatorAssignmentCacheContract : Prop :=
  IndexedOperatorCache ∧ SingleOperatorAssignmentCache

/-- Boundary expansion precedes view rewriting, including invalid array-position boundaries. -/
def ViewsMacroBoundaryContract : Prop :=
  ∀ {Module : Type} (replaceHooks : ReplaceHooks Module) (rewriteHooks : ViewsHooks),
    ExprarrayLaw rewriteHooks → ∀ (moduleValue : Module) (arrayName : String) (serial : Nat),
      let array := ViewSyntax.symbol arrayName
      let temporary := ViewSyntax.generated "S" serial
      viewsMacro replaceHooks rewriteHooks moduleValue (.expr "ref" [array, .symbol "begin"]) serial =
        if arrayName = "begin" then some (.error (.errorException "Invalid use of begin outside []"))
        else if arrayName = "end" then some (.error (.errorException "Invalid use of end outside []"))
        else some (.ok (.expr "escape"
          [.expr "block"
            [.expr "local" [.expr "=" [temporary, array]],
             .expr "call" [.global "Base.maybeview", temporary, firstIndexExpr temporary]]], serial + 1))

@[simp] theorem zeroDimension : isZeroDimension (.integer 0) = true := rfl

@[simp] theorem replaceSymbol {Module : Type} (hooks : ReplaceHooks Module)
    (ctx : ReplaceCtx Module) (name : String) :
    replace_ref_begin_end_! hooks ctx (.symbol name) =
      boundaryOutcome ctx.inQuoteContext ctx.withex ctx.escapeDepth name (.symbol name)
        (.errorException "Invalid use of begin outside []")
        (.errorException "Invalid use of end outside []") := by
  rw [replace_ref_begin_end_!.eq_def]
  simp [isExpr, dispatchExpanded.eq_def]

@[simp] theorem replaceSplat {Module : Type} (hooks : ReplaceHooks Module)
    (owner : Module) (bounds : Option (ViewSyntax × ViewSyntax)) (index : ViewSyntax) :
    replace_ref_begin_end_! hooks
      { owner := owner, withex := bounds, inQuoteContext := false, escapeDepth := 0 }
      (.expr "..." [index]) =
      (do
        let (rewritten, used) ← replace_ref_begin_end_! hooks
          { owner := owner, withex := bounds, inQuoteContext := false, escapeDepth := 0 } index
        pure (.expr "..." [rewritten], used)) := by
  rw [replace_ref_begin_end_!.eq_def]
  simp [isExpr, dispatchExpanded.eq_def, endsInEquals, replaceArgs.eq_def]

theorem BeginEndUseReferenceAxes_proven : BeginEndUseReferenceAxes := by
  intro Module hooks moduleValue arrayName serial
  by_cases hb : arrayName = "begin"
  · subst hb
    simp [BeginEndUseReferenceAxes, replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
      dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
      StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]
  · by_cases he : arrayName = "end"
    · subst he
      simp [replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
        dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
        StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]
    · simp [hb, he, replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
        dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
        setListAt, updateAtPath, escapes, freshSyntax, syntaxCall, firstIndexExpr, lastIndexExpr,
        StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]

theorem ViewMacroContract_proven : ViewMacroContract := by
  intro Module hooks moduleValue
  constructor
  · intro expression serial hnot
    simp [viewMacro, hnot, StateT.bind, StateT.lift, ExceptT.bind, ExceptT.pure]
  · intro name index serial
    by_cases hb : name = "begin"
    · subst hb
      simp [viewMacro, replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
        dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
        StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]
    · by_cases he : name = "end"
      · subst he
        simp [viewMacro, replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
          dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
          StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]
      · simp [viewMacro, hb, he, replace_ref_begin_end!, replace_ref_begin_end_!.eq_def,
          dispatchExpanded.eq_def, handle_refexpr!.eq_def, boundaryOutcome, isExpr, syntaxArgs,
          setListAt, updateAtPath, escapes, freshSyntax, syntaxCall, escapeSyntax,
          StateT.bind, StateT.pure, StateT.lift, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]

theorem NestedBoundaryScope_proven : NestedBoundaryScope := by
  intro Module hooks moduleValue name outerFirst outerLast serial hb he
  simp [hb, he, replace_ref_begin_end_!.eq_def, dispatchExpanded.eq_def, handle_refexpr!.eq_def,
    boundaryOutcome, isExpr, syntaxArgs, setListAt, updateAtPath, escapes, freshSyntax,
    syntaxCall, firstIndexExpr, lastIndexExpr, StateT.bind, StateT.pure, StateT.lift,
    StateT.get, StateT.set, ExceptT.bind, ExceptT.pure]

theorem ReferenceBoundaryIsolation_proven : ReferenceBoundaryIsolation := by
  intro Module hooks context head array indices main path serial result used final h
  rw [handle_refexpr!.eq_def] at h
  cases hq : context.inQuoteContext with
  | true =>
    simp only [hq, ↓reduceIte, runThrow] at h
    cases Option.some.inj h
  | false =>
    simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨rewrittenArray, usedArray⟩, afterArray, ha, h⟩ :=
      successfulBind _ _ _ _ _ h
    refine ⟨rewrittenArray, usedArray, afterArray, ha, ?_⟩
    simp only [runBindFresh] at h
    cases indices with
    | nil =>
      simp only [runPure] at h
      exact (congrArg (fun pair => pair.1.2) (Except.ok.inj (Option.some.inj h))).symm
    | cons index rest =>
      cases rest with
      | nil =>
        obtain ⟨⟨rewrittenIndex, usedIndex⟩, afterIndex, _, h⟩ :=
          successfulBind _ _ _ _ _ h
        cases usedIndex <;> simp only [Bool.false_eq_true, ↓reduceIte, runPure] at h <;>
          exact (congrArg (fun pair => pair.1.2) (Except.ok.inj (Option.some.inj h))).symm
      | cons second rest =>
        obtain ⟨scan, afterScan, _, h⟩ := successfulBind _ _ _ _ _ h
        cases hb : scan.usedBoundary with
        | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte, runBindPure, runPure] at h
          exact (congrArg (fun pair => pair.1.2) (Except.ok.inj (Option.some.inj h))).symm
        | true =>
          simp only [hb, ↓reduceIte] at h
          obtain ⟨⟨rewrittenArgs, assignments⟩, afterAssignments, _, h⟩ :=
            successfulBind _ _ _ _ _ h
          obtain ⟨sourceArray, afterSource, _, h⟩ := successfulBind _ _ _ _ _ h
          simp only [runPure] at h
          exact (congrArg (fun pair => pair.1.2) (Except.ok.inj (Option.some.inj h))).symm

theorem ReferenceEvaluationPreserved_proven : ReferenceEvaluationPreserved := by
  intro Module hooks moduleValue hAst array index serial
  have hExpr : ∀ head args, hooks.isAstNode (.expr head args) = true := hAst
  dsimp only [ReferenceEvaluationPreserved]
  cases ha : replace_ref_begin_end_! hooks
      { owner := moduleValue, withex := none, inQuoteContext := false, escapeDepth := 0 } array serial with
  | none =>
    simp [ha, handle_refexpr!.eq_def, syntaxArgs, StateT.bind, ExceptT.bind]
  | some outcome =>
    cases outcome with
    | error error =>
      simp [ha, handle_refexpr!.eq_def, syntaxArgs, StateT.bind, ExceptT.bind]
    | ok pair =>
      obtain ⟨⟨rewrittenArray, usedArray⟩, afterArray⟩ := pair
      dsimp only
      cases hi : replace_ref_begin_end_! hooks
          { owner := moduleValue, withex :=
              some (firstIndexExpr (ViewSyntax.generated "S" afterArray) (some (.integer 2)),
                    lastIndexExpr (ViewSyntax.generated "S" afterArray) (some (.integer 2))),
            inQuoteContext := false, escapeDepth := 0 } index (afterArray + 2) with
      | none =>
        simp only [firstIndexExpr, lastIndexExpr, syntaxCall, Option.toList_some] at hi
        simp [ha, hi, handle_refexpr!.eq_def, boundaryOutcome, scanStep.eq_def,
          isExpr, hExpr, firstIndexExpr, lastIndexExpr, syntaxCall, freshSyntax, setListAt,
          updateAtPath, escapes, bindingInitializer, bindingTarget, syntaxArgs, Nat.add_assoc]
      | some outcome =>
        cases outcome with
        | error error =>
          simp only [firstIndexExpr, lastIndexExpr, syntaxCall, Option.toList_some] at hi
          simp [ha, hi, handle_refexpr!.eq_def, boundaryOutcome, scanStep.eq_def,
            isExpr, hExpr, firstIndexExpr, lastIndexExpr, syntaxCall, freshSyntax, setListAt,
            updateAtPath, escapes, bindingInitializer, bindingTarget, syntaxArgs, Nat.add_assoc]
        | ok pair =>
          obtain ⟨⟨rewrittenIndex, usedIndex⟩, afterIndex⟩ := pair
          simp only [firstIndexExpr, lastIndexExpr, syntaxCall, Option.toList_some] at hi
          cases hc : hooks.isAstNode rewrittenIndex <;>
            simp [ha, hi, hc, handle_refexpr!.eq_def, boundaryOutcome, scanStep.eq_def,
              isExpr, hExpr, firstIndexExpr, lastIndexExpr, syntaxCall, freshSyntax, setListAt,
              updateAtPath, escapes, bindingInitializer, bindingTarget, List.foldlM,
              syntaxArgs, syntaxArg, Nat.add_assoc]

theorem ReferenceHandlerContract_proven : ReferenceHandlerContract :=
  ⟨ReferenceBoundaryIsolation_proven, ReferenceEvaluationPreserved_proven⟩

theorem FreshNameSupply_proven : FreshNameSupply := by
  intro Module hooks p q m n first second afterFirst afterSecond hfirst hsecond
  simp only [runFresh, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfirst hsecond
  obtain ⟨rfl, rfl⟩ := hfirst
  obtain ⟨rfl, rfl⟩ := hsecond
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro hmn heq
    exact hmn (ViewSyntax.generated.inj heq).2
  · intro user heq
    cases heq

theorem TemporaryHygiene_proven : TemporaryHygiene := by
  refine ⟨FreshNameSupply_proven, ?_⟩
  dsimp only [CachedTemporaryHygiene]
  intro Module hooks moduleValue users hAst hSymbol arrayName indexName serial result used final hrun
  have hExpr : ∀ head args, hooks.isAstNode (.expr head args) = true := hAst
  have hSym : ∀ name, hooks.isAstNode (.symbol name) = true := hSymbol
  by_cases hba : arrayName = "begin"
  · subst arrayName
    simp [handle_refexpr!.eq_def, boundaryOutcome, isExpr] at hrun
    cases Option.some.inj hrun
  · by_cases hea : arrayName = "end"
    · subst arrayName
      simp [handle_refexpr!.eq_def, boundaryOutcome, isExpr] at hrun
      cases Option.some.inj hrun
    · by_cases hbi : indexName = "begin" <;> by_cases hei : indexName = "end" <;>
        simp [hba, hea, hbi, hei, handle_refexpr!.eq_def, boundaryOutcome, isExpr,
          scanStep.eq_def, List.foldlM, hExpr, hSym, firstIndexExpr, lastIndexExpr,
          syntaxCall, freshSyntax, setListAt, updateAtPath, escapes, syntaxArgs, syntaxArg,
          Nat.add_assoc] at hrun <;>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrun <;>
        simp [bindingTarget, List.pairwise_cons]

theorem viewsRead (hooks : ViewsHooks) (args : List ViewSyntax) :
    viewsExpr hooks "ref" args =
      (do
        let rewritten ← args.mapM (viewsAny hooks)
        pure (syntaxCall (.global "Base.maybeview") rewritten)) := by
  rw [viewsExpr.eq_def]
  simp

theorem viewsAssignment (hooks : ViewsHooks) (args : List ViewSyntax) (rhs : ViewSyntax) :
    viewsExpr hooks "=" [.expr "ref" args, rhs] =
      (do
        let rewritten ← args.mapM (viewsAny hooks)
        let rewrittenRhs ← viewsAny hooks rhs
        pure (.expr "=" [.expr "ref" rewritten, rewrittenRhs])) := by
  rw [viewsExpr.eq_def]
  simp [isExpr, syntaxArgs]

theorem viewsExplicitCall (hooks : ViewsHooks) (args : List ViewSyntax) :
    viewsExpr hooks "call" (.global "Base.getindex" :: args) =
      (do
        let rewritten ← args.mapM (viewsAny hooks)
        pure (hooks.exprarray "call" (.global "Base.getindex" :: rewritten))) := by
  rw [viewsExpr.eq_def]
  simp [endsInEquals]

theorem viewsFallback (hooks : ViewsHooks) (head : String) (args : List ViewSyntax)
    (heq : head ≠ "=") (hdot : head ≠ ".=") (href : head ≠ "ref")
    (hskip : endsInEquals head = false ∨ !isExpr (args.headD (.opaque "missing-left-hand-side")) "ref") :
    viewsExpr hooks head args =
      if head == "" || (endsInEquals head && args.isEmpty) then throw .boundsError else
        (do
          let rewritten ← args.mapM (viewsAny hooks)
          pure (hooks.exprarray head rewritten)) := by
  rw [viewsExpr.eq_def]
  by_cases hempty : head = ""
  · simp [hempty]
  · rcases hskip with hskip | hskip
    · simp [heq, hdot, href, hempty, hskip]
    · cases args with
      | nil => simp [heq, hdot, href, hempty]
      | cons first rest => simp_all

@[simp] theorem viewsExpression (hooks : ViewsHooks) (head : String) (args : List ViewSyntax) :
    viewsAny hooks (.expr head args) = viewsExpr hooks head args := by
  rw [viewsAny.eq_def]

@[simp] theorem viewsBlock (hooks : ViewsHooks) (args : List ViewSyntax) :
    viewsExpr hooks "block" args =
      (do let rewritten ← args.mapM (viewsAny hooks)
          pure (hooks.exprarray "block" rewritten)) :=
  viewsFallback hooks "block" args (by decide) (by decide) (by decide) (.inl (by decide))

@[simp] theorem viewsLocal (hooks : ViewsHooks) (args : List ViewSyntax) :
    viewsExpr hooks "local" args =
      (do let rewritten ← args.mapM (viewsAny hooks)
          pure (hooks.exprarray "local" rewritten)) :=
  viewsFallback hooks "local" args (by decide) (by decide) (by decide) (.inl (by decide))

@[simp] theorem viewsCall (hooks : ViewsHooks) (args : List ViewSyntax) :
    viewsExpr hooks "call" args =
      (do let rewritten ← args.mapM (viewsAny hooks)
          pure (hooks.exprarray "call" rewritten)) :=
  viewsFallback hooks "call" args (by decide) (by decide) (by decide) (.inl (by decide))

@[simp] theorem viewsSymbolAssignment (hooks : ViewsHooks) (lhs rhs : String) :
    viewsExpr hooks "=" [.symbol lhs, .symbol rhs] =
      pure (.expr "=" [.symbol lhs, .symbol rhs]) := by
  rw [viewsExpr.eq_def]
  simp [isExpr]

@[simp] theorem viewsGeneratedAssignment (hooks : ViewsHooks) (tag rhs : String) (serial : Nat) :
    viewsExpr hooks "=" [.generated tag serial, .symbol rhs] =
      pure (.expr "=" [.generated tag serial, .symbol rhs]) := by
  rw [viewsExpr.eq_def]
  simp [isExpr]


theorem ViewsReadAssignmentContract_proven : ViewsReadAssignmentContract := by
  intro hooks hexpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro args serial result final h
    rw [viewsRead] at h
    obtain ⟨rewritten, after, hargs, hout⟩ := successfulBind _ _ _ _ _ h
    simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    exact ⟨rewritten, hargs, rfl⟩
  · intro args rhs serial result final h
    rw [viewsAssignment] at h
    obtain ⟨rewritten, after, hargs, hout⟩ := successfulBind _ _ _ _ _ h
    obtain ⟨rewrittenRhs, last, hrhs, hout⟩ := successfulBind _ _ _ _ _ hout
    simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    exact ⟨rewritten, rewrittenRhs, after, hargs, hrhs, rfl⟩
  · intro args serial result final h
    rw [viewsExplicitCall] at h
    obtain ⟨rewritten, after, hargs, hout⟩ := successfulBind _ _ _ _ _ h
    simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    exact ⟨rewritten, hargs, hexpr "call" _⟩
  · intro head args serial result final heq hdot href hskip h
    rw [viewsFallback hooks head args heq hdot href hskip] at h
    by_cases hbad : (head == "" || (endsInEquals head && args.isEmpty)) = true
    · simp only [if_pos hbad, runThrow] at h
      cases Option.some.inj h
    · rw [if_neg hbad] at h
      obtain ⟨rewritten, after, hargs, hout⟩ := successfulBind _ _ _ _ _ h
      simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      exact ⟨rewritten, hargs, hexpr head _⟩

theorem indexListLength {α : Type} (xs : List α) (start : Nat) :
    (indexList start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simpa only [indexList, List.length_cons] using congrArg Nat.succ (ih (start + 1))

theorem successfulMapMLength {α β : Type} (f : α → ViewResult β)
    (xs : List α) (serial final : Nat) (result : List β)
    (h : xs.mapM f serial = some (.ok (result, final))) :
    result.length = xs.length := by
  induction xs generalizing serial final result with
  | nil =>
    simp only [List.mapM_nil, runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨value, after, _, hout⟩ := successfulBind _ _ _ _ _ h
    obtain ⟨values, last, hvalues, hout⟩ := successfulBind _ _ _ _ _ hout
    simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    exact congrArg Nat.succ (ih after final values hvalues)

theorem IndexedOperatorCache_proven : IndexedOperatorCache := by
  intro hooks head array indices rhs serial result final heq hdot href hempty hlast h
  rw [viewsExpr.eq_def] at h
  simp only [beq_eq_false_iff_ne.mpr heq, beq_eq_false_iff_ne.mpr hdot,
    beq_eq_false_iff_ne.mpr href, beq_eq_false_iff_ne.mpr hempty, hlast, Bool.false_or,
    Bool.false_eq_true, if_false, List.isEmpty_cons, Bool.and_false,
    List.head?_cons, Option.any_some, isExpr, beq_self_eq_true,
    Bool.and_true, if_true, syntaxArg, List.getElem?_cons_zero,
    syntaxArgs, List.drop_succ_cons, List.drop_zero, runBindPure] at h
  obtain ⟨indexed, afterIndices, hindices, hout⟩ := successfulBind _ _ _ _ _ h
  simp only [runBindPure] at hout
  obtain ⟨rewrittenArray, afterArray, _, hout⟩ := successfulBind _ _ _ _ _ hout
  obtain ⟨rewrittenBindings, afterBindings, hbindings, hout⟩ := successfulBind _ _ _ _ _ hout
  obtain ⟨escapedRhs, last, hrhs, hout⟩ := successfulBind _ _ _ _ _ hout
  simp only [runPure, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hout
  obtain ⟨rfl, rfl⟩ := hout
  have hindexed : indexed.length = indices.length := by
    unfold prepareOpIndices at hindices
    exact (successfulMapMLength _ _ _ _ _ hindices).trans (indexListLength indices 1)
  have hbindLength := successfulMapMLength _ _ _ _ _ hbindings
  have hrhsLength := successfulMapMLength _ _ _ _ _ hrhs
  refine ⟨indexed.map Prod.fst,
    [.expr "=" [.symbol "a", escapeSyntax rewrittenArray]] ++ rewrittenBindings,
    escapedRhs, ?_, ?_, hrhsLength, rfl⟩
  · simpa only [List.length_map] using hindexed
  · simp only [List.length_append, List.length_cons, List.length_nil, hbindLength,
      indexListLength, List.length_map, hindexed]
    omega

theorem SingleOperatorAssignmentCache_proven : SingleOperatorAssignmentCache := by
  intro hooks hexpr arrayName indexName rhs serial
  cases hout : viewsAny hooks rhs serial with
  | none =>
    simp [viewsExpr.eq_def, prepareOpIndices, indexList, syntaxArgs, isExpr, endsInEquals, startsInDot,
      dropLastChar, List.mapM_cons, List.mapM_nil, hout, bindingInitializer, bindingTarget, StateT.bind,
      StateT.pure, ExceptT.bind, ExceptT.pure]
  | some outcome =>
    cases outcome with
    | error error =>
      simp [viewsExpr.eq_def, prepareOpIndices, indexList, syntaxArgs, isExpr, endsInEquals, startsInDot,
        dropLastChar, List.mapM_cons, List.mapM_nil, hout, bindingInitializer, bindingTarget, StateT.bind,
        StateT.pure, ExceptT.bind, ExceptT.pure]
    | ok pair =>
      obtain ⟨rewritten, after⟩ := pair
      simp [viewsExpr.eq_def, prepareOpIndices, indexList, syntaxArgs, isExpr, endsInEquals, startsInDot,
        dropLastChar, List.mapM_cons, List.mapM_nil, hout, bindingInitializer, bindingTarget, syntaxCall,
        StateT.bind, StateT.pure, ExceptT.bind, ExceptT.pure] <;>
        exact ⟨by decide, congrArg (fun s => escapeSyntax (.symbol s)) (by decide), by decide⟩

theorem OperatorAssignmentCacheContract_proven : OperatorAssignmentCacheContract :=
  ⟨IndexedOperatorCache_proven, SingleOperatorAssignmentCache_proven⟩

theorem ViewsMacroBoundaryContract_proven : ViewsMacroBoundaryContract := by
  intro Module replaceHooks rewriteHooks hexpr moduleValue arrayName serial
  dsimp only [ExprarrayLaw] at hexpr
  have hbegin := (BeginEndUseReferenceAxes_proven replaceHooks moduleValue arrayName serial).1
  by_cases hb : arrayName = "begin"
  · simp [hb] at hbegin
    simp [viewsMacro, hbegin, hb]
  · by_cases he : arrayName = "end"
    · simp [hb, he] at hbegin
      simp [viewsMacro, hbegin, hb, he]
    · simp [hb, he] at hbegin
      simp [viewsMacro, hbegin, hb, he, viewsRead, hexpr, ExprarrayLaw,
        syntaxCall, firstIndexExpr, escapeSyntax]


/-!
Nothing to promise:
- `escapes@22`: internal escape-depth plumbing used by the recursive transformer.
- `_views(x)@247`: identity fallback for non-expression values.
-/

def entries : List Entry := [
  { id := "views-source-boundary-index", juliaFile := "base/views.jl"
    juliaFns := ["replace_ref_begin_end!@17", "replace_ref_begin_end_!@19"]
    statement := "For a one-index reference, begin and end select its firstindex and lastindex; boundary symbols in the array position or outside a reference raise ErrorException."
    source := "base/views.jl:6-17,103-120"
    status := .proven, prop := ``BeginEndUseReferenceAxes, thm := some ``BeginEndUseReferenceAxes_proven },
  { id := "views-source-reference-handler", juliaFile := "base/views.jl"
    juliaFns := ["handle_refexpr!@28"]
    statement := "Every successful reference rewrite keeps its own index boundaries scoped to that reference. For begin followed by a splatted arbitrary expression, it caches the rewritten array and indices in source order and uses their separate temporaries, including when source expressions coincide."
    source := "base/views.jl:28-102; scope and evaluation-order invariants"
    status := .proven, prop := ``ReferenceHandlerContract, thm := some ``ReferenceHandlerContract_proven
    notes := "Cache initializer positions measure evaluations. Counting equal AST subtrees would miscount nested rewrites and repeated user expressions." },
  { id := "views-source-view-macro", juliaFile := "base/views.jl"
    juliaFns := ["@view@210"]
    statement := "@view rejects non-reference syntax with ArgumentError, rewrites a simple reference to a view call, and propagates invalid boundary-symbol errors."
    source := "base/views.jl:162-208,210-228"
    status := .proven, prop := ``ViewMacroContract, thm := some ``ViewMacroContract_proven },
  { id := "views-source-maybeview", juliaFile := "base/views.jl"
    juliaFns := ["maybeview@235", "maybeview@236", "maybeview@237", "maybeview@238", "maybeview@239"]
    statement := "Scalar and nonarray access preserves getindex results and errors, while array slicing preserves view results and their storage aliases."
    source := "base/views.jl:233-239"
    status := .proven, prop := ``MaybeViewBehavior, thm := some ``MaybeViewBehavior_proven },
  { id := "views-source-read-and-assignment", juliaFile := "base/views.jl"
    juliaFns := ["_views(::Expr)@248"]
    statement := "Successful @views rewrites use maybeview for reads, preserve indexed assignment targets and explicit getindex calls, and retain other expression heads."
    source := "base/views.jl:296-303,248-294"
    status := .proven, prop := ``ViewsReadAssignmentContract, thm := some ``ViewsReadAssignmentContract_proven },
  { id := "views-source-opassign-cache", juliaFile := "base/views.jl"
    juliaFns := ["_views(::Expr)@248"]
    statement := "Indexed operator rewrites preserve the number of index-cache slots and RHS operands, and use the same cached indices for the assignment target and maybeview read. A one-index += rewrite preserves both cache initializers and the arbitrary RHS result or error."
    source := "base/views.jl:258-289; evaluation-order invariant"
    status := .proven, prop := ``OperatorAssignmentCacheContract, thm := some ``OperatorAssignmentCacheContract_proven
    notes := "RHS repetitions are separate user evaluations; equal array and index names still occupy two source positions." },
  { id := "views-source-macro-boundary", juliaFile := "base/views.jl"
    juliaFns := ["@views@332"]
    statement := "@views resolves begin in the current reference before rewriting the read to maybeview and escaping the result; invalid array-position boundaries propagate their error."
    source := "base/views.jl:296-314,332-334"
    status := .proven, prop := ``ViewsMacroBoundaryContract, thm := some ``ViewsMacroBoundaryContract_proven },
  { id := "views-source-nested-scope", juliaFile := "base/views.jl"
    juliaFns := ["replace_ref_begin_end_!@19", "handle_refexpr!@28"]
    statement := "An inner reference uses its own lastindex, independently of enclosing endpoints, and does not report its own end as using the enclosing reference."
    source := "base/views.jl:6-15,31,42-45,97-102"
    status := .proven, prop := ``NestedBoundaryScope, thm := some ``NestedBoundaryScope_proven },
  { id := "views-source-temporary-hygiene", juliaFile := "base/views.jl"
    juliaFns := ["handle_refexpr!@28"]
    statement := "Generated names are fresh; a reference with begin followed by a splatted symbol uses three pairwise-distinct cache names, all disjoint from existing user symbols."
    source := "base/views.jl:32,71,79-99; gensym freshness contract"
    status := .proven, prop := ``TemporaryHygiene, thm := some ``TemporaryHygiene_proven }
]

end JuliaLean.Proofs.base.views

