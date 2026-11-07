import JuliaLean.Proofs.base.show.methodSupport
import JuliaLean.Core
import JuliaLean.base.show
import JuliaLean.base.dict
import JuliaLean.base.strings.io
import JuliaLean.Registry.Types

/-!
# Properties of `base/show.jl` IOContext behavior

The registry entries are open for their proof worker.
-/

namespace JuliaLean.Proofs.base.show

open JuliaLean JuliaLean.base.show JuliaLean.base.dict JuliaLean.base.strings.io JuliaLean.Registry

set_option linter.unusedVariables false

private def observedIOBufferShow (showCall : BufferShowM Unit Unit) :
    Except (Error Unit) JuliaString := do
  let initial ← (newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64)
    (some (JuliaLean.base.iobuffer.i 0))).mapError Error.buffer
  let action : BufferShowM Unit Bytes := do
    let _ ← showCall
    liftBuffer JuliaLean.base.iobuffer.takestring
  match action initial with
  | .ok bytes _ => pure ⟨bytes⟩
  | .error error _ => .error error

private def showIOPrims : IOPrims (BufferShowM Unit) Unit Unit :=
  bufferPrims (JuliaLean.base.int.lit .i64 24, JuliaLean.base.int.lit .i64 80)

/-- The installed `show(io, ::Nothing)` output observed through the installed IOBuffer writes and
`takestring!` models is the Julia literal `nothing` (`base/show.jl:1424`). -/
def NothingShowOutput : Prop :=
  observedIOBufferShow (show_Nothing showIOPrims (.plain ())) =
    .ok ⟨lit "nothing"⟩

def IOContextNewestPairOverride : Prop :=
  ∀ {m Io V Ty} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (parent : IOContext Io V)
    (key : Sym) (new fallback : V) (child : IOContext Io V),
    IOContext_pair p a (fieldConv Sym) (fieldConv V) (.context parent) (key, new) = pure child →
      get_IOContext symEq child key fallback = .inl new ∧
      haskey (.context child) key = true

def IOContextBooleanOptionOverride : Prop :=
  ∀ {m Io V Ty} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V)
    (key : Sym) (value : Bool) (child : IOContext Io V),
    (key = "compact" ∨ key = "limit" ∨ key = "color" ∨ key = "hexunsigned") →
    IOContext_pair p a (fieldConv Sym) (boolConv a) io (key, value) = pure child →
      get_IOContext symEq child key (a.ofBool (!value)) = .inl (a.ofBool value) ∧
      haskey (.context child) key = true

def IOContextTypeinfoOverride : Prop :=
  ∀ {m Io V Ty} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) (T : Ty)
    (child : IOContext Io V),
    withTypeinfo p a io T = pure (.context child) →
      get_IOContext symEq child "typeinfo" (a.ofType T) = .inl (a.ofType T) ∧
      haskey (.context child) "typeinfo" = true

def IOContextParentLookupInheritance : Prop :=
  ∀ {m Io V Ty} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (replacement : Io)
    (parent child : IOContext Io V),
    IOContext_IO_IO p a (.plain replacement) (.context parent) = pure child →
      ∀ (key : Sym) (fallback : V),
        get_IOContext symEq child key fallback = get_IOContext symEq parent key fallback ∧
        haskey (.context child) key = haskey (.context parent) key

def IOContextGetImpliesHaskey : Prop :=
  ∀ {Io V} (ctx : IOContext Io V) (key : Sym) (fallback value : V),
    get_IOContext symEq ctx key fallback = .inl value →
      haskey (.context ctx) key = true

def IOContextMissingKeyUsesDefault : Prop :=
  ∀ {Io V} (ctx : IOContext Io V) (key : Sym) (fallback : V),
    haskey (.context ctx) key = false →
      get_IOContext symEq ctx key fallback = .inr fallback

def IOContextGetHaskey : Prop :=
  IOContextGetImpliesHaskey ∧ IOContextMissingKeyUsesDefault

namespace Round3

open _root_.JuliaLean.base.show _root_.JuliaLean.base.dict

/-- A new IOContext pair takes precedence and remains present. -/
def IOContextNewestPairOverride : Prop :=
  ∀ {Io V Ty} (p : IOPrims (Except ShowError) Io V) (a : AnyOps V Ty)
    (parent : IOContext Io V) (key : Sym) (new fallback : V) (child : IOContext Io V),
    IOContext_pair p a (fieldConv Sym) (fieldConv V) (.context parent) (key, new) = pure child →
      get_IOContext symEq child key fallback = .inl new ∧
      haskey (.context child) key = true

/-- The four documented Bool options retain their values and remain present. -/
def IOContextBooleanOptionOverride : Prop :=
  ∀ {Io V Ty} (p : IOPrims (Except ShowError) Io V) (a : AnyOps V Ty) (io : JIO Io V)
    (key : Sym) (value : Bool) (child : IOContext Io V),
    (key = "compact" ∨ key = "limit" ∨ key = "color" ∨ key = "hexunsigned") →
    IOContext_pair p a (fieldConv Sym) (boolConv a) io (key, value) = pure child →
      get_IOContext symEq child key (a.ofBool (!value)) = .inl (a.ofBool value) ∧
      haskey (.context child) key = true

/-- `withTypeinfo` installs its type under `:typeinfo` and keeps the key present. -/
def IOContextTypeinfoOverride : Prop :=
  ∀ {Io V Ty} (p : IOPrims (Except ShowError) Io V) (a : AnyOps V Ty)
    (io : JIO Io V) (T : Ty) (child : IOContext Io V),
    withTypeinfo p a io T = pure (.context child) →
      get_IOContext symEq child "typeinfo" (a.ofType T) = .inl (a.ofType T) ∧
      haskey (.context child) "typeinfo" = true

/-- Replacing an IOContext's stream preserves lookups and key presence. -/
def IOContextParentLookupInheritance : Prop :=
  ∀ {Io V Ty} (p : IOPrims (Except ShowError) Io V) (a : AnyOps V Ty)
    (replacement : Io) (parent child : IOContext Io V),
    IOContext_IO_IO p a (.plain replacement) (.context parent) = pure child →
      ∀ (key : Sym) (fallback : V),
        get_IOContext symEq child key fallback = get_IOContext symEq parent key fallback ∧
        haskey (.context child) key = haskey (.context parent) key

end Round3

namespace ChatGPTBatch2.Group3

open _root_.JuliaLean.base.dict _root_.JuliaLean.base.show

/-- Finding a stored value certifies presence in the immutable dictionary. -/
theorem lookupValueHasKey {K V Q D : Type} (eqKey : K → Q → Bool)
    (dict : ImmutableDict K V) (query : Q) (fallback : D) (value : V)
    (h : immutableGet eqKey dict query fallback = .inl value) :
    immutableHasKey eqKey dict query = true := by
  revert h
  induction dict with
  | nil =>
    intro h
    change Sum.inr fallback = Sum.inl value at h
    cases h
  | cons pair rest ih =>
    intro h
    rcases pair with ⟨key, stored⟩
    cases heq : eqKey key query with
    | false =>
      simp only [immutableGet, heq, Bool.false_eq_true, ite_false] at h
      simp only [immutableHasKey, heq, Bool.false_or]
      exact ih h
    | true =>
      simp only [immutableHasKey, heq, Bool.true_or]

/-- Absence in the immutable dictionary makes lookup return the default. -/
theorem lookupMissingUsesDefault {K V Q D : Type} (eqKey : K → Q → Bool)
    (dict : ImmutableDict K V) (query : Q) (fallback : D)
    (h : immutableHasKey eqKey dict query = false) :
    immutableGet eqKey dict query fallback = .inr fallback := by
  revert h
  induction dict with
  | nil =>
    intro h
    rfl
  | cons pair rest ih =>
    intro h
    rcases pair with ⟨key, stored⟩
    cases heq : eqKey key query with
    | false =>
      simp only [immutableHasKey, heq, Bool.false_or] at h
      simp only [immutableGet, heq, Bool.false_eq_true, ite_false]
      exact ih h
    | true =>
      have hbad : true = false := by
        simpa only [immutableHasKey, heq, Bool.true_or] using h
      cases hbad

/-- The two public lookup guarantees hold for every represented context. -/
theorem ShowR2IocontextGetHaskey_proven :
    JuliaLean.Proofs.base.show.IOContextGetHaskey := by
  constructor
  · intro Io V ctx key fallback value h
    exact lookupValueHasKey symEq ctx.dict key fallback value h
  · intro Io V ctx key fallback h
    exact lookupMissingUsesDefault symEq ctx.dict key fallback h

end ChatGPTBatch2.Group3
end JuliaLean.Proofs.base.show

namespace JuliaLean.ChatGPT.Batch3.Group4

open JuliaLean.base.show JuliaLean.base.dict

/-- A decidable observation of a result needs no equality operation on its errors. -/
def showBytesMatch {E : Type}
    (result : Except E JuliaLean.base.strings.io.JuliaString)
    (bytes : List UInt8) : Bool :=
  match result with
  | .ok value => decide (value.bytes = bytes)
  | .error _ => false

/-- Successful byte observation determines the complete successful result. -/
theorem showBytesMatchSound {E : Type}
    (result : Except E JuliaLean.base.strings.io.JuliaString)
    (bytes : List UInt8) (h : showBytesMatch result bytes = true) :
    result = .ok ⟨bytes⟩ := by
  cases result with
  | error error => cases h
  | ok value =>
    cases value with
    | mk actual =>
      have he : actual = bytes := of_decide_eq_true h
      cases he
      rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- show-r4-nothing-show-output: the concrete buffer action writes the literal. -/
theorem ShowR4NothingShowOutput_proven : JuliaLean.Proofs.base.show.NothingShowOutput := by
  unfold JuliaLean.Proofs.base.show.NothingShowOutput
  apply showBytesMatchSound
  decide +kernel

/-- Looking up the just-prepended symbol returns its stored value. -/
theorem showLookupPrepend {V D : Type} (key : Sym) (value : V)
    (parent : ImmutableDict Sym V) (fallback : D) :
    immutableGet symEq ((key, value) :: parent) key fallback = .inl value := by
  simp only [immutableGet, symEq, beq_self_eq_true, ite_true]

/-- The just-prepended symbol is present. -/
theorem showHaskeyPrepend {V : Type} (key : Sym) (value : V)
    (parent : ImmutableDict Sym V) :
    immutableHasKey symEq ((key, value) :: parent) key = true := by
  simp only [immutableHasKey, symEq, beq_self_eq_true, Bool.true_or]

/-- Changing the stream used by a context leaves its dictionary unchanged. -/
theorem showMkContextDict {Io V : Type} (io : JIO Io V)
    (dict : ImmutableDict Sym V) :
    (mkIOContext io dict).dict = dict := by
  cases io <;> rfl

/-- show-r2-iocontext-newest: the new pair precedes the inherited dictionary. -/
theorem ShowR2IocontextNewest_proven :
    JuliaLean.Proofs.base.show.Round3.IOContextNewestPairOverride := by
  intro Io V Ty p a parent key new fallback child h
  have hc : mkIOContext (.context parent) ((key, new) :: parent.dict) = child := by
    change Except.ok (mkIOContext (.context parent) ((key, new) :: parent.dict)) =
      Except.ok child at h
    exact Except.ok.inj h
  rw [← hc]
  constructor
  · exact showLookupPrepend key new parent.dict fallback
  · exact showHaskeyPrepend key new parent.dict

/-- Successful pair construction records the converted value at the head. -/
theorem showPairSuccess {Io V Ty W : Type}
    (p : IOPrims (Except ShowError) Io V) (a : AnyOps V Ty)
    (io : JIO Io V) (key : Sym) (input : W) (value : V)
    (conv : ValueConv W V) (hconv : convertValue conv input = .ok value)
    (child : IOContext Io V)
    (h : IOContext_pair p a (fieldConv Sym) conv io (key, input) = .ok child) :
    ∃ dict, child = mkIOContext io ((key, value) :: dict) := by
  unfold IOContext_pair at h
  cases hd : ioproperties p a io with
  | error error =>
    simp only [hd, bind, Except.bind] at h
    cases h
  | ok dict =>
    have hp : immutablePrepend (fieldConv Sym) conv dict key input =
        .ok ((key, value) :: dict) := by
      unfold immutablePrepend
      change Except.bind (convertValue conv input)
        (fun stored => .ok ((key, stored) :: dict)) = .ok ((key, value) :: dict)
      rw [hconv]
      rfl
    have hc : mkIOContext io ((key, value) :: dict) = child := by
      simpa only [hd, bind, Except.bind, hp, ofDict, pure, Except.pure,
        Except.ok.injEq] using h
    exact ⟨dict, hc.symm⟩

/-- show-r2-iocontext-bool-options: successful Bool conversion preserves the option. -/
theorem ShowR2IocontextBoolOptions_proven :
    JuliaLean.Proofs.base.show.Round3.IOContextBooleanOptionOverride := by
  intro Io V Ty p a io key value child _ h
  obtain ⟨dict, rfl⟩ := showPairSuccess p a io key value (a.ofBool value)
    (boolConv a) rfl child h
  constructor
  · change immutableGet symEq (mkIOContext io ((key, a.ofBool value) :: dict)).dict
      key (a.ofBool (!value)) = .inl (a.ofBool value)
    rw [showMkContextDict]
    exact showLookupPrepend key (a.ofBool value) dict (a.ofBool (!value))
  · change immutableHasKey symEq (mkIOContext io ((key, a.ofBool value) :: dict)).dict
      key = true
    rw [showMkContextDict]
    exact showHaskeyPrepend key (a.ofBool value) dict

/-- show-r2-iocontext-typeinfo: successful type conversion stores the type value. -/
theorem ShowR2IocontextTypeinfo_proven :
    JuliaLean.Proofs.base.show.Round3.IOContextTypeinfoOverride := by
  intro Io V Ty p a io T child h
  have hp : IOContext_pair p a (fieldConv Sym) (typeConv a) io ("typeinfo", T) =
      .ok child := by
    unfold withTypeinfo at h
    cases he : IOContext_pair p a (fieldConv Sym) (typeConv a) io ("typeinfo", T) with
    | error error =>
      simp only [he, bind, Except.bind] at h
      cases h
    | ok result =>
      have hc : result = child := by
        rw [he] at h
        change Except.ok (JIO.context result) = Except.ok (JIO.context child) at h
        exact JIO.context.inj (Except.ok.inj h)
      rw [hc]
  obtain ⟨dict, rfl⟩ := showPairSuccess p a io "typeinfo" T (a.ofType T)
    (typeConv a) rfl child hp
  constructor
  · change immutableGet symEq (mkIOContext io (("typeinfo", a.ofType T) :: dict)).dict
      "typeinfo" (a.ofType T) = .inl (a.ofType T)
    rw [showMkContextDict]
    exact showLookupPrepend "typeinfo" (a.ofType T) dict (a.ofType T)
  · change immutableHasKey symEq (mkIOContext io (("typeinfo", a.ofType T) :: dict)).dict
      "typeinfo" = true
    rw [showMkContextDict]
    exact showHaskeyPrepend "typeinfo" (a.ofType T) dict


/-- show-r2-iocontext-parent: replacement preserves the entire dictionary. -/
theorem ShowR2IocontextParent_proven :
    JuliaLean.Proofs.base.show.Round3.IOContextParentLookupInheritance := by
  intro Io V Ty p a replacement parent child h
  have hc : mkIOContext (.plain replacement) parent.dict = child := by
    change Except.ok (mkIOContext (.plain replacement) parent.dict) = Except.ok child at h
    exact Except.ok.inj h
  rw [← hc]
  intro key fallback
  exact ⟨rfl, rfl⟩
end JuliaLean.ChatGPT.Batch3.Group4


namespace JuliaLean.ShowCov.Methods.ShowFile

set_option linter.unusedVariables false

open JuliaLean.Registry
open JuliaLean.ShowCov.Methods
open JuliaLean.ShowCov
open JuliaLean.Show
open JuliaLean.Strings

def P6 : Prop := ∀ (compact : Bool), (m6 compact) = Values.showUndefPlain compact
theorem p6 : P6 := fun compact => rfl

def P14 : Prop := ∀ runtime r, m14 runtime r = [runtime.render r]
theorem p14 : P14 := fun _ _ => rfl

def P16 : Prop := ∀ runtime compact r, m16 runtime compact r =
  [runtime.render r] ++ (if !compact && runtime.isempty r then [" (empty range)"] else [])
theorem p16 : P16 := fun _ _ _ => rfl

def P23 : Prop := ∀ runtime r, m23 runtime r =
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLinRange r]
theorem p23 : P23 := fun _ _ => rfl

def P34 : Prop := ∀ runtime r, m34 runtime r =
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLogRange r]
theorem p34 : P34 := fun _ _ => rfl

def P41 : Prop := ∀ runtime ft, m41 runtime ft =
  let ftname := ft.typeName
  let name := ftname.singletonName
  if ftname.name == name then false
  else
    let mod := runtime.parentModule ft
    let bpart := runtime.lookupBindingPartition runtime.worldAge mod name
    if runtime.bindingKind bpart = runtime.backdatedConstKind then
      ft.id = runtime.typeOf bpart.restriction
    else runtime.isDefinedGlobal mod name &&
      ft.id = runtime.typeOf (runtime.getGlobal mod name)
theorem p41 : P41 := fun _ _ => rfl

def P55 : Prop := ∀ runtime compact f, m55 runtime compact f =
  if compact then runtime.render f
  else
    let ft := f.datatype
    let name := ft.typeName.singletonName
    match f.kind with
    | .intrinsic => runtime.render f ++ " (intrinsic function #" ++
        toString (runtime.bitcastInt32 f) ++ ")"
    | .builtin => name ++ " (built-in function)"
    | .generic =>
      let n := f.methods.length
      let methodWord := if n = 1 then "method" else "methods"
      let stringName := name
      let shownName := if isSelfBody runtime.selfRuntime ft || stringName.contains '#' then
        stringName else "(::" ++ runtime.renderType ft ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"
theorem p55 : P55 := fun _ _ _ => rfl

def P75 : Prop := ∀ runtime c, m75 runtime c = [runtime.render c]
theorem p75 : P75 := fun _ _ => rfl

def P76 : Prop := ∀ runtime c, m76 runtime c = [runtime.render c]
theorem p76 : P76 := fun _ _ => rfl

def P77 : Prop := ∀ runtime s, m77 runtime s = [runtime.render s]
theorem p77 : P77 := fun _ _ => rfl

def P85 : Prop := ∀ (tok : Truncate.Tok), (m85 tok) = Truncate.Tok.ncu tok
theorem p85 : P85 := fun tok => rfl

def P86 : Prop := ∀ (tw : Char → Nat) (tok : Truncate.Tok), (m86 tw tok) = Truncate.Tok.width tw tok
theorem p86 : P86 := fun tw tok => rfl

def P92 : Prop := ∀ (s : List Char), (m92 s) = Truncate.ansiTokens s
theorem p92 : P92 := fun s => rfl

def P94 : Prop := ∀ iteratorType : String, m94 iteratorType = Truncate.iteratorSizeANSI
theorem p94 : P94 := fun _ => rfl

def P95 : Prop := ∀ iteratorType : String, m95 iteratorType = Truncate.eltypeANSI
theorem p95 : P95 := fun _ => rfl

def P96 : Prop := ∀ captures i, m96 captures i =
  match captureIter captures with
  | none => none
  | some (capture, (j, newState)) =>
    let token := if (capture.matchText.map Char.utf8Size).sum = 1 then
      match capture.matchText with
      | [c] => Truncate.Tok.ch c
      | _ => Truncate.Tok.ansi capture.matchText
    else Truncate.Tok.ansi capture.matchText
    some ((i, token), (j, captureIter newState))
theorem p96 : P96 := fun _ _ => rfl

def P102 : Prop := ∀ (tw : Char → Nat) (s : List Char), (m102 tw s) = Truncate.ansiWidth tw s
theorem p102 : P102 := fun tw s => rfl

def P104 : Prop := ∀ (tw : Char → Nat) (ignore : Bool) (s : List Char) (width : Int) (rpad : Bool) (chars mark : List Char), (m104 tw ignore s width rpad chars mark) = Truncate.truncateAt tw ignore s width rpad chars mark
theorem p104 : P104 := fun tw ignore s width rpad chars mark => rfl

def P137 : Prop := ∀ runtime iter, m137 runtime iter =
  let entries := iter.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value)
        (max 4 (runtime.displaysize.2 - 2)).toNat : Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  if entries.isEmpty && runtime.compact then runtime.renderIter iter
  else if entries.isEmpty then runtime.summary iter
  else if runtime.limit && rows < 2 then runtime.summary iter ++ ". " ++
    (if iter.isKeySet then "Keys" else "Values") ++ ": …"
  else
    let room := if runtime.limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if runtime.limit then e.limited else e.full)
    let ellipsis := if runtime.limit && room < entries.length then ["\n  ⋮"] else []
    runtime.summary iter ++ ". " ++ (if iter.isKeySet then "Keys" else "Values") ++
      ":" ++ String.join (lines ++ ellipsis)
theorem p137 : P137 := by unfold P137; intros; rfl

def P168 : Prop := ∀ runtime dict,
  HasResult (m168 runtime dict) ∧
  (dict.pairs.isEmpty || !dict.hasLength → m168 runtime dict = runtime.renderDict dict) ∧
  (!dict.pairs.isEmpty → dict.hasLength → runtime.circular dict →
    m168 runtime dict = runtime.summary dict ++ ":")
theorem p168 : P168 := by
  intro runtime dict
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h
    simp only [m168, showDictBody]
    split <;> simp_all
  · intro hne hlen hcirc
    cases h : dict.pairs with
    | nil => simp [h] at hne
    | cons head tail => simp [m168, showDictBody, h, hlen, hcirc]

def P235 : Prop := ∀ runtime set, m235 runtime set =
  [runtime.showarg set true, " with ", toString set.elements.length,
    if set.elements.length = 1 then " element" else " elements"]
theorem p235 : P235 := fun _ _ => rfl

def P241 : Prop := ∀ runtime set, m241 runtime set =
  let cols := max 4 (runtime.displaysize.2 - 2)
  let entries := set.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value) cols.toNat :
        Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  if entries.isEmpty then runtime.renderSet set
  else if runtime.circular set then runtime.summary set ++ ":"
  else if runtime.limit && rows < 2 then runtime.summary set ++ ": …"
  else
    let room := if runtime.limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if runtime.limit then e.limited else e.full)
    let ellipsis := if runtime.limit && room < entries.length then ["\n  ⋮ "] else []
    runtime.summary set ++ ":" ++ String.join (lines ++ ellipsis)
theorem p241 : P241 := by unfold P241; intros; rfl

def P278 : Prop := ∀ runtime opt, m278 runtime opt =
  let nfields := opt.fields.length
  ["JLOptions(", "\n"] ++ opt.fields.zipIdx.flatMap (fun ((field, value), index) =>
    let value := normalizeOptionValue runtime value
    ["  ", field, " = ", runtime.repr value,
      if index + 1 < nfields then "," else "", "\n"]) ++ [")"]
theorem p278 : P278 := fun _ _ => rfl

def P294 : Prop := ∀ runtime task, m294 runtime task =
  [runtime.render task] ++
    if runtime.isFailed task then ["\n", runtime.showException task false] else []
theorem p294 : P294 := fun _ _ => rfl

def P304 : Prop := ∀ runtime source, m304 runtime source =
  ["CancellationTokenSource("] ++
  [match runtime.cancelSeverity source with
   | none => "active"
   | some severity =>
     let request := severity.request
     if request = 0x1 then "cancelled"
     else if request = 0x3 then "cancelled, abandon external"
     else if request = 0x4 then "cancelled, abandon all"
     else "cancelled, severity " ++ runtime.repr request] ++
  (if source.nparents > 0 then [", ", toString source.nparents,
    if source.nparents = 1 then " parent" else " parents"] else []) ++ [")"]
theorem p304 : P304 := fun _ _ => rfl

def P322 : Prop := ∀ name, m322 name = name
theorem p322 : P322 := fun _ => rfl

def P336 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m336 io dict) = IOCtx.mkCtx io dict
theorem p336 : P336 := fun io dict => rfl

def P343 : Prop := ∀ runtime io, m343 runtime io =
  if runtime.getColor io then [("color", .bool true)] else []
theorem p343 : P343 := fun _ _ => rfl

def P344 : Prop := ∀ (io : IOCtx.JIO), (m344 io) = IOCtx.ioproperties io
theorem p344 : P344 := fun io => rfl

def P346 : Prop := ∀ (io : IOCtx.JIO), (m346 io) = IOCtx.unwrapcontext io
theorem p346 : P346 := fun io => rfl

def P347 : Prop := ∀ (io : IOCtx.JIO), (m347 io) = IOCtx.unwrapcontext io
theorem p347 : P347 := fun io => rfl

def P349 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m349 io dict) = IOCtx.ioContextDict io dict
theorem p349 : P349 := fun io dict => rfl

def P353 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m353 io dict) = IOCtx.ioContextDict io dict
theorem p353 : P353 := fun io dict => rfl

def P358 : Prop := ∀ (io : IOCtx.JIO), (m358 io) = IOCtx.convertCtx io
theorem p358 : P358 := fun io => rfl

def P359 : Prop := ∀ (io : IOCtx.JIO), (m359 io) = IOCtx.convertCtx io
theorem p359 : P359 := fun io => rfl

def P360 : Prop := ∀ (io : IOCtx.JIO), (m360 io) = IOCtx.convertCtx io
theorem p360 : P360 := fun io => rfl

def P361 : Prop := ∀ (io : IOCtx.JIO), (m361 io) = IOCtx.convertCtx io
theorem p361 : P361 := fun io => rfl

def P363 : Prop := ∀ (io : IOCtx.JIO), (m363 io) = IOCtx.ioContext1 io
theorem p363 : P363 := fun io => rfl

def P364 : Prop := ∀ (io : IOCtx.JIO), (m364 io) = IOCtx.ioContext1 io
theorem p364 : P364 := fun io => rfl

def P366 : Prop := ∀ (io : IOCtx.JIO) (kv : String × IOCtx.PV), (m366 io kv) = IOCtx.ioContextPair io kv
theorem p366 : P366 := fun io kv => rfl

def P381 : Prop := ∀ (io context : IOCtx.JIO), (m381 io context) = IOCtx.ioContextIO io context
theorem p381 : P381 := fun io context => rfl

def P456 : Prop := ∀ (io : IOCtx.JIO) (kvs : List (String × IOCtx.PV)), (m456 io kvs) = IOCtx.ioContextPairs io kvs
theorem p456 : P456 := fun io kvs => rfl

def P458 : Prop := ∀ runtime ctx, m458 runtime ctx =
  match IOCtx.unwrapcontext ctx with
  | .plain base => ["IOContext(", runtime.renderBase base, ")"]
  | .ctx base _ => ["IOContext(", runtime.renderBase base, ")"]
theorem p458 : P458 := fun _ _ => rfl

def P460 : Prop := ∀ (io : IOCtx.JIO), (m460 io) = IOCtx.pipeReader io
theorem p460 : P460 := fun io => rfl

def P461 : Prop := ∀ (io : IOCtx.JIO), (m461 io) = IOCtx.pipeWriter io
theorem p461 : P461 := fun io => rfl

def P462 : Prop := ∀ io, (m462 io).2 = .lock
theorem p462 : P462 := by intro io; cases io <;> rfl

def P463 : Prop := ∀ io, (m463 io).2 = .unlock
theorem p463 : P463 := by intro io; cases io <;> rfl

def P465 : Prop := ∀ kv io, m465 kv io = IOCtx.inWith IOCtx.sameIdentity kv io
theorem p465 : P465 := fun _ _ => rfl

def P466 : Prop := ∀ (kv : String × IOCtx.PV) (base : IOCtx.BaseIO), (m466 kv base) = IOCtx.inCtx kv (.plain base)
theorem p466 : P466 := fun kv base => rfl

def P467 : Prop := ∀ (io : IOCtx.JIO) (key : String), (m467 io key) = IOCtx.haskeyCtx key io
theorem p467 : P467 := fun io key => rfl

def P468 : Prop := ∀ (base : IOCtx.BaseIO) (key : String), (m468 base key) = IOCtx.haskeyCtx key (.plain base)
theorem p468 : P468 := fun base key => rfl

def P469 : Prop := ∀ (io : IOCtx.JIO) (key : String), (m469 io key) = IOCtx.getindexCtx key io
theorem p469 : P469 := fun io key => rfl

def P470 : Prop := ∀ (base : IOCtx.BaseIO) (key : String), (m470 base key) = IOCtx.getindexCtx key (.plain base)
theorem p470 : P470 := fun base key => rfl

def P471 : Prop := ∀ (io : IOCtx.JIO) (key : String) (default : IOCtx.PV), (m471 io key default) = IOCtx.getCtx key default io
theorem p471 : P471 := fun io key default => rfl

def P472 : Prop := ∀ (base : IOCtx.BaseIO) (key : String) (default : IOCtx.PV), (m472 base key default) = IOCtx.getCtx key default (.plain base)
theorem p472 : P472 := fun base key default => rfl

def P473 : Prop := ∀ (io : IOCtx.JIO), (m473 io) = IOCtx.keysCtx io
theorem p473 : P473 := fun io => rfl

def P474 : Prop := ∀ (base : IOCtx.BaseIO), (m474 base) = IOCtx.keysCtx (.plain base)
theorem p474 : P474 := fun base => rfl

def P476 : Prop := ∀ (io : IOCtx.JIO), (m476 io) = IOCtx.displaysizeCtx io
theorem p476 : P476 := fun io => rfl

def P478 : Prop := ∀ (x : IOCtx.PV) (base : IOCtx.BaseIO), (m478 x base) = IOCtx.showCircular x (.plain base)
theorem p478 : P478 := fun x base => rfl

def P479 : Prop := ∀ (x : IOCtx.PV) (io : IOCtx.JIO), (m479 x io) = IOCtx.showCircular x io
theorem p479 : P479 := fun x io => rfl

def P520 : Prop := ∀ runtime io x, m520 runtime io x = runtime.showDefault io x
theorem p520 : P520 := fun _ _ _ => rfl

def P522 : Prop := ∀ runtime x, m522 runtime x = runtime.showOn runtime.stdout x
theorem p522 : P522 := fun _ _ => rfl

def P525 : Prop := ∀ runtime io x, m525 runtime io x =
  runtime.showDefaultInner io (runtime.inferenceBarrier x)
theorem p525 : P525 := fun _ _ _ => rfl

def P527 : Prop := ∀ runtime io x, m527 runtime io x =
  let fields := defaultFields runtime io x
  let bits := if !x.fields.isEmpty || x.byteSize = 0 then none
    else some (x.bytes, x.bitSize)
  [runtime.renderType x.typeId, "("] ++
  (match bits with
   | none =>
     if let some marker := runtime.showCircular io x then [marker] else
     let shown := fields.map fun field => match field with
       | .undef => "#undef"
       | .val text => text
     shown.zipIdx.flatMap fun (text, index) =>
       [text] ++ if index + 1 < fields.length then [", "] else []
   | some (bytes, nbits) =>
     let nbytes := (nbits + 7) / 8
     ["0x"] ++ (List.range nbytes).reverse.map (fun index =>
       let byte := (bytes.getD index 0).toNat
       if index = nbytes - 1 ∧ nbits % 8 ≠ 0 then
         Values.hexPad (byte % 2 ^ (nbits % 8)) ((nbits % 8 + 3) / 4)
       else Values.hexPad byte 2)) ++ [")"]
theorem p527 : P527 := fun _ _ _ => rfl

def P570 : Prop := ∀ runtime, m570 runtime =
  if runtime.isPureContext () then
    .error (.errorException "active_module() should not be called from a pure context")
  else match runtime.activeReplDefined (), runtime.activeRepl with
    | false, _ => .ok "Main"
    | true, none => .ok "Main"
    | true, some repl => .ok (runtime.invokeLatest repl)
theorem p570 : P570 := fun _ => rfl

def P583 : Prop := ∀ runtime io function compact fallback,
  HasResult (m583 runtime io function compact fallback) ∧
  (function.datatype.typeName.name = function.datatype.typeName.singletonName →
    m583 runtime io function compact fallback = functionFallback runtime fallback function) ∧
  (function.datatype.typeName.name ≠ function.datatype.typeName.singletonName → compact = true →
    m583 runtime io function compact fallback = function.datatype.typeName.singletonName)
theorem p583 : P583 := by
  intro runtime io function compact fallback
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h; simp [m583, showFunctionCore, h]
  · intro h hc; simp [m583, showFunctionCore, h, hc]

def P603 : Prop := ∀ runtime io function,
  m603 runtime io function = showFunctionCore runtime io function io.compact .showDefault
theorem p603 : P603 := fun _ _ _ => rfl

def P604 : Prop := ∀ runtime io function,
  m604 runtime io function = showFunctionCore runtime io function true .show
theorem p604 : P604 := fun _ _ _ => rfl

def P606 : Prop := ∀ io function, m606 io function =
  (if io.compact then "" else "Core.Intrinsics.") ++ function.datatype.typeName.singletonName
theorem p606 : P606 := fun _ _ => rfl

def P613 : Prop := ∀ function, m613 function = function.datatype.typeName.singletonName
theorem p613 : P613 := fun _ => rfl

def P615 : Prop := ∀ io, m615 io = ["Union{}"]
theorem p615 : P615 := fun _ => rfl

def P617 : Prop := ∀ runtime value, m617 runtime value =
  match runtime.unwrapUnionall value with
  | .dataType wrapperId => wrapperId = value.id
  | .other => false
theorem p617 : P617 := fun _ _ => rfl

def P622 : Prop := ∀ runtime io name value, m622 runtime io name value =
  io.dict.any fun binding =>
    binding.1 == "unionall_env" && match binding.2 with
    | .typeVar typevar => typevar.name == name && runtime.hasTypevar value typevar
    | .other _ => false
theorem p622 : P622 := fun _ _ _ _ => rfl

def P630 : Prop := ∀ name, m630 name = false
theorem p630 : P630 := fun _ => rfl

def P632 : Prop := ∀ upper, m632 upper = Remaining.modulesOf upper
theorem p632 : P632 := fun _ => rfl

def P633 : Prop := ∀ runtime value, m633 runtime value =
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
theorem p633 : P633 := fun _ _ => rfl

def P638 : Prop := ∀ runtime value, m638 runtime value =
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
theorem p638 : P638 := fun _ _ => rfl

def P639 : Prop := ∀ runtime input moduleName,
  runtime.dataModule (runtime.unwrapUnionall input) = some moduleName →
    m639 runtime input = [moduleName]
theorem p639 : P639 := by
  intro runtime input moduleName h
  simp [m639, modulesOfTypeBody, h]

def P654 : Prop := ∀ runtime value freeBefore, m654 runtime value freeBefore =
  if !runtime.hasFreeTypevars value then false
  else (runtime.findFreeTypevars value).any fun freeVar =>
    !(freeBefore.any fun previous => previous.id == freeVar.id)
theorem p654 : P654 := fun _ _ _ => rfl

def P674 : Prop := ∀ runtime alias,
  HasResult (m674 runtime alias) ∧
  (match alias with
   | .atom id => m674 runtime alias = .atom id
   | .unionAll binder body =>
     if binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId then
       m674 runtime alias = .unionAll binder (unboundedAlias runtime body)
     else outerBinderUnbounded runtime (m674 runtime alias) = true)
theorem p674 : P674 := by
  intro runtime alias
  refine ⟨hasResult _, ?_⟩
  cases alias with
  | atom id => rfl
  | unionAll binder body =>
    by_cases h : binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId
    · by_cases hb : unboundedAlias runtime body = body
      · simp only [h, if_true]
        unfold m674
        rw [unboundedAlias, if_pos h, if_pos hb]
        exact congrArg (AliasExpr.unionAll binder) hb.symm
      · simp only [h, if_true]
        unfold m674
        rw [unboundedAlias, if_pos h, if_neg hb]
        simp
    · simp only [h, if_false]
      unfold m674
      rw [unboundedAlias, if_neg h]
      simp only [outerBinderUnbounded, runtime.newTypeVarLower,
        runtime.newTypeVarUpper, beq_self_eq_true, Bool.and_self]

def P692 : Prop := ∀ context value, m692 context value =
  match context with
  | none => value
  | some io => io.dict.foldl (fun result binding =>
      if binding.1 == "unionall_env" then match binding.2 with
        | .typeVar freeVar => .unionAll freeVar result
        | .other _ => result
      else result) value
theorem p692 : P692 := fun _ _ => rfl

def P703 : Prop := ∀ runtime context input,
  HasResult (m703 runtime context input) ∧
  (input.id = runtime.anyId → m703 runtime context input = none) ∧
  (runtime.isTupleSubtype input = true → m703 runtime context input = none)
theorem p703 : P703 := by
  intro runtime context input
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h; simp [m703, makeTypealiasBody, h]
  · intro h; simp [m703, makeTypealiasBody, h]

def P769 : Prop := ∀ runtime symbol,
  m769 runtime symbol = (runtime.string symbol).contains '#'
theorem p769 : P769 := fun _ _ => rfl

def P771 : Prop := ∀ runtime parameter wheres elide env skip,
  HasResult (m771 runtime parameter wheres elide env skip) ∧
  (elide = 0 → m771 runtime parameter wheres elide env skip = false)
theorem p771 : P771 := by
  intro runtime parameter wheres elide env skip
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m771, showCanElideBody, h]

def P786 : Prop := ∀ runtime env orig wheres, (m786 runtime env orig wheres).2.IsPrefix wheres
theorem p786 : P786 := by
  intro runtime env orig wheres
  simp only [m786, showTypeparamsBody]
  exact List.take_prefix _ _

def P789 : Prop := ∀ runtime parameter other, m789 runtime parameter other =
  match other with
  | .other _ => false
  | .typeVar value =>
    runtime.structurallyEquivalent parameter.upper value.upper &&
      runtime.structurallyEquivalent parameter.lower value.lower
theorem p789 : P789 := fun _ _ _ => rfl

def P832 : Prop := ∀ runtime reference, m832 runtime reference =
  (if runtime.compact then [] else match runtime.fromModule with
   | none => [runtime.renderModule reference.moduleName, "."]
   | some origin => if runtime.visible reference.name reference.moduleName origin then []
     else [runtime.renderModule reference.moduleName, "."]) ++ [reference.name]
theorem p832 : P832 := fun _ _ => rfl

def P847 : Prop := ∀ runtime alias env wheres,
  (m847 runtime alias env wheres).2.IsPrefix wheres
theorem p847 : P847 := by
  intro runtime alias env wheres
  simp only [m847, showTypealiasBody]
  split
  · exact List.prefix_refl _
  · exact List.take_prefix _ _

def P864 : Prop := ∀ runtime context env value,
  HasResult (m864 runtime context env value) ∧
  (context = none → env = [] → (∀ id, value = .atom id → m864 runtime context env value = []))
theorem p864 : P864 := by
  intro runtime context env value
  refine ⟨hasResult _, ?_⟩
  intro hc he id hv
  subst context; subst env; subst value
  simp [m864, makeWheresBody, outerWheres]

def P894 : Prop := ∀ runtime wheres,
  HasResult (m894 runtime wheres) ∧ (wheres = [] → m894 runtime wheres = [])
theorem p894 : P894 := by
  intro runtime wheres
  refine ⟨hasResult _, ?_⟩
  intro h; subst h; rfl

def P908 : Prop := ∀ runtime value,
  (m908 runtime value).1 = (runtime.makeAlias value).isSome
theorem p908 : P908 := by
  intro runtime value
  cases h : runtime.makeAlias value <;> simp [m908, showTypealiasDispatchBody, h]

def P917 : Prop := ∀ runtime input,
  HasResult (m917 runtime input) ∧
  (input.id = runtime.base.anyId → m917 runtime input = ([], runtime.emptyUnion))
theorem p917 : P917 := by
  intro runtime input
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m917, makeTypealiasesBody, h]

def P1002 : Prop := ∀ runtime input,
  (m1002 runtime input).1 = !(makeTypealiasesBody runtime.aliases input).1.isEmpty
theorem p1002 : P1002 := by
  intro runtime input
  generalize h : makeTypealiasesBody runtime.aliases input = result
  rcases result with ⟨aliases, applied⟩
  cases aliases <;> simp [m1002, showUnionAliasesBody, h]

def P1046 : Prop := ∀ runtime input,
  runtime.printWithoutParams input = false → (runtime.makeAlias input).isSome = true →
    (m1046 runtime input).head? = some (.plain (runtime.renderCompact input))
theorem p1046 : P1046 := by
  intro runtime input hp ha
  simp [m1046, showTypePlainBody, hp, ha]

def P1071 : Prop := ∀ runtime value, m1071 runtime value =
  "Core.TypeEgal{" ++ runtime.renderType (runtime.typeParameter value) ++ "}"
theorem p1071 : P1071 := fun _ _ => rfl

def P1076 : Prop := ∀ runtime value,
  value.kind = .bottom → m1076 runtime value = "Union{}"
theorem p1076 : P1076 := by
  intro runtime value h
  cases value with
  | mk object kind => cases kind <;> simp_all [m1076, showAnyTypeBody]

def P1091 : Prop := ∀ runtime value, m1091 runtime value =
  (if runtime.compact then "Type{" else "TypeEq{") ++
    runtime.renderType (runtime.typeParameter value) ++ "}"
theorem p1091 : P1091 := fun _ _ => rfl

def P1096 : Prop := ∀ runtime input,
  HasResult (m1096 runtime input) ∧
  (runtime.isTypeEgal input = true → m1096 runtime input = runtime.showTypeEgal input)
theorem p1096 : P1096 := by
  intro runtime input
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1096, showTypeDispatchBody, h]

def P1159 : Prop := ∀ runtime symbol parent origin,
  HasResult (m1159 runtime symbol parent origin) ∧
  (runtime.isDeprecated parent symbol = true → m1159 runtime symbol parent origin = false)
theorem p1159 : P1159 := by
  intro runtime symbol parent origin
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1159, isVisibleBody, h]

def P1179 : Prop := ∀ runtime typeName globalName,
  HasResult (m1179 runtime typeName globalName) ∧
  (globalName = none → m1179 runtime typeName globalName = false)
theorem p1179 : P1179 := by
  intro runtime typeName globalName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1179, isGlobalFunctionBody, h]

def P1191 : Prop := ∀ runtime typeName,
  HasResult (m1191 runtime typeName) ∧
  (runtime.bindingDefined typeName = false → m1191 runtime typeName = none)
theorem p1191 : P1191 := by
  intro runtime typeName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1191, checkWorldBody, h]

def P1211 : Prop := ∀ runtime typeName,
  HasResult (m1211 runtime typeName) ∧
  (typeName.id = runtime.unionAllNameId → m1211 runtime typeName = "UnionAll")
theorem p1211 : P1211 := by
  intro runtime typeName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1211, showTypeNameBody, h]

def P1248 : Prop := ∀ runtime datatype,
  HasResult (m1248 runtime datatype) ∧
  (datatype.name.id ≠ runtime.pairsTypeNameId → m1248 runtime datatype = none)
theorem p1248 : P1248 := by
  intro runtime datatype
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1248, maybeKwargsBody, h]

def P1266 : Prop := ∀ runtime datatype wheres,
  datatype.name.id = runtime.tupleNameId → datatype.parameters = [] →
    m1266 runtime datatype wheres = "Tuple{}"
theorem p1266 : P1266 := by
  intro runtime datatype wheres hn hp
  simp [m1266, showDatatypeBody, hn, hp]

def P1362 : Prop := ∀ runtime types,
  m1362 runtime [] types = ""
theorem p1362 : P1362 := by unfold P1362; intros; rfl

def P1378 : Prop := ∀ runtime type,
  type.id = runtime.anyTypeId → m1378 runtime type = runtime.render type
theorem p1378 : P1378 := by
  intro runtime type h
  simp [m1378, showSupertypesBody, h]

def P1386 : Prop := ∀ runtime type, m1386 runtime type = m1378 runtime type
theorem p1386 : P1386 := fun _ _ => rfl

def P1406 : Prop := ∀ runtime expressions,
  (m1406 runtime expressions).lines.length = expressions.length
theorem p1406 : P1406 := by
  intro runtime expressions
  simp [m1406, showMacroBody]

def P1416 : Prop := ∀ runtime name,
  m1416 runtime name = "typename(" ++ m1211 runtime name ++ ")"
theorem p1416 : P1416 := fun _ _ => rfl

def P1422 : Prop := ∀ runtime io, m1422 runtime io =
  runtime.nonmissingType (runtime.nonnothingType io.typeinfo)
theorem p1422 : P1422 := fun _ _ => rfl

def P1423 : Prop := ∀ runtime io value, m1423 runtime io value =
  [if runtime.nonmissingType (runtime.nonnothingType io.typeinfo) = runtime.boolType then
    if value then "1" else "0" else if value then "true" else "false"]
theorem p1423 : P1423 := fun _ _ _ => rfl

def P1424 : Prop := ∀ io, m1424 io = ["nothing"]
theorem p1424 : P1424 := fun _ => rfl

def P1425 : Prop := ∀ runtime value, m1425 runtime value = [runtime.stringSigned value]
theorem p1425 : P1425 := fun _ _ => rfl

def P1426 : Prop := ∀ runtime io value, m1426 runtime io value =
  if io.hexUnsigned then ["0x", runtime.stringUnsignedHex value ((runtime.bitSize value + 3) / 4)]
  else if io.typeinfo = runtime.typeOfUnsigned value then [runtime.stringUnsignedDecimal value]
  else [runtime.renderType (runtime.typeOfUnsigned value), "(", runtime.stringUnsignedDecimal value, ")"]
theorem p1426 : P1426 := fun _ _ _ => rfl

def P1437 : Prop := ∀ runtime value, m1437 runtime value = [runtime.stringUnsignedDecimal value]
theorem p1437 : P1437 := fun _ _ => rfl

def P1439 : Prop := ∀ runtime pair, m1439 runtime pair =
  (runtime.typeOfValue pair.first = pair.firstParameter &&
    runtime.typeOfValue pair.second = pair.secondParameter)
theorem p1439 : P1439 := fun _ _ => rfl

def P1443 : Prop := ∀ io x : String, m1443 io x = true
theorem p1443 : P1443 := fun _ _ => rfl

def P1444 : Prop := ∀ runtime function, m1444 runtime function =
  !runtime.isOperator (runtime.symbolOfFunction function)
theorem p1444 : P1444 := fun _ _ => rfl

def P1448 : Prop := ∀ runtime io pair, m1448 runtime io pair =
  !(hasTightTypeBody runtime pair || io.typeinfo = runtime.typeOfPair pair)
theorem p1448 : P1448 := fun _ _ _ => rfl

def P1450 : Prop := ∀ runtime io pair, m1450 runtime io pair =
  if runtime.pairIsa pair io.typeinfo && runtime.subtype io.typeinfo runtime.pairSupertype then
    (runtime.fieldType io.typeinfo 1, runtime.fieldType io.typeinfo 2)
  else (runtime.anyType, runtime.anyType)
theorem p1450 : P1450 := fun _ _ _ => rfl

def P1457 : Prop := ∀ runtime io pair,
  HasResult (m1457 runtime io pair) ∧
  (pairDelimitedBody runtime io pair = true → m1457 runtime io pair =
    [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second])
theorem p1457 : P1457 := by
  intro runtime io pair
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1457, showPairBody, h]

def P1469 : Prop := ∀ runtime pair, m1469 runtime pair =
  [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
theorem p1469 : P1469 := fun _ _ => rfl

def P1474 : Prop := ∀ runtime module,
  HasResult (m1474 runtime module) ∧
  (runtime.isRootModule module = true → m1474 runtime module = [module.name])
theorem p1474 : P1474 := by
  intro runtime module
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1474, showModuleBody, h]

def P1484 : Prop := ∀ runtime module,
  HasResult (m1484 runtime module) ∧
  (module.parentId = module.id → runtime.moduleCount > 0 →
    m1484 runtime module = [runtime.showSymbol module.name])
theorem p1484 : P1484 := by
  intro runtime module
  refine ⟨hasResult _, ?_⟩
  intro hp hf
  cases h : runtime.moduleCount with
  | zero => omega
  | succ fuel =>
    simp only [m1484, h, printFullnameBody]
    rw [hp, runtime.lookupSelf]
    simp

def P1495 : Prop := ∀ runtime source,
  m1495 runtime source = sourceSlotnamesBody runtime source.slotnames
theorem p1495 : P1495 := fun _ _ => rfl

def P1496 : Prop := ∀ runtime slotnames,
  HasResult (m1496 runtime slotnames) ∧ (slotnames = [] → m1496 runtime slotnames = [])
theorem p1496 : P1496 := by
  intro runtime slotnames
  refine ⟨hasResult _, ?_⟩
  intro h; subst h; rfl

def P1518 : Prop := ∀ runtime miValue,
  m1518 runtime miValue = showMethodInstanceBody runtime miValue false
theorem p1518 : P1518 := fun _ _ => rfl

def P1519 : Prop := ∀ runtime codeValue,
  HasResult (m1519 runtime codeValue) ∧
  (codeValue.owner.isSome = true → ∃ stem, m1519 runtime codeValue = stem ++ " (foreign)")
theorem p1519 : P1519 := by
  intro runtime codeValue
  refine ⟨hasResult _, ?_⟩
  intro h
  cases ho : codeValue.owner with
  | none => simp [ho] at h
  | some owner =>
    cases hd : codeValue.definition with
    | methodInstance mi =>
      exact ⟨"CodeInstance for " ++ showMethodInstanceBody runtime mi false,
        by simp [m1519, showCodeInstanceBody, ho, hd]⟩
    | abiOverride mi =>
      exact ⟨"CodeInstance for " ++ showMethodInstanceBody runtime mi false ++
        " (ABI Overridden)", by simp [m1519, showCodeInstanceBody, ho, hd]⟩

def P1533 : Prop := ∀ runtime miValue fromStackframe,
  HasResult (m1533 runtime miValue fromStackframe) ∧
  (fromStackframe = true → match miValue.definition with
    | .toplevel _ => m1533 runtime miValue fromStackframe = "Toplevel MethodInstance thunk"
    | .method _ => True)
theorem p1533 : P1533 := by
  intro runtime miValue fromStackframe
  refine ⟨hasResult _, ?_⟩
  intro h; subst h
  cases miValue with
  | mk id definition specTypes cache =>
    cases definition <;> simp [m1533, showMethodInstanceBody]

def P1562 : Prop := ∀ runtime array op delim close delimOne first last,
  HasResult (m1562 runtime array op delim close delimOne first last) ∧
  (∀ marker, runtime.showCircular array = some marker →
    m1562 runtime array op delim close delimOne first last = [op, marker, close])
theorem p1562 : P1562 := by
  intro runtime array op delim close delimOne first last
  refine ⟨hasResult _, ?_⟩
  intro marker h
  simp [m1562, Containers.showDelimArray, h]

def P1591 : Prop := ∀ runtime iterator op delim close delimOne first count,
  HasResult (m1591 runtime iterator op delim close delimOne first count) ∧
  (∀ marker, runtime.showCircular iterator = some marker →
    m1591 runtime iterator op delim close delimOne first count = [op, marker, close])
theorem p1591 : P1591 := by
  intro runtime iterator op delim close delimOne first count
  refine ⟨hasResult _, ?_⟩
  intro marker h
  simp [m1591, showDelimIteratorBody, h]

def P1625 : Prop := ∀ runtime tuple,
  m1625 runtime tuple = m1562 runtime tuple "(" "," ")" true 1 tuple.slots.length
theorem p1625 : P1625 := fun _ _ => rfl

def P1626 : Prop := ∀ runtime vector,
  m1626 runtime vector = m1562 runtime vector "svec(" "," ")" false 1 vector.slots.length
theorem p1626 : P1626 := fun _ _ => rfl

def P1628 : Prop := ∀ runtime io symbol,
  m1628 runtime io symbol = runtime.showQuoteSymbol io symbol 0 0
theorem p1628 : P1628 := fun _ _ _ => rfl

def P1666 : Prop := ∀ runtime io expression,
  m1666 runtime io expression = runtime.showUnquoted ⟨false⟩ expression 0 (-1)
theorem p1666 : P1666 := fun _ _ _ => rfl

def P1667 : Prop := ∀ runtime io expression,
  m1667 runtime io expression = runtime.showQuoteExpr ⟨true⟩ expression 0 (-1)
theorem p1667 : P1667 := fun _ _ _ => rfl

def P1668 : Prop := ∀ runtime io expression,
  m1668 runtime io expression = runtime.showUnquoted io expression 0 0
theorem p1668 : P1668 := fun _ _ _ => rfl

def P1669 : Prop := ∀ runtime io expression indent,
  m1669 runtime io expression indent = runtime.showUnquoted io expression indent 0
theorem p1669 : P1669 := fun _ _ _ _ => rfl

def P1670 : Prop := ∀ runtime io value,
  m1670 runtime io value = runtime.showFallback io value
theorem p1670 : P1670 := fun _ _ _ => rfl

def P1671 : Prop := ∀ runtime io expression indent prec quoteLevel,
  m1671 runtime io expression indent prec quoteLevel =
    runtime.showUnquoted io expression indent prec
theorem p1671 : P1671 := fun _ _ _ _ _ _ => rfl

def P1713 : Prop := ∀ runtime symbol, m1713 runtime symbol = runtime.precedence symbol
theorem p1713 : P1713 := fun _ _ => rfl

def P1714 : Prop := ∀ x : String, m1714 x = 0
theorem p1714 : P1714 := fun _ => rfl

def P1739 : Prop := ∀ runtime symbol,
  runtime.precedence symbol ∈ [runtime.arrow, runtime.assignment, runtime.controlFlow,
    runtime.pair, runtime.power] → m1739 runtime symbol = .right
theorem p1739 : P1739 := by
  intro runtime symbol h
  simp [m1739, operatorAssociativityBody, h]

def P1750 : Prop := ∀ ex : DelimElement, m1750 ex = false
theorem p1750 : P1750 := fun _ => rfl

def P1751 : Prop := ∀ node : QuoteNodeValue, m1751 node = true
theorem p1751 : P1751 := fun _ => rfl

def P1752 : Prop := ∀ expression, m1752 expression =
  ((expression.head = "quote" || expression.head = "inert") && expression.args.length = 1)
theorem p1752 : P1752 := fun _ => rfl

def P1754 : Prop := ∀ node, m1754 node = node.value
theorem p1754 : P1754 := fun _ => rfl

def P1755 : Prop := ∀ expression, m1755 expression =
  match expression.args with | value :: _ => .ok value | [] => .error .boundsError
theorem p1755 : P1755 := fun _ => rfl

def P1762 : Prop := ∀ runtime io text color, m1762 runtime io text color =
  if runtime.colorEnabled io then [.styled text color true]
  else [.plain (runtime.uppercase text)]
theorem p1762 : P1762 := fun _ _ _ _ => rfl

def P1766 : Prop := ∀ runtime line, m1766 runtime line =
  [.styled ("#= line " ++ runtime.renderLine line ++ " =#") "light_black" false]
theorem p1766 : P1766 := fun _ _ => rfl

def P1767 : Prop := ∀ runtime line file, m1767 runtime line file =
  [.styled ("#= " ++ runtime.renderFile file ++ ":" ++ runtime.renderLine line ++ " =#")
    "light_black" false]
theorem p1767 : P1767 := fun _ _ _ => rfl

def P1768 : Prop := ∀ runtime line, m1768 runtime line = m1766 runtime line
theorem p1768 : P1768 := fun _ _ => rfl

def P1771 : Prop := ∀ runtime head indent quoteLevel,
  m1771 runtime head [] (.expr "block" []) indent quoteLevel =
    head ++ "\n" ++ String.ofList (List.replicate indent.toNat ' ')
theorem p1771 : P1771 := by
  intro runtime head indent quoteLevel
  simp [m1771, showAstBlockBody]

def P1790 : Prop := ∀ runtime head body indent quoteLevel,
  m1790 runtime head body indent quoteLevel = m1771 runtime head [] body indent quoteLevel
theorem p1790 : P1790 := fun _ _ _ _ _ => rfl

def P1791 : Prop := ∀ runtime head arguments body indent quoteLevel,
  m1791 runtime head (.expr "block" arguments) body indent quoteLevel =
    m1771 runtime head arguments body indent quoteLevel
theorem p1791 : P1791 := by unfold P1791; intros; rfl

def P1800 : Prop := ∀ runtime separator indent prec quoteLevel encloseOperators keyword,
  m1800 runtime [] separator indent prec quoteLevel encloseOperators keyword = ""
theorem p1800 : P1800 := by unfold P1800; intros; rfl

def P1828 : Prop := ∀ runtime openToken items separator closeToken indent prec quoteLevel encloseOperators keyword,
  m1828 runtime openToken items separator closeToken indent prec quoteLevel encloseOperators keyword =
    openToken ++ m1800 runtime items separator indent prec quoteLevel encloseOperators keyword ++ closeToken
theorem p1828 : P1828 := fun _ _ _ _ _ _ _ _ _ _ => rfl

def P1837 : Prop := ∀ runtime head reference indent quoteLevel keyword,
  head ≠ "." →
  runtime.callDelimiters head = ("(", ")") →
  m1837 runtime head (.globalRef reference) [] indent quoteLevel keyword =
    runtime.renderUnquoted (.globalRef reference) indent 0 quoteLevel ++ "()"
theorem p1837 : P1837 := by
  intro runtime head reference indent quoteLevel keyword hdot h
  simp [m1837, showAstCallBody, showAstListBody, h, hdot, String.append_assoc]

def P1867 : Prop := ∀ runtime symbol allowMacroname,
  HasResult (m1867 runtime symbol allowMacroname) ∧
  (runtime.isValidIdentifier symbol = true →
    m1867 runtime symbol allowMacroname = runtime.string symbol)
theorem p1867 : P1867 := by
  intro runtime symbol allowMacroname
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1867, showSymBody, h]

def P1880 : Prop := ∀ runtime io value,
  HasResult (m1880 runtime io value) ∧
  (runtime.maxId io < value.id →
    m1880 runtime io value = [.styled ("%" ++ toString value.id) "red" false])
theorem p1880 : P1880 := by
  intro runtime io value
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1880, showSSABody, h]

def P1895 : Prop := ∀ runtime symbol, m1895 runtime symbol = showSymBody runtime symbol false
theorem p1895 : P1895 := fun _ _ => rfl

def P1896 : Prop := ∀ runtime node,
  m1896 runtime node = showLineBody runtime node.line node.file
theorem p1896 : P1896 := fun _ _ => rfl

def P1897 : Prop := ∀ label, m1897 label = "goto %" ++ toString label
theorem p1897 : P1897 := fun label => rfl

def P1898 : Prop := ∀ runtime reference,
  m1898 runtime reference = showGlobalRefBody runtime reference false
theorem p1898 : P1898 := fun _ _ => rfl

def P1899 : Prop := ∀ runtime partition,
  m1899 runtime partition = showGlobalRefBody runtime partition.owner false
theorem p1899 : P1899 := fun _ _ => rfl

def P1902 : Prop := ∀ runtime reference allowMacroname,
  m1902 runtime reference allowMacroname = showGlobalRefBody runtime reference allowMacroname
theorem p1902 : P1902 := fun _ _ _ => rfl

def P1914 : Prop := ∀ io slot,
  (io.sourceSlotnames.isSome = true → slot.id = 0 → m1914 io slot = .error .boundsError) ∧
  HasResult (m1914 io slot)
theorem p1914 : P1914 := by
  intro io slot
  refine ⟨?_, hasResult _⟩
  intro hs hid
  cases slot with
  | mk id =>
    simp only at hid
    subst id
    cases h : io.sourceSlotnames with
    | none => simp [h] at hs
    | some names => simp [m1914, showSlotBody, h]

def P1924 : Prop := ∀ runtime io node indent,
  HasResult (m1924 runtime io node indent) ∧
  (∀ symbol, node.value = .symbol symbol →
    m1924 runtime io node indent = showQuotedBody runtime io (.symbol symbol) indent 0)
theorem p1924 : P1924 := by
  intro runtime io node indent
  refine ⟨hasResult _, ?_⟩
  intro symbol h
  cases node with
  | mk value => simp only at h; subst value; rfl

def P1937 : Prop := ∀ runtime io symbol indent quoteLevel,
  runtime.quotedIds.contains symbol.id = true →
  m1937 runtime io (.symbol symbol) indent quoteLevel =
    ":(" ++ runtime.symbols.string symbol ++ ")"
theorem p1937 : P1937 := by
  intro runtime io symbol indent quoteLevel h
  have hm : symbol.id ∈ runtime.quotedIds := by
    rw [← List.contains_iff_mem]
    exact h
  simp [m1937, showQuotedBody, hm]

def P1962 : Prop := ∀ runtime expression indent quoteLevel,
  let collected := collectGenerator expression
  m1962 runtime expression indent quoteLevel =
    runtime.showUnquoted collected.1 indent 0 quoteLevel ++
      String.join (collected.2.map fun range => " for " ++
        runtime.showList range ", " indent 0 quoteLevel)
theorem p1962 : P1962 := fun _ _ _ _ => rfl

def P1983 : Prop := ∀ node allowAs, m1983 node allowAs = validImportPathBody node allowAs
theorem p1983 : P1983 := fun _ _ => rfl

def P1990 : Prop := ∀ runtime symbol quoteLevel,
  m1990 runtime (.symbol symbol) quoteLevel =
    .ok (runtime.renderUnquoted (.symbol symbol) 0 0 0)
theorem p1990 : P1990 := by
  unfold P1990 m1990 showImportPathBody
  intros
  rfl

def P2023 : Prop := ∀ runtime reference,
  m2023 runtime (.globalRef reference) = .expr "macroname" [.globalRef reference]
theorem p2023 : P2023 := by unfold P2023; intros; rfl

def P2034 : Prop := ∀ runtime reference macroName,
  m2034 runtime reference macroName =
    isCoreMacroBody reference (runtime.symbolFromString macroName)
theorem p2034 : P2034 := fun _ _ _ => rfl

def P2035 : Prop := ∀ reference macroName, m2035 reference macroName =
  (reference.moduleValue.name = "Core" && reference.name.id = macroName.id)
theorem p2035 : P2035 := fun _ _ => rfl

def P2036 : Prop := ∀ arg macroName, m2036 arg macroName = false
theorem p2036 : P2036 := fun _ _ => rfl

def P2037 : Prop := ∀ arg macroName, m2037 arg macroName = false
theorem p2037 : P2037 := fun _ _ => rfl

def P2043 : Prop := ∀ runtime expression,
  m2043 runtime expression = "$(Expr(" ++ runtime.render expression.head ++
    String.join (expression.args.map fun arg => ", " ++ runtime.render arg) ++ "))"
theorem p2043 : P2043 := fun _ _ => rfl

def P2054 : Prop := ∀ runtime unquoteFallback beginsym expression indent prec quoteLevel,
  (∀ id, expression = .other id →
    m2054 runtime unquoteFallback beginsym expression indent prec quoteLevel =
      runtime.ast.renderUnquoted (.other id) indent prec quoteLevel)
theorem p2054 : P2054 := by
  intro runtime unquoteFallback beginsym expression indent prec quoteLevel id h
  subst expression; rfl

def P2608 : Prop := ∀ runtime name, m2608 runtime name =
  runtime.symbolFromString (demangleFunctionBody (runtime.string name))
theorem p2608 : P2608 := fun _ _ => rfl

def P2609 : Prop := ∀ name, m2609 name =
  let pieces := name.splitOn "#"
  match pieces with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name
theorem p2609 : P2609 := fun _ => rfl

def P2620 : Prop := ∀ runtime input demangle argumentName html qualified,
  runtime.asDataType (runtime.unwrapUnionall input) = none →
  runtime.isType input = false → html = true →
  m2620 runtime input demangle argumentName html qualified =
    "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
theorem p2620 : P2620 := by
  intro runtime input demangle argumentName html qualified hd ht hh
  simp [m2620, showSignatureFunctionBody, hd, ht, hh]

def P2645 : Prop := ∀ io pieces color bold, m2645 io pieces color bold =
  if io.backtrace then [.styled (String.join pieces) color bold]
  else [.plain (String.join pieces)]
theorem p2645 : P2645 := fun _ _ _ _ => rfl

def P2653 : Prop := ∀ runtime name signature demangle kwargs argumentNames qualified hasFirst,
  signature = .tupleRoot → m2653 runtime name signature demangle kwargs argumentNames qualified hasFirst =
    runtime.symbols.string (if demangle then runtime.symbols.symbolFromString
      (demangleFunctionBody (runtime.symbols.string name)) else name) ++ "(...)"
theorem p2653 : P2653 := by
  intro runtime name signature demangle kwargs argumentNames qualified hasFirst h
  subst signature; rfl

def P2712 : Prop := ∀ runtime context text,
  HasResult (m2712 runtime context text) ∧
  (context.limitedFlag = none → m2712 runtime context text = (text, none))
theorem p2712 : P2712 := by
  intro runtime context text
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2712, typeLimitedBody, h]

def P2726 : Prop := ∀ (tw : Char → Nat) (s : List Char) (width : Int) (maxDepth : Option Int), (m2726 tw s width maxDepth) = Truncate.typeDepthLimit tw s width maxDepth
theorem p2726 : P2726 := fun tw s width maxDepth => rfl

def P2734 : Prop := ∀ state bit, m2734 state bit = ((state &&& bit) != 0)
theorem p2734 : P2734 := fun _ _ => rfl

def P2735 : Prop := ∀ state, m2735 state =
  ((state &&& 2) != 0 || (state &&& 4) != 0)
theorem p2735 : P2735 := fun _ => rfl

def P2736 : Prop := ∀ state bit, m2736 state bit = (state ||| bit)
theorem p2736 : P2736 := fun _ _ => rfl

def P2737 : Prop := ∀ state bit, m2737 state bit = state - (state &&& bit)
theorem p2737 : P2737 := fun _ _ => rfl

def P2818 : Prop := ∀ runtime io type color innerColor useColor,
  m2818 runtime io type color innerColor useColor =
    printTypeBicolorText (runtime.renderType type io) color innerColor useColor
theorem p2818 : P2818 := fun _ _ _ _ _ _ => rfl

def P2823 : Prop := ∀ text color innerColor useColor,
  HasResult (m2823 text color innerColor useColor) ∧
  (useColor = false → m2823 text color innerColor useColor = [.plain text])
theorem p2823 : P2823 := by
  intro text color innerColor useColor
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2823, printTypeBicolorText, h]

def P2840 : Prop := ∀ node, m2840 node = .value node
theorem p2840 : P2840 := fun _ => rfl

def P2841 : Prop := ∀ value, m2841 value = .value value
theorem p2841 : P2841 := fun _ => rfl

def P2842 : Prop := ∀ runtime symbol, m2842 runtime symbol =
  resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
theorem p2842 : P2842 := fun _ _ => rfl

def P2843 : Prop := ∀ runtime id,
  m2843 runtime (.other id) = .value (.other id)
theorem p2843 : P2843 := by unfold P2843; intros; rfl

def P2852 : Prop := ∀ runtime reference,
  (runtime.isDefined reference = false → m2852 runtime reference = .nothing) ∧
  HasResult (m2852 runtime reference)
theorem p2852 : P2852 := by
  intro runtime reference
  refine ⟨?_, hasResult _⟩
  intro h; simp [m2852, resolveGlobalBody, h]

def P2860 : Prop := ∀ runtime expression, m2860 runtime expression =
  isModuleCallBody runtime expression
theorem p2860 : P2860 := fun _ _ => rfl

def P2866 : Prop := ∀ runtime context typevar,
  typevarInEnv context typevar = true →
    m2866 runtime context typevar = runtime.renderName typevar.name
theorem p2866 : P2866 := by
  intro runtime context typevar h
  simp [m2866, showTypevarBody, h]

def P2873 : Prop := ∀ runtime bound, m2873 runtime bound =
  (if runtime.isUnionAll bound && !runtime.printWithoutParams bound then "(" else "") ++
    runtime.renderBound bound ++
    if runtime.isUnionAll bound && !runtime.printWithoutParams bound then ")" else ""
theorem p2873 : P2873 := fun _ _ => rfl

def P2901 : Prop := ∀ runtime value,
  HasResult (m2901 runtime value) ∧
  (value.typeField = none → m2901 runtime value = "Vararg")
theorem p2901 : P2901 := by
  intro runtime value
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2901, showVarargBody, h]

def P2916 : Prop := ∀ runtime source debugInfo, m2916 runtime source debugInfo =
  "CodeInfo(\n" ++ runtime.showIR source
    (source.slotnames.map (sourceSlotnamesBody runtime.slotRuntime))
    (runtime.debugInfoConfig debugInfo source) ++ ")"
theorem p2916 : P2916 := fun _ _ _ => rfl

def P2931 : Prop := ∀ io argument, m2931 io argument = m1914 io ⟨argument.n⟩
theorem p2931 : P2931 := fun _ _ => rfl

def P2933 : Prop := ∀ runtime node indent,
  m2933 runtime node indent = showPhiBody runtime node indent "%"
theorem p2933 : P2933 := fun _ _ _ => rfl

def P2934 : Prop := ∀ runtime values indent labelPrefix,
  m2934 runtime ⟨[], values⟩ indent labelPrefix = "φ ()"
theorem p2934 : P2934 := by unfold P2934; intros; rfl

def P2949 : Prop := ∀ runtime node indent,
  m2949 runtime node indent = showPhiCBody runtime node indent
theorem p2949 : P2949 := fun _ _ _ => rfl

def P2959 : Prop := ∀ runtime node indent, m2959 runtime node indent =
  [.plain ("π (" ++ runtime.renderUnquoted node.value indent ++ ", "),
    .styled (runtime.renderType node.type) "cyan" false, .plain ")"]
theorem p2959 : P2959 := fun _ _ _ => rfl

def P2967 : Prop := ∀ runtime indent,
  m2967 runtime ⟨none⟩ indent = "ϒ (#undef)"
theorem p2967 : P2967 := by unfold P2967; intros; rfl

def P2975 : Prop := ∀ runtime indent,
  m2975 runtime ⟨none⟩ indent = "unreachable"
theorem p2975 : P2975 := by unfold P2975; intros; rfl

def P2984 : Prop := ∀ runtime node indent,
  m2984 runtime node indent = showGotoIfNotBody runtime node indent "%"
theorem p2984 : P2984 := fun _ _ _ => rfl

def P2985 : Prop := ∀ runtime node indent labelPrefix,
  m2985 runtime node indent labelPrefix = showGotoIfNotBody runtime node indent labelPrefix
theorem p2985 : P2985 := fun _ _ _ _ => rfl

def P2990 : Prop := ∀ runtime limit depth indent value,
  value = .simpleVector [] → m2990 runtime limit depth indent value = "empty SimpleVector"
theorem p2990 : P2990 := by
  intro runtime limit depth indent value h
  subst value; cases depth <;> simp [m2990, dumpBody]

def P3010 : Prop := ∀ runtime limit depth indent value,
  value = .bottom → m3010 runtime limit depth indent value = runtime.renderBottom
theorem p3010 : P3010 := by
  intro runtime limit depth indent value h
  subst value; cases depth <;> simp [m3010, dumpBody]

def P3043 : Prop := ∀ runtime module,
  m3043 runtime module = "Module " ++ runtime.renderModule module
theorem p3043 : P3043 := fun _ _ => rfl

def P3044 : Prop := ∀ runtime value,
  m3044 runtime value = "String " ++ runtime.renderString value
theorem p3044 : P3044 := fun _ _ => rfl

def P3045 : Prop := ∀ runtime symbol,
  m3045 runtime symbol = "Symbol " ++ runtime.renderSymbol symbol
theorem p3045 : P3045 := fun _ _ => rfl

def P3046 : Prop := ∀ runtime type, m3046 runtime type = runtime.renderType type
theorem p3046 : P3046 := fun _ _ => rfl

def P3047 : Prop := ∀ runtime address, m3047 runtime address = runtime.renderPointer address
theorem p3047 : P3047 := fun _ _ => rfl

def P3049 : Prop := ∀ runtime depth indent slots first,
  first > 0 → m3049 runtime depth indent slots first (first - 1) = ""
theorem p3049 : P3049 := by
  intro runtime depth indent slots first h
  simp [m3049, dumpElementsBody, Nat.sub_add_cancel (by omega : 1 ≤ first)]

def P3061 : Prop := ∀ runtime limit depth indent array,
  (∀ elementType shape slots, array = .array elementType shape true slots →
    m3061 runtime limit depth indent array =
      "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ") " ++
        runtime.renderValue (.array elementType shape true slots))
theorem p3061 : P3061 := by
  intro runtime limit depth indent array elementType shape slots h
  subst array; simp [m3061, dumpBody]

def P3087 : Prop := ∀ runtime depth indent datatype,
  datatype.isAny = true → depth = 0 →
    m3087 runtime depth indent datatype =
      (if datatype.isMutable && datatype.isStruct then "mutable " else "") ++
      (if datatype.isStruct && !datatype.isTuple then "struct " else "") ++
      (if datatype.isPrimitive then "primitive type " else "") ++
      (if datatype.isAbstract then "abstract type " else "") ++
      runtime.renderType datatype.typeId
theorem p3087 : P3087 := by
  intro runtime depth indent datatype ha hd
  subst depth
  simp [m3087, dumpBody, ha]

def P3130 : Prop := ∀ runtime limit maxDepth value,
  m3130 runtime limit maxDepth value = dumpBody runtime limit maxDepth "" value ++ "\n"
theorem p3130 : P3130 := fun _ _ _ _ => rfl

def P3163 : Prop := ∀ runtime maxDepth value,
  m3163 runtime maxDepth value = m3130 runtime true maxDepth value
theorem p3163 : P3163 := fun _ _ _ => rfl

def P3169 : Prop := ∀ io, (m3169 io).color = false
theorem p3169 : P3169 := fun _ => rfl

def P3170 : Prop := ∀ runtime io value, m3170 runtime io value =
  Truncate.textwidth runtime.charWidth (runtime.render (noColorIO io) value).toList
theorem p3170 : P3170 := fun _ _ _ => rfl

def P3172 : Prop := ∀ runtime io value, m3172 runtime io value =
  Truncate.textwidth runtime.charWidth
    (runtime.renderPlainString (noColorIO io) value).toList
theorem p3172 : P3172 := fun _ _ _ => rfl

def P3191 : Prop := ∀ runtime io value, m3191 runtime io value =
  (0, m3170 runtime io value)
theorem p3191 : P3191 := fun _ _ _ => rfl

def P3192 : Prop := ∀ runtime io value, m3192 runtime io value =
  (m3170 runtime io value, 0)
theorem p3192 : P3192 := fun _ _ _ => rfl

def P3193 : Prop := ∀ runtime io value, m3193 runtime io value =
  (m3170 runtime io value, 0)
theorem p3193 : P3193 := fun _ _ _ => rfl

def P3194 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3194 runtime io value = (0, 0)
theorem p3194 : P3194 := by
  intro runtime io value h
  simp [m3194, h, Containers.alignmentReal, Containers.splitRealAt]

def P3200 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3200 runtime io value = (0, 0)
theorem p3200 : P3200 := by
  intro runtime io value h
  simp [m3200, h, Containers.alignmentComplex, Containers.splitComplex,
    Containers.alignmentAny]

def P3206 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3206 runtime io value = (0, 0)
theorem p3206 : P3206 := by
  intro runtime io value h
  simp [m3206, h, Containers.alignmentRational, Containers.splitRational,
    Containers.alignmentAny]

def P3213 : Prop := ∀ runtime io pair,
  pairDelimitedBody runtime.pairRuntime io pair = true →
  m3213 runtime io pair =
    (0, stringWidth runtime.charWidth (runtime.renderPair io pair))
theorem p3213 : P3213 := by
  intro runtime io pair h
  simp [m3213, alignmentPairBody, h]

def P3228 : Prop := ∀ io, m3228 io = ["UndefInitializer()"]
theorem p3228 : P3228 := fun _ => rfl

def P3249 : Prop := ∀ runtime value, m3249 runtime value = runtime.renderType value.typeId
theorem p3249 : P3249 := fun _ _ => rfl

def P3250 : Prop := ∀ runtime value, m3250 runtime value = m3249 runtime value
theorem p3250 : P3250 := fun _ _ => rfl

def P3258 : Prop := m3258 [] = "0-dimensional" ∧
  ∀ length, m3258 [length] = toString length ++ "-element"
theorem p3258 : P3258 := by
  constructor
  · rfl
  · intro length; rfl

def P3262 : Prop := ∀ runtime axes, m3262 runtime axes =
  "×".intercalate (axes.map (axisText runtime))
theorem p3262 : P3262 := fun _ _ => rfl

def P3263 : Prop := ∀ runtime axis, m3263 runtime axis = runtime.renderValue axis.value
theorem p3263 : P3263 := fun _ _ => rfl

def P3264 : Prop := ∀ runtime axis, m3264 runtime axis =
  runtime.renderValue (axis.indices.getD axis.value)
theorem p3264 : P3264 := fun _ _ => rfl

def P3267 : Prop := ∀ runtime array,
  (runtime.axes array).all (·.oneTo) = true →
  m3267 runtime array = arraySummaryBody runtime array (runtime.axes array) false
theorem p3267 : P3267 := by
  intro runtime array h
  unfold m3267
  simp [h]

def P3268 : Prop := ∀ runtime array axes,
  m3268 runtime array axes = dimsText (axes.map (·.length)) ++ " " ++ runtime.showarg array true
theorem p3268 : P3268 := by
  intro runtime array axes
  simp [m3268, arraySummaryBody]

def P3272 : Prop := ∀ runtime array axes,
  m3272 runtime array axes = dimsText (axes.map (·.length)) ++ " " ++
    runtime.showarg array true ++ " with indices " ++ axesText runtime axes
theorem p3272 : P3272 := by
  intro runtime array axes
  simp [m3272, arraySummaryBody, String.append_assoc]

def P3279 : Prop := ∀ runtime reference, m3279 runtime reference =
  toString (reference.memoryLength - reference.offset + 1) ++ "-element " ++
    runtime.showargMemory reference true
theorem p3279 : P3279 := fun _ _ => rfl

def P3287 : Prop := ∀ runtime function,
  m3287 runtime function = runtime.showPlainFunction function
theorem p3287 : P3287 := fun _ _ => rfl

def P3335 : Prop := ∀ runtime value top, m3335 runtime value top =
  (if top then "" else "::") ++ runtime.renderType value.typeId
theorem p3335 : P3335 := fun _ _ _ => rfl

def P3339 : Prop := ∀ runtime type top, m3339 runtime type top =
  (if top then "" else "::") ++ "Type{" ++ runtime.renderType type ++ "}"
theorem p3339 : P3339 := fun _ _ _ => rfl

def P3344 : Prop := ∀ runtime array top, m3344 runtime array top = m3335 runtime array top
theorem p3344 : P3344 := fun _ _ _ => rfl

def P3350 : Prop := ∀ runtime view,
  m3350 runtime view false = "view(" ++ runtime.showParent view.parent false ++
    showIndicesBody runtime.summary view.indices ++ ")"
theorem p3350 : P3350 := by
  unfold P3350
  intros
  simp [m3350, String.append_assoc]

def P3358 : Prop := ∀ runtime rest,
  m3358 runtime rest = ", :" ++ showIndicesBody runtime rest
theorem p3358 : P3358 := fun _ _ => rfl

def P3360 : Prop := ∀ runtime first rest,
  m3360 runtime first rest = ", " ++ axisText runtime first ++ showIndicesBody runtime rest
theorem p3360 : P3360 := fun _ _ _ => rfl

def P3362 : Prop := ∀ io, m3362 io = ""
theorem p3362 : P3362 := fun _ => rfl

def P3364 : Prop := ∀ runtime array,
  m3364 runtime array false = "reshape(" ++ runtime.showParent array.parent false ++
    (if array.dimensions.isEmpty then "" else ", " ++ ", ".intercalate (array.dimensions.map toString)) ++ ")"
theorem p3364 : P3364 := by
  unfold P3364
  intros
  simp [m3364, String.append_assoc]

def P3375 : Prop := ∀ runtime array, m3375 runtime array =
  "reinterpret(" ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
theorem p3375 : P3375 := fun _ _ => rfl

def P3381 : Prop := ∀ runtime array,
  m3381 runtime array false = "reinterpret(reshape, " ++
    runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
theorem p3381 : P3381 := by
  unfold P3381
  intros
  simp [m3381, String.append_assoc]

def P3391 : Prop := ∀ runtime wrapper, m3391 runtime wrapper =
  "enumerate(" ++ runtime.showIterator wrapper.iterator ++ ")"
theorem p3391 : P3391 := fun _ _ => rfl

def P3396 : Prop := ∀ runtime items,
  m3396 runtime items = m1562 runtime items "zip(" "," ")" false 1 items.slots.length
theorem p3396 : P3396 := fun _ _ => rfl

def P3399 : Prop := ∀ runtime arrayType, m3399 runtime arrayType =
  "pairs(IndexLinear(), ::" ++ runtime.renderType arrayType ++ ")"
theorem p3399 : P3399 := fun _ _ => rfl

def P3403 : Prop := ∀ values : List DelimElement, ∀ toplevel : Bool,
  m3403 values toplevel = "pairs(::NamedTuple)"
theorem p3403 : P3403 := fun _ _ => rfl

def P3407 : Prop := ∀ runtime dictType indexType, m3407 runtime dictType indexType =
  "Iterators.Pairs(::" ++ runtime.renderType dictType ++ ", ::" ++
    runtime.renderType indexType ++ ")"
theorem p3407 : P3407 := fun _ _ _ => rfl

def P3415 : Prop := ∀ io chunk length, m3415 io chunk length =
  (Containers.printBitChunk chunk length).map fun char => ⟨io, String.singleton char⟩
theorem p3415 : P3415 := fun _ _ _ => rfl

def P3425 : Prop := ∀ stdout chunk length,
  m3425 stdout chunk length = m3415 stdout chunk length
theorem p3425 : P3425 := fun _ _ _ => rfl

def P3426 : Prop := ∀ stdout chunk, m3426 stdout chunk = m3415 stdout chunk 64
theorem p3426 : P3426 := fun _ _ => rfl

def P3428 : Prop := ∀ io array,
  HasResult (m3428 io array) ∧ (array.length = 0 → m3428 io array = [])
theorem p3428 : P3428 := by
  intro io array
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m3428, bitshowBody, h]

def P3438 : Prop := ∀ stdout array, m3438 stdout array = m3428 stdout array
theorem p3438 : P3438 := fun _ _ => rfl

def P3440 : Prop := ∀ array, m3440 array =
  String.join ((bitshowBody ⟨0⟩ array).map (·.text))
theorem p3440 : P3440 := fun _ => rfl

def P3443 : Prop := ∀ runtime closure, m3443 runtime closure =
  showTupleCallBody runtime.tupleRuntime ⟨0⟩ closure.argumentType false none none false false ++
    "->◌::" ++ runtime.renderResultType closure.resultType
theorem p3443 : P3443 := fun _ _ => rfl

def P3450 : Prop := ∀ runtime closure, m3450 runtime closure = m3443 runtime closure
theorem p3450 : P3450 := fun _ _ => rfl

def P3455 : Prop := ∀ runtime partition,
  partition.maxWorld = runtime.maxWorldValue →
  (m3455 runtime partition).contains '∞' = true
theorem p3455 : P3455 := by
  intro runtime partition h
  simp [m3455, printPartitionBody, h]

def P3507 : Prop := ∀ runtime partition, m3507 runtime partition =
  "BindingPartition(for " ++ runtime.renderGlobalRef (runtime.owner partition) ++ ": " ++
    printPartitionBody runtime partition ++ ")"
theorem p3507 : P3507 := fun _ _ => rfl

def P3513 : Prop := ∀ runtime partition, m3513 runtime partition =
  "BindingPartition for " ++ runtime.renderGlobalRef (runtime.owner partition) ++
    "\n   " ++ printPartitionBody runtime partition
theorem p3513 : P3513 := fun _ _ => rfl

def P3519 : Prop := ∀ runtime binding,
  HasResult (m3519 runtime binding) ∧
  (binding.partitionsDefined = false →
    m3519 runtime binding = "Binding " ++ runtime.renderGlobalRef binding.globalRef ++
      " - No partitions")
theorem p3519 : P3519 := by
  intro runtime binding
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m3519, h]

def P3539 : Prop := ∀ runtime value,
  runtime.getGlobal value.moduleValue "include" = value.id →
    m3539 runtime value = runtime.renderModule value.moduleValue ++ ".include"
theorem p3539 : P3539 := by
  intro runtime value h
  simp [m3539, showIntoBody, h, String.append_assoc]

def P3548 : Prop := ∀ runtime value,
  runtime.getGlobal value.moduleValue "eval" = value.id →
    m3548 runtime value = runtime.renderModule value.moduleValue ++ ".eval"
theorem p3548 : P3548 := by
  intro runtime value h
  simp [m3548, showIntoBody, h, String.append_assoc]

end JuliaLean.ShowCov.Methods.ShowFile
namespace JuliaLean.Proofs.base.show
open JuliaLean.Registry


open JuliaLean.ShowCov.Methods JuliaLean.ShowCov.Methods.ShowFile in
def entries : List Entry := [
  { id := "show-r2-iocontext-bool-options", juliaFile := "base/show.jl"
    juliaFns := ["IOContext(io::IO, KV::Pair...)", "get(io::IOContext, key, default)",
      "haskey(io::IOContext, key)"]
    statement := "For :compact, :limit, :color, and :hexunsigned, the public pair constructor preserves the supplied Bool for get and marks the key present."
    source := "base/show.jl:383-457,465-475,510-531; base/dict.jl:828-849"
    status := .proven, prop := ``Round3.IOContextBooleanOptionOverride, thm := some ``JuliaLean.ChatGPT.Batch3.Group4.ShowR2IocontextBoolOptions_proven },
  { id := "show-r2-iocontext-typeinfo", juliaFile := "base/show.jl"
    juliaFns := ["IOContext(io::IO, KV::Pair...)", "get(io::IOContext, key, default)",
      "haskey(io::IOContext, key)"]
    statement := "A public IOContext pair with :typeinfo=>T is returned by get and remains present."
    source := "base/show.jl:383-457,465-475,520-531; base/dict.jl:828-849"
    status := .proven, prop := ``Round3.IOContextTypeinfoOverride, thm := some ``JuliaLean.ChatGPT.Batch3.Group4.ShowR2IocontextTypeinfo_proven },
  { id := "show-r2-iocontext-parent", juliaFile := "base/show.jl"
    juliaFns := ["IOContext(io::IO, context::IOContext)", "get(io::IOContext, key, default)",
      "haskey(io::IOContext, key)"]
    statement := "Wrapping an IOContext with a replacement stream preserves get results and key presence for every key."
    source := "base/show.jl:371-382,465-475"
    status := .proven, prop := ``Round3.IOContextParentLookupInheritance, thm := some ``JuliaLean.ChatGPT.Batch3.Group4.ShowR2IocontextParent_proven },
  { id := "show-r2-iocontext-newest", juliaFile := "base/show.jl"
    juliaFns := ["IOContext(io::IO, KV::Pair...)", "get(io::IOContext, key, default)",
      "haskey(io::IOContext, key)"]
    statement := "A newly added pair takes precedence over an older value for the same key and remains present."
    source := "base/show.jl:366-370,383-457,465-475; base/dict.jl:782,828-849"
    status := .proven, prop := ``Round3.IOContextNewestPairOverride, thm := some ``JuliaLean.ChatGPT.Batch3.Group4.ShowR2IocontextNewest_proven },
  { id := "show-r2-iocontext-get-haskey", juliaFile := "base/show.jl"
    juliaFns := ["get(io::IOContext, key, default)", "haskey(io::IOContext, key)"]
    statement := "A successful get result implies haskey is true, and an absent key returns the caller's default."
    source := "base/show.jl:465-475; base/dict.jl:828-849"
    status := .proven, prop := ``IOContextGetHaskey, thm := some ``ChatGPTBatch2.Group3.ShowR2IocontextGetHaskey_proven },
  { id := "show-r4-nothing-show-output", juliaFile := "base/show.jl"
    juliaFns := ["show(io, ::Nothing)"]
    statement := "For an IOBuffer, the public show method produces the bytes for the Julia literal nothing."
    source := "base/show.jl:1424"
    status := .proven, prop := ``NothingShowOutput, thm := some ``JuliaLean.ChatGPT.Batch3.Group4.ShowR4NothingShowOutput_proven }
] ++ [
  entry "showcov-show-l6" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", u::UndefInitializer)" "The source-order model of show(io::IO, ::MIME\"text/plain\", u::UndefInitializer) has a result for every allowed input." ``P6 ``p6,
  entry "showcov-show-l14" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::AbstractRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::AbstractRange) has a result for every allowed input." ``P14 ``p14,
  entry "showcov-show-l16" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::UnitRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::UnitRange) has a result for every allowed input." ``P16 ``p16,
  entry "showcov-show-l23" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::LinRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::LinRange) has a result for every allowed input." ``P23 ``p23,
  entry "showcov-show-l34" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::LogRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::LogRange) has a result for every allowed input." ``P34 ``p34,
  entry "showcov-show-l41" "base/show.jl" "_isself(ft::DataType)" "The source-order model of _isself(ft::DataType) has a result for every allowed input." ``P41 ``p41,
  entry "showcov-show-l55" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", f::Function)" "The source-order model of show(io::IO, ::MIME\"text/plain\", f::Function) has a result for every allowed input." ``P55 ``p55,
  entry "showcov-show-l75" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", c::ComposedFunction)" "The source-order model of show(io::IO, ::MIME\"text/plain\", c::ComposedFunction) has a result for every allowed input." ``P75 ``p75,
  entry "showcov-show-l76" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", c::Returns)" "The source-order model of show(io::IO, ::MIME\"text/plain\", c::Returns) has a result for every allowed input." ``P76 ``p76,
  entry "showcov-show-l77" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", s::Splat)" "The source-order model of show(io::IO, ::MIME\"text/plain\", s::Splat) has a result for every allowed input." ``P77 ``p77,
  entry "showcov-show-l85" "base/show.jl" "ncodeunits(c::ANSIDelimiter)" "The source-order model of ncodeunits(c::ANSIDelimiter) has a result for every allowed input." ``P85 ``p85,
  entry "showcov-show-l86" "base/show.jl" "textwidth(::ANSIDelimiter)" "The source-order model of textwidth(::ANSIDelimiter) has a result for every allowed input." ``P86 ``p86,
  entry "showcov-show-l92" "base/show.jl" "ANSIIterator(s::AbstractString)" "The source-order model of ANSIIterator(s::AbstractString) has a result for every allowed input." ``P92 ``p92,
  entry "showcov-show-l94" "base/show.jl" "IteratorSize(::Type{<:ANSIIterator})" "The source-order model of IteratorSize(::Type{<:ANSIIterator}) has a result for every allowed input." ``P94 ``p94,
  entry "showcov-show-l95" "base/show.jl" "eltype(::Type{<:ANSIIterator})" "The source-order model of eltype(::Type{<:ANSIIterator}) has a result for every allowed input." ``P95 ``p95,
  entry "showcov-show-l96" "base/show.jl" "iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures)))" "The source-order model of iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures))) has a result for every allowed input." ``P96 ``p96,
  entry "showcov-show-l102" "base/show.jl" "textwidth(I::ANSIIterator)" "The source-order model of textwidth(I::ANSIIterator) has a result for every allowed input." ``P102 ``p102,
  entry "showcov-show-l104" "base/show.jl" "_truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars=\"\\r\\n\", truncmark=\"…\")" "The source-order model of _truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars=\"\\r\\n\", truncmark=\"…\") has a result for every allowed input." ``P104 ``p104,
  entry "showcov-show-l137" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", iter::Union{KeySet,ValueIterator})" "The source-order model of show(io::IO, ::MIME\"text/plain\", iter::Union{KeySet,ValueIterator}) has a result for every allowed input." ``P137 ``p137,
  entry "showcov-show-l168" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::AbstractDict{K,V}) where {K,V}" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::AbstractDict{K,V}) where {K,V} has a result for every allowed input." ``P168 ``p168,
  entry "showcov-show-l235" "base/show.jl" "summary(io::IO, t::AbstractSet)" "The source-order model of summary(io::IO, t::AbstractSet) has a result for every allowed input." ``P235 ``p235,
  entry "showcov-show-l241" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::AbstractSet{T}) where T" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::AbstractSet{T}) where T has a result for every allowed input." ``P241 ``p241,
  entry "showcov-show-l278" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", opt::JLOptions)" "The source-order model of show(io::IO, ::MIME\"text/plain\", opt::JLOptions) has a result for every allowed input." ``P278 ``p278,
  entry "showcov-show-l294" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::Task)" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::Task) has a result for every allowed input." ``P294 ``p294,
  entry "showcov-show-l304" "base/show.jl" "show(io::IO, src::Core.CancellationTokenSource)" "The source-order model of show(io::IO, src::Core.CancellationTokenSource) has a result for every allowed input." ``P304 ``p304,
  entry "showcov-show-l322" "base/show.jl" "print(io::IO, s::Symbol)" "The source-order model of print(io::IO, s::Symbol) has a result for every allowed input." ``P322 ``p322,
  entry "showcov-show-l336" "base/show.jl" "IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO" "The source-order model of IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO has a result for every allowed input." ``P336 ``p336,
  entry "showcov-show-l343" "base/show.jl" "ioproperties(io::IO)" "The source-order model of ioproperties(io::IO) has a result for every allowed input." ``P343 ``p343,
  entry "showcov-show-l344" "base/show.jl" "ioproperties(io::IOContext)" "The source-order model of ioproperties(io::IOContext) has a result for every allowed input." ``P344 ``p344,
  entry "showcov-show-l346" "base/show.jl" "unwrapcontext(io::IO)" "The source-order model of unwrapcontext(io::IO) has a result for every allowed input." ``P346 ``p346,
  entry "showcov-show-l347" "base/show.jl" "unwrapcontext(io::IOContext)" "The source-order model of unwrapcontext(io::IOContext) has a result for every allowed input." ``P347 ``p347,
  entry "showcov-show-l349" "base/show.jl" "IOContext(io::IO, dict::ImmutableDict{Symbol, Any})" "The source-order model of IOContext(io::IO, dict::ImmutableDict{Symbol, Any}) has a result for every allowed input." ``P349 ``p349,
  entry "showcov-show-l353" "base/show.jl" "IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any})" "The source-order model of IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any}) has a result for every allowed input." ``P353 ``p353,
  entry "showcov-show-l358" "base/show.jl" "convert(::Type{IOContext}, io::IOContext)" "The source-order model of convert(::Type{IOContext}, io::IOContext) has a result for every allowed input." ``P358 ``p358,
  entry "showcov-show-l359" "base/show.jl" "convert(::Type{IOContext}, io::IO)" "The source-order model of convert(::Type{IOContext}, io::IO) has a result for every allowed input." ``P359 ``p359,
  entry "showcov-show-l360" "base/show.jl" "convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t}" "The source-order model of convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t} has a result for every allowed input." ``P360 ``p360,
  entry "showcov-show-l361" "base/show.jl" "convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t}" "The source-order model of convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t} has a result for every allowed input." ``P361 ``p361,
  entry "showcov-show-l363" "base/show.jl" "IOContext(io::IO)" "The source-order model of IOContext(io::IO) has a result for every allowed input." ``P363 ``p363,
  entry "showcov-show-l364" "base/show.jl" "IOContext{IO_t}(io::IO) where {IO_t}" "The source-order model of IOContext{IO_t}(io::IO) where {IO_t} has a result for every allowed input." ``P364 ``p364,
  entry "showcov-show-l366" "base/show.jl" "IOContext(io::IO, KV::Pair)" "The source-order model of IOContext(io::IO, KV::Pair) has a result for every allowed input." ``P366 ``p366,
  entry "showcov-show-l381" "base/show.jl" "IOContext(io::IO, context::IO)" "The source-order model of IOContext(io::IO, context::IO) has a result for every allowed input." ``P381 ``p381,
  entry "showcov-show-l456" "base/show.jl" "IOContext(io::IO, KV::Pair, KVs::Pair...)" "The source-order model of IOContext(io::IO, KV::Pair, KVs::Pair...) has a result for every allowed input." ``P456 ``p456,
  entry "showcov-show-l458" "base/show.jl" "show(io::IO, ctx::IOContext)" "The source-order model of show(io::IO, ctx::IOContext) has a result for every allowed input." ``P458 ``p458,
  entry "showcov-show-l460" "base/show.jl" "pipe_reader(io::IOContext)" "The source-order model of pipe_reader(io::IOContext) has a result for every allowed input." ``P460 ``p460,
  entry "showcov-show-l461" "base/show.jl" "pipe_writer(io::IOContext)" "The source-order model of pipe_writer(io::IOContext) has a result for every allowed input." ``P461 ``p461,
  entry "showcov-show-l462" "base/show.jl" "lock(io::IOContext)" "The source-order model of lock(io::IOContext) has a result for every allowed input." ``P462 ``p462,
  entry "showcov-show-l463" "base/show.jl" "unlock(io::IOContext)" "The source-order model of unlock(io::IOContext) has a result for every allowed input." ``P463 ``p463,
  entry "showcov-show-l465" "base/show.jl" "in(key_value::Pair, io::IOContext)" "The source-order model of in(key_value::Pair, io::IOContext) has a result for every allowed input." ``P465 ``p465,
  entry "showcov-show-l466" "base/show.jl" "in(key_value::Pair, io::IO)" "The source-order model of in(key_value::Pair, io::IO) has a result for every allowed input." ``P466 ``p466,
  entry "showcov-show-l467" "base/show.jl" "haskey(io::IOContext, key)" "The source-order model of haskey(io::IOContext, key) has a result for every allowed input." ``P467 ``p467,
  entry "showcov-show-l468" "base/show.jl" "haskey(io::IO, key)" "The source-order model of haskey(io::IO, key) has a result for every allowed input." ``P468 ``p468,
  entry "showcov-show-l469" "base/show.jl" "getindex(io::IOContext, key)" "The source-order model of getindex(io::IOContext, key) has a result for every allowed input." ``P469 ``p469,
  entry "showcov-show-l470" "base/show.jl" "getindex(io::IO, key)" "The source-order model of getindex(io::IO, key) has a result for every allowed input." ``P470 ``p470,
  entry "showcov-show-l471" "base/show.jl" "get(io::IOContext, key, default)" "The source-order model of get(io::IOContext, key, default) has a result for every allowed input." ``P471 ``p471,
  entry "showcov-show-l472" "base/show.jl" "get(io::IO, key, default)" "The source-order model of get(io::IO, key, default) has a result for every allowed input." ``P472 ``p472,
  entry "showcov-show-l473" "base/show.jl" "keys(io::IOContext)" "The source-order model of keys(io::IOContext) has a result for every allowed input." ``P473 ``p473,
  entry "showcov-show-l474" "base/show.jl" "keys(io::IO)" "The source-order model of keys(io::IO) has a result for every allowed input." ``P474 ``p474,
  entry "showcov-show-l476" "base/show.jl" "displaysize(io::IOContext)" "The source-order model of displaysize(io::IOContext) has a result for every allowed input." ``P476 ``p476,
  entry "showcov-show-l478" "base/show.jl" "show_circular(io::IO, @nospecialize(x))" "The source-order model of show_circular(io::IO, @nospecialize(x)) has a result for every allowed input." ``P478 ``p478,
  entry "showcov-show-l479" "base/show.jl" "show_circular(io::IOContext, @nospecialize(x))" "The source-order model of show_circular(io::IOContext, @nospecialize(x)) has a result for every allowed input." ``P479 ``p479,
  entry "showcov-show-l520" "base/show.jl" "show(io::IO, @nospecialize(x))" "The source-order model of show(io::IO, @nospecialize(x)) has a result for every allowed input." ``P520 ``p520,
  entry "showcov-show-l522" "base/show.jl" "show(x)" "The source-order model of show(x) has a result for every allowed input." ``P522 ``p522,
  entry "showcov-show-l525" "base/show.jl" "show_default(io::IO, @nospecialize(x))" "The source-order model of show_default(io::IO, @nospecialize(x)) has a result for every allowed input." ``P525 ``p525,
  entry "showcov-show-l527" "base/show.jl" "_show_default(io::IO, @nospecialize(x))" "The source-order model of _show_default(io::IO, @nospecialize(x)) has a result for every allowed input." ``P527 ``p527,
  entry "showcov-show-l570" "base/show.jl" "active_module()" "The source-order model of active_module() has a result for every allowed input." ``P570 ``p570,
  entry "showcov-show-l583" "base/show.jl" "show_function(io::IO, f::Function, compact::Bool, fallback::Function)" "The source-order model of show_function(io::IO, f::Function, compact::Bool, fallback::Function) has a result for every allowed input." ``P583 ``p583,
  entry "showcov-show-l603" "base/show.jl" "show(io::IO, f::Function)" "The source-order model of show(io::IO, f::Function) has a result for every allowed input." ``P603 ``p603,
  entry "showcov-show-l604" "base/show.jl" "print(io::IO, f::Function)" "The source-order model of print(io::IO, f::Function) has a result for every allowed input." ``P604 ``p604,
  entry "showcov-show-l606" "base/show.jl" "show(io::IO, f::Core.IntrinsicFunction)" "The source-order model of show(io::IO, f::Core.IntrinsicFunction) has a result for every allowed input." ``P606 ``p606,
  entry "showcov-show-l613" "base/show.jl" "print(io::IO, f::Core.IntrinsicFunction)" "The source-order model of print(io::IO, f::Core.IntrinsicFunction) has a result for every allowed input." ``P613 ``p613,
  entry "showcov-show-l615" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", ::Core.TypeofBottom)" "The source-order model of show(io::IO, ::MIME\"text/plain\", ::Core.TypeofBottom) has a result for every allowed input." ``P615 ``p615,
  entry "showcov-show-l617" "base/show.jl" "print_without_params(@nospecialize(x))" "The source-order model of print_without_params(@nospecialize(x)) has a result for every allowed input." ``P617 ``p617,
  entry "showcov-show-l622" "base/show.jl" "io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x))" "The source-order model of io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x)) has a result for every allowed input." ``P622 ``p622,
  entry "showcov-show-l630" "base/show.jl" "io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x))" "The source-order model of io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x)) has a result for every allowed input." ``P630 ``p630,
  entry "showcov-show-l632" "base/show.jl" "modulesof!(s::Set{Module}, x::TypeVar)" "The source-order model of modulesof!(s::Set{Module}, x::TypeVar) has a result for every allowed input." ``P632 ``p632,
  entry "showcov-show-l633" "base/show.jl" "modulesof!(s::Set{Module}, x::TypeEq)" "The source-order model of modulesof!(s::Set{Module}, x::TypeEq) has a result for every allowed input." ``P633 ``p633,
  entry "showcov-show-l638" "base/show.jl" "modulesof!(s::Set{Module}, x::Core.TypeEgal)" "The source-order model of modulesof!(s::Set{Module}, x::Core.TypeEgal) has a result for every allowed input." ``P638 ``p638,
  entry "showcov-show-l639" "base/show.jl" "modulesof!(s::Set{Module}, x::Type)" "The source-order model of modulesof!(s::Set{Module}, x::Type) has a result for every allowed input." ``P639 ``p639,
  entry "showcov-show-l654" "base/show.jl" "has_other_free_typevars(@nospecialize(x), free_before)" "The source-order model of has_other_free_typevars(@nospecialize(x), free_before) has a result for every allowed input." ``P654 ``p654,
  entry "showcov-show-l674" "base/show.jl" "unbounded_typealias(@nospecialize(alias))" "The source-order model of unbounded_typealias(@nospecialize(alias)) has a result for every allowed input." ``P674 ``p674,
  entry "showcov-show-l692" "base/show.jl" "reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x))" "The source-order model of reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x)) has a result for every allowed input." ``P692 ``p692,
  entry "showcov-show-l703" "base/show.jl" "make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing)" "The source-order model of make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing) has a result for every allowed input." ``P703 ``p703,
  entry "showcov-show-l769" "base/show.jl" "isgensym(s::Symbol)" "The source-order model of isgensym(s::Symbol) has a result for every allowed input." ``P769 ``p769,
  entry "showcov-show-l771" "base/show.jl" "show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int)" "The source-order model of show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int) has a result for every allowed input." ``P771 ``p771,
  entry "showcov-show-l786" "base/show.jl" "show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector)" "The source-order model of show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector) has a result for every allowed input." ``P786 ``p786,
  entry "showcov-show-l789" "base/show.jl" "egal_var(p::TypeVar, @nospecialize o)" "The source-order model of egal_var(p::TypeVar, @nospecialize o) has a result for every allowed input." ``P789 ``p789,
  entry "showcov-show-l832" "base/show.jl" "show_typealias_name(io::IO, name::GlobalRef)" "The source-order model of show_typealias_name(io::IO, name::GlobalRef) has a result for every allowed input." ``P832 ``p832,
  entry "showcov-show-l847" "base/show.jl" "show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector)" "The source-order model of show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector) has a result for every allowed input." ``P847 ``p847,
  entry "showcov-show-l864" "base/show.jl" "make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type))" "The source-order model of make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type)) has a result for every allowed input." ``P864 ``p864,
  entry "showcov-show-l894" "base/show.jl" "show_wheres(io::IO, wheres::Vector{TypeVar})" "The source-order model of show_wheres(io::IO, wheres::Vector{TypeVar}) has a result for every allowed input." ``P894 ``p894,
  entry "showcov-show-l908" "base/show.jl" "show_typealias(io::IO, @nospecialize(x::Type))" "The source-order model of show_typealias(io::IO, @nospecialize(x::Type)) has a result for every allowed input." ``P908 ``p908,
  entry "showcov-show-l917" "base/show.jl" "make_typealiases(@nospecialize(x::Type))" "The source-order model of make_typealiases(@nospecialize(x::Type)) has a result for every allowed input." ``P917 ``p917,
  entry "showcov-show-l1002" "base/show.jl" "show_unionaliases(io::IO, x::Union)" "The source-order model of show_unionaliases(io::IO, x::Union) has a result for every allowed input." ``P1002 ``p1002,
  entry "showcov-show-l1046" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", @nospecialize(x::Type))" "The source-order model of show(io::IO, ::MIME\"text/plain\", @nospecialize(x::Type)) has a result for every allowed input." ``P1046 ``p1046,
  entry "showcov-show-l1071" "base/show.jl" "show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal))" "The source-order model of show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal)) has a result for every allowed input." ``P1071 ``p1071,
  entry "showcov-show-l1076" "base/show.jl" "show(io::IO, @nospecialize(x::Core.AnyType))" "The source-order model of show(io::IO, @nospecialize(x::Core.AnyType)) has a result for every allowed input." ``P1076 ``p1076,
  entry "showcov-show-l1091" "base/show.jl" "show_typeeq(io::IO, @nospecialize(x::TypeEq))" "The source-order model of show_typeeq(io::IO, @nospecialize(x::TypeEq)) has a result for every allowed input." ``P1091 ``p1091,
  entry "showcov-show-l1096" "base/show.jl" "_show_type(io::IO, @nospecialize(x::Type))" "The source-order model of _show_type(io::IO, @nospecialize(x::Type)) has a result for every allowed input." ``P1096 ``p1096,
  entry "showcov-show-l1159" "base/show.jl" "isvisible(sym::Symbol, parent::Module, from::Module)" "The source-order model of isvisible(sym::Symbol, parent::Module, from::Module) has a result for every allowed input." ``P1159 ``p1159,
  entry "showcov-show-l1179" "base/show.jl" "is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing})" "The source-order model of is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing}) has a result for every allowed input." ``P1179 ``p1179,
  entry "showcov-show-l1191" "base/show.jl" "check_world_bounded(tn::Core.TypeName)" "The source-order model of check_world_bounded(tn::Core.TypeName) has a result for every allowed input." ``P1191 ``p1191,
  entry "showcov-show-l1211" "base/show.jl" "show_type_name(io::IO, tn::Core.TypeName)" "The source-order model of show_type_name(io::IO, tn::Core.TypeName) has a result for every allowed input." ``P1211 ``p1211,
  entry "showcov-show-l1248" "base/show.jl" "maybe_kws_nt(x::DataType)" "The source-order model of maybe_kws_nt(x::DataType) has a result for every allowed input." ``P1248 ``p1248,
  entry "showcov-show-l1266" "base/show.jl" "show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[])" "The source-order model of show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[]) has a result for every allowed input." ``P1266 ``p1266,
  entry "showcov-show-l1362" "base/show.jl" "show_at_namedtuple(io::IO, syms::Tuple, types::DataType)" "The source-order model of show_at_namedtuple(io::IO, syms::Tuple, types::DataType) has a result for every allowed input." ``P1362 ``p1362,
  entry "showcov-show-l1378" "base/show.jl" "show_supertypes(io::IO, typ::DataType)" "The source-order model of show_supertypes(io::IO, typ::DataType) has a result for every allowed input." ``P1378 ``p1378,
  entry "showcov-show-l1386" "base/show.jl" "show_supertypes(typ::DataType)" "The source-order model of show_supertypes(typ::DataType) has a result for every allowed input." ``P1386 ``p1386,
  entry "showcov-show-l1406" "base/show.jl" "show(exs...)" "The source-order model of show(exs...) has a result for every allowed input." ``P1406 ``p1406,
  entry "showcov-show-l1416" "base/show.jl" "show(io::IO, tn::Core.TypeName)" "The source-order model of show(io::IO, tn::Core.TypeName) has a result for every allowed input." ``P1416 ``p1416,
  entry "showcov-show-l1422" "base/show.jl" "nonnothing_nonmissing_typeinfo(io::IO)" "The source-order model of nonnothing_nonmissing_typeinfo(io::IO) has a result for every allowed input." ``P1422 ``p1422,
  entry "showcov-show-l1423" "base/show.jl" "show(io::IO, b::Bool)" "The source-order model of show(io::IO, b::Bool) has a result for every allowed input." ``P1423 ``p1423,
  entry "showcov-show-l1424" "base/show.jl" "show(io::IO, ::Nothing)" "The source-order model of show(io::IO, ::Nothing) has a result for every allowed input." ``P1424 ``p1424,
  entry "showcov-show-l1425" "base/show.jl" "show(io::IO, n::Signed)" "The source-order model of show(io::IO, n::Signed) has a result for every allowed input." ``P1425 ``p1425,
  entry "showcov-show-l1426" "base/show.jl" "show(io::IO, n::Unsigned)" "The source-order model of show(io::IO, n::Unsigned) has a result for every allowed input." ``P1426 ``p1426,
  entry "showcov-show-l1437" "base/show.jl" "print(io::IO, n::Unsigned)" "The source-order model of print(io::IO, n::Unsigned) has a result for every allowed input." ``P1437 ``p1437,
  entry "showcov-show-l1439" "base/show.jl" "has_tight_type(p::Pair)" "The source-order model of has_tight_type(p::Pair) has a result for every allowed input." ``P1439 ``p1439,
  entry "showcov-show-l1443" "base/show.jl" "isdelimited(io::IO, x)" "The source-order model of isdelimited(io::IO, x) has a result for every allowed input." ``P1443 ``p1443,
  entry "showcov-show-l1444" "base/show.jl" "isdelimited(io::IO, x::Function)" "The source-order model of isdelimited(io::IO, x::Function) has a result for every allowed input." ``P1444 ``p1444,
  entry "showcov-show-l1448" "base/show.jl" "isdelimited(io::IO, p::Pair)" "The source-order model of isdelimited(io::IO, p::Pair) has a result for every allowed input." ``P1448 ``p1448,
  entry "showcov-show-l1450" "base/show.jl" "gettypeinfos(io::IO, p::Pair)" "The source-order model of gettypeinfos(io::IO, p::Pair) has a result for every allowed input." ``P1450 ``p1450,
  entry "showcov-show-l1457" "base/show.jl" "show(io::IO, p::Pair)" "The source-order model of show(io::IO, p::Pair) has a result for every allowed input." ``P1457 ``p1457,
  entry "showcov-show-l1469" "base/show.jl" "show_pairtyped(io::IO, p::Pair{K,V}) where {K,V}" "The source-order model of show_pairtyped(io::IO, p::Pair{K,V}) where {K,V} has a result for every allowed input." ``P1469 ``p1469,
  entry "showcov-show-l1474" "base/show.jl" "show(io::IO, m::Module)" "The source-order model of show(io::IO, m::Module) has a result for every allowed input." ``P1474 ``p1474,
  entry "showcov-show-l1484" "base/show.jl" "print_fullname(io::IO, m::Module)" "The source-order model of print_fullname(io::IO, m::Module) has a result for every allowed input." ``P1484 ``p1484,
  entry "showcov-show-l1495" "base/show.jl" "sourceinfo_slotnames(src::CodeInfo)" "The source-order model of sourceinfo_slotnames(src::CodeInfo) has a result for every allowed input." ``P1495 ``p1495,
  entry "showcov-show-l1496" "base/show.jl" "sourceinfo_slotnames(slotnames::Vector{Symbol})" "The source-order model of sourceinfo_slotnames(slotnames::Vector{Symbol}) has a result for every allowed input." ``P1496 ``p1496,
  entry "showcov-show-l1518" "base/show.jl" "show(io::IO, mi::Core.MethodInstance)" "The source-order model of show(io::IO, mi::Core.MethodInstance) has a result for every allowed input." ``P1518 ``p1518,
  entry "showcov-show-l1519" "base/show.jl" "show(io::IO, codeinst::Core.CodeInstance)" "The source-order model of show(io::IO, codeinst::Core.CodeInstance) has a result for every allowed input." ``P1519 ``p1519,
  entry "showcov-show-l1533" "base/show.jl" "show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false)" "The source-order model of show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false) has a result for every allowed input." ``P1533 ``p1533,
  entry "showcov-show-l1562" "base/show.jl" "show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr)))" "The source-order model of show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr))) has a result for every allowed input." ``P1562 ``p1562,
  entry "showcov-show-l1591" "base/show.jl" "show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))" "The source-order model of show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int)) has a result for every allowed input." ``P1591 ``p1591,
  entry "showcov-show-l1625" "base/show.jl" "show(io::IO, t::Tuple)" "The source-order model of show(io::IO, t::Tuple) has a result for every allowed input." ``P1625 ``p1625,
  entry "showcov-show-l1626" "base/show.jl" "show(io::IO, v::SimpleVector)" "The source-order model of show(io::IO, v::SimpleVector) has a result for every allowed input." ``P1626 ``p1626,
  entry "showcov-show-l1628" "base/show.jl" "show(io::IO, s::Symbol)" "The source-order model of show(io::IO, s::Symbol) has a result for every allowed input." ``P1628 ``p1628,
  entry "showcov-show-l1666" "base/show.jl" "print( io::IO, ex::ExprNode)" "The source-order model of print( io::IO, ex::ExprNode) has a result for every allowed input." ``P1666 ``p1666,
  entry "showcov-show-l1667" "base/show.jl" "show( io::IO, ex::ExprNode)" "The source-order model of show( io::IO, ex::ExprNode) has a result for every allowed input." ``P1667 ``p1667,
  entry "showcov-show-l1668" "base/show.jl" "show_unquoted(io::IO, ex)" "The source-order model of show_unquoted(io::IO, ex) has a result for every allowed input." ``P1668 ``p1668,
  entry "showcov-show-l1669" "base/show.jl" "show_unquoted(io::IO, ex, indent::Int)" "The source-order model of show_unquoted(io::IO, ex, indent::Int) has a result for every allowed input." ``P1669 ``p1669,
  entry "showcov-show-l1670" "base/show.jl" "show_unquoted(io::IO, ex, ::Int,::Int)" "The source-order model of show_unquoted(io::IO, ex, ::Int,::Int) has a result for every allowed input." ``P1670 ``p1670,
  entry "showcov-show-l1671" "base/show.jl" "show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int) has a result for every allowed input." ``P1671 ``p1671,
  entry "showcov-show-l1713" "base/show.jl" "operator_precedence(s::Symbol)" "The source-order model of operator_precedence(s::Symbol) has a result for every allowed input." ``P1713 ``p1713,
  entry "showcov-show-l1714" "base/show.jl" "operator_precedence(x::Any)" "The source-order model of operator_precedence(x::Any) has a result for every allowed input." ``P1714 ``p1714,
  entry "showcov-show-l1739" "base/show.jl" "operator_associativity(s::Symbol)" "The source-order model of operator_associativity(s::Symbol) has a result for every allowed input." ``P1739 ``p1739,
  entry "showcov-show-l1750" "base/show.jl" "is_quoted(ex)" "The source-order model of is_quoted(ex) has a result for every allowed input." ``P1750 ``p1750,
  entry "showcov-show-l1751" "base/show.jl" "is_quoted(ex::QuoteNode)" "The source-order model of is_quoted(ex::QuoteNode) has a result for every allowed input." ``P1751 ``p1751,
  entry "showcov-show-l1752" "base/show.jl" "is_quoted(ex::Expr)" "The source-order model of is_quoted(ex::Expr) has a result for every allowed input." ``P1752 ``p1752,
  entry "showcov-show-l1754" "base/show.jl" "unquoted(ex::QuoteNode)" "The source-order model of unquoted(ex::QuoteNode) has a result for every allowed input." ``P1754 ``p1754,
  entry "showcov-show-l1755" "base/show.jl" "unquoted(ex::Expr)" "The source-order model of unquoted(ex::Expr) has a result for every allowed input." ``P1755 ``p1755,
  entry "showcov-show-l1762" "base/show.jl" "emphasize(io, str::AbstractString, col = Base.error_color())" "The source-order model of emphasize(io, str::AbstractString, col = Base.error_color()) has a result for every allowed input." ``P1762 ``p1762,
  entry "showcov-show-l1766" "base/show.jl" "show_linenumber(io::IO, line)" "The source-order model of show_linenumber(io::IO, line) has a result for every allowed input." ``P1766 ``p1766,
  entry "showcov-show-l1767" "base/show.jl" "show_linenumber(io::IO, line, file)" "The source-order model of show_linenumber(io::IO, line, file) has a result for every allowed input." ``P1767 ``p1767,
  entry "showcov-show-l1768" "base/show.jl" "show_linenumber(io::IO, line, file::Nothing)" "The source-order model of show_linenumber(io::IO, line, file::Nothing) has a result for every allowed input." ``P1768 ``p1768,
  entry "showcov-show-l1771" "base/show.jl" "show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int)" "The source-order model of show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int) has a result for every allowed input." ``P1771 ``p1771,
  entry "showcov-show-l1790" "base/show.jl" "show_block(io::IO,head, block,i::Int, quote_level::Int)" "The source-order model of show_block(io::IO,head, block,i::Int, quote_level::Int) has a result for every allowed input." ``P1790 ``p1790,
  entry "showcov-show-l1791" "base/show.jl" "show_block(io::IO, head, arg, block, i::Int, quote_level::Int)" "The source-order model of show_block(io::IO, head, arg, block, i::Int, quote_level::Int) has a result for every allowed input." ``P1791 ``p1791,
  entry "showcov-show-l1800" "base/show.jl" "show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false)" "The source-order model of show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false) has a result for every allowed input." ``P1800 ``p1800,
  entry "showcov-show-l1828" "base/show.jl" "show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false)" "The source-order model of show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false) has a result for every allowed input." ``P1828 ``p1828,
  entry "showcov-show-l1837" "base/show.jl" "show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool)" "The source-order model of show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool) has a result for every allowed input." ``P1837 ``p1837,
  entry "showcov-show-l1867" "base/show.jl" "show_sym(io::IO, sym::Symbol; allow_macroname=false)" "The source-order model of show_sym(io::IO, sym::Symbol; allow_macroname=false) has a result for every allowed input." ``P1867 ``p1867,
  entry "showcov-show-l1880" "base/show.jl" "show_unquoted(io::IO, val::SSAValue, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, val::SSAValue, ::Int, ::Int) has a result for every allowed input." ``P1880 ``p1880,
  entry "showcov-show-l1895" "base/show.jl" "show_unquoted(io::IO, sym::Symbol, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, sym::Symbol, ::Int, ::Int) has a result for every allowed input." ``P1895 ``p1895,
  entry "showcov-show-l1896" "base/show.jl" "show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int) has a result for every allowed input." ``P1896 ``p1896,
  entry "showcov-show-l1897" "base/show.jl" "show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int) has a result for every allowed input." ``P1897 ``p1897,
  entry "showcov-show-l1898" "base/show.jl" "show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int) has a result for every allowed input." ``P1898 ``p1898,
  entry "showcov-show-l1899" "base/show.jl" "show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int) has a result for every allowed input." ``P1899 ``p1899,
  entry "showcov-show-l1902" "base/show.jl" "show_globalref(io::IO, ex::GlobalRef; allow_macroname=false)" "The source-order model of show_globalref(io::IO, ex::GlobalRef; allow_macroname=false) has a result for every allowed input." ``P1902 ``p1902,
  entry "showcov-show-l1914" "base/show.jl" "show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int) has a result for every allowed input." ``P1914 ``p1914,
  entry "showcov-show-l1924" "base/show.jl" "show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int)" "The source-order model of show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int) has a result for every allowed input." ``P1924 ``p1924,
  entry "showcov-show-l1937" "base/show.jl" "show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int)" "The source-order model of show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int) has a result for every allowed input." ``P1937 ``p1937,
  entry "showcov-show-l1962" "base/show.jl" "show_generator(io, ex::Expr, indent, quote_level)" "The source-order model of show_generator(io, ex::Expr, indent, quote_level) has a result for every allowed input." ``P1962 ``p1962,
  entry "showcov-show-l1983" "base/show.jl" "valid_import_path(@nospecialize(ex), allow_as = true)" "The source-order model of valid_import_path(@nospecialize(ex), allow_as = true) has a result for every allowed input." ``P1983 ``p1983,
  entry "showcov-show-l1990" "base/show.jl" "show_import_path(io::IO, ex, quote_level)" "The source-order model of show_import_path(io::IO, ex, quote_level) has a result for every allowed input." ``P1990 ``p1990,
  entry "showcov-show-l2023" "base/show.jl" "allow_macroname(ex)" "The source-order model of allow_macroname(ex) has a result for every allowed input." ``P2023 ``p2023,
  entry "showcov-show-l2034" "base/show.jl" "is_core_macro(arg::GlobalRef, macro_name::AbstractString)" "The source-order model of is_core_macro(arg::GlobalRef, macro_name::AbstractString) has a result for every allowed input." ``P2034 ``p2034,
  entry "showcov-show-l2035" "base/show.jl" "is_core_macro(arg::GlobalRef, macro_name::Symbol)" "The source-order model of is_core_macro(arg::GlobalRef, macro_name::Symbol) has a result for every allowed input." ``P2035 ``p2035,
  entry "showcov-show-l2036" "base/show.jl" "is_core_macro(@nospecialize(arg), macro_name::AbstractString)" "The source-order model of is_core_macro(@nospecialize(arg), macro_name::AbstractString) has a result for every allowed input." ``P2036 ``p2036,
  entry "showcov-show-l2037" "base/show.jl" "is_core_macro(@nospecialize(arg), macro_name::Symbol)" "The source-order model of is_core_macro(@nospecialize(arg), macro_name::Symbol) has a result for every allowed input." ``P2037 ``p2037,
  entry "showcov-show-l2043" "base/show.jl" "show_unquoted_expr_fallback(io::IO, ex::Expr)" "The source-order model of show_unquoted_expr_fallback(io::IO, ex::Expr) has a result for every allowed input." ``P2043 ``p2043,
  entry "showcov-show-l2054" "base/show.jl" "show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0)" "The source-order model of show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0) has a result for every allowed input." ``P2054 ``p2054,
  entry "showcov-show-l2608" "base/show.jl" "demangle_function_name(name::Symbol)" "The source-order model of demangle_function_name(name::Symbol) has a result for every allowed input." ``P2608 ``p2608,
  entry "showcov-show-l2609" "base/show.jl" "demangle_function_name(name::AbstractString)" "The source-order model of demangle_function_name(name::AbstractString) has a result for every allowed input." ``P2609 ``p2609,
  entry "showcov-show-l2620" "base/show.jl" "show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname=\"\", html=false, qualified=false)" "The source-order model of show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname=\"\", html=false, qualified=false) has a result for every allowed input." ``P2620 ``p2620,
  entry "showcov-show-l2645" "base/show.jl" "print_within_stacktrace(io, s...; color=:normal, bold=false)" "The source-order model of print_within_stacktrace(io, s...; color=:normal, bold=false) has a result for every allowed input." ``P2645 ``p2645,
  entry "showcov-show-l2653" "base/show.jl" "show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true)" "The source-order model of show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true) has a result for every allowed input." ``P2653 ``p2653,
  entry "showcov-show-l2712" "base/show.jl" "type_limited_string_from_context(out::IO, str::String)" "The source-order model of type_limited_string_from_context(out::IO, str::String) has a result for every allowed input." ``P2712 ``p2712,
  entry "showcov-show-l2726" "base/show.jl" "type_depth_limit(str::String, n::Int; maxdepth = nothing)" "The source-order model of type_depth_limit(str::String, n::Int; maxdepth = nothing) has a result for every allowed input." ``P2726 ``p2726,
  entry "showcov-show-l2734" "base/show.jl" "stateis(s)" "The source-order model of stateis(s) has a result for every allowed input." ``P2734 ``p2734,
  entry "showcov-show-l2735" "base/show.jl" "quoted()" "The source-order model of quoted() has a result for every allowed input." ``P2735 ``p2735,
  entry "showcov-show-l2736" "base/show.jl" "enter(s)" "The source-order model of enter(s) has a result for every allowed input." ``P2736 ``p2736,
  entry "showcov-show-l2737" "base/show.jl" "leave(s)" "The source-order model of leave(s) has a result for every allowed input." ``P2737 ``p2737,
  entry "showcov-show-l2818" "base/show.jl" "print_type_bicolor(io, type; kwargs...)" "The source-order model of print_type_bicolor(io, type; kwargs...) has a result for every allowed input." ``P2818 ``p2818,
  entry "showcov-show-l2823" "base/show.jl" "print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true)" "The source-order model of print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true) has a result for every allowed input." ``P2823 ``p2823,
  entry "showcov-show-l2840" "base/show.jl" "resolvebinding(@nospecialize(ex))" "The source-order model of resolvebinding(@nospecialize(ex)) has a result for every allowed input." ``P2840 ``p2840,
  entry "showcov-show-l2841" "base/show.jl" "resolvebinding(ex::QuoteNode)" "The source-order model of resolvebinding(ex::QuoteNode) has a result for every allowed input." ``P2841 ``p2841,
  entry "showcov-show-l2842" "base/show.jl" "resolvebinding(ex::Symbol)" "The source-order model of resolvebinding(ex::Symbol) has a result for every allowed input." ``P2842 ``p2842,
  entry "showcov-show-l2843" "base/show.jl" "resolvebinding(ex::Expr)" "The source-order model of resolvebinding(ex::Expr) has a result for every allowed input." ``P2843 ``p2843,
  entry "showcov-show-l2852" "base/show.jl" "resolvebinding(ex::GlobalRef)" "The source-order model of resolvebinding(ex::GlobalRef) has a result for every allowed input." ``P2852 ``p2852,
  entry "showcov-show-l2860" "base/show.jl" "ismodulecall(ex::Expr)" "The source-order model of ismodulecall(ex::Expr) has a result for every allowed input." ``P2860 ``p2860,
  entry "showcov-show-l2866" "base/show.jl" "show(io::IO, tv::TypeVar)" "The source-order model of show(io::IO, tv::TypeVar) has a result for every allowed input." ``P2866 ``p2866,
  entry "showcov-show-l2873" "base/show.jl" "show_bound(io::IO, @nospecialize(b))" "The source-order model of show_bound(io::IO, @nospecialize(b)) has a result for every allowed input." ``P2873 ``p2873,
  entry "showcov-show-l2901" "base/show.jl" "show(io::IO, vm::Core.TypeofVararg)" "The source-order model of show(io::IO, vm::Core.TypeofVararg) has a result for every allowed input." ``P2901 ``p2901,
  entry "showcov-show-l2916" "base/show.jl" "show(io::IO, src::CodeInfo; debuginfo::Symbol=:source)" "The source-order model of show(io::IO, src::CodeInfo; debuginfo::Symbol=:source) has a result for every allowed input." ``P2916 ``p2916,
  entry "showcov-show-l2931" "base/show.jl" "show_unquoted(io::IO, val::Argument, indent::Int, prec::Int)" "The source-order model of show_unquoted(io::IO, val::Argument, indent::Int, prec::Int) has a result for every allowed input." ``P2931 ``p2931,
  entry "showcov-show-l2933" "base/show.jl" "show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int) has a result for every allowed input." ``P2933 ``p2933,
  entry "showcov-show-l2934" "base/show.jl" "show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String)" "The source-order model of show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String) has a result for every allowed input." ``P2934 ``p2934,
  entry "showcov-show-l2949" "base/show.jl" "show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int) has a result for every allowed input." ``P2949 ``p2949,
  entry "showcov-show-l2959" "base/show.jl" "show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int) has a result for every allowed input." ``P2959 ``p2959,
  entry "showcov-show-l2967" "base/show.jl" "show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int) has a result for every allowed input." ``P2967 ``p2967,
  entry "showcov-show-l2975" "base/show.jl" "show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int) has a result for every allowed input." ``P2975 ``p2975,
  entry "showcov-show-l2984" "base/show.jl" "show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int) has a result for every allowed input." ``P2984 ``p2984,
  entry "showcov-show-l2985" "base/show.jl" "show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String)" "The source-order model of show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String) has a result for every allowed input." ``P2985 ``p2985,
  entry "showcov-show-l2990" "base/show.jl" "dump(io::IOContext, x::SimpleVector, n::Int, indent)" "The source-order model of dump(io::IOContext, x::SimpleVector, n::Int, indent) has a result for every allowed input." ``P2990 ``p2990,
  entry "showcov-show-l3010" "base/show.jl" "dump(io::IOContext, @nospecialize(x), n::Int, indent)" "The source-order model of dump(io::IOContext, @nospecialize(x), n::Int, indent) has a result for every allowed input." ``P3010 ``p3010,
  entry "showcov-show-l3043" "base/show.jl" "dump(io::IOContext, x::Module, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Module, n::Int, indent) has a result for every allowed input." ``P3043 ``p3043,
  entry "showcov-show-l3044" "base/show.jl" "dump(io::IOContext, x::String, n::Int, indent)" "The source-order model of dump(io::IOContext, x::String, n::Int, indent) has a result for every allowed input." ``P3044 ``p3044,
  entry "showcov-show-l3045" "base/show.jl" "dump(io::IOContext, x::Symbol, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Symbol, n::Int, indent) has a result for every allowed input." ``P3045 ``p3045,
  entry "showcov-show-l3046" "base/show.jl" "dump(io::IOContext, x::Union, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Union, n::Int, indent) has a result for every allowed input." ``P3046 ``p3046,
  entry "showcov-show-l3047" "base/show.jl" "dump(io::IOContext, x::Ptr, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Ptr, n::Int, indent) has a result for every allowed input." ``P3047 ``p3047,
  entry "showcov-show-l3049" "base/show.jl" "dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1)" "The source-order model of dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1) has a result for every allowed input." ``P3049 ``p3049,
  entry "showcov-show-l3061" "base/show.jl" "dump(io::IOContext, x::Array, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Array, n::Int, indent) has a result for every allowed input." ``P3061 ``p3061,
  entry "showcov-show-l3087" "base/show.jl" "dump(io::IOContext, x::DataType, n::Int, indent)" "The source-order model of dump(io::IOContext, x::DataType, n::Int, indent) has a result for every allowed input." ``P3087 ``p3087,
  entry "showcov-show-l3130" "base/show.jl" "dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH)" "The source-order model of dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH) has a result for every allowed input." ``P3130 ``p3130,
  entry "showcov-show-l3163" "base/show.jl" "dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH)" "The source-order model of dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH) has a result for every allowed input." ``P3163 ``p3163,
  entry "showcov-show-l3169" "base/show.jl" "nocolor(io::IO)" "The source-order model of nocolor(io::IO) has a result for every allowed input." ``P3169 ``p3169,
  entry "showcov-show-l3170" "base/show.jl" "alignment_from_show(io::IO, x::Any)" "The source-order model of alignment_from_show(io::IO, x::Any) has a result for every allowed input." ``P3170 ``p3170,
  entry "showcov-show-l3172" "base/show.jl" "alignment_from_show(io::IO, x::AbstractString)" "The source-order model of alignment_from_show(io::IO, x::AbstractString) has a result for every allowed input." ``P3172 ``p3172,
  entry "showcov-show-l3191" "base/show.jl" "alignment(io::IO, x::Any)" "The source-order model of alignment(io::IO, x::Any) has a result for every allowed input." ``P3191 ``p3191,
  entry "showcov-show-l3192" "base/show.jl" "alignment(io::IO, x::Number)" "The source-order model of alignment(io::IO, x::Number) has a result for every allowed input." ``P3192 ``p3192,
  entry "showcov-show-l3193" "base/show.jl" "alignment(io::IO, x::Integer)" "The source-order model of alignment(io::IO, x::Integer) has a result for every allowed input." ``P3193 ``p3193,
  entry "showcov-show-l3194" "base/show.jl" "alignment(io::IO, x::Real)" "The source-order model of alignment(io::IO, x::Real) has a result for every allowed input." ``P3194 ``p3194,
  entry "showcov-show-l3200" "base/show.jl" "alignment(io::IO, x::Complex)" "The source-order model of alignment(io::IO, x::Complex) has a result for every allowed input." ``P3200 ``p3200,
  entry "showcov-show-l3206" "base/show.jl" "alignment(io::IO, x::Rational)" "The source-order model of alignment(io::IO, x::Rational) has a result for every allowed input." ``P3206 ``p3206,
  entry "showcov-show-l3213" "base/show.jl" "alignment(io::IO, x::Pair)" "The source-order model of alignment(io::IO, x::Pair) has a result for every allowed input." ``P3213 ``p3213,
  entry "showcov-show-l3228" "base/show.jl" "show(io::IO, ::UndefInitializer)" "The source-order model of show(io::IO, ::UndefInitializer) has a result for every allowed input." ``P3228 ``p3228,
  entry "showcov-show-l3249" "base/show.jl" "summary(io::IO, x)" "The source-order model of summary(io::IO, x) has a result for every allowed input." ``P3249 ``p3249,
  entry "showcov-show-l3250" "base/show.jl" "summary(x)" "The source-order model of summary(x) has a result for every allowed input." ``P3250 ``p3250,
  entry "showcov-show-l3258" "base/show.jl" "dims2string(d)" "The source-order model of dims2string(d) has a result for every allowed input." ``P3258 ``p3258,
  entry "showcov-show-l3262" "base/show.jl" "inds2string(inds)" "The source-order model of inds2string(inds) has a result for every allowed input." ``P3262 ``p3262,
  entry "showcov-show-l3263" "base/show.jl" "_indsstring(i)" "The source-order model of _indsstring(i) has a result for every allowed input." ``P3263 ``p3263,
  entry "showcov-show-l3264" "base/show.jl" "_indsstring(i::Union{IdentityUnitRange, Slice})" "The source-order model of _indsstring(i::Union{IdentityUnitRange, Slice}) has a result for every allowed input." ``P3264 ``p3264,
  entry "showcov-show-l3267" "base/show.jl" "summary(io::IO, a::AbstractArray)" "The source-order model of summary(io::IO, a::AbstractArray) has a result for every allowed input." ``P3267 ``p3267,
  entry "showcov-show-l3268" "base/show.jl" "array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}})" "The source-order model of array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}}) has a result for every allowed input." ``P3268 ``p3268,
  entry "showcov-show-l3272" "base/show.jl" "array_summary(io::IO, a, inds)" "The source-order model of array_summary(io::IO, a, inds) has a result for every allowed input." ``P3272 ``p3272,
  entry "showcov-show-l3279" "base/show.jl" "summary(io::IO, mref::GenericMemoryRef)" "The source-order model of summary(io::IO, mref::GenericMemoryRef) has a result for every allowed input." ``P3279 ``p3279,
  entry "showcov-show-l3287" "base/show.jl" "summary(io::IO, f::Function)" "The source-order model of summary(io::IO, f::Function) has a result for every allowed input." ``P3287 ``p3287,
  entry "showcov-show-l3335" "base/show.jl" "showarg(io::IO, @nospecialize(x), toplevel)" "The source-order model of showarg(io::IO, @nospecialize(x), toplevel) has a result for every allowed input." ``P3335 ``p3335,
  entry "showcov-show-l3339" "base/show.jl" "showarg(io::IO, T::Type, toplevel)" "The source-order model of showarg(io::IO, T::Type, toplevel) has a result for every allowed input." ``P3339 ``p3339,
  entry "showcov-show-l3344" "base/show.jl" "showarg(io::IO, a::Array{Union{}}, toplevel)" "The source-order model of showarg(io::IO, a::Array{Union{}}, toplevel) has a result for every allowed input." ``P3344 ``p3344,
  entry "showcov-show-l3350" "base/show.jl" "showarg(io::IO, v::SubArray, toplevel)" "The source-order model of showarg(io::IO, v::SubArray, toplevel) has a result for every allowed input." ``P3350 ``p3350,
  entry "showcov-show-l3358" "base/show.jl" "showindices(io, ::Slice, inds...)" "The source-order model of showindices(io, ::Slice, inds...) has a result for every allowed input." ``P3358 ``p3358,
  entry "showcov-show-l3360" "base/show.jl" "showindices(io, ind1, inds...)" "The source-order model of showindices(io, ind1, inds...) has a result for every allowed input." ``P3360 ``p3360,
  entry "showcov-show-l3362" "base/show.jl" "showindices(io)" "The source-order model of showindices(io) has a result for every allowed input." ``P3362 ``p3362,
  entry "showcov-show-l3364" "base/show.jl" "showarg(io::IO, r::ReshapedArray, toplevel)" "The source-order model of showarg(io::IO, r::ReshapedArray, toplevel) has a result for every allowed input." ``P3364 ``p3364,
  entry "showcov-show-l3375" "base/show.jl" "showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T}" "The source-order model of showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T} has a result for every allowed input." ``P3375 ``p3375,
  entry "showcov-show-l3381" "base/show.jl" "showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T}" "The source-order model of showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T} has a result for every allowed input." ``P3381 ``p3381,
  entry "showcov-show-l3391" "base/show.jl" "show(io::IO, e::Iterators.Enumerate)" "The source-order model of show(io::IO, e::Iterators.Enumerate) has a result for every allowed input." ``P3391 ``p3391,
  entry "showcov-show-l3396" "base/show.jl" "show(io::IO, z::Iterators.Zip)" "The source-order model of show(io::IO, z::Iterators.Zip) has a result for every allowed input." ``P3396 ``p3396,
  entry "showcov-show-l3399" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray has a result for every allowed input." ``P3399 ``p3399,
  entry "showcov-show-l3403" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple}" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple} has a result for every allowed input." ``P3403 ``p3403,
  entry "showcov-show-l3407" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I}" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I} has a result for every allowed input." ``P3407 ``p3407,
  entry "showcov-show-l3415" "base/show.jl" "print_bit_chunk(io::IO, c::UInt64, l::Integer = 64)" "The source-order model of print_bit_chunk(io::IO, c::UInt64, l::Integer = 64) has a result for every allowed input." ``P3415 ``p3415,
  entry "showcov-show-l3425" "base/show.jl" "print_bit_chunk(c::UInt64, l::Integer)" "The source-order model of print_bit_chunk(c::UInt64, l::Integer) has a result for every allowed input." ``P3425 ``p3425,
  entry "showcov-show-l3426" "base/show.jl" "print_bit_chunk(c::UInt64)" "The source-order model of print_bit_chunk(c::UInt64) has a result for every allowed input." ``P3426 ``p3426,
  entry "showcov-show-l3428" "base/show.jl" "bitshow(io::IO, B::BitArray)" "The source-order model of bitshow(io::IO, B::BitArray) has a result for every allowed input." ``P3428 ``p3428,
  entry "showcov-show-l3438" "base/show.jl" "bitshow(B::BitArray)" "The source-order model of bitshow(B::BitArray) has a result for every allowed input." ``P3438 ``p3438,
  entry "showcov-show-l3440" "base/show.jl" "bitstring(B::BitArray)" "The source-order model of bitstring(B::BitArray) has a result for every allowed input." ``P3440 ``p3440,
  entry "showcov-show-l3443" "base/show.jl" "show(io::IO, oc::Core.OpaqueClosure)" "The source-order model of show(io::IO, oc::Core.OpaqueClosure) has a result for every allowed input." ``P3443 ``p3443,
  entry "showcov-show-l3450" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", oc::Core.OpaqueClosure{A, R}) where {A, R}" "The source-order model of show(io::IO, ::MIME\"text/plain\", oc::Core.OpaqueClosure{A, R}) where {A, R} has a result for every allowed input." ``P3450 ``p3450,
  entry "showcov-show-l3455" "base/show.jl" "print_partition(io::IO, partition::Core.BindingPartition)" "The source-order model of print_partition(io::IO, partition::Core.BindingPartition) has a result for every allowed input." ``P3455 ``p3455,
  entry "showcov-show-l3507" "base/show.jl" "show(io::IO, partition::Core.BindingPartition)" "The source-order model of show(io::IO, partition::Core.BindingPartition) has a result for every allowed input." ``P3507 ``p3507,
  entry "showcov-show-l3513" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", partition::Core.BindingPartition)" "The source-order model of show(io::IO, ::MIME\"text/plain\", partition::Core.BindingPartition) has a result for every allowed input." ``P3513 ``p3513,
  entry "showcov-show-l3519" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", bnd::Core.Binding)" "The source-order model of show(io::IO, ::MIME\"text/plain\", bnd::Core.Binding) has a result for every allowed input." ``P3519 ``p3519,
  entry "showcov-show-l3539" "base/show.jl" "show(io::IO, ii::IncludeInto)" "The source-order model of show(io::IO, ii::IncludeInto) has a result for every allowed input." ``P3539 ``p3539,
  entry "showcov-show-l3548" "base/show.jl" "show(io::IO, ei::Core.EvalInto)" "The source-order model of show(io::IO, ei::Core.EvalInto) has a result for every allowed input." ``P3548 ``p3548
]

end JuliaLean.Proofs.base.show

