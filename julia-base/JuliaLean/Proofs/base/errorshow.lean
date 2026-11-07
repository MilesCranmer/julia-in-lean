import JuliaLean.base.errorshow
import JuliaLean.base.strings.io
import JuliaLean.Registry.Types

namespace JuliaLean.CompletionState0

@[simp] theorem runBind {E S A B : Type} (action : ExceptT E (StateM S) A)
    (next : A → ExceptT E (StateM S) B) (state : S) :
    ((action >>= next).run state) =
      match action.run state with
      | (.ok value, final) => (next value).run final
      | (.error error, final) => (.error error, final) := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runMap {E S A B : Type} (action : ExceptT E (StateM S) A)
    (f : A → B) (state : S) :
    ((f <$> action).run state) =
      match action.run state with
      | (.ok value, final) => (.ok (f value), final)
      | (.error error, final) => (.error error, final) := by
  simp only [Functor.map, ExceptT.map, Bind.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runCatch {E S A : Type} (action : ExceptT E (StateM S) A)
    (handler : E → ExceptT E (StateM S) A) (state : S) :
    (tryCatchThe E action handler).run state =
      match action.run state with
      | (.ok value, final) => (.ok value, final)
      | (.error error, final) => (handler error).run final := by
  simp only [tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind,
    ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runPure {E S A : Type} (value : A) (state : S) :
    ((pure value : ExceptT E (StateM S) A).run state) = (.ok value, state) := rfl

@[simp] theorem runThrow {E S A : Type} (error : E) (state : S) :
    ((throwThe E error : ExceptT E (StateM S) A).run state) = (.error error, state) := rfl

@[simp] theorem runGet {E S : Type} (state : S) :
    ((get : ExceptT E (StateM S) S).run state) = (.ok state, state) := rfl

@[simp] theorem byteToListLength (bytes : ByteArray) : bytes.toList.length = bytes.size := by
  have loop : ∀ (i : Nat) (r : List UInt8),
      (ByteArray.toList.loop bytes i r).length = bytes.size - i + r.length := by
    intro i r
    fun_induction ByteArray.toList.loop bytes i r with
    | case1 i r h ih => simp only [List.length_cons] at ih; omega
    | case2 i r h => simp only [List.length_reverse]; omega
  exact loop 0 []


end JuliaLean.CompletionState0

namespace JuliaLean.Proofs.base.errorshow

namespace Round1

open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io

/-
Public forwarding/plumbing methods have no separate nontrivial statement:
* showerror@30 (base/errorshow.jl:30): the generic fallback delegates directly
  to public show(io, value); it adds no independent representation algorithm.
* showerror@120 (base/errorshow.jl:120): the two-argument LoadError overload
  supplies an empty backtrace to its three-argument renderer; the payload and
  location contracts belong to that renderer.
* showerror@127 (base/errorshow.jl:127): the two-argument InitError overload
  supplies an empty backtrace to its three-argument renderer; module and wrapped
  exception behavior belongs to that renderer.
* show@1709 (base/errorshow.jl:1709): ordinary ExceptionStack show delegates to
  its text/plain renderer; count, causal ordering and exception/backtrace
  behavior remain in that renderer's complete blocked contracts.
-/

/-- Observe an installed exception renderer after arbitrary prior bytes, using the
installed public `sprint` model with its default context and size hint.
The supplied action is the original renderer, never its expected output.
Julia source: base/strings/io.jl:104-114,242-246
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/io.jl:80-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def observeExceptionAfter {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (prior : Bytes)
    (render : JIO Unit V → BufferShowM Empty Unit) :
    Except (JuliaLean.base.strings.io.Error Empty) JuliaLean.base.strings.io.JuliaString :=
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64)
    displaySize a .none (JuliaLean.base.iobuffer.i 0)
    (fun io (_ : Unit) => do
      printBytes (bufferPrims displaySize) io prior
      render io) ()

/-- DivideError display appends its descriptive exception name and division-error
message, preserving every preceding byte, observed using canonical `sprint`.
Julia source: base/errorshow.jl:160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/errorshow.jl:3-24; base/strings/io.jl:80-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Exception documentation: base/docs/basedocs.jl:2304-2320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DivideErrorTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + (lit "DivideError: integer division error").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (showDivideError (bufferPrims displaySize)) =
      .ok ⟨prior ++ lit "DivideError: integer division error"⟩

/-- UndefRefError display appends its descriptive exception name and undefined-reference
message, preserving every preceding byte, observed using canonical `sprint`.
Julia source: base/errorshow.jl:162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/errorshow.jl:3-24; base/strings/io.jl:80-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Exception documentation: base/docs/basedocs.jl:1918-1939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UndefRefErrorTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + (lit "UndefRefError: access to undefined reference").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (showUndefRefError (bufferPrims displaySize)) =
      .ok ⟨prior ++ lit "UndefRefError: access to undefined reference"⟩

/-- EOFError display appends its descriptive exception name and end-of-file message,
preserving every preceding byte, observed using canonical `sprint`.
Julia source: base/errorshow.jl:163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/errorshow.jl:3-24; base/strings/io.jl:80-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Exception documentation: base/io.jl:12-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EOFErrorTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + (lit "EOFError: read end of file").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (showEOFError (bufferPrims displaySize)) =
      .ok ⟨prior ++ lit "EOFError: read end of file"⟩

/-- InterruptException display appends its descriptive exception name, preserving
every preceding byte, observed using canonical `sprint`.
Julia source: base/errorshow.jl:168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/errorshow.jl:3-24; base/strings/io.jl:80-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Exception documentation: base/docs/basedocs.jl:2164-2177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def InterruptExceptionTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + (lit "InterruptException:").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (showInterruptException (bufferPrims displaySize)) =
      .ok ⟨prior ++ lit "InterruptException:"⟩

/-- UndefKeywordError display preserves every byte of a constructible Symbol name
inside its missing-keyword message, including empty and non-UTF-8 names, while
preserving preceding bytes, observed using canonical `sprint`.
Julia source: base/errorshow.jl:174-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/errorshow.jl:3-24; base/strings/io.jl:80-102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Exception documentation: base/docs/basedocs.jl:2129-2148; base/boot.jl:553-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UndefKeywordErrorTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior name : Bytes),
    (0 : UInt8) ∉ name →
    prior.length + (lit "UndefKeywordError: keyword argument `").length + name.length +
      (lit "` not assigned").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (fun io => showUndefKeywordError (bufferPrims displaySize) io name) =
      .ok ⟨prior ++ lit "UndefKeywordError: keyword argument `" ++ name ++ lit "` not assigned"⟩

def TypeNameErrorTextCorrect : Prop :=
  ∀ (V Ty A : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior : Bytes) (value : A) (isUnion : A → Bool),
    let message := lit "TypeNameError: " ++
      (if isUnion value then
        lit "typename does not apply to unions whose components have different typenames"
      else lit "typename does not apply to this type")
    prior.length + message.length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (fun io => showTypeNameError (bufferPrims displaySize) isUnion io value) =
      .ok ⟨prior ++ message⟩

def BacktraceFinallyEffects : Prop :=
  ∀ (World Io V E BT R : Type)
    (render : JIO Io V → E → ExceptT ShowError (StateM World) R)
    (trace : JIO Io V → BT → ExceptT ShowError (StateM World) Unit)
    (io : JIO Io V) (ex : E) (bt : BT) (value : R)
    (initial middle final : World) (error : ShowError),
    ((render io ex).run initial = (.error error, middle) →
      (trace io bt).run middle = (.ok (), final) →
      (showErrorBacktraceWith (Ex := ShowError) render trace io ex bt true).run initial =
        (.error error, final)) ∧
    ((render io ex).run initial = (.ok value, middle) →
      (trace io bt).run middle = (.ok (), final) →
      (showErrorBacktraceWith (Ex := ShowError) render trace io ex bt true).run initial =
        (.ok value, final)) ∧
    ((render io ex).run initial = (.ok value, final) →
      (showErrorBacktraceWith (Ex := ShowError) render trace io ex bt false).run initial =
        (.ok value, final))

def InitErrorRenderingFailure : Prop :=
  ∀ (V Ty E BT : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior moduleName : Bytes) (ex : E) (bt : BT) (backtrace : Bool) (error : ShowError),
    prior.length + (lit "InitError: ").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (fun io => showInitError (bufferPrims displaySize)
        (fun _ (_ : E) (_ : BT) _ => throwThe ShowError error)
        io ex moduleName bt backtrace) = .error (.display error)

def InitErrorDefaultRenderingFailure : Prop :=
  ∀ (V Ty E Frame : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior moduleName : Bytes) (ex : E) (error : ShowError),
    prior.length + (lit "InitError: ").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (fun io => showInitErrorDefaultNative (bufferPrims displaySize)
        (fun _ (_ : E) (_ : List Frame) _ => throwThe ShowError error)
        io ex moduleName) = .error (.display error)

def CanonicalIndexRenderingFailure : Prop :=
  ∀ (V Ty A : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior func : Bytes) (value : A) (error : ShowError),
    prior.length + (lit "CanonicalIndexError: ").length + func.length +
      (lit " not defined for ").length < 2 ^ 62 →
    observeExceptionAfter a displaySize prior
      (fun io => showCanonicalIndexError (bufferPrims displaySize)
        (fun _ (_ : A) => throwThe ShowError error) io func value) = .error (.display error)

end Round1

end JuliaLean.Proofs.base.errorshow


namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean JuliaLean.base.iobuffer JuliaLean.base.show JuliaLean.base.strings.io
open JuliaLean.Proofs.base.errorshow.Round1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem esIVal (x : Int) (hlo : -2 ^ 63 ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (i x).val = x :=
  wrapInt_of_inRange .i64 x ⟨hlo, hhi⟩

theorem esUVal (x : Int) (hlo : 0 ≤ x) (hhi : x ≤ 2 ^ 64 - 1) :
    (u x).val = x :=
  wrapInt_of_inRange .u64 x ⟨hlo, hhi⟩

theorem esIAdd (a b : Int) : i a + i b = i (a + b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a + wrapInt .i64 b) = wrapInt .i64 (a + b)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega

theorem esISub (a b : Int) : i a - i b = i (a - b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a - wrapInt .i64 b) = wrapInt .i64 (a - b)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega

theorem esINeg (a : Int) : -i a = i (-a) := by
  apply Subtype.ext
  change wrapInt .i64 (-wrapInt .i64 a) = wrapInt .i64 (-a)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega

theorem esIRemU (a : Int) (hlo : 0 ≤ a) (hhi : a < 2 ^ 63) :
    JInt.rem .u64 (i a) = u a := by
  unfold JInt.rem
  rw [esIVal a (by omega) (by omega)]
  rfl

theorem esURemI (a : Int) (hlo : 0 ≤ a) (hhi : a < 2 ^ 63) :
    JInt.rem .i64 (u a) = i a := by
  unfold JInt.rem
  rw [esUVal a hlo (by omega)]
  rfl

theorem esBitLengthBound (fuel n : Nat) : bitLength fuel n ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [bitLength]
    split
    · omega
    · exact Nat.add_le_add_right (ih (n / 2)) 1

def esBuf (bytes : List UInt8) (used : Nat) : BufferState :=
  { data := bytes, isMemory := true, reinit := false, readable := true,
    writable := true, seekable := true, append := false, size := i used,
    maxsize := imaxval, ptr := i (used + 1), offset := i 0, mark := i (-1) }

theorem esGetOffset (bytes : List UInt8) (used : Nat) :
    getOffset (esBuf bytes used) = i 0 := rfl

theorem esGetCompacted (bytes : List UInt8) (used : Nat) :
    getCompacted (esBuf bytes used) = i 0 := rfl

theorem esUsedSpan (bytes : List UInt8) (used : Nat) :
    getUsedSpan (esBuf bytes used) = .ok (i 1, i used) := rfl

theorem esBufEmpty : newBufferState (bitsConversions .i64) (some (i 0)) =
    .ok (esBuf [] 0) := by
  decide


theorem esIMulThree (a : Int) : i a * i 3 = i (a * 3) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a * wrapInt .i64 3) = wrapInt .i64 (a * 3)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega


theorem esGrowthCalc (n p : Int) (hn0 : 0 ≤ n) (hn1 : n < 2 ^ 62)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 72057594037927936) :
    n ≤ (if n > (imaxval - (i p * i 3 + i (n.tdiv 8))).val then imaxval
      else i n + (i p * i 3 + i (n.tdiv 8))).val := by
  have hdiv : n.tdiv 8 = n / 8 := Int.tdiv_eq_ediv_of_nonneg hn0
  rw [esIMulThree, esIAdd]
  have hsum0 : -2 ^ 63 ≤ n + (p * 3 + n.tdiv 8) := by rw [hdiv]; omega
  have hsum1 : n + (p * 3 + n.tdiv 8) ≤ 2 ^ 63 - 1 := by rw [hdiv]; omega
  split
  · change n ≤ 2 ^ 63 - 1
    omega
  · rw [esIAdd, esIVal _ hsum0 hsum1, hdiv]
    omega

theorem esPowerBounds (e : Nat) (he : e ≤ 56) :
    0 ≤ (2 : Int) ^ e ∧ (2 : Int) ^ e ≤ 72057594037927936 := by
  have hp : 2 ^ e ≤ (72057594037927936 : Nat) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) he
  constructor
  · have hh : 0 ≤ (↑(2 ^ e : Nat) : Int) := Int.natCast_nonneg _
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using hh
  · have hh := Int.ofNat_le.mpr hp
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using hh

theorem esOverallocationInt (value : I) (hn0 : 0 ≤ value.val) (hn1 : value.val < 2 ^ 62) :
    value.val ≤ (overallocation value).val := by
  have hv : i value.val = value := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 value.val value.property
  have hbits := esBitLengthBound 64 value.val.toNat
  have he : bitLength 64 value.val.toNat * 7 / 8 ≤ 56 := by omega
  have hp := esPowerBounds _ he
  have hcalc := esGrowthCalc value.val _ hn0 hn1 hp.1 hp.2
  unfold overallocation
  simp only [show ¬ value.val < 0 from by omega, ite_false]
  simpa only [hv] using hcalc

theorem esOverallocation (n : Nat) (hn : n < 2 ^ 62) :
    (n : Int) ≤ (overallocation (i n)).val := by
  have hnval : (i n).val = n := esIVal _ (by omega) (by omega)
  have h := esOverallocationInt (i n) (by rw [hnval]; omega) (by rw [hnval]; omega)
  simpa only [hnval] using h



theorem esIMinRight (a b : I) (h : b.val ≤ a.val) : imin a b = b := by
  unfold imin
  split
  · rfl
  · apply Subtype.ext
    omega

theorem esIMinLeft (a b : I) (h : a.val ≤ b.val) : imin a b = a := by
  unfold imin
  rw [ite_eq_right (by omega)]

theorem esIMaxRight (a b : I) (h : a.val ≤ b.val) : imax a b = b := by
  unfold imax
  rw [ite_eq_right (by omega)]

theorem esIMaxLeft (a b : I) (h : b.val ≤ a.val) : imax a b = a := by
  unfold imax
  split
  · rfl
  · apply Subtype.ext
    omega

theorem esRangeLength (n : Nat) (hn : n < 2 ^ 63) : rangeLength (i 1) (i n) = i n := by
  have hnval := esIVal n (by omega) (by omega)
  unfold rangeLength
  rw [hnval]
  change (if (n : Int) < 1 then i 0 else i n - i 1 + i 1) = i n
  split
  · have : n = 0 := by omega
    subst n
    rfl
  · rw [esISub, esIAdd, Int.sub_add_cancel]

theorem esSlice (data : List UInt8) (n : Nat) : slice data 1 n = data.take n := by
  simp only [slice, Int.sub_self, Int.toNat_zero, List.drop_zero, Int.sub_add_cancel,
    Int.toNat_natCast]

theorem esCopyTo (data : List UInt8) (n cap : Nat) (hn : n ≤ data.length)
    (hc : n ≤ cap) (hn64 : n < 2 ^ 63) :
    copyto (List.replicate cap 0) (i 1) data (i 1) (i n) =
      .ok (data.take n ++ List.replicate (cap - n) 0) := by
  have hnval := esIVal n (by omega) (by omega)
  unfold copyto
  rw [hnval]
  change (if (n : Int) = 0 then _ else if (n : Int) < 0 then _ else if _ then _ else _) = _
  by_cases hz : n = 0
  · subst n
    simp only [Int.natCast_zero, ↓reduceIte, List.take_zero, Nat.sub_zero, List.nil_append]
  · have hnpos : ¬ (n : Int) = 0 := by omega
    have hnnonneg : ¬ (n : Int) < 0 := by omega
    simp only [hnpos, hnnonneg, ↓reduceIte]
    have hbound : 1 ≤ (i 1).val ∧ (i 1).val + (n : Int) - 1 ≤ (List.replicate cap (0 : UInt8)).length ∧
        1 ≤ (i 1).val ∧ (i 1).val + (n : Int) - 1 ≤ data.length := by
      change 1 ≤ (1 : Int) ∧ 1 + (n : Int) - 1 ≤ (List.replicate cap (0 : UInt8)).length ∧
        1 ≤ (1 : Int) ∧ 1 + (n : Int) - 1 ≤ data.length
      simp only [List.length_replicate]
      omega
    rw [ite_eq_left hbound]
    have hsum : (i 1).val + (n : Int) - 1 = n := by change 1 + (n : Int) - 1 = n; omega
    have hsum' : (i 1).val - 1 + (n : Int) = n := by change 1 - 1 + (n : Int) = n; omega
    rw [hsum, hsum']
    change Except.ok ([] ++ slice data 1 n ++ (List.replicate cap 0).drop n) = _
    rw [esSlice, List.nil_append, List.drop_replicate]



theorem esRunBind {ε σ α β : Type} (action : EStateM ε σ α)
    (next : α → EStateM ε σ β) (state : σ) :
    EStateM.run (EStateM.bind action next) state =
      match action.run state with
      | .ok value state => (next value).run state
      | .error error state => .error error state := by rfl

theorem esRunPure {ε σ α : Type} (value : α) (state : σ) :
    EStateM.run (EStateM.pure value : EStateM ε σ α) state = .ok value state := rfl

theorem esRunGet {ε σ : Type} (state : σ) :
    (get : EStateM ε σ σ).run state = .ok state state := rfl

theorem esRunSet {ε σ : Type} (state old : σ) :
    EStateM.run (EStateM.set state : EStateM ε σ PUnit) old = .ok ⟨⟩ state := rfl

def esLiftAction {ε ε' σ α : Type} (embed : ε → ε')
    (action : EStateM ε σ α) : EStateM ε' σ α :=
  fun state => match action state with
    | .ok value state => .ok value state
    | .error error state => .error (embed error) state

theorem esObserveLiftedActions {ε ε' σ α β γ δ : Type}
    (embed : ε → ε') (first : EStateM ε σ α) (second : EStateM ε σ β)
    (third : EStateM ε σ γ) (wrap : γ → δ) (initial : σ) :
    (match (EStateM.bind
      (EStateM.bind
        (EStateM.bind (esLiftAction embed first) (fun _ => EStateM.pure ()))
        (fun _ => EStateM.bind (esLiftAction embed second) (fun _ => EStateM.pure ())))
      (fun _ => esLiftAction embed third)).run initial with
    | .ok value _ => Except.ok (wrap value)
    | .error error _ => Except.error error) =
    (match first.run initial with
    | .error error _ => .error (embed error)
    | .ok _ state =>
      match second.run state with
      | .error error _ => .error (embed error)
      | .ok _ state =>
        match third.run state with
        | .error error _ => .error (embed error)
        | .ok value _ => .ok (wrap value)) := by
  simp only [EStateM.run, EStateM.bind, EStateM.pure, esLiftAction]
  cases hfirst : first initial with
  | error error state => rfl
  | ok value state =>
    simp only []
    cases hsecond : second state with
    | error error state' => rfl
    | ok value' state' =>
      simp only []
      cases third state' <;> rfl


theorem esResizeExactOk (state : BufferState) (capacity a b : I)
    (fresh out : List UInt8)
    (hspan : getUsedSpan state = .ok (a, b))
    (hsimilar : similarData state capacity = .ok fresh)
    (hcapacity : capacity.val ≠ 0)
    (hcopy : (if (rangeLength a b).val = 0 then Except.ok fresh
      else copyto fresh (i 1) state.data a (rangeLength a b)) = .ok out) :
    (resize capacity true).run state = .ok ()
      { state with
        data := out
        offset := -getCompacted state - (a - i 1 - getOffset state)
        ptr := state.ptr - (a - i 1)
        size := rangeLength a b } := by
  simp only [resize, bind, pure, set, esRunBind, esRunGet, esRunPure, esRunSet,
    ite_true, hspan, lift, hsimilar, hcapacity, ite_false]
  by_cases hz : (rangeLength a b).val = 0
  · have hfresh : fresh = out := by
      simpa only [hz, ite_true, Except.ok.injEq] using hcopy
    subst out
    simp only [hz, ite_true, bind, pure, set, esRunBind, esRunPure, esRunSet]
  · have hcopied : copyto fresh (i 1) state.data a (rangeLength a b) = .ok out := by
      simpa only [hz, ite_false] using hcopy
    simp only [hz, ite_false, hcopied, lift, bind, pure, set, esRunBind, esRunPure, esRunSet]

theorem esResizeRaw (data : List UInt8) (used : Nat) (capacity : I)
    (hu : used ≤ data.length) (hcap : used ≤ capacity.val.toNat) (hpos : 0 < capacity.val) :
    (resize capacity true).run (esBuf data used) =
      .ok () (esBuf (data.take used ++ List.replicate (capacity.val.toNat - used) 0) used) := by
  have hamax := capacity.property.2
  have hatoNat : (capacity.val.toNat : Int) = capacity.val := Int.toNat_of_nonneg (by omega)
  have hused : used < 2 ^ 63 := by
    change capacity.val ≤ 2 ^ 63 - 1 at hamax
    omega
  have hsimilar : similarData (esBuf data used) capacity =
      .ok (List.replicate capacity.val.toNat 0) := by
    simp only [similarData, esBuf, ite_true, stringMemory,
      Int.not_lt.mpr (show 0 ≤ capacity.val by omega), ite_false]
  have hrange := esRangeLength used hused
  have hcopy : (if (rangeLength (i 1) (i used)).val = 0 then
      Except.ok (List.replicate capacity.val.toNat 0)
      else copyto (List.replicate capacity.val.toNat 0) (i 1) data (i 1)
        (rangeLength (i 1) (i used))) =
      .ok (data.take used ++ List.replicate (capacity.val.toNat - used) 0) := by
    rw [hrange, esIVal _ (by omega) (by omega)]
    by_cases hz : used = 0
    · subst used
      simp only [Int.natCast_zero, ite_true, List.take_zero, Nat.sub_zero, List.nil_append]
    · rw [ite_eq_right (by omega : ¬ (used : Int) = 0)]
      exact esCopyTo data used _ hu hcap hused
  have hrun := esResizeExactOk (esBuf data used) capacity (i 1) (i used)
    (List.replicate capacity.val.toNat 0)
    (data.take used ++ List.replicate (capacity.val.toNat - used) 0)
    (esUsedSpan data used) hsimilar (by omega) hcopy
  simp only [esGetOffset, esGetCompacted, hrange, esISub, esINeg,
    Int.sub_self, Int.sub_zero, Int.neg_zero] at hrun
  simpa only [esBuf, esISub, Int.sub_zero] using hrun

theorem esResizePick (state : BufferState) (requested : I) :
    (resize requested false).run state =
      (resize (imin state.maxsize (overallocation requested)) true).run state := by
  simp only [resize, bind, pure, set, esRunBind, esRunGet, Bool.false_eq_true, ite_false, ite_true]

theorem esResize (data : List UInt8) (used requested : Nat)
    (hu : used ≤ data.length) (hur : used ≤ requested) (hr : requested < 2 ^ 62) :
    (resize (i requested) false).run (esBuf data used) =
      .ok () (esBuf (data.take used ++
        List.replicate ((overallocation (i requested)).val.toNat - used) 0) used) := by
  have ha := esOverallocation requested hr
  have hamax := (overallocation (i requested)).property.2
  have hapos : 0 < (overallocation (i requested)).val := by
    by_cases hz : requested = 0
    · subst requested
      decide
    · omega
  have hcap : used ≤ (overallocation (i requested)).val.toNat := by omega
  rw [esResizePick]
  simp only [show (esBuf data used).maxsize = imaxval from rfl,
    esIMinRight imaxval (overallocation (i requested)) hamax]
  exact esResizeRaw data used _ hu hcap hapos

theorem esAvailable (data : List UInt8) (used : Nat) (hu : used ≤ data.length)
    (hc : data.length < 2 ^ 63) :
    imin (i data.length - ((esBuf data used).ptr - i 1))
      ((esBuf data used).maxsize - ((esBuf data used).ptr - i 1 - getOffset (esBuf data used))) =
      i ((data.length : Int) - used) := by
  change imin (i data.length - (i ((used : Int) + 1) - i 1))
    (imaxval - (i ((used : Int) + 1) - i 1 - i 0)) = _
  simp only [esISub, Int.add_sub_cancel, Int.sub_zero, imaxval]
  apply esIMinLeft
  rw [esIVal _ (by omega) (by omega), esIVal _ (by omega) (by omega)]
  omega

theorem esUMinLeft (a b : U) (h : a.val ≤ b.val) : uminU a b = a := by
  unfold uminU
  rw [ite_eq_right (by omega)]

theorem esRoomEnough (data : List UInt8) (used count : Nat)
    (henough : used + count ≤ data.length) (hc : data.length < 2 ^ 63) :
    (ensureroom (u count)).run (esBuf data used) = .ok () (esBuf data used) := by
  have hav := esAvailable data used (by omega) hc
  have hrem := esURemI count (by omega) (by omega)
  simp only [ensureroom, bind, pure, set, esRunBind, esRunGet]
  simp only [show (esBuf data used).writable = true from rfl,
    show (esBuf data used).reinit = false from rfl,
    show (esBuf data used).append = false from rfl,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
  simp only [show (esBuf data used).data = data from rfl]
  rw [hav, hrem]
  rw [esIVal _ (by omega) (by omega), esIVal _ (by omega) (by omega)]
  rw [ite_eq_right (by omega)]
  rfl

theorem esWriteAt (data src : List UInt8) (used : Nat)
    (henough : used + src.length ≤ data.length) (hu : used + 1 < 2 ^ 63) :
    writeAt true data (i ((used : Int) + 1)) src =
      .ok (data.take used ++ src ++ data.drop (used + src.length)) := by
  unfold writeAt
  by_cases hs : src.length = 0
  · have he : src = [] := List.eq_nil_of_length_eq_zero hs
    subst src
    simp only [List.length_nil, Nat.add_zero, ite_true, List.append_nil,
      List.take_append_drop]
  · rw [ite_eq_right hs]
    rw [esIVal _ (by omega) (by omega)]
    rw [ite_eq_left (by omega)]
    have hsub : (used : Int) + 1 - 1 = used := by omega
    have htotal : (used : Int) + 1 - 1 + src.length = (used + src.length : Nat) := by omega
    rw [hsub, ← Int.natCast_add, Int.toNat_natCast, Int.toNat_natCast]


theorem esToIValue (value : I) : toI value.val = .ok value := by
  unfold toI JInt.convert
  rw [dite_eq_left value.property]

theorem esToI (n : Nat) (hn : n < 2 ^ 63) : toI n = .ok (i n) := by
  have hv := esIVal n (by omega) (by omega)
  have h := esToIValue (i n)
  simpa only [hv] using h

theorem esRoomSlow (data : List UInt8) (used count : Nat)
    (hu : used ≤ data.length) (hc : data.length < 2 ^ 63) (ht : used + count < 2 ^ 62) :
    (ensureroomSlowpath (u count) (i ((data.length : Int) - used))).run (esBuf data used) =
      (resize (i (used + count)) false).run (esBuf data used) := by
  have hcount : count < 2 ^ 63 := by omega
  have hconvert : toI (u count).val = .ok (i count) := by
    rw [esUVal _ (by omega) (by omega)]
    exact esToI count hcount
  have hdesired : i data.length + i count - i ((data.length : Int) - used) =
      i (used + count) := by
    rw [esIAdd, esISub]
    apply congrArg i
    omega
  simp only [ensureroomSlowpath, bind, pure, set, esRunBind, esRunGet, esUsedSpan, lift, esRunPure]
  simp only [show i 1 - i 1 = i 0 from rfl, show (i 0).val = (0 : Int) from rfl,
    show ¬ (0 : Int) ≥ 32 from by decide, false_and, ite_false]
  rw [hconvert]
  simp only [lift, bind, pure, set, esRunPure, esRunBind]
  simp only [show (esBuf data used).data = data from rfl,
    show (esBuf data used).maxsize = imaxval from rfl]
  rw [hdesired]
  rw [esIVal ((used : Int) + count) (by omega) (by omega)]
  rw [ite_eq_right (by change ¬ ((used : Int) + count) > (2 ^ 63 - 1 : Int); omega)]

theorem esRoom (data : List UInt8) (used count : Nat)
    (hu : used ≤ data.length) (hc : data.length < 2 ^ 63) (ht : used + count < 2 ^ 62) :
    ∃ grown : List UInt8,
      (ensureroom (u count)).run (esBuf data used) = .ok () (esBuf grown used) ∧
      grown.take used = data.take used ∧ used + count ≤ grown.length ∧ grown.length < 2 ^ 63 := by
  by_cases enough : used + count ≤ data.length
  · exact ⟨data, esRoomEnough data used count enough hc, rfl, enough, hc⟩
  · let cap := (overallocation (i ((used : Int) + (count : Int)))).val.toNat
    let grown := data.take used ++ List.replicate (cap - used) 0
    have ha : ((used : Int) + (count : Int)) ≤
        (overallocation (i ((used : Int) + (count : Int)))).val := by
      simpa only [Int.natCast_add] using esOverallocation (used + count) ht
    have hamax := (overallocation (i ((used : Int) + (count : Int)))).property.2
    have ha0 : 0 ≤ (overallocation (i ((used : Int) + (count : Int)))).val := by omega
    have hcap : used + count ≤ cap := by dsimp [cap]; omega
    have hcap64 : cap < 2 ^ 63 := by dsimp [cap]; change _ ≤ 2 ^ 63 - 1 at hamax; omega
    have hlen : grown.length = cap := by
      dsimp [grown]
      rw [List.length_append, List.length_take_of_le hu, List.length_replicate]
      omega
    refine ⟨grown, ?_, ?_, by rw [hlen]; exact hcap, by rw [hlen]; exact hcap64⟩
    · have hav := esAvailable data used hu hc
      simp only [ensureroom, bind, pure, set, esRunBind, esRunGet, esRunPure,
        show (esBuf data used).writable = true from rfl,
        show (esBuf data used).reinit = false from rfl,
        show (esBuf data used).append = false from rfl,
        show (esBuf data used).data = data from rfl,
        Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
      rw [hav]
      rw [esURemI count (by omega) (by omega)]
      rw [esIVal _ (by omega) (by omega), esIVal _ (by omega) (by omega)]
      rw [ite_eq_left (by omega)]
      rw [esRoomSlow data used count hu hc ht]
      simpa only [grown, cap, Int.natCast_add] using esResize data used (used + count) hu (by omega) ht
    · have hlt : (data.take used).length = used := List.length_take_of_le hu
      simpa only [hlt] using
        (List.take_append_length (l₁ := data.take used) (l₂ := List.replicate (cap - used) 0))


theorem esTakeString (data : List UInt8) (used : Nat) (hu : used < 2 ^ 63) :
    ∃ final, takestring.run (esBuf data used) = .ok (data.take used) final := by
  simp only [takestring, bind, pure, set, esRunBind, esRunGet,
    show (esBuf data used).isMemory = true from rfl,
    show (esBuf data used).reinit = false from rfl,
    show (esBuf data used).writable = true from rfl,
    Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rw [esUsedSpan]
  simp only [lift, bind, pure, set, esRunPure, esRunBind, esRunSet]
  rw [esRangeLength used hu, esIVal _ (by omega) (by omega)]
  by_cases hz : used = 0
  · subst used
    simp only [Int.natCast_zero, ite_true, List.take_zero]
    exact ⟨_, rfl⟩
  · rw [ite_eq_right (by omega : ¬(used : Int) = 0)]
    simp only [show (esBuf data used).data = data from rfl,
      show (i 1).val = (1 : Int) from rfl, esSlice]
    exact ⟨_, rfl⟩

theorem esLiftRun {α : Type} (action : M α) (state : BufferState) :
    (liftBuffer (E := Empty) action).run state =
      match action.run state with
      | .ok value state => .ok value state
      | .error error state => .error (.buffer error) state := rfl

theorem esPrintAction {V : Type} (ds : JInt64 × JInt64) (bytes : Bytes) :
    printBytes (bufferPrims (E := Empty) ds) (JIO.plain (V := V) ()) bytes =
      EStateM.bind (liftBuffer (E := Empty) (unsafeWrite bytes)) (fun _ => EStateM.pure ()) := rfl

theorem esPrintRun {V : Type} (ds : JInt64 × JInt64) (bytes : Bytes) (state : BufferState) :
    (printBytes (bufferPrims (E := Empty) ds) (JIO.plain (V := V) ()) bytes).run state =
      match (unsafeWrite bytes).run state with
      | .ok _ state => .ok () state
      | .error error state => .error (.buffer error) state := by
  rw [esPrintAction, esRunBind, esLiftRun]
  cases (unsafeWrite bytes).run state <;> rfl


end JuliaLean.ChatGPT.Batch4.Group24


namespace JuliaLean.ChatGPT.Batch9.Group18

open JuliaLean JuliaLean.base.iobuffer JuliaLean.base.show JuliaLean.base.strings.io
open JuliaLean.base.errorshow JuliaLean.Proofs.base.errorshow.Round1
open JuliaLean.ChatGPT.Batch4.Group24

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem errorCount (capacity used count : Nat)
    (henough : used + count ≤ capacity) (hcap : capacity < 2 ^ 63) :
    imax (i 0) (JInt.rem .i64
      (uminU (u count) (JInt.rem .u64 (i ((capacity : Int) - used))))) = i count := by
  rw [esIRemU _ (by omega) (by omega)]
  rw [esUMinLeft (u count) (u ((capacity : Int) - used)) (by
    rw [esUVal _ (by omega) (by omega), esUVal _ (by omega) (by omega)]
    omega)]
  rw [esURemI _ (by omega) (by omega)]
  apply esIMaxRight
  rw [esIVal (count : Int) (by omega) (by omega), esIVal 0 (by omega) (by omega)]
  omega

theorem errorUpdatedState (data output : List UInt8) (used count : Nat)
    (ht : used + count < 2 ^ 62) :
    { (esBuf data used) with
      data := output
      size := imax (esBuf data used).size ((esBuf data used).ptr - i 1 + i count)
      ptr := (esBuf data used).ptr + i count } = esBuf output (used + count) := by
  have hsize : imax (i used) (i ((used : Int) + 1) - i 1 + i count) =
      i ((used : Int) + count) := by
    rw [esISub, Int.add_sub_cancel, esIAdd]
    apply esIMaxRight
    rw [esIVal _ (by omega) (by omega), esIVal _ (by omega) (by omega)]
    omega
  simp only [esBuf, hsize, esIAdd, Int.natCast_add,
    show (used : Int) + 1 + count = (used : Int) + count + 1 from by omega]


theorem errorWriteRun (src : List UInt8) (initial next : BufferState)
    (count : I) (out : List UInt8)
    (hroom : (ensureroom (u src.length)).run initial = .ok () next)
    (happend : next.append = false)
    (hcount : imax (i 0) (JInt.rem .i64 (uminU (u src.length)
      (JInt.rem .u64 (imin (i next.data.length - (next.ptr - i 1))
        (next.maxsize - (next.ptr - i 1 - getOffset next)))))) = count)
    (hwrite : writeAt next.isMemory next.data next.ptr (src.take count.val.toNat) = .ok out) :
    (unsafeWrite src).run initial = .ok count
      { next with
        data := out
        size := imax next.size (next.ptr - i 1 + count)
        ptr := next.ptr + count } := by
  unfold unsafeWrite
  simp only [bind]
  rw [esRunBind, hroom]
  simp only []
  rw [esRunBind, esRunGet]
  simp only []
  rw [happend]
  simp only [Bool.false_eq_true, ite_false]
  rw [hcount]
  simp only [pure, set, bind]
  rw [esRunBind, hwrite]
  simp only [lift, pure]
  rw [esRunPure]
  simp only []
  rw [esRunBind, esRunSet]
  rfl

theorem errorWriteCanonical (data src : List UInt8) (used : Nat)
    (hu : used ≤ data.length) (hc : data.length < 2 ^ 63)
    (ht : used + src.length < 2 ^ 62) :
    ∃ output : List UInt8,
      (unsafeWrite src).run (esBuf data used) =
        .ok (i src.length) (esBuf output (used + src.length)) ∧
      output.take (used + src.length) = data.take used ++ src ∧
      used + src.length ≤ output.length ∧ output.length < 2 ^ 63 := by
  obtain ⟨grown, hroom, hprefix, henough, hcap⟩ := esRoom data used src.length hu hc ht
  let output := grown.take used ++ src ++ grown.drop (used + src.length)
  have hgrown : used ≤ grown.length := by omega
  have hlen : output.length = grown.length := by
    dsimp [output]
    simp only [List.length_append, List.length_take_of_le hgrown, List.length_drop]
    omega
  refine ⟨output, ?_, ?_, by rw [hlen]; exact henough, by rw [hlen]; exact hcap⟩
  · have hav := esAvailable grown used hgrown hcap
    have hwrite := esWriteAt grown src used henough (by omega)
    have hinner := errorCount grown.length used src.length henough hcap
    have hcount : imax (i 0) (JInt.rem .i64 (uminU (u src.length)
      (JInt.rem .u64 (imin (i (esBuf grown used).data.length - ((esBuf grown used).ptr - i 1))
        ((esBuf grown used).maxsize - ((esBuf grown used).ptr - i 1 - getOffset (esBuf grown used))))))) =
        i src.length := by
      change imax (i 0) (JInt.rem .i64 (uminU (u src.length)
        (JInt.rem .u64 (imin (i grown.length - ((esBuf grown used).ptr - i 1))
          ((esBuf grown used).maxsize - ((esBuf grown used).ptr - i 1 - getOffset (esBuf grown used))))))) = _
      rw [hav, hinner]
    have hwrite' : writeAt (esBuf grown used).isMemory (esBuf grown used).data
        (esBuf grown used).ptr (src.take (i src.length).val.toNat) = .ok output := by
      rw [esIVal (src.length : Int) (by omega) (by omega), Int.toNat_natCast, List.take_length]
      exact hwrite
    have hrun := errorWriteRun src (esBuf data used) (esBuf grown used) (i src.length)
      output hroom rfl hcount hwrite'
    rw [errorUpdatedState grown output used src.length ht] at hrun
    exact hrun
  · have hl : (grown.take used ++ src).length = used + src.length := by
      rw [List.length_append, List.length_take_of_le hgrown]
    dsimp [output]
    rw [← hl, List.take_append_length, hprefix]


theorem errorEvalBind {ε σ α β : Type} (action : EStateM ε σ α)
    (next : α → EStateM ε σ β) (state : σ) :
    EStateM.bind action next state =
      match action.run state with
      | .ok value state => (next value).run state
      | .error error state => .error error state := rfl

theorem errorPureBind {ε σ α β : Type} (value : α) (next : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure value) next = next value := rfl

theorem errorSprintSuccess {V Ty Args R : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (f : JIO Unit V → Args → BufferShowM Empty R)
    (args : Args) (result : R) (state final : BufferState) (bytes : Bytes)
    (hrun : (f (.plain ()) args).run (esBuf [] 0) = .ok result state)
    (htake : takestring.run state = .ok bytes final) :
    sprintIOBuffer (bitsConversions .i64) displaySize a .none (i 0) f args =
      .ok ⟨bytes⟩ := by
  unfold sprintIOBuffer
  rw [esBufEmpty]
  simp only [Except.mapError, Except.bind, bind, pure, sprintContext]
  rw [errorPureBind]
  simp only [Except.pure]
  rw [errorEvalBind, hrun]
  simp only []
  rw [esLiftRun, htake]

theorem errorPrintSuccess {V : Type} (displaySize : JInt64 × JInt64)
    (bytes : Bytes) (initial final : BufferState) (count : I)
    (hwrite : (unsafeWrite bytes).run initial = .ok count final) :
    (printBytes (bufferPrims (E := Empty) displaySize) (JIO.plain (V := V) ()) bytes).run initial =
      .ok () final := by
  rw [esPrintRun, hwrite]

theorem errorRunTwo {ε σ α β : Type} (first : EStateM ε σ α)
    (second : EStateM ε σ β) (initial middle final : σ) (a : α) (b : β)
    (hfirst : first.run initial = .ok a middle)
    (hsecond : second.run middle = .ok b final) :
    (first >>= fun _ => second).run initial = .ok b final := by
  simp only [bind]
  rw [esRunBind, hfirst]
  exact hsecond

theorem errorObserveSuccess {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (prior message result : Bytes)
    (first second final : BufferState) (nprior nmessage : I)
    (hfirst : (unsafeWrite prior).run (esBuf [] 0) = .ok nprior first)
    (hsecond : (unsafeWrite message).run first = .ok nmessage second)
    (htake : takestring.run second = .ok result final) :
    observeExceptionAfter a displaySize prior
      (fun io => printBytes (bufferPrims displaySize) io message) = .ok ⟨result⟩ := by
  apply errorSprintSuccess a displaySize _ () () second final result
  · exact errorRunTwo _ _ _ _ _ () ()
      (errorPrintSuccess displaySize prior (esBuf [] 0) first nprior hfirst)
      (errorPrintSuccess displaySize message first second nmessage hsecond)
  · exact htake


theorem errorObserveBytes {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (prior message : Bytes)
    (ht : prior.length + message.length < 2 ^ 62) :
    observeExceptionAfter a displaySize prior
      (fun io => printBytes (bufferPrims displaySize) io message) =
      .ok ⟨prior ++ message⟩ := by
  obtain ⟨first, hfirst, hpfirst, hufirst, hcfirst⟩ :=
    errorWriteCanonical [] prior 0 (by simp only [List.length_nil, Nat.le_refl])
      (by decide) (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at hfirst hpfirst hufirst
  obtain ⟨second, hsecond, hpsecond, husecond, hcsecond⟩ :=
    errorWriteCanonical first message prior.length hufirst hcfirst ht
  obtain ⟨final, htake⟩ := esTakeString second (prior.length + message.length) (by omega)
  have hout : second.take (prior.length + message.length) = prior ++ message := by
    rw [hpsecond, hpfirst]
  apply errorObserveSuccess a displaySize prior message (prior ++ message)
    (esBuf first prior.length) (esBuf second (prior.length + message.length))
    final (i prior.length) (i message.length) hfirst hsecond
  rw [htake, hout]

/-- errorshow-errorshow-l160-v2. -/
theorem ErrorshowErrorshowL160V2_proven : JuliaLean.Proofs.base.errorshow.Round1.DivideErrorTextCorrect := by
  intro V Ty a displaySize prior ht
  exact errorObserveBytes a displaySize prior (lit "DivideError: integer division error") ht

/-- errorshow-errorshow-l162-v2. -/
theorem ErrorshowErrorshowL162V2_proven : JuliaLean.Proofs.base.errorshow.Round1.UndefRefErrorTextCorrect := by
  intro V Ty a displaySize prior ht
  exact errorObserveBytes a displaySize prior (lit "UndefRefError: access to undefined reference") ht

/-- errorshow-errorshow-l163-v2. -/
theorem ErrorshowErrorshowL163V2_proven : JuliaLean.Proofs.base.errorshow.Round1.EOFErrorTextCorrect := by
  intro V Ty a displaySize prior ht
  exact errorObserveBytes a displaySize prior (lit "EOFError: read end of file") ht

/-- errorshow-errorshow-l168-v2. -/
theorem ErrorshowErrorshowL168V2_proven : JuliaLean.Proofs.base.errorshow.Round1.InterruptExceptionTextCorrect := by
  intro V Ty a displaySize prior ht
  exact errorObserveBytes a displaySize prior (lit "InterruptException:") ht

/-- errorshow-errorshow-l174-v2. -/
theorem ErrorshowErrorshowL174V2_proven : JuliaLean.Proofs.base.errorshow.Round1.UndefKeywordErrorTextCorrect := by
  intro V Ty a displaySize prior name _ ht
  have hbound : prior.length +
      (lit "UndefKeywordError: keyword argument `" ++ name ++ lit "` not assigned").length < 2 ^ 62 := by
    simp only [List.length_append]
    omega
  have h := errorObserveBytes a displaySize prior
    (lit "UndefKeywordError: keyword argument `" ++ name ++ lit "` not assigned") hbound
  simpa only [showUndefKeywordError, List.append_assoc] using h

end JuliaLean.ChatGPT.Batch9.Group18

namespace JuliaLean.Proofs.base.errorshow

open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io

def StackOverflowTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + (lit "StackOverflowError:").length < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (showStackOverflowError (bufferPrims displaySize)) =
      .ok ⟨prior ++ lit "StackOverflowError:"⟩

def ErrorExceptionTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior message : Bytes),
    prior.length + message.length < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showErrorException (bufferPrims displaySize) io message) =
      .ok ⟨prior ++ message⟩

def LabelledMessageTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior message : Bytes),
    prior.length + (lit "DimensionMismatch: ").length + message.length < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showArgumentError (bufferPrims displaySize) io message) =
        .ok ⟨prior ++ lit "ArgumentError: " ++ message⟩ ∧
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showDimensionMismatch (bufferPrims displaySize) io message) =
        .ok ⟨prior ++ lit "DimensionMismatch: " ++ message⟩ ∧
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showAssertionError (bufferPrims displaySize) io message) =
        .ok ⟨prior ++ lit "AssertionError: " ++ message⟩ ∧
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showOverflowError (bufferPrims displaySize) io message) =
        .ok ⟨prior ++ lit "OverflowError: " ++ message⟩

def FallbackErrors : Prop :=
  ∀ (S Io V A R : Type) (printer : JIO Io V → A → ExceptT ShowError (StateM S) R)
    (io : JIO Io V) (value : A) (initial final : S) (error : ShowError),
    (printer io value).run initial = (.error error, final) →
    (showerrorAny printer io value).run initial = (.error error, final) ∧
    (showIndexAny printer io value).run initial = (.error error, final)

def IndexForwardingErrors : Prop :=
  ∀ (S Io V A B R : Type) (field : A → B)
    (printer : JIO Io V → B → ExceptT ShowError (StateM S) R)
    (io : JIO Io V) (value : A) (initial final : S) (error : ShowError),
    (printer io (field value)).run initial = (.error error, final) →
    (showIndexSlice field printer io value).run initial = (.error error, final) ∧
    (showIndexLogical field printer io value).run initial = (.error error, final)

def ColonIndexTextCorrect : Prop :=
  ∀ (V Ty : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64) (prior : Bytes),
    prior.length + 1 < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (showIndexColon (bufferPrims displaySize)) = .ok ⟨prior ++ lit ":"⟩

def KeyErrorRenderingFailure : Prop :=
  ∀ (V Ty A : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior : Bytes) (key : A) (error : ShowError),
    prior.length + (lit "KeyError: key ").length < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showKeyError (bufferPrims displaySize)
        (fun _ (_ : A) => throwThe ShowError error) io key) =
      .error (.display error)

def OneToRenderingFailure : Prop :=
  ∀ (V Ty I : Type) (a : AnyOps V Ty) (displaySize : JInt64 × JInt64)
    (prior : Bytes) (stop : I) (error : ShowError),
    prior.length + 2 < 2 ^ 62 →
    Round1.observeExceptionAfter a displaySize prior
      (fun io => showIndexOneTo (bufferPrims displaySize)
        (fun _ (_ : I) => throwThe ShowError error) io stop) =
      .error (.display error)

def IncompleteTagFallback : Prop :=
  ∀ (A : Type) (value : A), incompleteTagAny value = "none"

def IncompleteTagParseFailure : Prop :=
  ∀ (S D R : Type) (tag : D → ExceptT ShowError (StateM S) R)
    (detail : D) (initial final : S) (error : ShowError),
    (tag detail).run initial = (.error error, final) →
    (incompleteTagParseErrorWith tag detail).run initial = (.error error, final)

end JuliaLean.Proofs.base.errorshow

namespace JuliaLean.Proofs.base.errorshow

open JuliaLean.Registry
namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem stackOverflowText : StackOverflowTextCorrect := by
  intro V Ty a displaySize prior ht
  exact errorObserveBytes a displaySize prior (lit "StackOverflowError:") ht

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem errorExceptionText : ErrorExceptionTextCorrect := by
  intro V Ty a displaySize prior message ht
  exact errorObserveBytes a displaySize prior message ht

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem colonIndexText : ColonIndexTextCorrect := by
  intro V Ty a displaySize prior ht
  apply errorObserveBytes a displaySize prior (lit ":")
  simpa [lit, show ":".utf8ByteSize = 1 from by decide +kernel] using ht

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem fallbackErrors : FallbackErrors := by
  intro S Io V A R printer io value initial final error h
  exact ⟨h, h⟩

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem indexForwardingErrors : IndexForwardingErrors := by
  intro S Io V A B R field printer io value initial final error h
  exact ⟨h, h⟩

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem incompleteTagFallback : IncompleteTagFallback := by
  intro A value
  rfl

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem incompleteTagParseFailure : IncompleteTagParseFailure := by
  intro S D R tag detail initial final error h
  exact h

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io JuliaLean.base.iobuffer
open JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean.ChatGPT.Batch9.Group18

theorem observeTwoBytes {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (prior left right : Bytes)
    (ht : prior.length + left.length + right.length < 2 ^ 62) :
    Round1.observeExceptionAfter a displaySize prior
      (fun io => do
        printBytes (bufferPrims displaySize) io left
        printBytes (bufferPrims displaySize) io right) =
      .ok ⟨prior ++ left ++ right⟩ := by
  obtain ⟨first, hfirst, hpfirst, hufirst, hcfirst⟩ :=
    errorWriteCanonical [] prior 0 (by simp) (by decide) (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at hfirst hpfirst hufirst
  obtain ⟨second, hsecond, hpsecond, husecond, hcsecond⟩ :=
    errorWriteCanonical first left prior.length hufirst hcfirst (by omega)
  obtain ⟨third, hthird, hpthird, huthird, hcthird⟩ :=
    errorWriteCanonical second right (prior.length + left.length) husecond hcsecond ht
  obtain ⟨final, htake⟩ :=
    esTakeString third (prior.length + left.length + right.length) (by omega)
  have hbytes : third.take (prior.length + left.length + right.length) =
      prior ++ left ++ right := by
    rw [hpthird, hpsecond, hpfirst]
  unfold Round1.observeExceptionAfter
  apply errorSprintSuccess a displaySize _ () ()
    (esBuf third (prior.length + left.length + right.length)) final (prior ++ left ++ right)
  · exact errorRunTwo _ _ _ _ _ () ()
      (errorPrintSuccess displaySize prior _ _ _ hfirst)
      (errorRunTwo _ _ _ _ _ () ()
        (errorPrintSuccess displaySize left _ _ _ hsecond)
        (errorPrintSuccess displaySize right _ _ _ hthird))
  · rw [htake, hbytes]

theorem typeNameErrorText : Round1.TypeNameErrorTextCorrect := by
  intro V Ty A a displaySize prior value isUnion
  dsimp only
  intro htotal
  cases hbranch : isUnion value with
  | false =>
    have hbound : prior.length + (lit "TypeNameError: ").length +
        (lit "typename does not apply to this type").length < 2 ^ 62 := by
      simpa only [hbranch, Bool.false_eq_true, ite_false, List.length_append,
        Nat.add_assoc] using htotal
    simpa only [showTypeNameError, hbranch, Bool.false_eq_true, ite_false,
      printStr, printBytes, List.append_assoc] using
      observeTwoBytes a displaySize prior (lit "TypeNameError: ")
        (lit "typename does not apply to this type") hbound
  | true =>
    have hbound : prior.length + (lit "TypeNameError: ").length +
        (lit "typename does not apply to unions whose components have different typenames").length < 2 ^ 62 := by
      simpa only [hbranch, ite_true, List.length_append, Nat.add_assoc] using htotal
    simpa only [showTypeNameError, hbranch, ite_true, printStr, printBytes, List.append_assoc] using
      observeTwoBytes a displaySize prior (lit "TypeNameError: ")
        (lit "typename does not apply to unions whose components have different typenames") hbound

theorem sprintFailure {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64)
    (render : JIO Unit V → Unit → BufferShowM Empty Unit)
    (final : BufferState) (error : JuliaLean.base.strings.io.Error Empty)
    (hrun : (render (.plain ()) ()).run (esBuf [] 0) = .error error final) :
    sprintIOBuffer (bitsConversions .i64) displaySize a .none (i 0) render () =
      .error error := by
  unfold sprintIOBuffer
  rw [esBufEmpty]
  simp only [Except.mapError, Except.bind, bind, pure, sprintContext]
  rw [errorPureBind]
  simp only [Except.pure]
  rw [errorEvalBind, hrun]

theorem runBeforeError {ε σ α β : Type} (first : EStateM ε σ α)
    (second : EStateM ε σ β) (initial middle final : σ) (value : α) (error : ε)
    (hfirst : first.run initial = .ok value middle)
    (hsecond : second.run middle = .error error final) :
    (first >>= fun _ => second).run initial = .error error final := by
  simp only [bind]
  rw [esRunBind, hfirst]
  exact hsecond

theorem throwBeforeAction (error : ShowError) (suffix : BufferShowM Empty Unit)
    (state : BufferState) :
    ((throwThe ShowError error : BufferShowM Empty Unit) >>= fun _ => suffix).run state =
      .error (.display error) state := rfl

theorem observeAfterPrefixFailure {V Ty : Type} (a : AnyOps V Ty)
    (displaySize : JInt64 × JInt64) (prior leading : Bytes) (error : ShowError)
    (suffix : JIO Unit V → BufferShowM Empty Unit)
    (ht : prior.length + leading.length < 2 ^ 62) :
    Round1.observeExceptionAfter a displaySize prior
      (fun io => do
        printBytes (bufferPrims displaySize) io leading
        (throwThe ShowError error : BufferShowM Empty Unit)
        suffix io) = .error (.display error) := by
  obtain ⟨first, hfirst, hpfirst, hufirst, hcfirst⟩ :=
    errorWriteCanonical [] prior 0 (by simp) (by decide) (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at hfirst hpfirst hufirst
  obtain ⟨second, hsecond, hpsecond, husecond, hcsecond⟩ :=
    errorWriteCanonical first leading prior.length hufirst hcfirst ht
  have hp := errorPrintSuccess (V := V) displaySize prior _ _ _ hfirst
  have hq := errorPrintSuccess (V := V) displaySize leading _ _ _ hsecond
  unfold Round1.observeExceptionAfter
  apply sprintFailure a displaySize _ (esBuf second (prior.length + leading.length)) (.display error)
  exact runBeforeError _ _ _ _ _ () _ hp
    (runBeforeError _ _ _ _ _ () _ hq (throwBeforeAction error (suffix (.plain ())) _))

theorem keyErrorRenderingFailure : KeyErrorRenderingFailure := by
  intro V Ty A a displaySize prior key error hbound
  simpa only [showKeyError, printStr, printBytes] using
    observeAfterPrefixFailure a displaySize prior (lit "KeyError: key ") error
      (fun io => printStr (bufferPrims displaySize) io " not found") hbound

theorem initErrorRenderingFailure : Round1.InitErrorRenderingFailure := by
  intro V Ty E BT a displaySize prior moduleName ex bt backtrace error hbound
  simpa only [showInitError, printStr, printBytes] using
    observeAfterPrefixFailure a displaySize prior (lit "InitError: ") error
      (fun io => printAll (bufferPrims displaySize) io
        [printStr (bufferPrims displaySize) io "\nduring initialization of module ",
         printBytes (bufferPrims displaySize) io moduleName]) hbound

theorem initErrorDefaultRenderingFailure : Round1.InitErrorDefaultRenderingFailure := by
  intro V Ty E Frame a displaySize prior moduleName ex error hbound
  exact initErrorRenderingFailure V Ty E (List Frame) a displaySize prior moduleName ex [] true error hbound

private theorem bufferCatchRethrow {A : Type} (action : BufferShowM Empty A) :
    tryCatchThe ShowError action (fun error => throwThe ShowError error) = action := by
  funext state
  simp only [tryCatchThe, MonadExceptOf.tryCatch, throwThe, MonadExceptOf.throw]
  cases result : action state with
  | ok value final => rfl
  | error error final => cases error <;> rfl

private theorem bufferUnitReturn (action : BufferShowM Empty Unit) :
    (do action; pure ()) = action := by
  funext state
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  cases result : action state with
  | ok value final => cases value; rfl
  | error error final => rfl

private theorem bufferPrintPair {V : Type} (displaySize : JInt64 × JInt64)
    (io : JIO Unit V) (left right : BufferShowM Empty Unit) :
    printAll (bufferPrims displaySize) io [left, right] = (do left; right) := by
  cases io <;>
    simp only [printAll, lockIO, unlockIO, lock_IOContext, unlock_IOContext,
      bufferPrims, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind,
      bufferUnitReturn, bufferCatchRethrow]

theorem labelledMessageText : LabelledMessageTextCorrect := by
  intro V Ty a displaySize prior message hbound
  have harg : prior.length + (lit "ArgumentError: ").length + message.length < 2 ^ 62 := by
    have : (lit "ArgumentError: ").length ≤ (lit "DimensionMismatch: ").length := by decide +kernel
    omega
  have hassert : prior.length + (lit "AssertionError: ").length + message.length < 2 ^ 62 := by
    have : (lit "AssertionError: ").length ≤ (lit "DimensionMismatch: ").length := by decide +kernel
    omega
  have hover : prior.length + (lit "OverflowError: ").length + message.length < 2 ^ 62 := by
    have : (lit "OverflowError: ").length ≤ (lit "DimensionMismatch: ").length := by decide +kernel
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [showArgumentError, showArgumentErrorWith, bufferPrintPair, printStr, printBytes] using
      observeTwoBytes a displaySize prior (lit "ArgumentError: ") message harg
  · simpa only [showDimensionMismatch, showDimensionMismatchWith, bufferPrintPair, printStr, printBytes] using
      observeTwoBytes a displaySize prior (lit "DimensionMismatch: ") message hbound
  · simpa only [showAssertionError, showAssertionErrorWith, bufferPrintPair, printStr, printBytes] using
      observeTwoBytes a displaySize prior (lit "AssertionError: ") message hassert
  · simpa only [showOverflowError, showOverflowErrorWith, bufferPrintPair, printStr, printBytes] using
      observeTwoBytes a displaySize prior (lit "OverflowError: ") message hover

theorem oneToRenderingFailure : OneToRenderingFailure := by
  intro V Ty I a displaySize prior stop error hbound
  have hprefix : prior.length + (lit "1:").length < 2 ^ 62 := by
    simpa only [show (lit "1:").length = 2 from by decide +kernel] using hbound
  obtain ⟨first, hfirst, hpfirst, hufirst, hcfirst⟩ :=
    errorWriteCanonical [] prior 0 (by simp) (by decide) (by omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at hfirst hpfirst hufirst
  obtain ⟨second, hsecond, hpsecond, husecond, hcsecond⟩ :=
    errorWriteCanonical first (lit "1:") prior.length hufirst hcfirst hprefix
  have hp := errorPrintSuccess (V := V) displaySize prior _ _ _ hfirst
  have hq := errorPrintSuccess (V := V) displaySize (lit "1:") _ _ _ hsecond
  unfold Round1.observeExceptionAfter
  apply sprintFailure a displaySize _ (esBuf second (prior.length + (lit "1:").length)) (.display error)
  apply runBeforeError _ _ _ _ _ () _ hp
  simpa only [showIndexOneTo, bufferPrintPair, printStr, printBytes] using
    runBeforeError _ _ _ _ _ () _ hq
      (show (throwThe ShowError error : BufferShowM Empty Unit).run
        (esBuf second (prior.length + (lit "1:").length)) =
        .error (.display error) (esBuf second (prior.length + (lit "1:").length)) from rfl)

end Completion

def entries : List JuliaLean.Registry.Entry := [
  { id := "errorshow-errorshow-l160-v2", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::DivideError)"],
    statement := "The descriptive text produced by showerror for this nullary exception, observed through the installed canonical sprint/IOBuffer path, is 'DivideError: integer division error'. Arbitrary bounded prior bytes are preserved exactly. The statement observes the complete exception-value domain through actual buffer construction/write/takestring execution; it does not assert arbitrary stream-specific failure behavior or equate the printer to its definition body. Source: base/errorshow.jl:160. Documentation: base/errorshow.jl:3-7; base/docs/basedocs.jl:2304-2320. Observation documentation: base/strings/io.jl:80-114. Realizability: bound total emitted bytes below 2^62 to exclude Int length/capacity wraparound.",
    source := "base/errorshow.jl:160; doctest base/docs/basedocs.jl:2304-2320; test/errorshow.jl:435-436",
    status := .proven, prop := ``Round1.DivideErrorTextCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group18.ErrorshowErrorshowL160V2_proven },
  { id := "errorshow-errorshow-l162-v2", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::UndefRefError)"],
    statement := "The descriptive text produced by showerror for this nullary exception, observed through the installed canonical sprint/IOBuffer path, is 'UndefRefError: access to undefined reference'. Arbitrary bounded prior bytes are preserved exactly. The statement observes the complete exception-value domain through actual buffer construction/write/takestring execution; it does not assert arbitrary stream-specific failure behavior or equate the printer to its definition body. Source: base/errorshow.jl:162. Documentation: base/errorshow.jl:3-7; base/docs/basedocs.jl:1918-1939; doc/src/manual/arrays.md:517-529. Observation documentation: base/strings/io.jl:80-114. Realizability: bound total emitted bytes below 2^62 to exclude Int length/capacity wraparound.",
    source := "base/errorshow.jl:162; doctest base/docs/basedocs.jl:1918-1939; test/errorshow.jl:437-438",
    status := .proven, prop := ``Round1.UndefRefErrorTextCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group18.ErrorshowErrorshowL162V2_proven },
  { id := "errorshow-errorshow-l163-v2", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::EOFError)"],
    statement := "The descriptive text produced by showerror for this nullary exception, observed through the installed canonical sprint/IOBuffer path, is 'EOFError: read end of file'. Arbitrary bounded prior bytes are preserved exactly. The statement observes the complete exception-value domain through actual buffer construction/write/takestring execution; it does not assert arbitrary stream-specific failure behavior or equate the printer to its definition body. Source: base/errorshow.jl:163. Documentation: base/errorshow.jl:3-7; base/io.jl:12-17. Observation documentation: base/strings/io.jl:80-114. Realizability: bound total emitted bytes below 2^62 to exclude Int length/capacity wraparound.",
    source := "base/errorshow.jl:163; test pin test/errorshow.jl:441-442",
    status := .proven, prop := ``Round1.EOFErrorTextCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group18.ErrorshowErrorshowL163V2_proven },
  { id := "errorshow-errorshow-l168-v2", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::InterruptException)"],
    statement := "The descriptive text produced by showerror for this nullary exception, observed through the installed canonical sprint/IOBuffer path, is 'InterruptException:'. Arbitrary bounded prior bytes are preserved exactly. The statement observes the complete exception-value domain through actual buffer construction/write/takestring execution; it does not assert arbitrary stream-specific failure behavior or equate the printer to its definition body. Source: base/errorshow.jl:168. Documentation: base/errorshow.jl:3-7; base/docs/basedocs.jl:2164-2177. Observation documentation: base/strings/io.jl:80-114. Realizability: bound total emitted bytes below 2^62 to exclude Int length/capacity wraparound.",
    source := "base/errorshow.jl:168; test pin test/errorshow.jl:445-446",
    status := .proven, prop := ``Round1.InterruptExceptionTextCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group18.ErrorshowErrorshowL168V2_proven },
  { id := "errorshow-errorshow-l174-v2", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::UndefKeywordError)"],
    statement := "For every Julia Symbol name, including empty and non-UTF-8 bytes but excluding NUL as required by Symbol construction, the descriptive text of UndefKeywordError retains the complete missing keyword name between its diagnostic label and unassigned-keyword explanation. Observed through the installed canonical sprint/IOBuffer path, after arbitrary bounded prior bytes; preserves those bytes exactly. No payload is pre-rendered by an assumed callback. Source: base/errorshow.jl:174-175. Documentation: base/errorshow.jl:3-7; base/docs/basedocs.jl:2129-2148; base/boot.jl:553-555. Observation documentation: base/strings/io.jl:80-114. Realizability: bound total emitted bytes below 2^62 to exclude Int length/capacity wraparound.",
    source := "base/errorshow.jl:174-175; doctest base/docs/basedocs.jl:2129-2148",
    status := .proven, prop := ``Round1.UndefKeywordErrorTextCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group18.ErrorshowErrorshowL174V2_proven },
  { id := "errorshow-stackoverflow-text", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ::StackOverflowError)"],
    statement := "StackOverflowError appends its exact diagnostic label through the installed sprint and IOBuffer implementation while preserving all prior bytes.",
    source := "base/errorshow.jl:161", status := .proven,
    prop := ``StackOverflowTextCorrect, thm := some ``Completion.stackOverflowText },
  { id := "errorshow-error-exception-text", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::ErrorException)"],
    statement := "The ordinary String-message specialization prints every byte of the ErrorException message unchanged, including empty and invalid UTF-8 payloads, preserving all prior output.",
    source := "base/errorshow.jl:164", status := .proven,
    prop := ``ErrorExceptionTextCorrect, thm := some ``Completion.errorExceptionText,
    notes := "The full method model showErrorExceptionWith also retains arbitrary AbstractString print dispatch and raw returns." },
  { id := "errorshow-labelled-message-text", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(::IO, ::ArgumentError)", "showerror(::IO, ::DimensionMismatch)",
      "showerror(::IO, ::AssertionError)", "showerror(::IO, ::OverflowError)"],
    statement := "The ordinary String-message specializations append their exact diagnostic label and the complete message without changing prior output.",
    source := "base/errorshow.jl:169-172", status := .proven,
    prop := ``LabelledMessageTextCorrect, thm := some ``Completion.labelledMessageText,
    notes := "The full With models retain arbitrary AbstractString printing effects inside the installed variadic printer's lock/finally protocol." },
  { id := "errorshow-fallback-errors", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex)", "show_index(io::IO, x::Any)"],
    statement := "Fallback rendering propagates every exception and prior user-visible state change produced by a custom show method.",
    source := "base/errorshow.jl:30,32", status := .proven,
    prop := ``FallbackErrors, thm := some ``Completion.fallbackErrors },
  { id := "errorshow-index-forwarding-errors", juliaFile := "base/errorshow.jl",
    juliaFns := ["show_index(io::IO, x::Slice)", "show_index(io::IO, x::LogicalIndex)"],
    statement := "Rendering a Slice's indices or a LogicalIndex's mask propagates the selected custom renderer's exception and prior state changes.",
    source := "base/errorshow.jl:33-34", status := .proven,
    prop := ``IndexForwardingErrors, thm := some ``Completion.indexForwardingErrors },
  { id := "errorshow-colon-index-text", juliaFile := "base/errorshow.jl",
    juliaFns := ["show_index(io::IO, x::Colon)"],
    statement := "A Colon index prints exactly one colon after arbitrary prior bytes through the installed sprint and IOBuffer implementation.",
    source := "base/errorshow.jl:36", status := .proven,
    prop := ``ColonIndexTextCorrect, thm := some ``Completion.colonIndexText },
  { id := "errorshow-keyerror-rendering-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::KeyError)"],
    statement := "KeyError rendering propagates any exception raised by the key's custom show method instead of suppressing it or reporting a completed diagnostic.",
    source := "base/errorshow.jl:165-167", status := .proven,
    prop := ``KeyErrorRenderingFailure, thm := some ``Completion.keyErrorRenderingFailure },
  { id := "errorshow-oneto-rendering-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["show_index(io::IO, x::OneTo)"],
    statement := "Rendering a OneTo index propagates an exception from its stop value's custom printer, for every Integer stop type.",
    source := "base/errorshow.jl:35", status := .proven,
    prop := ``OneToRenderingFailure, thm := some ``Completion.oneToRenderingFailure },
  { id := "errorshow-incomplete-tag-fallback", juliaFile := "base/errorshow.jl",
    juliaFns := ["incomplete_tag(ex)"],
    statement := "Values handled by the generic incomplete-tag fallback have no incomplete parser construct and return the symbol none.",
    source := "base/errorshow.jl:1714", status := .proven,
    prop := ``IncompleteTagFallback, thm := some ``Completion.incompleteTagFallback },
  { id := "errorshow-incomplete-tag-parse-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["incomplete_tag(exc::Meta.ParseError)"],
    statement := "Inspecting a ParseError preserves any exception and state changes from classifying its arbitrary detail payload.",
    source := "base/errorshow.jl:1734", status := .proven,
    prop := ``IncompleteTagParseFailure, thm := some ``Completion.incompleteTagParseFailure }
]

end JuliaLean.Proofs.base.errorshow

namespace JuliaLean.Proofs.base.errorshow.Models2Group17

open JuliaLean.base.errorshow.Models2Group17

/-!
Independent, executable-call observations for the three generic hint handlers.
Each selected call records both its exact arguments and its raw response.  A
failed call records the exception after preserving that call's post-state.
The specifications below describe the permitted complete observations directly
as event lists; they neither call the model nor use an unfolding equation as
the expected result.  Exception observations must stop at a permitted call's
response position.  The public properties additionally compare the underlying
world/result with the uninstrumented execution, retaining all callback effects.
-/

inductive HintEvent (E V : Type) where
  | propertyCall (object : V) (property : HintProperty)
  | propertyResult (value : V)
  | subtypeCall (candidate : V)
  | subtypeResult (value : Bool)
  | stringCall (arguments : List V)
  | stringResult (value : V)
  | printCall (first : V) (arguments : List V)
  | printResult (value : V)
  | styledCall (first : V) (arguments : List V) (color : HintColor)
  | styledResult (value : V)
  | printlnCall (argument : V)
  | printlnResult (value : V)
  | raised (error : E)

abbrev HintTraceM (E W V : Type) :=
  EStateM E (W × List (HintEvent E V))

def hintObserveCall (event : HintEvent E V)
    (response : A → HintEvent E V) (action : EStateM E W A) :
    HintTraceM E W V A := fun state =>
  match action state.1 with
  | .ok value world =>
      .ok value (world, state.2 ++ [event, response value])
  | .error error world =>
      .error error (world, state.2 ++ [event, .raised error])

def hintTraceBuiltins (b : HintBuiltinPrims (EStateM E W) V) :
    HintBuiltinPrims (HintTraceM E W V) V where
  literal := b.literal
  nothingValue := b.nothingValue
  isaNumber := b.isaNumber
  subtypeAbstractDict := fun value =>
    hintObserveCall (.subtypeCall value) .subtypeResult
      (b.subtypeAbstractDict value)
  identicalApplyTypeSymbol := b.identicalApplyTypeSymbol
  identicalUnionAllType := b.identicalUnionAllType

def hintTraceDispatch (d : HintDispatch (EStateM E W) V) :
    HintDispatch (HintTraceM E W V) V where
  getproperty := fun object property =>
    hintObserveCall (.propertyCall object property) .propertyResult
      (d.getproperty object property)
  string := fun arguments =>
    hintObserveCall (.stringCall arguments) .stringResult (d.string arguments)
  print := fun first arguments =>
    hintObserveCall (.printCall first arguments) .printResult
      (d.print first arguments)
  printstyled := fun first arguments color =>
    hintObserveCall (.styledCall first arguments color) .styledResult
      (d.printstyled first arguments color)
  println := fun argument =>
    hintObserveCall (.printlnCall argument) .printlnResult (d.println argument)

structure HintRunView (E W V : Type) where
  result : Except E V
  world : W
  events : List (HintEvent E V)

def hintRunView (run : EStateM.Result E (W × List (HintEvent E V)) V) :
    HintRunView E W V :=
  match run with
  | .ok value state => ⟨.ok value, state.1, state.2⟩
  | .error error state => ⟨.error error, state.1, state.2⟩

def hintPlainView (run : EStateM.Result E W V) : Except E V × W :=
  match run with
  | .ok value world => (.ok value, world)
  | .error error world => (.error error, world)

def hintIsResponse (event : HintEvent E V) : Prop :=
  match event with
  | .propertyResult _ | .subtypeResult _ | .stringResult _ |
    .printResult _ | .styledResult _ | .printlnResult _ => True
  | _ => False

def hintRaisedPrefix (actual complete : List (HintEvent E V)) (error : E) : Prop :=
  ∃ (before after : List (HintEvent E V)) (response : HintEvent E V),
    complete = before ++ (response :: after) ∧
    hintIsResponse response ∧
    actual = before ++ [.raised error]

def hintTraceSpec (success : List (HintEvent E V) → V → Prop)
    (events : List (HintEvent E V)) (result : Except E V) : Prop :=
  match result with
  | .ok value => success events value
  | .error error =>
      ∃ complete value, success complete value ∧
        hintRaisedPrefix events complete error

/-- Exact no-hint and hint observations; the last print's result is the result. -/
def noncallableNumberHintSuccess (literal : String → V) (nothingValue : V)
    (isaNumber : V → Bool) (io ex : V)
    (events : List (HintEvent E V)) (result : V) : Prop :=
  (∃ f, isaNumber f = false ∧
    events = [.propertyCall ex .f, .propertyResult f] ∧
    result = nothingValue) ∨
  (∃ f firstResult styledResult, isaNumber f = true ∧
    events =
      [.propertyCall ex .f, .propertyResult f,
       .printCall io [literal "\nMaybe you forgot to use an operator such as "],
       .printResult firstResult,
       .styledCall io [literal "*, ^, %, / etc. "] .cyan,
       .styledResult styledResult,
       .printCall io [literal "?"], .printResult result])

/--
Both property reads precede the subtype call.  The same raw field value appears
in the two independent interpolations; each returned interpolation value feeds
the appropriate selected output method.  The final println response is the
handler response.
-/
def fielderrorDictHintSuccess (literal : String → V) (nothingValue : V)
    (io exc : V) (events : List (HintEvent E V)) (result : V) : Prop :=
  (∃ field type,
    events =
      [.propertyCall exc .field, .propertyResult field,
       .propertyCall exc .type, .propertyResult type,
       .subtypeCall type, .subtypeResult false] ∧
    result = nothingValue) ∨
  (∃ field type message printed styledMessage styled,
    events =
      [.propertyCall exc .field, .propertyResult field,
       .propertyCall exc .type, .propertyResult type,
       .subtypeCall type, .subtypeResult true,
       .stringCall
         [literal "\nDid you mean to access dict values using key: `:", field,
          literal "` ? Consider using indexing syntax "],
       .stringResult message,
       .printCall io [message], .printResult printed,
       .stringCall [literal "dict[:", field, literal "]"],
       .stringResult styledMessage,
       .styledCall io [styledMessage] .cyan, .styledResult styled,
       .printlnCall io, .printlnResult result])

/--
The three branches distinguish the first failed identity test, the second
failed identity test, and the single full variadic print.  Getter effects for
expected/got are absent whenever their respective guards short-circuit.
-/
def applyTypeUnionallHintSuccess (literal : String → V) (nothingValue : V)
    (isApplyType isUnionAll : V → Bool) (io ex : V)
    (events : List (HintEvent E V)) (result : V) : Prop :=
  (∃ func, isApplyType func = false ∧
    events = [.propertyCall ex .func, .propertyResult func] ∧
    result = nothingValue) ∨
  (∃ func expected, isApplyType func = true ∧ isUnionAll expected = false ∧
    events =
      [.propertyCall ex .func, .propertyResult func,
       .propertyCall ex .expected, .propertyResult expected] ∧
    result = nothingValue) ∨
  (∃ func expected got, isApplyType func = true ∧ isUnionAll expected = true ∧
    events =
      [.propertyCall ex .func, .propertyResult func,
       .propertyCall ex .expected, .propertyResult expected,
       .propertyCall ex .got, .propertyResult got,
       .printCall io [literal "\nHint: `", got,
         literal "` takes no type parameters."],
       .printResult result])

/--
For every world and selected dispatch, expose the exact output calls, the
Number guard, genuine nothing on the inactive branch, the final raw return,
all possible exception prefixes, and preservation of underlying state effects.
-/
def NoncallableNumberHintEffects : Prop :=
  ∀ (E W V : Type) (b : HintBuiltinPrims (EStateM E W) V)
    (d : HintDispatch (EStateM E W) V) (io ex argTypes kwargs : V) (world : W),
    let observed := hintRunView
      (noncallableNumberHint (hintTraceBuiltins b) (hintTraceDispatch d)
        io ex argTypes kwargs (world, []))
    hintTraceSpec
      (noncallableNumberHintSuccess b.literal b.nothingValue b.isaNumber io ex)
      observed.events observed.result ∧
    (observed.result, observed.world) =
      hintPlainView (noncallableNumberHint b d io ex argTypes kwargs world)

/--
The complete generic field-value domain reaches the builtin subtype operation.
The observation fixes both interpolation argument lists, their data flow, cyan
keyword dispatch, the final println return, all errors, and world effects.
-/
def FielderrorDictHintEffects : Prop :=
  ∀ (E W V : Type) (b : HintBuiltinPrims (EStateM E W) V)
    (d : HintDispatch (EStateM E W) V) (io exc : V) (world : W),
    let observed := hintRunView
      (fielderrorDictHint (hintTraceBuiltins b) (hintTraceDispatch d)
        io exc (world, []))
    hintTraceSpec
      (fielderrorDictHintSuccess b.literal b.nothingValue io exc)
      observed.events observed.result ∧
    (observed.result, observed.world) =
      hintPlainView (fielderrorDictHint b d io exc world)

/--
The two identity guards short-circuit their dependent getters.  A successful
hint makes one exact variadic print call and preserves its arbitrary result;
inactive paths yield the supplied genuine Julia nothing, and errors/state
effects are observed without catching or replacing them.
-/
def ApplyTypeUnionallHintEffects : Prop :=
  ∀ (E W V : Type) (b : HintBuiltinPrims (EStateM E W) V)
    (d : HintDispatch (EStateM E W) V) (io ex : V) (world : W),
    let observed := hintRunView
      (applyTypeUnionallHint (hintTraceBuiltins b) (hintTraceDispatch d)
        io ex (world, []))
    hintTraceSpec
      (applyTypeUnionallHintSuccess b.literal b.nothingValue
        b.identicalApplyTypeSymbol b.identicalUnionAllType io ex)
      observed.events observed.result ∧
    (observed.result, observed.world) =
      hintPlainView (applyTypeUnionallHint b d io ex world)

end JuliaLean.Proofs.base.errorshow.Models2Group17

namespace JuliaLean.Proofs.base.errorshow.ShowCompletion
open JuliaLean.base.errorshow.Models2Group17 JuliaLean.Proofs.base.errorshow.Models2Group17
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
private theorem numberRunBind {E S A B : Type} (a : EStateM E S A) (f : A → EStateM E S B) (s : S) :
    (a >>= f) s = match a s with
      | .ok x t => f x t
      | .error e t => .error e t := rfl

theorem numberHint : NoncallableNumberHintEffects := by
  intro E W V b d io ex argTypes kwargs initial
  dsimp +zetaDelta only
  dsimp +instances only [noncallableNumberHint, hintTraceDispatch, hintTraceBuiltins]
  simp only [EStateM.run, numberRunBind, hintObserveCall]
  dsimp only [hintRunView, hintPlainView]
  cases hf : d.getproperty ex .f initial with
  | error error final =>
    simp only [hf, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
    constructor
    · cases hb : b.isaNumber ex with
      | false =>
        refine ⟨[.propertyCall ex .f, .propertyResult ex], b.nothingValue,
          Or.inl ⟨ex, hb, rfl, rfl⟩, ?_⟩
        exact ⟨[.propertyCall ex .f], [], .propertyResult ex, rfl, trivial, rfl⟩
      | true =>
        refine ⟨_, ex, Or.inr ⟨ex, ex, ex, hb, rfl⟩, ?_⟩
        exact ⟨[.propertyCall ex .f], _, .propertyResult ex, rfl, trivial, rfl⟩
    · trivial
  | ok func middle =>
    simp only [hf, numberRunBind, hintObserveCall]
    by_cases hb : b.isaNumber func = false
    · simp only [hb, Bool.false_eq_true, if_false, EStateM.pure, hintRunView,
        hintPlainView, EStateM.run, hintTraceSpec]
      exact ⟨Or.inl ⟨func, hb, rfl, rfl⟩, by trivial⟩
    · have hb : b.isaNumber func = true := Bool.eq_true_of_ne_false hb
      simp only [hb, if_true, numberRunBind, hintObserveCall]
      cases hp : d.print io [b.literal "\nMaybe you forgot to use an operator such as "] middle with
      | error error final =>
        simp only [hp, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
        refine ⟨⟨_, ex, Or.inr ⟨func, ex, ex, hb, rfl⟩, ?_⟩, by trivial⟩
        exact ⟨[.propertyCall ex .f, .propertyResult func,
          .printCall io [b.literal "\nMaybe you forgot to use an operator such as "]],
          _, .printResult ex, rfl, trivial, rfl⟩
      | ok first next =>
        simp only [hp, numberRunBind, hintObserveCall]
        cases hs : d.printstyled io [b.literal "*, ^, %, / etc. "] .cyan next with
        | error error final =>
          simp only [hs, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
          refine ⟨⟨_, ex, Or.inr ⟨func, first, ex, hb, rfl⟩, ?_⟩, by trivial⟩
          exact ⟨[.propertyCall ex .f, .propertyResult func,
            .printCall io [b.literal "\nMaybe you forgot to use an operator such as "],
            .printResult first, .styledCall io [b.literal "*, ^, %, / etc. "] .cyan],
            _, .styledResult ex, rfl, trivial, rfl⟩
        | ok styled last =>
          simp only [hs, numberRunBind, hintObserveCall]
          cases hq : d.print io [b.literal "?"] last with
          | error error final =>
            simp only [hq, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
            refine ⟨⟨_, ex, Or.inr ⟨func, first, styled, hb, rfl⟩, ?_⟩, by trivial⟩
            exact ⟨[.propertyCall ex .f, .propertyResult func,
              .printCall io [b.literal "\nMaybe you forgot to use an operator such as "],
              .printResult first, .styledCall io [b.literal "*, ^, %, / etc. "] .cyan,
              .styledResult styled, .printCall io [b.literal "?"]],
              [], .printResult ex, rfl, trivial, rfl⟩
          | ok result final =>
            simp only [hq, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
            exact ⟨Or.inr ⟨func, first, styled, hb, rfl⟩, by trivial⟩
end JuliaLean.Proofs.base.errorshow.ShowCompletion


namespace JuliaLean.Proofs.base.errorshow.ShowCompletion
open JuliaLean.base.errorshow.Models2Group17 JuliaLean.Proofs.base.errorshow.Models2Group17
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private theorem applyHintRunBind {E S A B : Type} (a : EStateM E S A) (f : A → EStateM E S B) (s : S) :
    (a >>= f) s = match a s with
      | .ok x t => f x t
      | .error e t => .error e t := rfl

 theorem applyHint : ApplyTypeUnionallHintEffects := by
  intro E W V b d io ex initial
  dsimp +zetaDelta only
  dsimp +instances only [applyTypeUnionallHint, hintTraceDispatch, hintTraceBuiltins]
  simp only [EStateM.run, applyHintRunBind, hintObserveCall]
  dsimp only [hintRunView, hintPlainView]
  cases hf : d.getproperty ex .func initial with
  | error error final =>
    simp only [hf, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
    constructor
    · cases hb : b.identicalApplyTypeSymbol ex with
      | false =>
        refine ⟨[.propertyCall ex .func, .propertyResult ex], b.nothingValue, ?_, ?_⟩
        · exact Or.inl ⟨ex, hb, rfl, rfl⟩
        · exact ⟨[.propertyCall ex .func], [], .propertyResult ex, rfl, trivial, rfl⟩
      | true =>
        cases he : b.identicalUnionAllType ex with
        | false =>
          refine ⟨_, b.nothingValue, Or.inr (Or.inl ⟨ex, ex, hb, he, rfl, rfl⟩), ?_⟩
          exact ⟨[.propertyCall ex .func], _, .propertyResult ex, rfl, trivial, rfl⟩
        | true =>
          refine ⟨_, ex, Or.inr (Or.inr ⟨ex, ex, ex, hb, he, rfl⟩), ?_⟩
          exact ⟨[.propertyCall ex .func], _, .propertyResult ex, rfl, trivial, rfl⟩
    · trivial
  | ok func middle =>
    simp only [hf, applyHintRunBind, hintObserveCall]
    by_cases hb : b.identicalApplyTypeSymbol func = false
    · simp only [hb, Bool.false_eq_true, if_false, EStateM.pure, hintRunView,
        hintPlainView, EStateM.run, hintTraceSpec]
      exact ⟨Or.inl ⟨func, hb, rfl, rfl⟩, by trivial⟩
    · have hb : b.identicalApplyTypeSymbol func = true := Bool.eq_true_of_ne_false hb
      simp only [hb, if_true, applyHintRunBind, hintObserveCall]
      cases he : d.getproperty ex .expected middle with
      | error error final =>
        simp only [he, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
        constructor
        · cases hu : b.identicalUnionAllType ex with
          | false =>
            refine ⟨_, b.nothingValue, Or.inr (Or.inl ⟨func, ex, hb, hu, rfl, rfl⟩), ?_⟩
            exact ⟨[.propertyCall ex .func, .propertyResult func, .propertyCall ex .expected],
              _, .propertyResult ex, rfl, trivial, rfl⟩
          | true =>
            refine ⟨_, ex, Or.inr (Or.inr ⟨func, ex, ex, hb, hu, rfl⟩), ?_⟩
            exact ⟨[.propertyCall ex .func, .propertyResult func, .propertyCall ex .expected],
              _, .propertyResult ex, rfl, trivial, rfl⟩
        · trivial
      | ok expected next =>
        simp only [he, applyHintRunBind, hintObserveCall]
        by_cases hu : b.identicalUnionAllType expected = false
        · simp only [hu, Bool.false_eq_true, if_false, EStateM.pure, hintRunView,
            hintPlainView, EStateM.run, hintTraceSpec]
          exact ⟨Or.inr (Or.inl ⟨func, expected, hb, hu, rfl, rfl⟩), by trivial⟩
        · have hu : b.identicalUnionAllType expected = true := Bool.eq_true_of_ne_false hu
          simp only [hu, if_true, applyHintRunBind, hintObserveCall]
          cases hg : d.getproperty ex .got next with
          | error error final =>
            simp only [hg, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
            refine ⟨⟨_, ex, Or.inr (Or.inr ⟨func, expected, ex, hb, hu, rfl⟩), ?_⟩, by trivial⟩
            exact ⟨[.propertyCall ex .func, .propertyResult func,
              .propertyCall ex .expected, .propertyResult expected, .propertyCall ex .got],
              _, .propertyResult ex, rfl, trivial, rfl⟩
          | ok got last =>
            simp only [hg, applyHintRunBind, hintObserveCall]
            cases hp : d.print io [b.literal "\nHint: `", got,
                b.literal "` takes no type parameters."] last with
            | error error final =>
              simp only [hp, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
              refine ⟨⟨_, ex, Or.inr (Or.inr ⟨func, expected, got, hb, hu, rfl⟩), ?_⟩, by trivial⟩
              exact ⟨[.propertyCall ex .func, .propertyResult func,
                .propertyCall ex .expected, .propertyResult expected,
                .propertyCall ex .got, .propertyResult got,
                .printCall io [b.literal "\nHint: `", got, b.literal "` takes no type parameters."]],
                [], .printResult ex, rfl, trivial, rfl⟩
            | ok value final =>
              simp only [hp, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
              exact ⟨Or.inr (Or.inr ⟨func, expected, got, hb, hu, rfl⟩), by trivial⟩
end JuliaLean.Proofs.base.errorshow.ShowCompletion

namespace JuliaLean.Proofs.base.errorshow.DictHintCompletion
open JuliaLean.base.errorshow.Models2Group17
open JuliaLean.Proofs.base.errorshow.Models2Group17

private theorem dictRunBind {E S A B : Type} (action : EStateM E S A)
    (next : A → EStateM E S B) (state : S) :
    (action >>= next) state = match action state with
      | .ok value final => next value final
      | .error error final => .error error final := rfl

theorem dictionaryHint : FielderrorDictHintEffects := by
  intro E W V b d io exc initial
  dsimp +zetaDelta only
  dsimp +instances only [fielderrorDictHint, hintTraceDispatch, hintTraceBuiltins]
  simp only [EStateM.run, dictRunBind, hintObserveCall]
  dsimp only [hintRunView, hintPlainView]
  cases hf : d.getproperty exc .field initial with
  | error error final =>
    simp only [hf, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
    refine ⟨⟨_, b.nothingValue, Or.inl ⟨exc, exc, rfl, rfl⟩, ?_⟩, by trivial⟩
    exact ⟨[.propertyCall exc .field],
      [.propertyCall exc .type, .propertyResult exc, .subtypeCall exc, .subtypeResult false],
      .propertyResult exc, rfl, trivial, rfl⟩
  | ok field afterField =>
    simp only [hf, dictRunBind, hintObserveCall]
    cases ht : d.getproperty exc .type afterField with
    | error error final =>
      simp only [ht, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
      refine ⟨⟨_, b.nothingValue, Or.inl ⟨field, exc, rfl, rfl⟩, ?_⟩, by trivial⟩
      exact ⟨[.propertyCall exc .field, .propertyResult field, .propertyCall exc .type],
        [.subtypeCall exc, .subtypeResult false], .propertyResult exc, rfl, trivial, rfl⟩
    | ok type afterType =>
      simp only [ht, dictRunBind, hintObserveCall]
      cases hs : b.subtypeAbstractDict type afterType with
      | error error final =>
        simp only [hs, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
        refine ⟨⟨_, b.nothingValue, Or.inl ⟨field, type, rfl, rfl⟩, ?_⟩, by trivial⟩
        exact ⟨[.propertyCall exc .field, .propertyResult field,
          .propertyCall exc .type, .propertyResult type, .subtypeCall type],
          [], .subtypeResult false, rfl, trivial, rfl⟩
      | ok isDict afterSubtype =>
        cases isDict with
        | false =>
          simp only [hs, Bool.false_eq_true, ite_false, EStateM.pure,
            hintRunView, hintPlainView, EStateM.run, hintTraceSpec]
          exact ⟨Or.inl ⟨field, type, rfl, rfl⟩, by trivial⟩
        | true =>
          simp only [hs, ite_true, dictRunBind, hintObserveCall]
          cases hm : d.string
              [b.literal "\nDid you mean to access dict values using key: `:", field,
               b.literal "` ? Consider using indexing syntax "] afterSubtype with
          | error error final =>
            simp only [hm, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
            refine ⟨⟨_, exc, Or.inr ⟨field, type, exc, exc, exc, exc, rfl⟩, ?_⟩, by trivial⟩
            exact ⟨[.propertyCall exc .field, .propertyResult field,
              .propertyCall exc .type, .propertyResult type, .subtypeCall type, .subtypeResult true,
              .stringCall [b.literal "\nDid you mean to access dict values using key: `:", field,
                b.literal "` ? Consider using indexing syntax "]],
              [.printCall io [exc], .printResult exc,
                .stringCall [b.literal "dict[:", field, b.literal "]"], .stringResult exc,
                .styledCall io [exc] .cyan, .styledResult exc, .printlnCall io, .printlnResult exc],
              .stringResult exc, rfl, trivial, rfl⟩
          | ok message afterMessage =>
            simp only [hm, dictRunBind, hintObserveCall]
            cases hp : d.print io [message] afterMessage with
            | error error final =>
              simp only [hp, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
              refine ⟨⟨_, exc, Or.inr ⟨field, type, message, exc, exc, exc, rfl⟩, ?_⟩, by trivial⟩
              exact ⟨[.propertyCall exc .field, .propertyResult field,
                .propertyCall exc .type, .propertyResult type, .subtypeCall type, .subtypeResult true,
                .stringCall [b.literal "\nDid you mean to access dict values using key: `:", field,
                  b.literal "` ? Consider using indexing syntax "], .stringResult message,
                .printCall io [message]],
                [.stringCall [b.literal "dict[:", field, b.literal "]"], .stringResult exc,
                  .styledCall io [exc] .cyan, .styledResult exc, .printlnCall io, .printlnResult exc],
                .printResult exc, rfl, trivial, rfl⟩
            | ok printed afterPrint =>
              simp only [hp, dictRunBind, hintObserveCall]
              cases hsm : d.string [b.literal "dict[:", field, b.literal "]"] afterPrint with
              | error error final =>
                simp only [hsm, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
                refine ⟨⟨_, exc, Or.inr ⟨field, type, message, printed, exc, exc, rfl⟩, ?_⟩, by trivial⟩
                exact ⟨[.propertyCall exc .field, .propertyResult field,
                  .propertyCall exc .type, .propertyResult type, .subtypeCall type, .subtypeResult true,
                  .stringCall [b.literal "\nDid you mean to access dict values using key: `:", field,
                    b.literal "` ? Consider using indexing syntax "], .stringResult message,
                  .printCall io [message], .printResult printed,
                  .stringCall [b.literal "dict[:", field, b.literal "]"]],
                  [.styledCall io [exc] .cyan, .styledResult exc, .printlnCall io, .printlnResult exc],
                  .stringResult exc, rfl, trivial, rfl⟩
              | ok styledMessage afterStyledMessage =>
                simp only [hsm, dictRunBind, hintObserveCall]
                cases hstyle : d.printstyled io [styledMessage] .cyan afterStyledMessage with
                | error error final =>
                  simp only [hstyle, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
                  refine ⟨⟨_, exc, Or.inr ⟨field, type, message, printed, styledMessage, exc, rfl⟩, ?_⟩,
                    by trivial⟩
                  exact ⟨[.propertyCall exc .field, .propertyResult field,
                    .propertyCall exc .type, .propertyResult type, .subtypeCall type, .subtypeResult true,
                    .stringCall [b.literal "\nDid you mean to access dict values using key: `:", field,
                      b.literal "` ? Consider using indexing syntax "], .stringResult message,
                    .printCall io [message], .printResult printed,
                    .stringCall [b.literal "dict[:", field, b.literal "]"], .stringResult styledMessage,
                    .styledCall io [styledMessage] .cyan],
                    [.printlnCall io, .printlnResult exc], .styledResult exc, rfl, trivial, rfl⟩
                | ok styled afterStyled =>
                  simp only [hstyle, dictRunBind, hintObserveCall]
                  cases hline : d.println io afterStyled with
                  | error error final =>
                    simp only [hline, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
                    refine ⟨⟨_, exc, Or.inr ⟨field, type, message, printed, styledMessage, styled, rfl⟩, ?_⟩,
                      by trivial⟩
                    exact ⟨[.propertyCall exc .field, .propertyResult field,
                      .propertyCall exc .type, .propertyResult type, .subtypeCall type, .subtypeResult true,
                      .stringCall [b.literal "\nDid you mean to access dict values using key: `:", field,
                        b.literal "` ? Consider using indexing syntax "], .stringResult message,
                      .printCall io [message], .printResult printed,
                      .stringCall [b.literal "dict[:", field, b.literal "]"], .stringResult styledMessage,
                      .styledCall io [styledMessage] .cyan, .styledResult styled, .printlnCall io],
                      [], .printlnResult exc, rfl, trivial, rfl⟩
                  | ok result final =>
                    simp only [hline, hintRunView, hintPlainView, hintTraceSpec, EStateM.run]
                    exact ⟨Or.inr ⟨field, type, message, printed, styledMessage, styled, rfl⟩, by trivial⟩

end JuliaLean.Proofs.base.errorshow.DictHintCompletion

namespace JuliaLean.Proofs.base.errorshow.Models2Group17

open JuliaLean JuliaLean.base.show JuliaLean.base.errorshow.Models2Group17

/-- Observation retains both native display exceptions and arbitrary
user-thrown values without allowing a native catch to intercept the latter. -/
local instance noStdioShowError {Error World : Type} :
    MonadExceptOf ShowError (EStateM (ShowError ⊕ Error) World) where
  throw error := fun state => .error (.inl error) state
  tryCatch action handler := fun state =>
    match action.run state with
    | .ok value final => .ok value final
    | .error (.inl error) final => (handler error).run final
    | .error (.inr error) final => .error (.inr error) final

/-- Completed native and open-dispatch operations, retaining their actual
arguments and full raw return or exception. The two literal conversions
are concrete computations and are not exposed as observer callbacks. -/
inductive NoStdioCall (Message MessageRoot Wrong Error ErrorRoot Value Raised : Type) where
  | stderr (outcome : Except Raised (JuliaLean.base.pointer.Ptr Unit))
  | messageConvert (argument : Message) (outcome : Except Raised MessageRoot)
  | messageUnsafe (argument : MessageRoot)
      (outcome : Except Raised
        (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion NativeCString Wrong))
  | printf (stream : JuliaLean.base.pointer.Ptr Unit) (format : NativeCString)
      (outcome : Except Raised (JInt .i32))
  | errorConvert (argument : Error) (outcome : Except Raised ErrorRoot)
  | errorUnsafe (argument : ErrorRoot) (outcome : Except Raised Value)
  | staticShow (stream : JuliaLean.base.pointer.Ptr Unit) (argument : Value)
      (outcome : Except Raised (JInt .u64))

/-- The event log is mathematical observation data, separate from the
arbitrary world mutated by the called operation. -/
structure NoStdioEvent (Message MessageRoot Wrong Error ErrorRoot Value Raised World : Type) where
  call : NoStdioCall Message MessageRoot Wrong Error ErrorRoot Value Raised
  before : World
  after : World

/-- Observe one operation without constraining its state updates, result,
or exception. Its final world is retained even when it throws. -/
def recordNoStdioCall
    {Message MessageRoot Wrong Error ErrorRoot Value Raised World Result : Type}
    (call : Except Raised Result →
      NoStdioCall Message MessageRoot Wrong Error ErrorRoot Value Raised)
    (action : EStateM Raised World Result) :
    EStateM Raised
      (World × List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World)) Result :=
  fun state =>
    match action.run state.1 with
    | .ok value final =>
        .ok value (final, state.2 ++ [⟨call (.ok value), state.1, final⟩])
    | .error error final =>
        .error error (final, state.2 ++ [⟨call (.error error), state.1, final⟩])

/-- Instrument the exact native ABI calls. No behavior of the native
entry points is assumed by the statement. -/
def tracingNoStdioRuntime
    {Message MessageRoot Wrong Error ErrorRoot Value Raised World : Type}
    (runtime : NoStdioRuntime (EStateM Raised World) Value) :
    NoStdioRuntime
      (EStateM Raised
        (World × List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World))) Value where
  stderrStream := recordNoStdioCall .stderr runtime.stderrStream
  printf := fun stream format =>
    recordNoStdioCall (.printf stream format) (runtime.printf stream format)
  staticShow := fun stream value =>
    recordNoStdioCall (.staticShow stream value) (runtime.staticShow stream value)

/-- Instrument both pairs of automatically inserted conversions on the
unfixed message and error types, preserving every intermediate result. -/
def tracingNoStdioDispatch
    {Message MessageRoot Wrong Error ErrorRoot Value Raised World : Type}
    (dispatch : NoStdioDispatch (EStateM Raised World)
      Message MessageRoot Wrong Error ErrorRoot Value) :
    NoStdioDispatch
      (EStateM Raised
        (World × List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World)))
      Message MessageRoot Wrong Error ErrorRoot Value where
  cconvertMessage := fun message =>
    recordNoStdioCall (.messageConvert message) (dispatch.cconvertMessage message)
  unsafeConvertMessage := fun root =>
    recordNoStdioCall (.messageUnsafe root) (dispatch.unsafeConvertMessage root)
  cconvertError := fun error =>
    recordNoStdioCall (.errorConvert error) (dispatch.cconvertError error)
  unsafeConvertError := fun root =>
    recordNoStdioCall (.errorUnsafe root) (dispatch.unsafeConvertError root)

/-- Operation classes used only to describe observable ordering. -/
def noStdioCallKind {Message MessageRoot Wrong Error ErrorRoot Value Raised : Type} :
    NoStdioCall Message MessageRoot Wrong Error ErrorRoot Value Raised → Nat
  | .stderr _ => 0
  | .messageConvert _ _ => 1
  | .messageUnsafe _ _ => 2
  | .printf _ _ _ => 3
  | .errorConvert _ _ => 4
  | .errorUnsafe _ _ => 5
  | .staticShow _ _ _ => 6

/-- Extract an operation's actual exception without erasing its class or
payload. Successful raw values are retained in the event itself. -/
def noStdioCallFailure {Message MessageRoot Wrong Error ErrorRoot Value Raised : Type} :
    NoStdioCall Message MessageRoot Wrong Error ErrorRoot Value Raised → Option Raised
  | .stderr result => match result with | .ok _ => none | .error error => some error
  | .messageConvert _ result => match result with | .ok _ => none | .error error => some error
  | .messageUnsafe _ result => match result with | .ok _ => none | .error error => some error
  | .printf _ _ result => match result with | .ok _ => none | .error error => some error
  | .errorConvert _ result => match result with | .ok _ => none | .error error => some error
  | .errorUnsafe _ result => match result with | .ok _ => none | .error error => some error
  | .staticShow _ _ result => match result with | .ok _ => none | .error error => some error

/-- Adjacent operations share the actual post/pre-call world, including
the last failing operation. No mutation is reset or silently discarded. -/
def noStdioStateChain
    {Message MessageRoot Wrong Error ErrorRoot Value Raised World : Type} :
    World → List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World) → World → Prop
  | initial, [], final => initial = final
  | initial, event :: rest, final =>
      event.before = initial ∧ noStdioStateChain event.after rest final

/-- Data-flow invariant on the observed calls: all output uses the stream
returned by the first operation; custom conversions receive the original
value or actual preceding root; first printf receives the checked CString;
fixed literals retain their own pointer bits; static_show receives the
actual Any conversion result. This inspects the trace without invoking any
callee or computing the method's expected result. -/
def noStdioDataFlow
    {Message MessageRoot Wrong Error ErrorRoot Value Raised World : Type}
    (error : Error) (message : Message) (literals : NoStdioLiteralPointers)
    (events : List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World)) : Prop :=
  ∀ (index : Nat) (event : NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value Raised World),
    events[index]? = some event →
    match event.call with
    | .stderr _ => index = 0
    | .messageConvert argument _ => argument = message
    | .messageUnsafe root _ =>
        ∃ before after,
          events[1]? = some ⟨.messageConvert message (.ok root), before, after⟩
    | .printf stream format _ =>
        (∃ before after, events[0]? = some ⟨.stderr (.ok stream), before, after⟩) ∧
        ((index = 3 ∧ ∃ root before after,
            events[2]? = some ⟨.messageUnsafe root (.ok (.accepted format)), before, after⟩) ∨
          (index = 4 ∧ format.address = literals.separator.address) ∨
          (index = 8 ∧ format.address = literals.newline.address))
    | .errorConvert argument _ => argument = error
    | .errorUnsafe root _ =>
        ∃ before after,
          events[5]? = some ⟨.errorConvert error (.ok root), before, after⟩
    | .staticShow stream value _ =>
        (∃ before after, events[0]? = some ⟨.stderr (.ok stream), before, after⟩) ∧
        (∃ root before after,
          events[6]? = some ⟨.errorUnsafe root (.ok value), before, after⟩)

/-- An independent protocol invariant, not an expected implementation.
Every execution has a nonempty prefix of the permitted call classes,
correct data flow, continuous state, and stops at its first failure. A
wrong CString return raises native TypeError before any printf. Normal
completion returns exactly the final printf's signed 32-bit value, with
no positivity check and no substitution of an earlier byte count. -/
def noStdioObservedProtocol
    {Message MessageRoot Wrong Error ErrorRoot Value UserError World : Type}
    (error : Error) (message : Message) (literals : NoStdioLiteralPointers)
    (initial : World)
    (actual : EStateM.Result (ShowError ⊕ UserError)
      (World × List (NoStdioEvent Message MessageRoot Wrong Error ErrorRoot Value
        (ShowError ⊕ UserError) World)) (JInt .i32)) : Prop :=
  let observed := hintPlainView actual
  let result := observed.1
  let final := observed.2.1
  let events := observed.2.2
  events ≠ [] ∧
  (∃ suffix, events.map (fun event => noStdioCallKind event.call) ++ suffix =
    [0, 1, 2, 3, 3, 4, 5, 6, 3]) ∧
  noStdioStateChain initial events final ∧
  noStdioDataFlow error message literals events ∧
  (∀ index event raised,
    events[index]? = some event → noStdioCallFailure event.call = some raised →
      index + 1 = events.length ∧ result = .error raised) ∧
  (∀ root wrong before after,
    events[2]? = some ⟨.messageUnsafe root (.ok (.rejected wrong)), before, after⟩ →
      events.length = 3 ∧ result = .error (.inl ShowError.typeError)) ∧
  (match result with
   | .ok value =>
       events.length = 9 ∧ ∃ stream format before after,
         events[8]? = some ⟨.printf stream format (.ok value), before, after⟩
   | .error raised =>
       ∃ priorCalls event, events = priorCalls ++ [event] ∧
         (noStdioCallFailure event.call = some raised ∨
           (raised = .inl ShowError.typeError ∧
             ∃ root wrong, event.call = .messageUnsafe root (.ok (.rejected wrong)))))

/-- The no-stdio error renderer acquires stderr before converting its full
AbstractString message and follows the documented ccall conversion/data
flow protocol for every selected custom conversion, all native results,
all native/custom exceptions, and all mutated states. Its two concrete
literal conversions are included through the observed format-pointer
requirements. Source: base/errorshow.jl:450-456;
base/docs/basedocs.jl:1490-1493;
doc/src/manual/calling-c-and-fortran-code.md:246-268,370-388. -/
def ShowErrorNoStdioCallEffects : Prop :=
  ∀ (Message MessageRoot Wrong Error ErrorRoot Value UserError World : Type)
    (runtime : NoStdioRuntime (EStateM (ShowError ⊕ UserError) World) Value)
    (dispatch : NoStdioDispatch (EStateM (ShowError ⊕ UserError) World)
      Message MessageRoot Wrong Error ErrorRoot Value)
    (literals : NoStdioLiteralPointers) (error : Error) (message : Message)
    (initial : World),
    noStdioObservedProtocol error message literals initial
      ((JuliaLean.base.errorshow.Models2Group17.showErrorNoStdio
        (tracingNoStdioRuntime runtime) (tracingNoStdioDispatch dispatch)
        literals error message).run (initial, []))

end JuliaLean.Proofs.base.errorshow.Models2Group17

namespace JuliaLean.Proofs.base.errorshow.Models2Group17

open JuliaLean.base.show

structure DispatchEvent (Io V X World Error R : Type) where
  io : JIO Io V
  argument : X
  before : World
  after : World
  outcome : Except Error R

def observeDispatch {Io V X World Error R : Type}
    (call : JIO Io V → X → EStateM Error World R) (io : JIO Io V) (argument : X) :
    EStateM Error (World × List (DispatchEvent Io V X World Error R)) R := fun state =>
  match call io argument state.1 with
  | .ok value world =>
      .ok value (world, state.2 ++ [⟨io, argument, state.1, world, .ok value⟩])
  | .error error world =>
      .error error (world, state.2 ++ [⟨io, argument, state.1, world, .error error⟩])

def singleDispatchObserved {Io V X World Error R : Type}
    (io : JIO Io V) (argument : X) (initial : World)
    (observed : EStateM.Result Error
      (World × List (DispatchEvent Io V X World Error R)) R) : Prop :=
  match observed with
  | .ok value (world, events) => events = [⟨io, argument, initial, world, .ok value⟩]
  | .error error (world, events) => events = [⟨io, argument, initial, world, .error error⟩]

end JuliaLean.Proofs.base.errorshow.Models2Group17

namespace JuliaLean.Proofs.base.errorshow.Models2Group17

open JuliaLean.base.show
open JuliaLean.base.errorshow.Models2Group17

/-- Instrument the two selected printing targets with a shared observation
payload: `(value, none)` records plain printing; `(value, some color)` records
styled printing. The selected method still executes with its original raw
result, exception and mutable world; no callee law is imposed. -/
def tracingCompareDispatch {Io V A B C World Error R : Type}
    (ops : CompareDispatch (EStateM Error World) Io V A B C R) :
    CompareDispatch
      (EStateM Error (World × List (DispatchEvent Io V (A × Option C) World Error R)))
      Io V A B C R :=
  let call : JIO Io V → (A × Option C) → EStateM Error World R :=
    fun io payload =>
      match payload.2 with
      | none => ops.printValue io payload.1
      | some color => ops.printStyled io payload.1 color
  { egal := ops.egal,
    printValue := fun io value => observeDispatch call io (value, none),
    printStyled := fun io value color => observeDispatch call io (value, some color) }

/-- Exactly one printing method is selected, with the original left value
and stream. Egal inputs use plain printing; otherwise the observed styled
call has exactly the original Symbol color. The observation includes the
selected method's raw return, exception and before/after world, so repeated
calls, changed arguments or colors, return coercion and dropped error-state
updates falsify the invariant. The right argument is used only by the pure
builtin identity observation and is never substituted for the left value.

All value types, arbitrary Symbol representations, IOContexts, native and
custom errors, raw results, state and both selected printing methods are
quantified without a correctness law. This is an internal rendering
invariant, not a promise about the bytes produced by arbitrary custom code.
Source: base/errorshow.jl:235-241;
doc/src/manual/types.md:1653-1661 (printing dispatch).
-/
def PrintWithCompareSelectionAndEffects : Prop :=
  ∀ (Io V A B C World Error R : Type)
    (ops : CompareDispatch (EStateM Error World) Io V A B C R)
    (io : JIO Io V) (a : A) (b : B) (color : C) (initial : World),
    singleDispatchObserved io (a, if ops.egal a b then none else some color) initial
      ((JuliaLean.base.errorshow.Models2Group17.printWithCompareAny
        (tracingCompareDispatch ops) io a b color).run (initial, []))

end JuliaLean.Proofs.base.errorshow.Models2Group17

namespace JuliaLean.Proofs.base.errorshow.Models2Group17

open JuliaLean.base.errorshow.Models2Group17

/-- The type and non-type methods have disjoint result classes. Type results
retain the original parameter, and non-type inputs do not affect the result.
Julia source: base/errorshow.jl:417-418. -/
def StriptypeClassification : Prop :=
  (∀ (Ty : Type) (type : Ty), (striptypeType type).isSome = true ∧
    ∀ returned, striptypeType type = some returned → returned = type) ∧
  (∀ (A B Ty : Type) (a : A) (b : B),
    (striptypeAny (Ty := Ty) a).isNone = true ∧
    striptypeAny (Ty := Ty) a = striptypeAny (Ty := Ty) b)

end JuliaLean.Proofs.base.errorshow.Models2Group17

namespace JuliaLean.Proofs.base.errorshow
open JuliaLean.Registry
namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem striptypeClassification : Models2Group17.StriptypeClassification := by
  constructor
  · intro Ty type
    constructor
    · rfl
    · intro returned h
      exact Option.some.inj h.symm
  · intro A B Ty a b
    exact ⟨rfl, rfl⟩

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem backtraceFinallyEffects : Round1.BacktraceFinallyEffects := by
  intro World Io V E BT R render trace io ex bt value initial middle final error
  constructor
  · intro hr ht
    simp [showErrorBacktraceWith, hr, ht]
  · constructor
    · intro hr ht
      simp [showErrorBacktraceWith, hr, ht]
    · intro hr
      simp [showErrorBacktraceWith, hr]

end Completion

namespace Completion
open JuliaLean JuliaLean.base.errorshow JuliaLean.base.show
open JuliaLean.base.strings.io
open JuliaLean.ChatGPT.Batch9.Group18

theorem printWithCompareSelection : Models2Group17.PrintWithCompareSelectionAndEffects := by
  intro Io V A B C World Error R ops io a b color initial
  by_cases h : ops.egal a b = true
  · simp only [JuliaLean.base.errorshow.Models2Group17.printWithCompareAny,
      Models2Group17.tracingCompareDispatch, h, ite_true]
    cases outcome : ops.printValue io a initial <;>
      simp [Models2Group17.observeDispatch, Models2Group17.singleDispatchObserved,
        EStateM.run, outcome]
  · simp only [JuliaLean.base.errorshow.Models2Group17.printWithCompareAny,
      Models2Group17.tracingCompareDispatch, h, ite_false]
    cases outcome : ops.printStyled io a color initial <;>
      simp [Models2Group17.observeDispatch, Models2Group17.singleDispatchObserved,
        EStateM.run, outcome]

end Completion

namespace EnvOptions

open JuliaLean.base.env JuliaLean.base.errorshow

/-- Julia's accepted true spellings; other nonempty values disable the option. -/
def enabledValue (value : String) (fallback : Bool) : Bool :=
  if value.isEmpty then fallback
  else ["t", "T", "true", "True", "TRUE", "y", "Y", "yes", "Yes", "YES", "1"].contains value

/-- Environment reads retain their errors, divergence and state changes.
Absent or empty variables use the documented default; all other values are
classified independently of the caller's BoolEnvOps formatting hooks. -/
def SettingCorrect
    (setting : (World : Type) → BoolEnvOps World → EnvAction World Bool)
    (name : String) (fallback : Bool) : Prop :=
  ∀ (World : Type) (ops : BoolEnvOps World) (initial : World),
    (∀ final, ops.hasKey name initial = some (.ok (false, final)) →
      setting World ops initial = some (.ok (fallback, final))) ∧
    (∀ middle value final,
      ops.hasKey name initial = some (.ok (true, middle)) →
      ops.getIndex name middle = some (.ok (value, final)) →
      setting World ops initial = some (.ok (enabledValue value fallback, final))) ∧
    (∀ error final, ops.hasKey name initial = some (.error (error, final)) →
      setting World ops initial = some (.error (error, final))) ∧
    (∀ middle error final,
      ops.hasKey name initial = some (.ok (true, middle)) →
      ops.getIndex name middle = some (.error (error, final)) →
      setting World ops initial = some (.error (error, final))) ∧
    (ops.hasKey name initial = none → setting World ops initial = none) ∧
    (∀ middle, ops.hasKey name initial = some (.ok (true, middle)) →
      ops.getIndex name middle = none → setting World ops initial = none)

private theorem settingCorrect (name : String) (fallback : Bool) :
    SettingCorrect
      (fun _ ops => do return (← stacktraceBoolEnv ops name fallback) == some true)
      name fallback := by
  intro World ops initial
  simp only [SettingCorrect] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro final hkey
    cases fallback <;>
      simp [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, hkey,
        Bind.bind, Functor.map, pure, JuliaLean.base.io.instMonadM]
  · intro middle value final hkey hvalue
    change ((do return (← stacktraceBoolEnv ops name fallback) == some true) :
      EnvAction World Bool) initial =
      some (Except.ok ((if value.isEmpty then fallback else getBoolEnvTruthy.contains value), final))
    cases fallback <;> cases hempty : value.isEmpty <;>
      cases htrue : getBoolEnvTruthy.contains value <;>
      cases hfalse : getBoolEnvFalsy.contains value <;>
      simp only [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, parseBoolEnv,
        Bind.bind, Functor.map, Pure.pure, JuliaLean.base.io.instMonadM,
        Option.bind, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ite_true, ite_false, hkey, hvalue, hempty, htrue, hfalse] <;> rfl
  · intro error final hkey
    simp [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, hkey,
      Bind.bind, pure, JuliaLean.base.io.instMonadM]
  · intro middle error final hkey hvalue
    simp [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, hkey, hvalue,
      Bind.bind, pure, JuliaLean.base.io.instMonadM]
  · intro hkey
    simp [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, hkey,
      Bind.bind, pure, JuliaLean.base.io.instMonadM]
  · intro middle hkey hvalue
    simp [stacktraceBoolEnv, getBoolEnvDefault, getBoolEnvLazy, hkey, hvalue,
      Bind.bind, pure, JuliaLean.base.io.instMonadM]

def StacktraceEnvironmentOptions : Prop :=
  SettingCorrect (fun _ => stacktraceExpandBasepathsNative) "JULIA_STACKTRACE_EXPAND_BASEPATHS" false ∧
  SettingCorrect (fun _ => stacktraceContractUserdirNative) "JULIA_STACKTRACE_CONTRACT_HOMEDIR" true ∧
  SettingCorrect (fun _ => stacktraceLinebreaksNative) "JULIA_STACKTRACE_LINEBREAKS" false ∧
  SettingCorrect (fun _ => stacktraceFullLoadingNative) "JULIA_STACKTRACE_FULL_LOADING" false

theorem stacktraceEnvironmentOptions : StacktraceEnvironmentOptions :=
  ⟨settingCorrect _ false, settingCorrect _ true, settingCorrect _ false, settingCorrect _ false⟩

end EnvOptions

def entriesModels2Group17 : List Entry := [
  { id := "errorshow-stacktrace-environment-options", juliaFile := "base/errorshow.jl",
    juliaFns := ["stacktrace_expand_basepaths()", "stacktrace_contract_userdir()",
      "stacktrace_linebreaks()", "stacktrace_full_loading()"],
    statement := "The four stacktrace environment settings use their documented defaults for missing or empty values, accept exactly the recognized true spellings, disable on all other nonempty values, and preserve errors, divergence and state changes from environment reads.",
    source := "base/errorshow.jl:458-461; base/env.jl:132-177", status := .proven,
    prop := ``EnvOptions.StacktraceEnvironmentOptions,
    thm := some ``EnvOptions.stacktraceEnvironmentOptions },
  { id := "errorshow-typename-error-text", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::Core.TypeNameError)"],
    statement := "TypeNameError emits the exact union-specific or ordinary typename diagnostic after arbitrary prior output.",
    source := "base/errorshow.jl:46-53", status := .proven,
    prop := ``Round1.TypeNameErrorTextCorrect, thm := some ``Completion.typeNameErrorText },
  { id := "errorshow-backtrace-finally-effects", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex, bt; backtrace=true)"],
    statement := "Backtrace display follows normal rendering and exceptions through finally, retains all prior effects, preserves a successful renderer's raw result, and is omitted when disabled.",
    source := "base/errorshow.jl:107-113", status := .proven,
    prop := ``Round1.BacktraceFinallyEffects, thm := some ``Completion.backtraceFinallyEffects },
  { id := "errorshow-initerror-rendering-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::InitError, bt; backtrace=true)"],
    statement := "Initialization-error display propagates an exception raised while rendering the wrapped error instead of printing a completed initialization diagnostic.",
    source := "base/errorshow.jl:122-126", status := .proven,
    prop := ``Round1.InitErrorRenderingFailure, thm := some ``Completion.initErrorRenderingFailure },
  { id := "errorshow-initerror-default-rendering-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::InitError)"],
    statement := "Default initialization-error display retains exceptions from its wrapped error while supplying the source's empty backtrace.",
    source := "base/errorshow.jl:127", status := .proven,
    prop := ``Round1.InitErrorDefaultRenderingFailure, thm := some ``Completion.initErrorDefaultRenderingFailure },
  { id := "errorshow-canonical-index-rendering-failure", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror(io::IO, ex::CanonicalIndexError)"],
    statement := "CanonicalIndexError display preserves an exception from custom printing of its arbitrary type-field payload.",
    source := "base/errorshow.jl:207-209", status := .todo,
    prop := ``Round1.CanonicalIndexRenderingFailure, thm := none },
{ id := "errorshow-noncallable-number-hint-effects",
  juliaFile := "base/errorshow.jl",
  juliaFns := ["noncallable_number_hint_handler(io, ex, arg_types, kwargs)"],
  statement := "The Number hint preserves the arbitrary field domain, exact selected print/styled calls, final raw return versus genuine nothing, exception prefixes, and state effects.",
  source := "base/errorshow.jl:1451-1458",
  status := .proven,
  prop := ``Models2Group17.NoncallableNumberHintEffects,
  thm := some ``ShowCompletion.numberHint },
{ id := "errorshow-fielderror-dict-hint-effects",
  juliaFile := "base/errorshow.jl",
  juliaFns := ["fielderror_dict_hint_handler(io, exc)"],
  statement := "The dictionary hint preserves both property reads before the raw-value builtin subtype check, exact interpolation arguments and output data flow, cyan keyword, final println return, errors, and state effects.",
  source := "base/errorshow.jl:1537-1546",
  status := .proven,
  prop := ``Models2Group17.FielderrorDictHintEffects,
  thm := some ``DictHintCompletion.dictionaryHint },
{ id := "errorshow-apply-type-unionall-hint-effects",
  juliaFile := "base/errorshow.jl",
  juliaFns := ["apply_type_unionall_hint_handler(io, ex)"],
  statement := "The apply_type hint preserves both identity-guard short circuits, conditional property reads, the exact variadic print call, its arbitrary return versus genuine nothing, errors, and state effects.",
  source := "base/errorshow.jl:1577-1582",
  status := .proven,
  prop := ``Models2Group17.ApplyTypeUnionallHintEffects,
  thm := some ``ShowCompletion.applyHint },

  { id := "errorshow-no-stdio-call-effects", juliaFile := "base/errorshow.jl",
    juliaFns := ["showerror_nostdio(@nospecialize(err), msg::AbstractString)"],
    statement := "The no-stdio renderer acquires stderr before message conversion, preserves all implicit custom conversion arguments and effects, uses the concrete separator and newline Cstring pointers, and makes its five native ABI calls in source order. The first exception or failed CString assertion stops later calls with the same final state; normal completion returns the last printf's raw Int32 result, regardless of sign or earlier numeric results.",
    source := "base/errorshow.jl:450-456; base/strings/cstring.jl:31,65,78-88; base/docs/basedocs.jl:1490-1493; doc/src/manual/calling-c-and-fortran-code.md:246-268,370-388",
    status := .todo, prop := ``Models2Group17.ShowErrorNoStdioCallEffects, thm := none,
    notes := "Needs the full nine-operation trace proof: state continuity, indexed conversion/stream data flow, all first-error prefixes and the rejected-CString TypeError branch, plus the final signed printf return. Native runtime behavior is abstracted explicitly, so this is a missing protocol proof, not a runtime bug." },

  { id := "errorshow-print-with-compare-selection-effects", juliaFile := "base/errorshow.jl",
    juliaFns := ["print_with_compare(io::IO, @nospecialize(a), @nospecialize(b), color::Symbol)"],
    statement := "Generic comparison printing invokes exactly one selected printer on the original left value and stream: plain printing for an egal pair, styled printing with the unchanged Symbol color otherwise. The selected method's arbitrary raw return, exception and mutated state survive unchanged; no law about custom printing is assumed.",
    source := "base/errorshow.jl:235-241; doc/src/manual/types.md:1653-1661",
    status := .proven, prop := ``Models2Group17.PrintWithCompareSelectionAndEffects, thm := some ``Completion.printWithCompareSelection },

  { id := "errorshow-striptype-classification", juliaFile := "base/errorshow.jl",
    juliaFns := ["striptype(::Type{T}) where {T}", "striptype(::Any)"],
    statement := "Type stripping distinguishes type and non-type results, preserves the exact type parameter, and ignores every non-type payload.",
    source := "base/errorshow.jl:417-418", status := .proven,
    prop := ``Models2Group17.StriptypeClassification, thm := some ``Completion.striptypeClassification }

]
end JuliaLean.Proofs.base.errorshow
