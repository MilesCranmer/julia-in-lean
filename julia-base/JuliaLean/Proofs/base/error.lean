import JuliaLean.base.error
import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.Registry.Types
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

/-!
# Property statements for `base/error.jl`

Each registry entry is a source-level specification for the typed model. The property
vocabulary describes exception values, backtrace ordering, exponential delay steps, and retry
execution events without replacing any Julia method with a proof-local implementation.
-/

namespace JuliaLean.Proofs.base.error

open JuliaLean JuliaLean.Float JuliaLean.Registry JuliaLean.base.error

def errorMessageSpec : Prop :=
  ∀ (α : Type) arguments,
    ∃ message,
      errorVararg (α := α) arguments = .error (.errorException message) ∧
      message = String.intercalate "" (arguments.map ErrorArgument.stringValue)

def rethrowContextSpec : Prop :=
  ∀ (α Exception Trace : Type) (context : ExceptionContext Exception Trace)
      (replacement : Exception),
    rethrowCurrent (α := α) context = .error context ∧
    rethrowOther (α := α) context replacement = .error { context with exception := replacement }

def backtraceSentinel : BacktraceWord := BitVec.ofNat 64 (2 ^ 64 - 1)

def unknownTagMetadata (tag : Nat) : BacktraceWord := BitVec.ofNat 64 (tag * 64)

def interpreterMetadata (header : Nat) : BacktraceWord := BitVec.ofNat 64 (2 + 64 + header * 1024)

def backtraceFormatSpec : Prop :=
  (∀ (pointers : Array BacktraceWord) (managed : Array BacktraceManaged),
    (∀ index, index < pointers.size → pointers[index]? ≠ some backtraceSentinel) →
      reformatBacktrace pointers managed = .ok (pointers.map BacktraceLocation.native)) ∧
  (∀ tag, tag < 16 → tag ≠ 1 →
    reformatBacktrace #[backtraceSentinel, unknownTagMetadata tag] #[] =
      .error (.argumentError s!"Unexpected extended backtrace entry tag {tag} at bt[1]")) ∧
  (∀ header codeId moduleName, header < 2 ^ 54 →
    reformatBacktrace #[backtraceSentinel, interpreterMetadata header]
      #[.code (.methodInstance codeId), .module moduleName] =
        .ok #[.interpreter ⟨.methodInstance codeId, header, some moduleName⟩])

def backtraceCaptureSpec : Prop :=
  ∀ (fromHere : Bool → Nat → Array BacktraceWord × Array BacktraceManaged)
      (fromCatch : Unit → Array BacktraceWord × Array BacktraceManaged),
    let current := fromHere false 1
    let caught := fromCatch ()
    (∀ index, index < current.1.size → current.1[index]? ≠ some backtraceSentinel) →
    (∀ index, index < caught.1.size → caught.1[index]? ≠ some backtraceSentinel) →
    backtrace fromHere = .ok (current.1.map BacktraceLocation.native) ∧
    catchBacktrace fromCatch = .ok (caught.1.map BacktraceLocation.native)

structure RawExceptionRecord (Exception : Type) where
  exception : Exception
  pointers : Array BacktraceWord
  managed : Array BacktraceManaged

def rawExceptionCells {Exception : Type} (record : RawExceptionRecord Exception) :
    List (ExceptionStackValue Exception) :=
  [.exception record.exception, .backtracePointers record.pointers, .backtraceValues record.managed]

def rawExceptionStackValues {Exception : Type} (records : List (RawExceptionRecord Exception)) :
    Array (ExceptionStackValue Exception) :=
  (records.flatMap rawExceptionCells).toArray

def noBacktraceEntry {Exception : Type} (exception : Exception) : ExceptionStackEntry Exception :=
  ⟨exception, none⟩

def expectedExceptionEntries {Exception : Type} :
    List (RawExceptionRecord Exception) → Except JuliaException (Array (ExceptionStackEntry Exception))
  | [] => .ok #[]
  | record :: rest => do
      let entries ← expectedExceptionEntries rest
      let formatted ← reformatBacktrace record.pointers record.managed
      pure (entries.push ⟨record.exception, some formatted⟩)

def expectedExceptionStack {Exception : Type} (records : List (RawExceptionRecord Exception)) :
    Except JuliaException (ExceptionStack Exception) := do
  let entries ← expectedExceptionEntries records
  pure ⟨entries⟩

def currentExceptionsSpec : Prop :=
  (∀ (Task Exception : Type) (currentTask task : Task)
      (getStack : Task → Bool → Int → Array (ExceptionStackValue Exception))
      (newestFirst : List Exception),
    getStack task false 2147483647 =
      (newestFirst.map ExceptionStackValue.exception).toArray →
    currentExceptions currentTask getStack task false =
      .ok ⟨(newestFirst.reverse.map noBacktraceEntry).toArray⟩) ∧
  (∀ (Task Exception : Type) (currentTask task : Task)
      (getStack : Task → Bool → Int → Array (ExceptionStackValue Exception))
      (newestFirst : List (RawExceptionRecord Exception)),
    getStack task true 2147483647 = rawExceptionStackValues newestFirst →
    currentExceptions currentTask getStack task true = expectedExceptionStack newestFirst)

def keywordAndSystemErrorsSpec : Prop :=
  (∀ (α : Type) keyword arguments worldAge,
    kwerr (α := α) keyword arguments worldAge =
      .error (.methodError "Core.kwcall" (keyword :: arguments) (worldAge ()))) ∧
  (∀ (α P : Type) (string : P → String) (errnoNow : Unit → Int) (p : P)
      (errno : Int) (extraInfo : String),
    systemerrorErrno (α := α) string p errno extraInfo =
      .error (.systemError (string p) errno extraInfo) ∧
    systemerrorBool string errnoNow p false extraInfo = .ok () ∧
    systemerrorBool string errnoNow p true extraInfo =
      .error (.systemError (string p) (errnoNow ()) extraInfo)) ∧
  (∀ (α P : Type) (string : P → String) (getLastError : Unit → BitVec 32)
      (p : P) (code : BitVec 32) (extraInfo : String),
    windowserrorCode (α := α) string p code extraInfo =
      .error (.windowsSystemError (string p) code extraInfo) ∧
    windowserrorBool string getLastError p false extraInfo = .ok () ∧
    windowserrorBool string getLastError p true extraInfo =
      .error (.windowsSystemError (string p) (getLastError ()) extraInfo))

def errorRuntimeContractSpec : Prop :=
  errorMessageSpec ∧ backtraceFormatSpec ∧ backtraceCaptureSpec ∧ keywordAndSystemErrorsSpec


def assertExpansionSpec : Prop :=
  (∀ condition text baseAvailable applicable baseString,
    let expansion := assertMacro condition [.string text] baseAvailable applicable baseString
    expansion.condition = .escaped condition ∧ expansion.message = .literal text) ∧
  (∀ condition expression baseAvailable applicable baseString,
    let term := AssertExpression.expression expression
    let expansion := assertMacro condition [term] baseAvailable applicable baseString
    expansion.condition = .escaped condition ∧ expansion.message = .runtimeStringify term) ∧
  (∀ text baseStringApplicable baseString,
    let condition := AssertExpression.other text
    let available := baseStringApplicable condition
    let expansion := assertMacro condition [] available baseStringApplicable baseString
    expansion.condition = .escaped condition ∧
    expansion.message =
      if available then .literal (baseString condition) else .quotedStringify condition) ∧
  (∀ condition first rest baseAvailable applicable baseString,
    assertMacro condition (first :: rest) baseAvailable applicable baseString =
      assertMacro condition [first] baseAvailable applicable baseString) ∧
  (∀ condition messages available applicable stringify barrier baseDefined println,
    let expansion := assertMacro condition messages available applicable stringify
    evaluateAssertExpansion expansion true barrier baseDefined stringify println = .ok () ∧
    evaluateAssertExpansion expansion false barrier baseDefined stringify println =
      .error (.assertionError (assertionMessageText barrier baseDefined stringify println expansion.message)))

def assertStringificationSpec : Prop :=
  ∀ (α : Type) (compilerBarrier : (α → String) → α → String)
      (barrierIdentity : ∀ function value, compilerBarrier function value = function value)
      (baseDefined : Bool) (baseString : α → String) (println : α → Unit) (message : α),
    assertToString compilerBarrier baseDefined baseString println message =
      (if baseDefined then baseString message else "Error during bootstrap. See stdout.")

def defaultBackoff : Except JuliaException ExponentialBackOff :=
  let defaults := backoffKeywordDefaults
  defaultExponentialBackOff nonnegativeInt nonnegativeFloat nonnegativeFloat
    nonnegativeFloat nonnegativeFloat identityInt identityFloat identityFloat
    identityFloat identityFloat defaults.1 defaults.2.1 defaults.2.2.1 defaults.2.2.2.1 defaults.2.2.2.2

def backoffConstructionSpec : Prop :=
  defaultBackoff = .ok ⟨1, F64.ofBits 0x3fa999999999999a, F64.ofBits 0x4024000000000000,
    F64.ofBits 0x4014000000000000, F64.ofBits 0x3fb999999999999a⟩ ∧
  (∀ {N A M F J : Type}
      (nonnegativeN : N → Bool) (nonnegativeA : A → Bool) (nonnegativeM : M → Bool)
      (nonnegativeF : F → Bool) (nonnegativeJ : J → Bool)
      (toInt : N → Except JuliaException Int)
      (toFirst : A → Except JuliaException F64) (toMax : M → Except JuliaException F64)
      (toFactor : F → Except JuliaException F64) (toJitter : J → Except JuliaException F64)
      (n : N) (firstDelay : A) (maxDelay : M) (factor : F) (jitter : J),
    (nonnegativeN n = false ∨ nonnegativeA firstDelay = false ∨ nonnegativeM maxDelay = false ∨
      nonnegativeF factor = false ∨ nonnegativeJ jitter = false) →
    makeExponentialBackOff nonnegativeN nonnegativeA nonnegativeM nonnegativeF nonnegativeJ
      toInt toFirst toMax toFactor toJitter n firstDelay maxDelay factor jitter =
      .error (.errorException "all inputs must be non-negative")) ∧
  (∀ {N A M F J : Type}
      (nonnegativeN : N → Bool) (nonnegativeA : A → Bool) (nonnegativeM : M → Bool)
      (nonnegativeF : F → Bool) (nonnegativeJ : J → Bool)
      (toInt : N → Except JuliaException Int)
      (toFirst : A → Except JuliaException F64) (toMax : M → Except JuliaException F64)
      (toFactor : F → Except JuliaException F64) (toJitter : J → Except JuliaException F64)
      (n : N) (firstDelay : A) (maxDelay : M) (factor : F) (jitter : J)
      (n64 : Int) (first64 max64 factor64 jitter64 : F64),
    nonnegativeN n = true → nonnegativeA firstDelay = true → nonnegativeM maxDelay = true →
    nonnegativeF factor = true → nonnegativeJ jitter = true →
    toInt n = .ok n64 → toFirst firstDelay = .ok first64 → toMax maxDelay = .ok max64 →
    toFactor factor = .ok factor64 → toJitter jitter = .ok jitter64 →
    makeExponentialBackOff nonnegativeN nonnegativeA nonnegativeM nonnegativeF nonnegativeJ
      toInt toFirst toMax toFactor toJitter n firstDelay maxDelay factor jitter =
      .ok ⟨n64, first64, max64, factor64, jitter64⟩)


def backoffIterationSpec : Prop :=
  (∀ backoff, lengthExponentialBackOff backoff = backoff.n ∧
    eltypeExponentialBackOff () = .float64) ∧
  (∀ minimum backoff rng,
    let (result, rngAfter) := iterateExponentialBackOff minimum backoff rng none
    if backoff.n < 1 then result = none ∧ rngAfter = rng
    else
      result = some (minimum backoff.first_delay backoff.max_delay,
        (backoff.n - 1,
          minimum backoff.max_delay
            (F64.mul (F64.mul (minimum backoff.first_delay backoff.max_delay) backoff.factor)
              (backoffRateFactor backoff.jitter (rng.sample rng.cursor))))) ∧
      rngAfter.cursor = rng.cursor + 1) ∧
  (∀ minimum backoff rng state,
    let (result, rngAfter) := iterateExponentialBackOff minimum backoff rng (some state)
    if state.1 < 1 then result = none ∧ rngAfter = rng
    else
      result = some (state.2,
        (state.1 - 1,
          minimum backoff.max_delay
            (F64.mul (F64.mul state.2 backoff.factor)
              (backoffRateFactor backoff.jitter (rng.sample rng.cursor))))) ∧
      rngAfter.cursor = rng.cursor + 1) ∧
  (∀ jitter sample,
    F64.le F64.zero jitter = true → F64.le F64.zero sample = true →
    F64.lt sample F64.one = true →
      F64.le (F64.sub F64.one jitter) (backoffRateFactor jitter sample) = true ∧
      F64.le (backoffRateFactor jitter sample) (F64.add F64.one jitter) = true)

def retryBehaviorSpec : Prop :=
  (∀ (Args Delays State Exception Trace Result : Type)
      (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
      (delays : Delays)
      (iterate : Delays → Float64RNG → Option State → Option (F64 × State) × Float64RNG)
      (check : Option (State → Exception → RetryCheckResult State))
      (sleep : F64 → Unit) (rng : Float64RNG) (args : Args)
      (result : RetryTrace Exception Trace State Result),
    retry f delays iterate check sleep rng args = some result →
    match result.events.getLast? with
    | some (.success value) => result.result = .ok value
    | some (.rejected _ context) => result.result = .error context
    | some (.final terminal) => result.result = terminal
    | some (.retry _ _ _ _) | none => False) ∧
  (∀ (Args Exception Trace Result : Type)
      (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
      (sleep : F64 → Unit) (rng : Float64RNG) (args : Args) (minimum : F64 → F64 → F64)
      (backoff : ExponentialBackOff),
    ∃ result, retry f backoff (iterateExponentialBackOff minimum) none sleep rng args =
      some result)

theorem errorMessage_proven : errorMessageSpec := by
  intro α arguments
  refine ⟨String.intercalate "" (arguments.map ErrorArgument.stringValue), ?_, rfl⟩
  cases arguments with
  | nil => rfl
  | cons argument rest =>
    cases rest with
    | nil => cases argument <;> simp [errorVararg, ErrorArgument.stringValue]
    | cons other rest => cases argument <;> rfl

theorem rethrowContext_proven : rethrowContextSpec := by
  intro α Exception Trace context replacement
  exact ⟨rfl, rfl⟩

theorem keywordAndSystemErrors_proven : keywordAndSystemErrorsSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intros; rfl
  · intros; exact ⟨rfl, rfl, rfl⟩
  · intros; exact ⟨rfl, rfl, rfl⟩

theorem assertExpansion_proven : assertExpansionSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intro text applicable string
    dsimp only
    cases h : applicable (.other text) <;> simp [assertMacro, h]
  · intro condition first rest available applicable string
    cases first <;> rfl
  · intros; exact ⟨rfl, rfl⟩

theorem assertStringification_proven : assertStringificationSpec := by
  intro α barrier identity defined string println message
  simp [assertToString, identity, bootstrapAssertToString]

theorem backoffConstruction_proven : backoffConstructionSpec := by
  refine ⟨by rfl, ?_, ?_⟩
  · intro N A M F J nn na nm nf nj ti ta tm tf tj n a m f j h
    rcases h with h | h | h | h | h <;>
      simp [makeExponentialBackOff, h, errorVararg]
  · intro N A M F J nn na nm nf nj ti ta tm tf tj n a m f j ni ai mi fi ji
      hn ha hm hf hj hi hia him hif hij
    simp [makeExponentialBackOff, hn, ha, hm, hf, hj, hi, hia, him, hif, hij]
    rfl

namespace BacktraceProof

theorem native_loop (bt : Array BacktraceWord) (bt2 : Array BacktraceManaged)
    (native : ∀ k, k < bt.size → bt[k]? ≠ some (BitVec.ofNat 64 (2^64-1)))
    (i j : Nat) (positive : 0 < i) (ret : Array BacktraceLocation) :
    reformatBacktraceLoop bt bt2 i j ret =
      .ok (ret ++ (bt.extract (i-1) bt.size).map BacktraceLocation.native) := by
  rw [reformatBacktraceLoop]
  split
  · rename_i hi
    have hindex : i-1 < bt.size := by omega
    have hget : arrayGet1 bt i = .ok bt[i-1] := by simp [arrayGet1, hindex]
    rw [hget]
    simp only [bind, Except.bind]
    have hne : bt[i-1] ≠ BitVec.ofNat 64 (2^64-1) := by
      intro he
      apply native (i-1) hindex
      simp [hindex, he]
    simp only [bne_iff_ne]
    rw [if_pos hne]
    rw [native_loop bt bt2 native (i+1) j (by omega)]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_append, Array.toList_push, Array.toList_map,
      Array.toList_extract]
    have hs : bt.toList.drop (i-1) = bt[i-1] :: bt.toList.drop i := by
      have h := List.drop_eq_getElem_cons (l := bt.toList) (i := i-1) (by simpa using hindex)
      simpa [Nat.sub_add_cancel positive, Array.getElem_toList] using h
    have hsize : bt.size - (i-1) = (bt.size-i)+1 := by omega
    simp [hs, List.map_cons, List.append_assoc, hsize, List.take_succ_cons]
  · rename_i hi
    have hz : bt.size ≤ i-1 := by omega
    have hextract : bt.extract (i-1) bt.size = #[] :=
      Array.extract_eq_empty_of_le (by simpa using hz)
    simp only [hextract, Array.map_empty, Array.append_empty]
    rfl
termination_by bt.size + 1 - i

theorem native_format (bt : Array BacktraceWord) (managed : Array BacktraceManaged)
    (native : ∀ k, k < bt.size → bt[k]? ≠ some (BitVec.ofNat 64 (2^64-1))) :
    reformatBacktrace bt managed = .ok (bt.map BacktraceLocation.native) := by
  simpa [reformatBacktrace] using native_loop bt managed native 1 1 (by decide) #[]

end BacktraceProof

namespace HeaderProof
theorem header (h : Nat) (bound : h < 2^54) :
    ((BitVec.ofNat 64 (2+64+h*1024)) >>> 10).toNat = h ∧
    ((BitVec.ofNat 64 (2+64+h*1024)) &&& BitVec.ofNat 64 7).toNat = 2 ∧
    (((BitVec.ofNat 64 (2+64+h*1024)) >>> 3) &&& BitVec.ofNat 64 7).toNat = 0 ∧
    (((BitVec.ofNat 64 (2+64+h*1024)) >>> 6) &&& BitVec.ofNat 64 15).toNat = 1 := by
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have hm : (2+64+h*1024) % 2^64 = 2+64+h*1024 := Nat.mod_eq_of_lt (by omega)
  rw [hm]
  simp only [Nat.shiftRight_eq_div_pow]
  change (2+64+h*1024)/1024 = h ∧
    (2+64+h*1024) &&& 7 = 2 ∧
    ((2+64+h*1024)/8) &&& 7 = 0 ∧
    ((2+64+h*1024)/64) &&& 15 = 1
  have hd : (2+64+h*1024)/1024 = h := by omega
  have h8 : (2+64+h*1024)/8 = 8+h*128 := by omega
  have h64 : (2+64+h*1024)/64 = 1+h*16 := by omega
  rw [hd, h8, h64]
  change h = h ∧ (2+64+h*1024) &&& (2^3-1) = 2 ∧
    (8+h*128) &&& (2^3-1) = 0 ∧ (1+h*16) &&& (2^4-1) = 1
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.add_mod, Nat.mul_mod]
end HeaderProof

namespace MetadataProof
theorem tag (tag : Nat) (h : tag < 16) :
    (((BitVec.ofNat 64 (tag * 64)) >>> 6) &&& BitVec.ofNat 64 15).toNat = tag := by
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have hmod : tag * 64 % 2 ^ 64 = tag * 64 := Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.shiftRight_eq_div_pow]
  change tag * 64 / 64 &&& 15 % 18446744073709551616 = tag
  have hdiv : tag * 64 / 64 = tag := by omega
  rw [hdiv]
  change tag &&& (2^4-1) = tag
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h
end MetadataProof

namespace FormatProof
theorem format : backtraceFormatSpec := by
  refine ⟨BacktraceProof.native_format, ?_, ?_⟩
  · intro tag bound different
    have ht := MetadataProof.tag tag bound
    rw [reformatBacktrace, reformatBacktraceLoop]
    simp only [arrayGet1, backtraceSentinel, unknownTagMetadata]
    simp only [Except.bind, bind]
    simp_all
    have hr : Nat.repr 1 = "1" := by decide
    rw [hr]
    simp [String.append_assoc]
    rfl
  · intro header codeId moduleName bound
    obtain ⟨hh, hn, hu, ht⟩ := HeaderProof.header header bound
    rw [reformatBacktrace, reformatBacktraceLoop]
    simp only [arrayGet1, backtraceSentinel, interpreterMetadata]
    simp only [Except.bind, bind]
    simp_all [managedCode, managedModule]
    rw [reformatBacktraceLoop]
    rfl
end FormatProof

namespace CaptureProof
theorem proven : backtraceCaptureSpec := by
  intro fromHere fromCatch
  dsimp only
  intro currentNative caughtNative
  constructor
  · exact BacktraceProof.native_format (fromHere false 1).1 (fromHere false 1).2 currentNative
  · exact BacktraceProof.native_format (fromCatch ()).1 (fromCatch ()).2 caughtNative
end CaptureProof

namespace CurrentProof

theorem get_append {α : Type} (a b : Array α) (i : Nat) (hi : 0 < i) (h : i ≤ a.size) :
    arrayGet1 (a ++ b) i = arrayGet1 a i := by
  simp [arrayGet1, Array.getElem?_append, show i - 1 < a.size by omega]

theorem entry_append {E : Type} (a b : Array (ExceptionStackValue E)) (bt : Bool)
    (i : Nat) (hi : 0 < i) (h : i + 2 ≤ a.size) :
    currentExceptionEntry (a ++ b) bt i = currentExceptionEntry a bt i := by
  simp only [currentExceptionEntry]
  rw [get_append a b i hi (by omega)]
  cases bt <;> simp only [Bool.false_eq_true, ↓reduceIte]
  rw [get_append a b (i+1) (by omega) (by omega),
      get_append a b (i+2) (by omega) (by omega)]

theorem loop_congr {E : Type} (a b : Array (ExceptionStackValue E)) (bt : Bool)
    (stride : Nat) (ks : List Nat) (ret : Array (ExceptionStackEntry E))
    (h : ∀ k ∈ ks, currentExceptionEntry a bt (1+k*stride) =
      currentExceptionEntry b bt (1+k*stride)) :
    currentExceptionsLoop a bt stride ks ret = currentExceptionsLoop b bt stride ks ret := by
  induction ks generalizing ret with
  | nil => rfl
  | cons k ks ih =>
    simp only [currentExceptionsLoop]
    rw [h k (by simp)]
    congr 1
    funext e
    exact ih _ (fun j hj => h j (by simp [hj]))

theorem raw_size {E : Type} (rs : List (RawExceptionRecord E)) :
    (rawExceptionStackValues rs).size = 3 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp [rawExceptionStackValues, rawExceptionCells, List.flatMap_cons] at *
    omega

theorem raw_snoc {E : Type} (rs : List (RawExceptionRecord E)) (r : RawExceptionRecord E) :
    rawExceptionStackValues (rs ++ [r]) =
      rawExceptionStackValues rs ++ #[.exception r.exception,
        .backtracePointers r.pointers, .backtraceValues r.managed] := by
  simp [rawExceptionStackValues, rawExceptionCells, List.flatMap_append]

theorem entry_snoc {E : Type} (rs : List (RawExceptionRecord E)) (r : RawExceptionRecord E) :
    currentExceptionEntry (rawExceptionStackValues (rs ++ [r])) true (1 + rs.length * 3) =
      (do let f ← reformatBacktrace r.pointers r.managed
          pure ⟨r.exception, some f⟩) := by
  rw [raw_snoc]
  have h1 : ¬ 1 + 3 * rs.length < 3 * rs.length := by omega
  have h2 : ¬ 1 + 3 * rs.length + 1 < 3 * rs.length := by omega
  have h3 : 1 + 3 * rs.length + 1 - 3 * rs.length = 2 := by omega
  simp [currentExceptionEntry, arrayGet1, Array.getElem?_append, raw_size,
    Nat.mul_comm, h1, h2, h3, stackException, stackBacktracePointers, stackBacktraceValues]
  rfl

theorem loop_acc {E : Type} (raw : Array (ExceptionStackValue E)) (bt : Bool)
    (stride : Nat) (ks : List Nat) (ret : Array (ExceptionStackEntry E)) :
    currentExceptionsLoop raw bt stride ks ret =
      (currentExceptionsLoop raw bt stride ks #[]).map (ret ++ ·) := by
  induction ks generalizing ret with
  | nil => simp [currentExceptionsLoop, Except.map]
  | cons k ks ih =>
    simp only [currentExceptionsLoop]
    cases h : currentExceptionEntry raw bt (1+k*stride) with
    | error e => rfl
    | ok e =>
      change currentExceptionsLoop raw bt stride ks (ret.push e) =
        (currentExceptionsLoop raw bt stride ks (#[e])).map (ret ++ ·)
      rw [ih, ih #[e]]
      cases h' : currentExceptionsLoop raw bt stride ks #[] with
      | error e => rfl
      | ok es =>
        simp only [Except.map]
        congr 1
        change ret.push e ++ es = ret ++ (#[e] ++ es)
        rw [Array.push_eq_append]
        exact Array.append_assoc

theorem expected_snoc {E : Type} (rs : List (RawExceptionRecord E)) (r : RawExceptionRecord E) :
    expectedExceptionEntries (rs ++ [r]) =
      (do let f ← reformatBacktrace r.pointers r.managed
          let es ← expectedExceptionEntries rs
          pure (#[⟨r.exception, some f⟩] ++ es)) := by
  induction rs with
  | nil =>
    simp only [List.nil_append, expectedExceptionEntries]
    cases reformatBacktrace r.pointers r.managed <;> rfl
  | cons a rs ih =>
    simp only [List.cons_append, expectedExceptionEntries]
    rw [ih]
    cases reformatBacktrace r.pointers r.managed <;>
      cases expectedExceptionEntries rs <;>
      cases reformatBacktrace a.pointers a.managed <;>
      simp [Except.bind, Except.pure, -Array.append_singleton, Array.push_eq_append,
        Array.append_assoc]

theorem loop_true_reverse {E : Type} (xs : List (RawExceptionRecord E)) :
    currentExceptionsLoop (rawExceptionStackValues xs.reverse) true 3
      (List.range xs.reverse.length).reverse #[] = expectedExceptionEntries xs.reverse := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    simp only [List.reverse_cons]
    generalize hrs : xs.reverse = rs at *
    simp only [List.length_append, List.length_singleton, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      currentExceptionsLoop]
    rw [entry_snoc]
    have hc : ∀ k ∈ (List.range rs.length).reverse,
        currentExceptionEntry (rawExceptionStackValues (rs ++ [r])) true (1+k*3) =
          currentExceptionEntry (rawExceptionStackValues rs) true (1+k*3) := by
      intro k hk
      have hk' : k < rs.length := List.mem_range.mp (List.mem_reverse.mp hk)
      rw [raw_snoc]
      exact entry_append _ _ true _ (by omega) (by rw [raw_size]; omega)
    cases hf : reformatBacktrace r.pointers r.managed with
    | error e => rw [expected_snoc, hf]; rfl
    | ok f =>
      change currentExceptionsLoop (rawExceptionStackValues (rs ++ [r])) true 3
        (List.range rs.length).reverse #[⟨r.exception, some f⟩] =
          expectedExceptionEntries (rs ++ [r])
      rw [loop_congr _ _ true 3 _ _ hc, loop_acc, ih, expected_snoc]
      rw [hf]
      cases expectedExceptionEntries rs <;> rfl

theorem loop_true {E : Type} (rs : List (RawExceptionRecord E)) :
    currentExceptionsLoop (rawExceptionStackValues rs) true 3
      (List.range rs.length).reverse #[] = expectedExceptionEntries rs := by
  simpa using loop_true_reverse rs.reverse

theorem entry_false_append {E : Type} (a b : Array (ExceptionStackValue E))
    (i : Nat) (hi : 0 < i) (h : i ≤ a.size) :
    currentExceptionEntry (a ++ b) false i = currentExceptionEntry a false i := by
  simp only [currentExceptionEntry, Bool.false_eq_true, ↓reduceIte]
  rw [get_append a b i hi h]

theorem loop_false_reverse {E : Type} (xs : List E) :
    currentExceptionsLoop (xs.reverse.map ExceptionStackValue.exception).toArray false 1
      (List.range xs.reverse.length).reverse #[] =
        .ok (xs.map noBacktraceEntry).toArray := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    simp only [List.reverse_cons]
    generalize hrs : xs.reverse = rs at *
    have he : currentExceptionEntry ((rs ++ [r]).map ExceptionStackValue.exception).toArray
        false (1 + rs.length * 1) = .ok (noBacktraceEntry r) := by
      simp [currentExceptionEntry, arrayGet1, List.map_append,
        Array.getElem?_append, stackException, noBacktraceEntry]
      rfl
    simp only [List.length_append, List.length_singleton, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      currentExceptionsLoop]
    rw [he]
    have hc : ∀ k ∈ (List.range rs.length).reverse,
        currentExceptionEntry ((rs ++ [r]).map ExceptionStackValue.exception).toArray false
          (1+k*1) =
        currentExceptionEntry (rs.map ExceptionStackValue.exception).toArray false (1+k*1) := by
      intro k hk
      have hk' : k < rs.length := List.mem_range.mp (List.mem_reverse.mp hk)
      simp only [List.map_append, List.map_singleton]
      have ha : ((rs.map ExceptionStackValue.exception) ++
          [ExceptionStackValue.exception r]).toArray =
          (rs.map ExceptionStackValue.exception).toArray ++
            #[ExceptionStackValue.exception r] := by simp
      rw [ha]
      exact entry_false_append _ _ _ (by omega) (by simp; omega)
    change currentExceptionsLoop _ false 1 _ #[noBacktraceEntry r] = _
    rw [loop_congr _ _ false 1 _ _ hc, loop_acc, ih]
    simp [Except.map, noBacktraceEntry]

theorem current_proven : currentExceptionsSpec := by
  constructor
  · intro T E current task get rs h
    simp only [currentExceptions, h, Bool.false_eq_true, ↓reduceIte,
      List.size_toArray, List.length_map]
    have hh := loop_false_reverse rs.reverse
    simp only [List.reverse_reverse] at hh
    simp only [Nat.add_sub_cancel, Nat.div_one]
    rw [hh]
    rfl
  · intro T E current task get rs h
    simp only [currentExceptions, h, ↓reduceIte, raw_size]
    have hn : (3 * rs.length + 3 - 1) / 3 = rs.length := by omega
    rw [hn, loop_true]
    rfl
end CurrentProof

namespace BoundsProof
def infinity : F64 := F64.ofBits 0x7ff0000000000000
theorem bounds_fail : ¬ backoffIterationSpec := by
  intro h
  have bounds := h.2.2.2 infinity F64.zero
  have hj : F64.le F64.zero infinity = true := by decide
  have hs : F64.le F64.zero F64.zero = true := by decide
  have hl : F64.lt F64.zero F64.one = true := by decide
  have invalid : F64.le (F64.sub F64.one infinity) (backoffRateFactor infinity F64.zero) = false := by decide
  have claim := (bounds hj hs hl).1
  rw [invalid] at claim
  contradiction
end BoundsProof

namespace RetryProof

def terminalInvariant {E T S R : Type} (trace : RetryTrace E T S R) : Prop :=
  match trace.events.getLast? with
  | some (.success value) => trace.result = .ok value
  | some (.rejected _ context) => trace.result = .error context
  | some (.final result) => trace.result = result
  | some (.retry _ _ _ _) | none => False

theorem terminal_cons {E T S R : Type} (trace : RetryTrace E T S R)
    (event : RetryEvent S E T R) (h : terminalInvariant trace) :
    terminalInvariant { trace with events := event :: trace.events } := by
  cases he : trace.events with
  | nil => simp [terminalInvariant, he] at h
  | cons a rest => simpa [terminalInvariant, he, List.getLast?_cons_cons] using h

theorem retry_terminal {Args Delays State Exception Trace Result : Type}
    (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
    (args : Args) (delays : Delays)
    (iterate : Delays → Float64RNG → Option State → Option (Float.F64 × State) × Float64RNG)
    (check : Option (State → Exception → RetryCheckResult State))
    (sleep : Float.F64 → Unit) (calls : Nat)
    (next : Option (Float.F64 × State) × Float64RNG)
    (result : RetryTrace Exception Trace State Result)
    (h : retryLoop f args delays iterate check sleep calls next = some result) :
    terminalInvariant result := by
  apply retryLoop.partial_correctness f args delays iterate check sleep
    (fun _ _ result => terminalInvariant result) ?_ calls next result h
  intro recur ih calls next result hresult
  split at hresult
  · cases hresult
    simp [terminalInvariant]
  · split at hresult
    · cases hresult
      simp [terminalInvariant]
    · dsimp only at hresult
      split at hresult
      · obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp hresult
        simp only [Option.pure_def, Option.some.injEq] at heq
        subst result
        exact terminal_cons rest _ (ih _ _ _ hr)
      · cases hresult
        simp [terminalInvariant, rethrowCurrent]

theorem retry_finite {Args Delays State Exception Trace Result : Type}
    (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
    (args : Args) (delays : Delays)
    (iterate : Delays → Float64RNG → Option State → Option (Float.F64 × State) × Float64RNG)
    (rank : State → Nat)
    (decreases : ∀ rng state delay state' rng',
      iterate delays rng (some state) = (some (delay, state'), rng') →
      rank state' < rank state)
    (sleep : Float.F64 → Unit) (calls : Nat)
    (next : Option (Float.F64 × State) × Float64RNG) :
    ∃ result, retryLoop f args delays iterate none sleep calls next = some result := by
  suffices ∀ n calls next,
      (∀ delay state, next.1 = some (delay, state) → rank state < n) →
      ∃ result, retryLoop f args delays iterate none sleep calls next = some result by
    cases hn : next.1 with
    | none => exact this 0 calls next (by simp [hn])
    | some pair =>
      rcases pair with ⟨d, s⟩
      exact this (rank s + 1) calls next (by
        intro delay state h
        simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
    intro calls next h
    cases hn : next.1 with
    | none => simp [retryLoop.eq_1, hn]
    | some pair => have := h pair.1 pair.2 hn; omega
  | succ n ih =>
    intro calls next h
    rw [retryLoop.eq_1]
    cases hn : next.1 with
    | none => simp [hn]
    | some pair =>
      simp only [hn]
      cases hf : f (calls + 1) args with
      | ok value => simp
      | error context =>
        simp only [retryCheck, Bool.true_eq, ↓reduceIte]
        obtain ⟨result, hr⟩ := ih (calls + 1)
          (iterate delays next.2 (some pair.2)) (by
            intro delay state he
            have hd := decreases next.2 pair.2 delay state
              (iterate delays next.2 (some pair.2)).2 (Prod.ext he rfl)
            have hb := h pair.1 pair.2 hn
            omega)
        simp [hr]

theorem exponential_decreases (min : Float.F64 → Float.F64 → Float.F64)
    (backoff : ExponentialBackOff) (rng : Float64RNG) (state : Int × Float.F64)
    (delay : Float.F64) (state' : Int × Float.F64) (rng' : Float64RNG)
    (h : iterateExponentialBackOff min backoff rng (some state) =
      (some (delay, state'), rng')) :
    state'.1.toNat < state.1.toNat := by
  simp only [iterateExponentialBackOff, Option.getD_some] at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨⟨_, hs⟩, _⟩ := h
    subst state'
    omega
end RetryProof

namespace RetrySpec
 theorem proven : retryBehaviorSpec := by
  constructor
  · intro Args Delays State Exception Trace Result f delays iterate check sleep rng args result h
    have terminal := RetryProof.retry_terminal f args delays iterate check sleep 0
      (iterate delays rng none) result h
    cases he : result.events.getLast? with
    | none => simp [RetryProof.terminalInvariant, he] at terminal
    | some event =>
      cases event <;> simpa [RetryProof.terminalInvariant, he] using terminal
  · intro Args Exception Trace Result f sleep rng args minimum backoff
    exact RetryProof.retry_finite f args backoff (iterateExponentialBackOff minimum)
      (fun state => state.1.toNat)
      (RetryProof.exponential_decreases minimum backoff) sleep 0
      (iterateExponentialBackOff minimum backoff rng none)
end RetrySpec

theorem backtraceFormat_proven : backtraceFormatSpec := FormatProof.format

theorem backtraceCapture_proven : backtraceCaptureSpec := CaptureProof.proven

theorem currentExceptions_proven : currentExceptionsSpec := CurrentProof.current_proven

theorem backoffIteration_refuted : ¬ backoffIterationSpec := BoundsProof.bounds_fail

theorem retryBehavior_proven : retryBehaviorSpec := RetrySpec.proven

theorem errorRuntimeContract_proven : errorRuntimeContractSpec :=
  ⟨errorMessage_proven, backtraceFormat_proven, backtraceCapture_proven,
    keywordAndSystemErrors_proven⟩

/-! Nothing to promise: error@33: generic function declaration; concrete error methods define its behavior. -/
def entries : List Entry := [
  { id := "error-error-message", juliaFile := "base/error.jl",
    juliaFns := ["error(s::Vararg{Any,N}) where {N}"],
    statement := "error raises an ErrorException with an empty message for no arguments, passes a single string through, and otherwise uses string(msg...).",
    source := "base/error.jl:42-57 (error docstring)", status := .proven,
    prop := ``errorMessageSpec, thm := some ``errorMessage_proven },
  { id := "error-rethrow-context", juliaFile := "base/error.jl",
    juliaFns := ["rethrow()", "rethrow(e)"],
    statement := "rethrow() propagates the current exception with its backtrace; rethrow(e) substitutes e while retaining that backtrace.",
    source := "base/error.jl:59-74 (rethrow docstring)", status := .proven,
    prop := ``rethrowContextSpec, thm := some ``rethrowContext_proven },
  { id := "error-backtrace-format", juliaFile := "base/error.jl",
    juliaFns := ["_reformat_bt"],
    statement := "Backtrace formatting preserves native frame order, decodes interpreter headers and optional modules, and rejects each unknown frame tag.",
    source := "base/error.jl:84-114; invariant: runtime backtrace tags and offsets", status := .proven,
    prop := ``backtraceFormatSpec, thm := some ``backtraceFormat_proven },
  { id := "error-backtrace-capture", juliaFile := "base/error.jl",
    juliaFns := ["backtrace()", "catch_backtrace()"],
    statement := "backtrace requests the current point while skipping its own frame; catch_backtrace returns the throwing point, and both use the same raw-frame format.",
    source := "backtrace and catch_backtrace docstrings, base/error.jl:116-155", status := .proven,
    prop := ``backtraceCaptureSpec, thm := some ``backtraceCapture_proven },
  { id := "error-current-exceptions-stack", juliaFile := "base/error.jl",
    juliaFns := ["current_exceptions"],
    statement := "current_exceptions reverses the runtime's newest-first records so the root cause is first, and sets every backtrace to nothing when backtrace=false.",
    source := "base/error.jl:161-189 (current_exceptions docstring)", status := .proven,
    prop := ``currentExceptionsSpec, thm := some ``currentExceptions_proven },
  { id := "error-keyword-system-errors", juliaFile := "base/error.jl",
    juliaFns := ["kwerr", "systemerror(p, b::Bool)", "systemerror(p, errno::Cint)", "windowserror(p, b::Bool)", "windowserror(p, code::UInt32)"],
    statement := "kwerr creates a Core.kwcall MethodError with the keyword and positional arguments at the current world; systemerror and windowserror throw only when their Boolean guard is true and otherwise return nothing.",
    source := "base/error.jl:191-220; systemerror and windowserror docstrings", status := .proven,
    prop := ``keywordAndSystemErrorsSpec, thm := some ``keywordAndSystemErrors_proven },
  { id := "error-assertion-expansion", juliaFile := "base/error.jl",
    juliaFns := ["@assert"],
    statement := "@assert preserves the condition, passes string messages through, stringifies expression messages at runtime, and succeeds for true conditions while throwing AssertionError for false conditions.",
    source := "base/error.jl:226-263 (@assert docstring and macro)", status := .proven,
    prop := ``assertExpansionSpec, thm := some ``assertExpansion_proven },
  { id := "error-assertion-stringification", juliaFile := "base/error.jl",
    juliaFns := ["_assert_tostring", "__assert_tostring"],
    statement := "Assertion message conversion calls Base.string when available; during bootstrap it prints the value and returns the documented fixed message.",
    source := "base/error.jl:265-268", status := .proven,
    prop := ``assertStringificationSpec, thm := some ``assertStringification_proven },
  { id := "error-backoff-construction", juliaFile := "base/error.jl",
    juliaFns := ["ExponentialBackOff(n, first_delay, max_delay, factor, jitter)", "ExponentialBackOff(; kwargs...)"],
    statement := "The backoff constructor rejects every negative field, stores accepted values in its Int and Float64 fields, and defaults to n=1, first_delay=0.05, max_delay=10.0, factor=5.0, jitter=0.1.",
    source := "base/error.jl:270-291 (constructor and iterator docstring)", status := .proven,
    prop := ``backoffConstructionSpec, thm := some ``backoffConstruction_proven },
  { id := "error-backoff-iteration", juliaFile := "base/error.jl",
    juliaFns := ["iterate(::ExponentialBackOff)", "length(::ExponentialBackOff)", "eltype(::Type{ExponentialBackOff})"],
    statement := "The iterator yields n Float64 delays, starts at min(first_delay,max_delay), decrements its count, multiplies each delay by factor times a jitter rate in [1-jitter,1+jitter), and clamps each result to max_delay.",
    source := "base/error.jl:283-300 (ExponentialBackOff docstring and iterator)", status := .refuted,
    prop := ``backoffIterationSpec, thm := some ``backoffIteration_refuted,
    issue := "none found (queries: ExponentialBackOff Inf jitter NaN; ExponentialBackOff in:title; jitter backoff in:title)" },
  { id := "error-retry-behavior", juliaFile := "base/error.jl",
    juliaFns := ["retry"],
    statement := "Every terminating retry run ends in a success, a rejected exception, or a final unguarded call with the corresponding result; a finite ExponentialBackOff without a check always terminates.",
    source := "base/error.jl:302-342 (retry docstring and implementation)", status := .proven,
    prop := ``retryBehaviorSpec, thm := some ``retryBehavior_proven },
  { id := "error-runtime-contract", juliaFile := "base/error.jl",
    juliaFns := ["error(s::Vararg{Any,N}) where {N}", "_reformat_bt", "backtrace", "catch_backtrace", "kwerr", "systemerror", "windowserror"],
    statement := "Error construction follows the documented string rules; backtrace capture and formatting preserve frame order and tags; keyword and system errors preserve their documented exception type and guard behavior.",
    source := "base/error.jl:42-57,84-220", status := .proven,
    prop := ``errorRuntimeContractSpec, thm := some ``errorRuntimeContract_proven }
]

end JuliaLean.Proofs.base.error
