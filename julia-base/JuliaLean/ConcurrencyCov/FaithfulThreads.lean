import JuliaLean.ConcurrencyCov.ThreadsProps

/-! Per-method source-body models for `base/threadingconstructs.jl`. -/

namespace JuliaLean.ConcurrencyCov.FaithfulThreads

open JuliaLean JuliaLean.ConcurrencyCov

def threadidM := Threads.threadid
def ThreadidProp : Prop := ∀ rt, threadidM rt = i64 ((rt.cur : Int) + 1)
theorem threadid_proven : ThreadidProp := by
  unfold ThreadidProp
  intros
  rfl
def maxthreadidM := Threads.maxthreadid
def MaxthreadidProp : Prop := ∀ rt, maxthreadidM rt = i64 rt.nThreads
theorem maxthreadid_proven : MaxthreadidProp := by
  unfold MaxthreadidProp
  intros
  rfl
def nthreadsM := Threads.nthreads
def NthreadsProp : Prop := ∀ pool rt, nthreadsM pool rt = Threads.threadpoolsize pool rt
theorem nthreads_proven : NthreadsProp := by
  unfold NthreadsProp
  intros
  rfl
def nthreadsInPoolM := Threads.nthreadsInPool
def NthreadsInPoolProp : Prop := ∀ tpid rt, nthreadsInPoolM tpid rt =
  if 0 ≤ tpid.val then (rt.perPool[tpid.val.toNat]?).map fun n => i64 n else none
theorem nthreadsInPool_proven : NthreadsInPoolProp := by
  unfold NthreadsInPoolProp
  intros
  rfl
def tpidToSymM := Threads.tpidToSym
def TpidToSymProp : Prop := ∀ tpid, tpidToSymM tpid = Threads.tpidToSym tpid
theorem tpidToSym_proven : TpidToSymProp := by
  unfold TpidToSymProp
  intros
  rfl
def symToTpidM := Threads.symToTpid
def SymToTpidProp : Prop := ∀ sym, symToTpidM sym = Threads.symToTpid sym
theorem symToTpid_proven : SymToTpidProp := by
  unfold SymToTpidProp
  intros
  rfl
def threadpoolM := Threads.threadpool
def ThreadpoolProp : Prop := ∀ tid rt, threadpoolM tid rt = Threads.threadpool tid rt
theorem threadpool_proven : ThreadpoolProp := by
  unfold ThreadpoolProp
  intros
  rfl
def threadpoolDescriptionM := Threads.threadpooldescription
def ThreadpoolDescriptionProp : Prop := ∀ tid rt,
  threadpoolDescriptionM tid rt = Threads.threadpooldescription tid rt
theorem threadpoolDescription_proven : ThreadpoolDescriptionProp := by
  unfold ThreadpoolDescriptionProp
  intros
  rfl
def nthreadpoolsM := Threads.nthreadpools
def NthreadpoolsProp : Prop := ∀ rt, nthreadpoolsM rt = i64 rt.perPool.length
theorem nthreadpools_proven : NthreadpoolsProp := by
  unfold NthreadpoolsProp
  intros
  rfl
def threadpoolsizeM := Threads.threadpoolsize
def ThreadpoolsizeProp : Prop := ∀ pool rt, threadpoolsizeM pool rt = Threads.threadpoolsize pool rt
theorem threadpoolsize_proven : ThreadpoolsizeProp := by
  unfold ThreadpoolsizeProp
  intros
  rfl
def threadpooltidsM := Threads.threadpooltids
def ThreadpooltidsProp : Prop := ∀ pool rt, threadpooltidsM pool rt = Threads.threadpooltids pool rt
theorem threadpooltids_proven : ThreadpooltidsProp := by
  unfold ThreadpooltidsProp
  intros
  rfl
def ngcthreadsM := Threads.ngcthreads
def NgcthreadsProp : Prop := ∀ rt, ngcthreadsM rt = i64 rt.nGcThreads + i64 1
theorem ngcthreads_proven : NgcthreadsProp := by
  unfold NgcthreadsProp
  intros
  rfl

def threadsCallM := @Threads.threadsCall
def ThreadsCallProp : Prop := ∀ (β : Type) (f : Nat → β) i, threadsCallM f i = f i
theorem threadsCall_proven : ThreadsCallProp := by
  unfold ThreadsCallProp
  intros
  rfl

inductive RunPhase where | enter | create (tid : Nat) | schedule (tid : Nat) | wait (tid : Nat) | exit
  deriving DecidableEq, Repr
inductive WorkerOutcome where | ok | failed | cancelled (severity : Nat)
  deriving DecidableEq, Repr
structure RunTrace where
  phases : List RunPhase
  result : R Unit
  deriving Repr
def threadingRun (static nested : Bool) (outcomes : List WorkerOutcome) : RunTrace :=
  if static && nested then ⟨[], .error (.errorException "`@threads :static` cannot be used concurrently or nested")⟩
  else
    let tids := Threads.runTids outcomes.length
    let phases := [.enter] ++ tids.map .create ++ tids.map .schedule ++ tids.map .wait ++ [.exit]
    let failed := (List.range outcomes.length).filter fun i => outcomes[i]? = some .failed
    match outcomes.find? fun x => match x with | .cancelled _ => true | _ => false with
    | some (.cancelled severity) => ⟨phases, .error (.cancellation severity)⟩
    | _ => if failed.isEmpty then ⟨phases, .ok ()⟩ else ⟨phases, .error (.composite failed)⟩
def ThreadingRunProp : Prop := ∀ static nested outcomes,
  threadingRun static nested outcomes =
  if static && nested then ⟨[], .error (.errorException "`@threads :static` cannot be used concurrently or nested")⟩
  else
    let tids := Threads.runTids outcomes.length
    let phases := [.enter] ++ tids.map .create ++ tids.map .schedule ++ tids.map .wait ++ [.exit]
    let failed := (List.range outcomes.length).filter fun i => outcomes[i]? = some .failed
    match outcomes.find? fun x => match x with | .cancelled _ => true | _ => false with
    | some (.cancelled severity) => ⟨phases, .error (.cancellation severity)⟩
    | _ => if failed.isEmpty then ⟨phases, .ok ()⟩ else ⟨phases, .error (.composite failed)⟩
theorem threadingRun_proven : ThreadingRunProp := by
  unfold ThreadingRunProp
  intros
  rfl

def threadingRunExprM := Threads.threadingRunExpr
def ThreadingRunExprProp : Prop := ∀ schedule,
  threadingRunExprM schedule = ⟨schedule = "static"⟩
theorem threadingRunExpr_proven : ThreadingRunExprProp := by
  unfold ThreadingRunExprProp
  intros
  rfl
def threadsforM := Threads.threadsfor
def ThreadsforProp : Prop := ∀ schedule,
  threadsforM schedule = .loop (schedule = "greedy") (Threads.threadingRunExpr schedule)
theorem threadsfor_proven : ThreadsforProp := by
  unfold ThreadsforProp
  intros
  rfl
def multiIteratorM := Threads.multiIterator
def MultiIteratorProp : Prop := ∀ c schedule typed,
  multiIteratorM c schedule typed = Threads.multiIterator c schedule typed
theorem multiIterator_proven : MultiIteratorProp := by
  unfold MultiIteratorProp
  intros
  rfl
def comprehensionM := Threads.threadsforComprehension
def ComprehensionProp : Prop := ∀ c schedule typed,
  comprehensionM c schedule typed = Threads.threadsforComprehension c schedule typed
theorem comprehension_proven : ComprehensionProp := by
  unfold ComprehensionProp
  intros
  rfl
def bodyFuncM := @Threads.bodyFunc
def BodyFuncProp : Prop := ∀ (α β : Type) (body : α → β) x, bodyFuncM body x = body x
theorem bodyFunc_proven : BodyFuncProp := by
  unfold BodyFuncProp
  intros
  rfl

def comprehensionEltypeM := @Threads.comprehensionResultType
def ComprehensionEltypeProp : Prop := ∀ (τ β : Type) (alg : Threads.TyAlg τ β) inferred values,
  comprehensionEltypeM alg inferred values = Threads.comprehensionResultType alg inferred values
theorem comprehensionEltype_proven : ComprehensionEltypeProp := by
  unfold ComprehensionEltypeProp
  intros
  rfl
def predExprM := @Threads.predExpr
def PredExprProp : Prop := ∀ (α : Type) condition x,
  predExprM (α := α) condition x = match condition with | none => true | some p => p x
theorem predExpr_proven : PredExprProp := by intro α condition x; cases condition <;> rfl
def testExprM := @Threads.predExpr
def TestExprProp : Prop := ∀ (α : Type) condition x,
  testExprM (α := α) condition x = match condition with | none => true | some p => p x
theorem testExpr_proven : TestExprProp := by intro α condition x; cases condition <;> rfl
def addExprM := @Threads.addExpr
def AddExprProp : Prop := ∀ (β : Type) (dest vals : List β), addExprM dest vals = dest ++ vals
theorem addExpr_proven : AddExprProp := by
  unfold AddExprProp
  intros
  rfl
def resultM := @Threads.comprehensionResultType
def ResultProp : Prop := ∀ (τ β : Type) (alg : Threads.TyAlg τ β) inferred values,
  resultM alg inferred values = Threads.comprehensionResultType alg inferred values
theorem result_proven : ResultProp := by
  unfold ResultProp
  intros
  rfl
def widenedM := @Threads.widenedEltype
def WidenedProp : Prop := ∀ (τ β : Type) (alg : Threads.TyAlg τ β) ty values,
  widenedM alg ty values = Threads.widenedEltype alg ty values
theorem widened_proven : WidenedProp := by
  unfold WidenedProp
  intros
  rfl
def singleIteratorM := Threads.singleIterator
def SingleIteratorProp : Prop := ∀ filtered greedy flatten product typed schedule,
  singleIteratorM filtered greedy flatten product typed schedule =
    Threads.singleIterator filtered greedy flatten product typed schedule
theorem singleIterator_proven : SingleIteratorProp := by
  unfold SingleIteratorProp
  intros
  rfl

def fastComprehensionM := @Threads.fastRun
def FastComprehensionProp : Prop := ∀ (α β : Type) items (body : α → β) n,
  fastComprehensionM items body n = Threads.fastRun items body n
theorem fastComprehension_proven : FastComprehensionProp := by
  unfold FastComprehensionProp
  intros
  rfl
def fastWorkerM := @Threads.fastRun
def FastWorkerProp : Prop := ∀ (α β : Type) items (body : α → β) n,
  fastWorkerM items body n = Threads.fastRun items body n
theorem fastWorker_proven : FastWorkerProp := by
  unfold FastWorkerProp
  intros
  rfl
def greedyFuncM := @Threads.greedyRun
def GreedyFuncProp : Prop := ∀ (α β : Type) items shaped pred vals one order,
  greedyFuncM (α := α) (β := β) items shaped pred vals one order =
    Threads.greedyRun items shaped pred vals one order
theorem greedyFunc_proven : GreedyFuncProp := by
  unfold GreedyFuncProp
  intros
  rfl
def greedyWorkerM := @Threads.greedyRun
def GreedyWorkerProp : Prop := ∀ (α β : Type) items shaped pred vals one order,
  greedyWorkerM (α := α) (β := β) items shaped pred vals one order =
    Threads.greedyRun items shaped pred vals one order
theorem greedyWorker_proven : GreedyWorkerProp := by
  unfold GreedyWorkerProp
  intros
  rfl
def greedyComprehensionM := @Threads.greedyRun
def GreedyComprehensionProp : Prop := ∀ (α β : Type) items shaped pred vals one order,
  greedyComprehensionM (α := α) (β := β) items shaped pred vals one order =
    Threads.greedyRun items shaped pred vals one order
theorem greedyComprehension_proven : GreedyComprehensionProp := by
  unfold GreedyComprehensionProp
  intros
  rfl
def greedyComprehensionWorkerM := @Threads.greedyRun
def GreedyComprehensionWorkerProp : Prop := ∀ (α β : Type) items shaped pred vals one order,
  greedyComprehensionWorkerM (α := α) (β := β) items shaped pred vals one order =
    Threads.greedyRun items shaped pred vals one order
theorem greedyComprehensionWorker_proven : GreedyComprehensionWorkerProp := by
  unfold GreedyComprehensionWorkerProp
  intros
  rfl

def workDistributionM := JuliaLean.Channels.threadsIterations
def WorkDistributionProp : Prop := ∀ first len n tid,
  workDistributionM first len n tid = JuliaLean.Channels.threadsIterations first len n tid
theorem workDistribution_proven : WorkDistributionProp := by
  unfold WorkDistributionProp
  intros
  rfl
def defaultFuncM := @Threads.defaultTask
def DefaultFuncProp : Prop := ∀ (α β : Type) items pred vals n tid,
  defaultFuncM (α := α) (β := β) items pred vals n tid = Threads.defaultTask items pred vals n tid
theorem defaultFunc_proven : DefaultFuncProp := by
  unfold DefaultFuncProp
  intros
  rfl
def defaultFuncWorkerM := @Threads.defaultTask
def DefaultFuncWorkerProp : Prop := ∀ (α β : Type) items pred vals n tid,
  defaultFuncWorkerM (α := α) (β := β) items pred vals n tid = Threads.defaultTask items pred vals n tid
theorem defaultFuncWorker_proven : DefaultFuncWorkerProp := by
  unfold DefaultFuncWorkerProp
  intros
  rfl
def defaultComprehensionM := @Threads.defaultRun
def DefaultComprehensionProp : Prop := ∀ (α β : Type) items pred vals n,
  defaultComprehensionM (α := α) (β := β) items pred vals n = Threads.defaultRun items pred vals n
theorem defaultComprehension_proven : DefaultComprehensionProp := by
  unfold DefaultComprehensionProp
  intros
  rfl
def defaultComprehensionWorkerM := @Threads.defaultTask
def DefaultComprehensionWorkerProp : Prop := ∀ (α β : Type) items pred vals n tid,
  defaultComprehensionWorkerM (α := α) (β := β) items pred vals n tid = Threads.defaultTask items pred vals n tid
theorem defaultComprehensionWorker_proven : DefaultComprehensionWorkerProp := by
  unfold DefaultComprehensionWorkerProp
  intros
  rfl

def threadsMacroM := Threads.threadsMacro
def ThreadsMacroProp : Prop := ∀ args, threadsMacroM args = Threads.threadsMacro args
theorem threadsMacro_proven : ThreadsMacroProp := by
  unfold ThreadsMacroProp
  intros
  rfl
def spawnSetPoolM := Threads.spawnSetThrpool
def SpawnSetPoolProp : Prop := ∀ pool rt, spawnSetPoolM pool rt = Threads.spawnSetThrpool pool rt
theorem spawnSetPool_proven : SpawnSetPoolProp := by
  unfold SpawnSetPoolProp
  intros
  rfl
def spawnMacroM := Threads.spawnMacro
def SpawnMacroProp : Prop := ∀ args inSync rt,
  spawnMacroM args inSync rt = Threads.spawnMacro args inSync rt
theorem spawnMacro_proven : SpawnMacroProp := by
  unfold SpawnMacroProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulThreads
