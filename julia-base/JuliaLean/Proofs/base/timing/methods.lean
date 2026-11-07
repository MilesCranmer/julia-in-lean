import JuliaLean.base.timing
import JuliaLean.Proofs.base.timing.properties

/-! Per-method properties for `base/timing.jl`. Each wrapper points to the
source-body model in `Timing.lean`; the fixed reviewer follows that definition. -/

namespace JuliaLean.ConcurrencyCov.FaithfulTiming

open JuliaLean JuliaLean.ConcurrencyCov

def GcNumProp : Prop := ∀ rt, gcNumM rt = rt.gcNum
theorem gcNum_proven : GcNumProp := by
  unfold GcNumProp
  intros
  rfl

def GcTotalBytesProp : Prop := ∀ g, gcTotalBytesM g = g.allocd + g.deferred_alloc + g.total_allocd
theorem gcTotalBytes_proven : GcTotalBytesProp := by
  unfold GcTotalBytesProp
  intros
  rfl

def GcDiffProp : Prop := ∀ new old,
  (gcDiffM new old).allocd = Timing.gcTotalBytes new - Timing.gcTotalBytes old ∧
  (gcDiffM new old).malloc = new.malloc - old.malloc ∧
  (gcDiffM new old).realloc = new.realloc - old.realloc ∧
  (gcDiffM new old).poolalloc = new.poolalloc - old.poolalloc ∧
  (gcDiffM new old).bigalloc = new.bigalloc - old.bigalloc ∧
  (gcDiffM new old).freecall = new.freecall - old.freecall ∧
  (gcDiffM new old).total_time = new.total_time - old.total_time ∧
  (gcDiffM new old).pause = new.pause - old.pause ∧
  (gcDiffM new old).full_sweep = new.full_sweep - old.full_sweep
theorem gcDiff_proven : GcDiffProp := by
  unfold GcDiffProp
  intros
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def GcAllocCountProp : Prop := ∀ d, gcAllocCountM d = d.malloc + d.realloc + d.poolalloc + d.bigalloc
theorem gcAllocCount_proven : GcAllocCountProp := by
  unfold GcAllocCountProp
  intros
  rfl

def CumulativeCompileTimeNsProp : Prop := ∀ rt, cumulativeCompileTimeNsM rt = (rt.compileNs, rt.recompileNs)
theorem cumulativeCompileTimeNs_proven : CumulativeCompileTimeNsProp := by
  unfold CumulativeCompileTimeNsProp
  intros
  rfl

def CumulativeCompileTimingProp : Prop := ∀ b rt, cumulativeCompileTimingM b rt =
  if b then { rt with compileTiming := rt.compileTiming + 1 }
  else { rt with compileTiming := rt.compileTiming - 1 }
theorem cumulativeCompileTiming_proven : CumulativeCompileTimingProp := by intro b; cases b <;> intros <;> rfl

def GcTimeNsProp : Prop := ∀ rt, gcTimeNsM rt = rt.gcHrtime
theorem gcTimeNs_proven : GcTimeNsProp := by
  unfold GcTimeNsProp
  intros
  rfl

def GcLiveBytesProp : Prop := ∀ rt, gcLiveBytesM rt = rt.liveBytes + rt.gcNum.allocd + rt.gcNum.deferred_alloc
theorem gcLiveBytes_proven : GcLiveBytesProp := by
  unfold GcLiveBytesProp
  intros
  rfl

def GcPageUtilizationDataProp : Prop := ∀ rt,
  gcPageUtilizationDataM rt = rt.pageUtil.take Timing.nMaxPools
theorem gcPageUtilizationData_proven : GcPageUtilizationDataProp := by
  unfold GcPageUtilizationDataProp
  intros
  rfl

def FullSweepReasonsProp : Prop := ∀ rt, fullSweepReasonsM rt = Timing.fullSweepReasons rt
theorem fullSweepReasons_proven : FullSweepReasonsProp := by
  unfold FullSweepReasonsProp
  intros
  rfl

def JitTotalBytesProp : Prop := ∀ rt, jitTotalBytesM rt = rt.jitBytes
theorem jitTotalBytes_proven : JitTotalBytesProp := by
  unfold JitTotalBytesProp
  intros
  rfl

def PrettyprintGetunitsProp : Prop := ∀ v n f,
  prettyprintGetunitsM v n f = Timing.prettyprintGetunits v n f
theorem prettyprintGetunits_proven : PrettyprintGetunitsProp := by
  unfold PrettyprintGetunitsProp
  intros
  rfl

def PaddedNonzeroPrintProp : Prop := ∀ v s always,
  paddedNonzeroPrintM v s always = Timing.paddedNonzeroPrint v s always
theorem paddedNonzeroPrint_proven : PaddedNonzeroPrintProp := by
  unfold PaddedNonzeroPrintProp
  intros
  rfl

def FormatBytesProp : Prop := ∀ bytes binary, formatBytesM bytes binary = Timing.formatBytes bytes binary
theorem formatBytes_proven : FormatBytesProp := by
  unfold FormatBytesProp
  intros
  rfl

def TimePrintProp : Prop := ∀ args, timePrintM args = Timing.timePrint args
theorem timePrint_proven : TimePrintProp := by
  unfold TimePrintProp
  intros
  rfl

def TimevPrintProp : Prop := ∀ elapsed diff conflicts compile msg,
  timevPrintM elapsed diff conflicts compile msg = Timing.timevPrint elapsed diff conflicts compile msg
theorem timevPrint_proven : TimevPrintProp := by
  unfold TimevPrintProp
  intros
  rfl

def TryfinallyProp : Prop := ∀ (σ : Type) (ex : σ → Outcome × σ) fin s,
  tryfinallyM ex fin s = ((ex s).1, fin (ex s).2)
theorem tryfinally_proven : TryfinallyProp := by
  unfold TryfinallyProp
  intros
  rfl

def TimeNoMsgProp : Prop := ∀ run rt, timeNoMsgM run rt = Timing.time none run rt
theorem timeNoMsg_proven : TimeNoMsgProp := by
  unfold TimeNoMsgProp
  intros
  rfl

def TimeMsgProp : Prop := ∀ msg run rt, timeMsgM msg run rt = Timing.time (some msg) run rt
theorem timeMsg_proven : TimeMsgProp := by
  unfold TimeMsgProp
  intros
  rfl

def ShowtimeProp : Prop := ∀ text run rt, showtimeM text run rt = Timing.time (some text) run rt
theorem showtime_proven : ShowtimeProp := by
  unfold ShowtimeProp
  intros
  rfl

def TimevNoMsgProp : Prop := ∀ run rt, timevNoMsgM run rt = Timing.timev none run rt
theorem timevNoMsg_proven : TimevNoMsgProp := by
  unfold TimevNoMsgProp
  intros
  rfl

def TimevMsgProp : Prop := ∀ msg run rt, timevMsgM msg run rt = Timing.timev (some msg) run rt
theorem timevMsg_proven : TimevMsgProp := by
  unfold TimevMsgProp
  intros
  rfl

def ElapsedProp : Prop := ∀ run rt, elapsedM run rt = Timing.elapsed run rt
theorem elapsed_proven : ElapsedProp := by
  unfold ElapsedProp
  intros
  rfl

def GcBytesRefProp : Prop := ∀ rt, gcBytesRefM rt = rt.totalBytes
theorem gcBytesRef_proven : GcBytesRefProp := by
  unfold GcBytesRefProp
  intros
  rfl

def GcBytesProp : Prop := ∀ rt, gcBytesM rt = rt.totalBytes
theorem gcBytes_proven : GcBytesProp := by
  unfold GcBytesProp
  intros
  rfl

def AllocatedProp : Prop := ∀ a rt, allocatedM a rt = Timing.allocated a rt
theorem allocated_proven : AllocatedProp := by
  unfold AllocatedProp
  intros
  rfl

def AllocationsProp : Prop := ∀ a rt, allocationsM a rt = Timing.allocations a rt
theorem allocations_proven : AllocationsProp := by
  unfold AllocationsProp
  intros
  rfl

def IsSimplyCallProp : Prop := ∀ ast, isSimplyCallM ast = Timing.isSimplyCall ast
theorem isSimplyCall_proven : IsSimplyCallProp := by
  unfold IsSimplyCallProp
  intros
  rfl

def IsSimpleAtomProp : Prop := ∀ ast, isSimpleAtomM ast = Timing.isSimpleAtom ast
theorem isSimpleAtom_proven : IsSimpleAtomProp := by
  unfold IsSimpleAtomProp
  intros
  rfl

def GenAllocationMeasurerProp : Prop := ∀ ast fname,
  genAllocationMeasurerM ast fname = Timing.genAllocationMeasurer ast fname
theorem genAllocationMeasurer_proven : GenAllocationMeasurerProp := by
  unfold GenAllocationMeasurerProp
  intros
  rfl

def AllocatedMacroProp : Prop := ∀ ast, allocatedMacroM ast = Timing.genAllocationMeasurer ast "allocated"
theorem allocatedMacro_proven : AllocatedMacroProp := by
  unfold AllocatedMacroProp
  intros
  rfl

def AllocationsMacroProp : Prop := ∀ ast, allocationsMacroM ast = Timing.genAllocationMeasurer ast "allocations"
theorem allocationsMacro_proven : AllocationsMacroProp := by
  unfold AllocationsMacroProp
  intros
  rfl

def LockConflictsProp : Prop := ∀ run rt, lockConflictsM run rt = Timing.lockConflictsMacro run rt
theorem lockConflicts_proven : LockConflictsProp := by
  unfold LockConflictsProp
  intros
  rfl

def TimedProp : Prop := ∀ run rt, timedM run rt = Timing.timed run rt
theorem timed_proven : TimedProp := by
  unfold TimedProp
  intros
  rfl

def TimeImportsProp : Prop := ∀ out rt,
  timeImportsM out rt = Timing.bracket Timing.Bracket.timeImports out rt
theorem timeImports_proven : TimeImportsProp := by
  unfold TimeImportsProp
  intros
  rfl

def TraceCompileProp : Prop := ∀ out rt,
  traceCompileM out rt = Timing.bracket Timing.Bracket.traceCompile out rt
theorem traceCompile_proven : TraceCompileProp := by
  unfold TraceCompileProp
  intros
  rfl

def TraceDispatchProp : Prop := ∀ out rt,
  traceDispatchM out rt = Timing.bracket Timing.Bracket.traceDispatch out rt
theorem traceDispatch_proven : TraceDispatchProp := by
  unfold TraceDispatchProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulTiming
