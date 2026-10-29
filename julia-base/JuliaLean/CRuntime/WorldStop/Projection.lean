import JuliaLean.CRuntime.WorldStop.Source

namespace JuliaLean.CRuntime.WorldStop

def witnessRegs : Vector Reg 31 := #v[
  .ptls, .target, .tid, .state, .oldState, .collectorOldState, .handlerState, .resumeState,
  .running, .disabled, .count, .array, .newArray, .size, .newSize, .i,
  .slot, .current, .suspend, .waitstate, .result, .page, .loaded, .task,
  .gcCount, .gcArray, .resumeCount, .threaded, .ioTid, .bootstrap, .handleSignals]

def witnessRegIndex : Reg → Fin 31
  | .ptls => 0 | .target => 1 | .tid => 2 | .state => 3 | .oldState => 4
  | .collectorOldState => 5 | .handlerState => 6 | .resumeState => 7
  | .running => 8 | .disabled => 9 | .count => 10 | .array => 11
  | .newArray => 12 | .size => 13 | .newSize => 14 | .i => 15
  | .slot => 16 | .current => 17 | .suspend => 18 | .waitstate => 19
  | .result => 20 | .page => 21 | .loaded => 22 | .task => 23
  | .gcCount => 24 | .gcArray => 25 | .resumeCount => 26 | .threaded => 27
  | .ioTid => 28 | .bootstrap => 29 | .handleSignals => 30

@[simp] theorem witnessRegs_index (r : Reg) : witnessRegs[(witnessRegIndex r).val] = r := by
  cases r <;> rfl

def witnessLocations : Vector Loc 22 := #v[
  .gcRunning, .disableCounter, .nThreads, .allTLS,
  .gcState 1, .gcState 2, .gcState 3, .safepoint 2, .safepoint 3,
  .suspendCount 1, .suspendCount 2, .currentTask 2, .threadedRegion, .ioLoopTid,
  .tlsSlot 1 0, .tlsSlot 1 1, .tlsSlot 1 2, .pageCount 1, .pageCount 2, .pageCount 3,
  .gcNThreads, .gcAllTLS]

def witnessLocationIndex : Loc → Option (Fin 22)
  | .gcRunning => some 0 | .disableCounter => some 1 | .nThreads => some 2
  | .allTLS => some 3 | .gcState 1 => some 4 | .gcState 2 => some 5
  | .gcState 3 => some 6 | .safepoint 2 => some 7 | .safepoint 3 => some 8
  | .suspendCount 1 => some 9 | .suspendCount 2 => some 10
  | .currentTask 2 => some 11 | .threadedRegion => some 12 | .ioLoopTid => some 13
  | .tlsSlot 1 0 => some 14 | .tlsSlot 1 1 => some 15 | .tlsSlot 1 2 => some 16
  | .pageCount 1 => some 17 | .pageCount 2 => some 18 | .pageCount 3 => some 19
  | .gcNThreads => some 20 | .gcAllTLS => some 21
  | _ => none

def WitnessTracked (loc : Loc) : Prop := ∃ i, witnessLocationIndex loc = some i

instance (loc : Loc) : Decidable (WitnessTracked loc) :=
  decidable_of_iff (witnessLocationIndex loc).isSome (by
    cases h : witnessLocationIndex loc <;> simp [WitnessTracked, h])

theorem witnessLocationIndex_sound (loc : Loc) (i : Fin 22)
    (h : witnessLocationIndex loc = some i) : witnessLocations[i.val] = loc := by
  unfold witnessLocationIndex at h
  split at h <;> simp_all [witnessLocations]
  all_goals cases h <;> rfl

theorem witnessLocations_tracked (i : Fin 22) : WitnessTracked witnessLocations[i] := by
  have h : ∀ i : Fin 22, witnessLocationIndex witnessLocations[i] = some i := by decide
  exact ⟨i, h i⟩

structure WitnessThread where
  todo : List Command
  calls : List (List Command)
  regs : Vector Nat 31
  regSources : Vector (List Nat) 31
  controlSources : List Nat
  parked : Option (Nat × Nat)
  fault : Option Nat
  inHandler : Bool
  handlerDepth : Option Nat
  aborted : Bool
  criticalPermit : Bool

def projectThread (t : Thread) : WitnessThread :=
  { todo := t.todo, calls := t.calls
    regs := Vector.ofFn fun i => t.regs witnessRegs[i]
    regSources := Vector.ofFn fun i => t.regSources witnessRegs[i]
    controlSources := t.controlSources, parked := t.parked, fault := t.fault
    inHandler := t.inHandler, handlerDepth := t.handlerDepth
    aborted := t.aborted, criticalPermit := t.criticalPermit }

def reifyThread (t : WitnessThread) : Thread :=
  { todo := t.todo, calls := t.calls
    regs := fun r => t.regs[witnessRegIndex r]
    regSources := fun r => t.regSources[witnessRegIndex r]
    controlSources := t.controlSources, parked := t.parked, fault := t.fault
    inHandler := t.inHandler, handlerDepth := t.handlerDepth
    aborted := t.aborted, criticalPermit := t.criticalPermit }

@[simp] theorem reify_projectThread (t : Thread) : reifyThread (projectThread t) = t := by
  simp [projectThread, reifyThread]

/-- Runtime tables retain all locals and all candidate, OS, and source events. -/
structure WitnessProjection where
  memory : Vector Nat 22
  threads : Vector WitnessThread 3
  pageProtected : Vector Bool 4
  locks : Vector (Option (Fin 3)) 7
  conditions : Vector Nat 5
  latest : Vector (Option Nat) 22
  moClock : Vector Nat 22
  scClock : Nat
  candidate : Memory.Candidate Loc Nat
  os : List OSEvent
  sourceTrace : List (Nat × String × Nat)
  collectionActive : Bool
  criticalDuringGC : Bool

def project (s : Machine 3) : WitnessProjection :=
  { memory := Vector.ofFn fun i => s.memory witnessLocations[i]
    threads := Vector.ofFn fun i => projectThread (s.threads i)
    pageProtected := Vector.ofFn fun i => s.pageProtected i.val
    locks := Vector.ofFn fun i => s.locks i.val
    conditions := Vector.ofFn fun i => s.conditions i.val
    latest := Vector.ofFn fun i => s.latest witnessLocations[i]
    moClock := Vector.ofFn fun i => s.moClock witnessLocations[i]
    scClock := s.scClock, candidate := s.candidate, os := s.os
    sourceTrace := s.sourceTrace, collectionActive := s.collectionActive
    criticalDuringGC := s.criticalDuringGC }

def witnessLookup (v : Vector α 22) (outside : α) (loc : Loc) : α :=
  match witnessLocationIndex loc with
  | some i => v[i]
  | none => outside

/-- Untracked cells are mathematical extensions; supported steps never read them. -/
def reify (p : WitnessProjection) : Machine 3 :=
  { memory := witnessLookup p.memory 0
    threads := fun i => reifyThread p.threads[i]
    pageProtected := fun k => if h : k < 4 then p.pageProtected[k] else false
    locks := fun k => if h : k < 7 then p.locks[k] else none
    conditions := fun k => if h : k < 5 then p.conditions[k] else 0
    latest := witnessLookup p.latest none
    moClock := witnessLookup p.moClock 0
    scClock := p.scClock, candidate := p.candidate, os := p.os
    sourceTrace := p.sourceTrace, collectionActive := p.collectionActive
    criticalDuringGC := p.criticalDuringGC }

theorem witnessLookup_project (f : Loc → α) (outside : α) (loc : Loc)
    (h : WitnessTracked loc) :
    witnessLookup (Vector.ofFn fun i => f witnessLocations[i]) outside loc = f loc := by
  obtain ⟨i, hi⟩ := h
  simp [witnessLookup, hi, witnessLocationIndex_sound loc i hi]

structure WitnessAgreement (s t : Machine 3) : Prop where
  memory : ∀ loc, WitnessTracked loc → s.memory loc = t.memory loc
  threads : s.threads = t.threads
  pageProtected : ∀ k, k < 4 → s.pageProtected k = t.pageProtected k
  locks : ∀ k, k < 7 → s.locks k = t.locks k
  conditions : ∀ k, k < 5 → s.conditions k = t.conditions k
  latest : ∀ loc, WitnessTracked loc → s.latest loc = t.latest loc
  moClock : ∀ loc, WitnessTracked loc → s.moClock loc = t.moClock loc
  scClock : s.scClock = t.scClock
  candidate : s.candidate = t.candidate
  os : s.os = t.os
  sourceTrace : s.sourceTrace = t.sourceTrace
  collectionActive : s.collectionActive = t.collectionActive
  criticalDuringGC : s.criticalDuringGC = t.criticalDuringGC

theorem reify_project_agreement (s : Machine 3) : WitnessAgreement s (reify (project s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro loc h
    exact (witnessLookup_project s.memory 0 loc h).symm
  · funext i
    simp [reify, project]
  · intro k h
    simp [reify, project, h]
  · intro k h
    simp [reify, project, h]
  · intro k h
    simp [reify, project, h]
  · intro loc h
    exact (witnessLookup_project s.latest none loc h).symm
  · intro loc h
    exact (witnessLookup_project s.moClock 0 loc h).symm

theorem WitnessAgreement.project_eq {s t : Machine 3} (h : WitnessAgreement s t) :
    project s = project t := by
  have hm : (fun i : Fin 22 => s.memory witnessLocations[i]) =
      (fun i : Fin 22 => t.memory witnessLocations[i]) := by
    funext i
    exact h.memory _ (witnessLocations_tracked i)
  have hp : (fun i : Fin 4 => s.pageProtected i.val) =
      (fun i : Fin 4 => t.pageProtected i.val) := by
    funext i
    exact h.pageProtected _ i.isLt
  have hl : (fun i : Fin 7 => s.locks i.val) = (fun i : Fin 7 => t.locks i.val) := by
    funext i
    exact h.locks _ i.isLt
  have hc : (fun i : Fin 5 => s.conditions i.val) =
      (fun i : Fin 5 => t.conditions i.val) := by
    funext i
    exact h.conditions _ i.isLt
  have hr : (fun i : Fin 22 => s.latest witnessLocations[i]) =
      (fun i : Fin 22 => t.latest witnessLocations[i]) := by
    funext i
    exact h.latest _ (witnessLocations_tracked i)
  have ho : (fun i : Fin 22 => s.moClock witnessLocations[i]) =
      (fun i : Fin 22 => t.moClock witnessLocations[i]) := by
    funext i
    exact h.moClock _ (witnessLocations_tracked i)
  simp only [project, hm, hp, hl, hc, hr, ho, h.threads, h.scClock, h.candidate,
    h.os, h.sourceTrace, h.collectionActive, h.criticalDuringGC]

end JuliaLean.CRuntime.WorldStop
