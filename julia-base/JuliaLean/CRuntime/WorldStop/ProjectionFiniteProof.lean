import JuliaLean.CRuntime.WorldStop.ProjectionFinite

namespace JuliaLean.CRuntime.WorldStop

private theorem witnessLocationIndex_witnessLocations :
    ∀ i : Fin 22, witnessLocationIndex witnessLocations[i] = some i := by decide

private theorem locationVector_roundtrip (values : Vector α 22) (outside : α) :
    Vector.ofFn (fun i => witnessLookup values outside witnessLocations[i]) = values := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn, witnessLookup]
  rw [witnessLocationIndex_witnessLocations ⟨i, hi⟩]
  rfl

private theorem natVector_roundtrip (values : Vector α n) (outside : α) :
    Vector.ofFn (fun i => if h : i.val < n then values[i.val]'h else outside) = values := by
  apply Vector.ext
  intro i
  intro hi
  simp

private theorem threadVector_roundtrip (threads : Vector WitnessThread 3) :
    Vector.ofFn (fun i => projectThread (reifyThread threads[i])) = threads := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn]
  exact project_reifyThread (threads[i]'hi)

private theorem finiteVectorSet_get (values : Vector α n) (index current : Fin n)
    (value : α) :
    (finiteVectorSet values index value)[current.val]'current.isLt =
      if current = index then value else values[current.val]'current.isLt := by
  unfold finiteVectorSet
  simp only [Vector.getElem_ofFn]
  rfl

private theorem natVector_replace (values : Vector α n) (outside : α)
    (index : Nat) (value : α) :
    Vector.ofFn (fun i =>
      replace (fun k => if h : k < n then values[k]'h else outside) index value i.val) =
      finiteNatSet values index value := by
  by_cases bounded : index < n
  · simp only [finiteNatSet, bounded]
    apply Vector.ext
    intro i
    intro hi
    by_cases equal : i = index
    · subst i
      simp [replace, finiteVectorSet]
    · have finNe : (⟨i, hi⟩ : Fin n) ≠ ⟨index, bounded⟩ := by
        intro h
        exact equal (congrArg Fin.val h)
      simp [replace, finiteVectorSet, equal, finNe]
  · simp only [finiteNatSet, bounded]
    apply Vector.ext
    intro i
    intro hi
    have unequal : i ≠ index := by
      intro equal
      exact bounded (equal ▸ hi)
    simp [replace, unequal]

private theorem locationVector_replace (values : Vector α 22) (outside : α)
    (loc : Loc) (value : α) :
    Vector.ofFn (fun i =>
      replace (witnessLookup values outside) loc value witnessLocations[i]) =
      finiteLocationSet values loc value := by
  cases tracked : witnessLocationIndex loc with
  | none =>
      simp only [finiteLocationSet, tracked]
      apply Vector.ext
      intro i
      intro hi
      simp only [Vector.getElem_ofFn]
      have unequal : witnessLocations[i]'hi ≠ loc := by
        intro equal
        have index := congrArg witnessLocationIndex equal
        have currentIndex : witnessLocationIndex (witnessLocations[i]'hi) =
            some ⟨i, hi⟩ := witnessLocationIndex_witnessLocations ⟨i, hi⟩
        rw [currentIndex, tracked] at index
        cases index
      change (if witnessLocations[i]'hi = loc then value else
        witnessLookup values outside (witnessLocations[i]'hi)) = values[i]'hi
      rw [if_neg unequal]
      unfold witnessLookup
      have currentIndex : witnessLocationIndex (witnessLocations[i]'hi) =
          some ⟨i, hi⟩ := witnessLocationIndex_witnessLocations ⟨i, hi⟩
      rw [currentIndex]
      rfl
  | some index =>
      simp only [finiteLocationSet, tracked]
      apply Vector.ext
      intro i
      intro hi
      simp only [Vector.getElem_ofFn]
      have same : witnessLocations[i]'hi = loc ↔ (⟨i, hi⟩ : Fin 22) = index := by
        constructor
        · intro equal
          have currentIndex := congrArg witnessLocationIndex equal
          have knownIndex : witnessLocationIndex (witnessLocations[i]'hi) =
              some ⟨i, hi⟩ := witnessLocationIndex_witnessLocations ⟨i, hi⟩
          rw [knownIndex, tracked] at currentIndex
          exact Option.some.inj currentIndex
        · intro equal
          exact (congrArg (fun k : Fin 22 => witnessLocations[k]) equal).trans
            (witnessLocationIndex_sound loc index tracked)
      rw [finiteVectorSet_get values index ⟨i, hi⟩ value]
      by_cases equalLoc : witnessLocations[i]'hi = loc
      · have equalFin := same.mp equalLoc
        subst index
        have exactLoc := witnessLocationIndex_sound loc ⟨i, hi⟩ tracked
        simp [replace, exactLoc]
      · have unequalFin : (⟨i, hi⟩ : Fin 22) ≠ index := fun equal =>
          equalLoc (same.mpr equal)
        unfold replace
        split
        · rename_i equal
          have indices := congrArg witnessLocationIndex equal
          rw [witnessLocationIndex_witnessLocations ⟨i, hi⟩, tracked] at indices
          exact (unequalFin (Option.some.inj indices)).elim
        · rename_i unequal
          unfold witnessLookup
          rw [witnessLocationIndex_witnessLocations ⟨i, hi⟩]
          rfl

private theorem witnessRegIndex_witnessRegs :
    ∀ i : Fin 31, witnessRegIndex witnessRegs[i] = i := by decide

private theorem witnessRegVector_roundtrip (values : Vector α 31) :
    Vector.ofFn (fun i => values[witnessRegIndex witnessRegs[i]]) = values := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn]
  exact congrArg (fun index : Fin 31 => values[index])
    (witnessRegIndex_witnessRegs ⟨i, hi⟩)

private theorem witnessThread_eq (a b : WitnessThread)
    (todo : a.todo = b.todo) (calls : a.calls = b.calls)
    (regs : a.regs = b.regs) (regSources : a.regSources = b.regSources)
    (controlSources : a.controlSources = b.controlSources)
    (parked : a.parked = b.parked) (fault : a.fault = b.fault)
    (inHandler : a.inHandler = b.inHandler)
    (handlerDepth : a.handlerDepth = b.handlerDepth)
    (aborted : a.aborted = b.aborted)
    (criticalPermit : a.criticalPermit = b.criticalPermit) : a = b := by
  cases a
  cases b
  simp_all

private theorem regVector_replace (values : Vector α 31) (dst : Reg) (value : α) :
    Vector.ofFn (fun i =>
      replace (fun reg => values[witnessRegIndex reg]) dst value witnessRegs[i]) =
      finiteVectorSet values (witnessRegIndex dst) value := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn]
  have same : witnessRegs[i]'hi = dst ↔
      (⟨i, hi⟩ : Fin 31) = witnessRegIndex dst := by
    constructor
    · intro equal
      exact (witnessRegIndex_witnessRegs ⟨i, hi⟩).symm.trans
        (congrArg witnessRegIndex equal)
    · intro equal
      exact (congrArg (fun k : Fin 31 => witnessRegs[k]) equal).trans
        (witnessRegs_index dst)
  rw [finiteVectorSet_get values (witnessRegIndex dst) ⟨i, hi⟩ value]
  by_cases equalReg : witnessRegs[i]'hi = dst
  · have equalFin := same.mp equalReg
    simp_all [replace]
  · have unequalFin : (⟨i, hi⟩ : Fin 31) ≠ witnessRegIndex dst := fun equal =>
      equalReg (same.mpr equal)
    unfold replace
    split
    · rename_i equal
      exact (unequalFin ((witnessRegIndex_witnessRegs ⟨i, hi⟩).symm.trans
        (congrArg witnessRegIndex equal))).elim
    · rename_i unequal
      let idx : Fin 31 := ⟨i, hi⟩
      have finNat : Vector.get values idx = values[i]'hi := by
        change values[idx.val]'idx.isLt = values[i]'hi
        rfl
      calc
        (fun reg => values[witnessRegIndex reg]) (Vector.get witnessRegs idx) =
            Vector.get values idx :=
          congrArg (Vector.get values) (witnessRegIndex_witnessRegs idx)
        _ = values[i]'hi := finNat

theorem project_reify (p : WitnessProjection) : project (reify p) = p := by
  cases p
  simp only [project, reify]
  rw [locationVector_roundtrip, threadVector_roundtrip,
    natVector_roundtrip, natVector_roundtrip, natVector_roundtrip,
    locationVector_roundtrip, locationVector_roundtrip]

private theorem projectThreadVector_replace (threads : Vector WitnessThread 3)
    (actor : Fin 3) (thd : WitnessThread) :
    Vector.ofFn (fun i =>
      projectThread
        (replace (fun j : Fin 3 => reifyThread threads[j]) actor (reifyThread thd) i)) =
      finiteVectorSet threads actor thd := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn, replace, finiteVectorSet]
  by_cases equal : (⟨i, hi⟩ : Fin 3) = actor
  · simp [equal, project_reifyThread]
  · simp [equal, project_reifyThread]

private theorem projectThreadVector_replace_machine (threads : Fin 3 → Thread)
    (actor : Fin 3) (thd : Thread) :
    Vector.ofFn (fun i => projectThread (replace threads actor thd i)) =
      finiteVectorSet (Vector.ofFn fun i => projectThread (threads i)) actor
        (projectThread thd) := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn, replace, finiteVectorSet]
  by_cases equal : (⟨i, hi⟩ : Fin 3) = actor
  · simp [equal]
  · simp [equal]

theorem project_setThread (s : Machine 3) (actor : Fin 3) (thd : Thread) :
    project (setThread s actor thd) =
      finiteSetThread (project s) actor (projectThread thd) := by
  unfold setThread finiteSetThread project
  rw [projectThreadVector_replace_machine]

theorem project_next (s : Machine 3) (actor : Fin 3) (thd : Thread)
    (tail : List Command) :
    project (next s actor thd tail) =
      finiteNext (project s) actor (projectThread thd) tail := by
  unfold next finiteNext
  rw [project_setThread]
  rfl

theorem project_next_reify_todo (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) (sourceTodo tail : List Command) :
    project (next (reify p) actor { reifyThread thd with todo := sourceTodo } tail) =
      finiteNext p actor thd tail := by
  rw [project_next, project_reify]
  have threadProjection :
      projectThread { reifyThread thd with todo := sourceTodo } =
        { thd with todo := sourceTodo } := by
    simpa [reifyThread] using project_reifyThread { thd with todo := sourceTodo }
  rw [threadProjection]
  unfold finiteNext
  rfl

theorem project_next_trace_reify_todo (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) (sourceTodo tail : List Command) (file : String) (line : Nat) :
    project (next { reify p with
        sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)] }
      actor { reifyThread thd with todo := sourceTodo } tail) =
      finiteNext { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor thd tail := by
  let logged := { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
  change project (next (reify logged) actor
    { reifyThread thd with todo := sourceTodo } tail) = finiteNext logged actor thd tail
  exact project_next_reify_todo logged actor thd sourceTodo tail

theorem project_setThread_reify (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) :
    project (setThread (reify p) actor (reifyThread thd)) =
      finiteSetThread p actor thd := by
  cases p
  simp only [setThread, finiteSetThread, project, reify]
  rw [locationVector_roundtrip, projectThreadVector_replace,
    natVector_roundtrip, natVector_roundtrip, natVector_roundtrip,
    locationVector_roundtrip, locationVector_roundtrip]

theorem project_trace_reify (p : WitnessProjection) (actor : Fin 3)
    (file : String) (line : Nat) :
    project { reify p with
      sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] } =
      { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] } := by
  change project (reify { p with
    sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }) = _
  exact project_reify _

theorem project_logged_reify (p : WitnessProjection) (actor : Fin 3)
    (file : String) (line : Nat) (op : Op) :
    project { reify p with
      sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
      criticalDuringGC := p.criticalDuringGC ||
        (p.collectionActive && sourceTouchesRoots file line op) } =
      { p with
        sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
        criticalDuringGC := p.criticalDuringGC ||
          (p.collectionActive && sourceTouchesRoots file line op) } := by
  change project (reify { p with
    sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
    criticalDuringGC := p.criticalDuringGC ||
      (p.collectionActive && sourceTouchesRoots file line op) }) = _
  exact project_reify _

theorem readChoice_reify (p : WitnessProjection) (loc : Loc) (choice : Choice) :
    readChoice (reify p) loc choice = finiteReadChoice p loc choice := by
  cases choice.read <;> rfl

theorem project_setReg_reifyThread (thd : WitnessThread) (dst : Reg)
    (value : Nat) (sources : List Nat := []) :
    projectThread (setReg (reifyThread thd) dst value sources) =
      finiteSetReg thd dst value sources := by
  unfold setReg finiteSetReg
  cases width : localWidth dst with
  | none =>
      simp only [width]
      unfold projectThread reifyThread
      rw [regVector_replace, regVector_replace]
  | some bits =>
      simp only [width]
      unfold projectThread reifyThread
      rw [regVector_replace, regVector_replace]

private theorem projectThread_todo (thd : WitnessThread) (todo : List Command) :
    projectThread { reifyThread thd with todo := todo } = { thd with todo := todo } := by
  simpa [reifyThread] using project_reifyThread { thd with todo := todo }

private theorem projectThread_todo_criticalFalse (thd : WitnessThread)
    (todo : List Command) :
    projectThread { reifyThread thd with todo := todo, criticalPermit := false } =
      { thd with todo := todo, criticalPermit := false } := by
  simpa [reifyThread] using
    project_reifyThread { thd with todo := todo, criticalPermit := false }

private theorem projectThread_todo_aborted (thd : WitnessThread) (todo : List Command) :
    projectThread { reifyThread thd with todo := todo, aborted := true } =
      { thd with todo := todo, aborted := true } := by
  simpa [reifyThread] using project_reifyThread { thd with todo := todo, aborted := true }

private theorem projectThread_todo_parked (thd : WitnessThread) (todo : List Command)
    (parked : Option (Nat × Nat)) :
    projectThread { reifyThread thd with todo := todo, parked := parked } =
      { thd with todo := todo, parked := parked } := by
  simpa [reifyThread] using project_reifyThread { thd with todo := todo, parked := parked }

private theorem witnessThread_setTodo_eq (thd : WitnessThread) (todo : List Command)
    (equal : thd.todo = todo) : { thd with todo := todo } = thd := by
  cases thd
  simp_all

private theorem witnessThread_setTodo_aborted_eq (thd : WitnessThread)
    (todo : List Command) (equal : thd.todo = todo) :
    { thd with todo := todo, aborted := true } = { thd with aborted := true } := by
  cases thd
  simp_all

private theorem projectThread_criticalPermit (source : Thread) (finite : WitnessThread)
    (equal : projectThread source = finite) (permit : Bool) :
    projectThread { source with criticalPermit := permit } =
      { finite with criticalPermit := permit } := by
  cases equal
  rfl

private theorem projectThread_fault (source : Thread) (finite : WitnessThread)
    (equal : projectThread source = finite) (fault : Option Nat) :
    projectThread { source with fault := fault } = { finite with fault := fault } := by
  cases equal
  rfl

private theorem project_emit_noWrite_reify (p : WitnessProjection) (actor : Fin 3)
    (action : Memory.Action Loc Nat) (rf : Option Nat) (deps : List Nat)
    (writeNone : action.writeValue = none) :
    project (emit (reify p) actor action rf deps) =
      finiteEmit p actor action rf deps := by
  let event : Memory.Event Loc Nat :=
    { thread := actor.val, action := action, readFrom := rf, mo := 0
      sc := p.scClock, dependsOn := p.threads[actor].controlSources ++ deps }
  let out := { p with
    candidate := p.candidate.append event
    scClock := p.scClock + if action.isSC then 1 else 0 }
  have sourceEq : emit (reify p) actor action rf deps = reify out := by
    unfold emit
    simp [writeNone, event, out, reify, reifyThread]
  have finiteEq : finiteEmit p actor action rf deps = out := by
    unfold finiteEmit
    simp [writeNone, event, out]
  rw [sourceEq, finiteEq, project_reify]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem project_emit_reify (p : WitnessProjection) (actor : Fin 3)
    (action : Memory.Action Loc Nat) (rf : Option Nat := none)
    (deps : List Nat := []) :
    project (emit (reify p) actor action rf deps) =
      finiteEmit p actor action rf deps := by
  cases action with
  | init loc value =>
    simp [emit, finiteEmit, project, reify, reifyThread,
      finiteMOClock, finiteLocationGet, witnessLookup,
      natVector_roundtrip, Memory.Action.location, Memory.Action.writeValue,
      Memory.Action.isPlain, Memory.Action.isSC]
    exact ⟨locationVector_replace _ _ _ _, threadVector_roundtrip _,
      locationVector_replace _ _ _ _, locationVector_replace _ _ _ _, rfl⟩
  | load loc order observed =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl
  | store loc order value =>
    simp [emit, finiteEmit, project, reify, reifyThread,
      finiteMOClock, finiteLocationGet, witnessLookup,
      natVector_roundtrip, Memory.Action.location, Memory.Action.writeValue,
      Memory.Action.isPlain, Memory.Action.isSC]
    exact ⟨locationVector_replace _ _ _ _, threadVector_roundtrip _,
      locationVector_replace _ _ _ _, locationVector_replace _ _ _ _, rfl⟩
  | rmw loc order before after =>
    simp [emit, finiteEmit, project, reify, reifyThread,
      finiteMOClock, finiteLocationGet, witnessLookup,
      natVector_roundtrip, Memory.Action.location, Memory.Action.writeValue,
      Memory.Action.isPlain, Memory.Action.isSC]
    exact ⟨locationVector_replace _ _ _ _, threadVector_roundtrip _,
      locationVector_replace _ _ _ _, locationVector_replace _ _ _ _, rfl⟩
  | cas loc successOrder failureOrder expected desired observed =>
      by_cases success : observed = expected
      · simp [emit, finiteEmit, project, reify, reifyThread, success,
          finiteMOClock, finiteLocationGet, witnessLookup,
          natVector_roundtrip, Memory.Action.location, Memory.Action.writeValue,
          Memory.Action.isPlain, Memory.Action.isSC]
        exact ⟨locationVector_replace _ _ _ _, threadVector_roundtrip _,
          locationVector_replace _ _ _ _, locationVector_replace _ _ _ _, rfl⟩
      · apply project_emit_noWrite_reify p actor _ rf deps
        simp [Memory.Action.writeValue, success]
  | fence order =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl
  | signalFence order =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl
  | plainLoad loc observed =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl
  | plainStore loc value =>
    simp [emit, finiteEmit, project, reify, reifyThread,
      witnessLookup, natVector_roundtrip, Memory.Action.location,
      Memory.Action.writeValue, Memory.Action.isPlain, Memory.Action.isSC]
    exact ⟨locationVector_replace _ _ _ _, threadVector_roundtrip _,
      locationVector_replace _ _ _ _, locationVector_roundtrip _ _⟩
  | lock mutex =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl
  | unlock mutex =>
      exact project_emit_noWrite_reify p actor _ rf deps rfl

theorem project_emit_logged_reify (p : WitnessProjection) (actor : Fin 3)
    (file : String) (line : Nat) (op : Op) (action : Memory.Action Loc Nat)
    (rf : Option Nat) (deps : List Nat) :
    project (emit { reify p with
        sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)]
        criticalDuringGC := (reify p).criticalDuringGC ||
          ((reify p).collectionActive && sourceTouchesRoots file line op) }
      actor action rf deps) =
      finiteEmit { p with
        sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
        criticalDuringGC := p.criticalDuringGC ||
          (p.collectionActive && sourceTouchesRoots file line op) }
        actor action rf deps := by
  let logged := { p with
    sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
    criticalDuringGC := p.criticalDuringGC ||
      (p.collectionActive && sourceTouchesRoots file line op) }
  change project (emit (reify logged) actor action rf deps) =
    finiteEmit logged actor action rf deps
  exact project_emit_reify logged actor action rf deps

theorem project_returnThread_reify (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) :
    project (returnThread (reify p) actor (reifyThread thd)) =
      finiteReturnThread p actor thd := by
  unfold returnThread finiteReturnThread
  cases callsEq : thd.calls with
  | nil =>
      let nextThread := { thd with todo := [] }
      simpa only [callsEq, reifyThread, nextThread] using
        project_setThread_reify p actor nextThread
  | cons todo calls =>
      simp only [reifyThread, callsEq]
      let handlerReturn := thd.inHandler && thd.handlerDepth == some calls.length
      let nextThread := { thd with
        todo := todo
        calls := calls
        inHandler := if handlerReturn then false else thd.inHandler
        handlerDepth := if handlerReturn then none else thd.handlerDepth }
      change { project (setThread (reify p) actor (reifyThread nextThread)) with
          os := if handlerReturn then p.os ++ [OSEvent.returnFromHandler actor.val] else p.os } =
        { finiteSetThread p actor nextThread with
          os := if handlerReturn then p.os ++ [OSEvent.returnFromHandler actor.val] else p.os }
      rw [project_setThread_reify]

theorem project_returnThread_reify_todo (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) (todo : List Command) :
    project (returnThread (reify p) actor { reifyThread thd with todo := todo }) =
      finiteReturnThread p actor thd := by
  have base := project_returnThread_reify p actor { thd with todo := todo }
  cases callsEq : thd.calls <;>
    simpa [finiteReturnThread, reifyThread, callsEq] using base

theorem project_returnThread_trace_reify_todo (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) (sourceTodo : List Command) (file : String) (line : Nat) :
    project (returnThread { reify p with
        sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)] }
      actor { reifyThread thd with todo := sourceTodo }) =
      finiteReturnThread { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor thd := by
  let logged := { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
  change project (returnThread (reify logged) actor
    { reifyThread thd with todo := sourceTodo }) = finiteReturnThread logged actor thd
  exact project_returnThread_reify_todo logged actor thd sourceTodo

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem project_step_reify (p : WitnessProjection) (actor : Fin 3)
    (choice : Choice) :
    project (step (reify p) actor choice) = finiteStep p actor choice := by
  unfold step finiteStep
  have sourceThread : (reify p).threads actor = reifyThread p.threads[actor] := rfl
  rw [sourceThread]
  simp only [reifyThread]
  split
  · rename_i blocked
    simpa only [blocked, if_true] using project_reify p
  · rename_i ready
    simp only [ready, Bool.false_eq_true, if_false]
    cases todoEq : p.threads[actor].todo with
    | nil =>
        simp only [todoEq]
        exact project_returnThread_reify_todo p actor p.threads[actor] []
    | cons command tail =>
        cases command with
        | ret file line =>
            simp only [todoEq]
            exact project_returnThread_trace_reify_todo p actor p.threads[actor]
              (.ret file line :: tail) file line
        | call file line proc =>
            let logged := { p with
              sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
            let nextThread := { p.threads[actor] with
              todo := program proc, calls := tail :: p.threads[actor].calls }
            simpa [logged, nextThread, todoEq, reify, reifyThread] using
              project_setThread_reify logged actor nextThread
        | branch file line test yes no =>
            simp only [todoEq]
            let nextThread := { p.threads[actor] with
              controlSources := p.threads[actor].controlSources ++
                test.sources (finiteRegSources p.threads[actor]) }
            exact project_next_trace_reify_todo p actor nextThread
              (.branch file line test yes no :: tail)
              ((if test.eval (finiteRegs p.threads[actor]) ≠ 0 then yes else no) ++ tail)
              file line
        | whileDo file line prelude test body =>
            simp only [todoEq]
            exact project_next_reify_todo p actor p.threads[actor]
              (.whileDo file line prelude test body :: tail)
              (prelude ++ [.testLoop file line prelude test body] ++ tail)
        | testLoop file line prelude test body =>
            simp only [todoEq]
            let nextThread := { p.threads[actor] with
              controlSources := p.threads[actor].controlSources ++
                test.sources (finiteRegSources p.threads[actor]) }
            exact project_next_trace_reify_todo p actor nextThread
              (.testLoop file line prelude test body :: tail)
              (if test.eval (finiteRegs p.threads[actor]) ≠ 0 then
                body ++ [.whileDo file line prelude test body] ++ tail else tail)
              file line
        | stmt file line op =>
            simp only [todoEq]
            cases op
            case assign dst value =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.assign dst value)) }
              have threadProjection :
                  projectThread
                      (setReg { reifyThread thd with
                          todo := .stmt file line (.assign dst value) :: tail }
                        dst (Expr.eval (finiteRegs thd) value)
                        (Expr.sources (finiteRegSources thd) value)) =
                    finiteSetReg { thd with
                        todo := .stmt file line (.assign dst value) :: tail }
                      dst (Expr.eval (finiteRegs thd) value)
                      (Expr.sources (finiteRegSources thd) value) := by
                simpa [reifyThread] using
                  project_setReg_reifyThread
                    { thd with todo := .stmt file line (.assign dst value) :: tail }
                    dst (Expr.eval (finiteRegs thd) value)
                    (Expr.sources (finiteRegSources thd) value)
              change project (next (reify logged) actor
                  (setReg { reifyThread thd with
                      todo := .stmt file line (.assign dst value) :: tail }
                    dst (Expr.eval (finiteRegs thd) value)
                    (Expr.sources (finiteRegSources thd) value)) tail) =
                finiteNext logged actor
                  (finiteSetReg { thd with
                      todo := .stmt file line (.assign dst value) :: tail }
                    dst (Expr.eval (finiteRegs thd) value)
                    (Expr.sources (finiteRegSources thd) value)) tail
              rw [project_next, project_reify, threadProjection]
            case load dst loc order =>
              simp only [readChoice_reify]
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) loc
              let finiteRead := finiteReadChoice p address choice
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.load dst loc order)) }
              have threadProjection :
                  projectThread
                      (setReg { reifyThread thd with
                          todo := .stmt file line (.load dst loc order) :: tail }
                        dst finiteRead.fst [p.candidate.events.size]) =
                    finiteSetReg { thd with
                        todo := .stmt file line (.load dst loc order) :: tail }
                      dst finiteRead.fst [p.candidate.events.size] := by
                simpa [reifyThread] using
                  project_setReg_reifyThread
                    { thd with todo := .stmt file line (.load dst loc order) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]
              change project (next
                  (emit (reify logged) actor (.load address order finiteRead.fst)
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor
                  (setReg { reifyThread thd with
                      todo := .stmt file line (.load dst loc order) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]) tail) =
                finiteNext
                  (finiteEmit logged actor (.load address order finiteRead.fst)
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor
                  (finiteSetReg { thd with
                      todo := .stmt file line (.load dst loc order) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]) tail
              rw [project_next,
                project_emit_reify (p := logged) (actor := actor)
                  (action := .load address order finiteRead.fst)
                  (rf := finiteRead.snd) (deps := Addr.sources (finiteRegSources thd) loc),
                threadProjection]
            case store loc order value =>
              simp only
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) loc
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.store loc order value)) }
              let out := finiteEmit logged actor
                (.store address order (truncate address (Expr.eval (finiteRegs thd) value)))
                none (Addr.sources (finiteRegSources thd) loc ++
                  Expr.sources (finiteRegSources thd) value)
              unfold finiteRegs finiteRegSources
              rw [project_next, project_emit_logged_reify]
              have readyFields :
                  (p.threads[actor].aborted = false ∧ p.threads[actor].parked = none) ∧
                    p.threads[actor].fault = none := by simpa using ready
              rcases readyFields with ⟨⟨abortedEq, parkedEq⟩, faultEq⟩
              split
              · rename_i same
                simp only [same, if_true]
                apply congrArg (fun nextThread => finiteNext _ actor nextThread tail)
                simpa [thd, reifyThread, abortedEq, parkedEq, faultEq] using
                  projectThread_todo_criticalFalse thd
                    (.stmt file line (.store loc order value) :: tail)
              · rename_i different
                simp only [different, if_false]
                apply congrArg (fun nextThread => finiteNext _ actor nextThread tail)
                have thdTodo : thd.todo = .stmt file line (.store loc order value) :: tail := by
                  simpa [thd] using todoEq
                have restored :
                    { thd with todo := .stmt file line (.store loc order value) :: tail } = thd :=
                  witnessThread_setTodo_eq thd _ thdTodo
                have combined := (projectThread_todo thd
                  (.stmt file line (.store loc order value) :: tail)).trans restored
                dsimp only [thd] at combined ⊢
                exact combined
            case plainLoad dst loc =>
              simp only [readChoice_reify]
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) loc
              let finiteRead := finiteReadChoice p address choice
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.plainLoad dst loc)) }
              have threadProjection :
                  projectThread
                      (setReg { reifyThread thd with
                          todo := .stmt file line (.plainLoad dst loc) :: tail }
                        dst finiteRead.fst [p.candidate.events.size]) =
                    finiteSetReg { thd with
                        todo := .stmt file line (.plainLoad dst loc) :: tail }
                      dst finiteRead.fst [p.candidate.events.size] := by
                simpa [reifyThread] using
                  project_setReg_reifyThread
                    { thd with todo := .stmt file line (.plainLoad dst loc) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]
              change project (next
                  (emit (reify logged) actor (.plainLoad address finiteRead.fst)
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor
                  (setReg { reifyThread thd with
                      todo := .stmt file line (.plainLoad dst loc) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]) tail) =
                finiteNext
                  (finiteEmit logged actor (.plainLoad address finiteRead.fst)
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor
                  (finiteSetReg { thd with
                      todo := .stmt file line (.plainLoad dst loc) :: tail }
                    dst finiteRead.fst [p.candidate.events.size]) tail
              rw [project_next,
                project_emit_reify (p := logged) (actor := actor)
                  (action := .plainLoad address finiteRead.fst)
                  (rf := finiteRead.snd) (deps := Addr.sources (finiteRegSources thd) loc),
                threadProjection]
            case plainStore loc value =>
              simp only
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) loc
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.plainStore loc value)) }
              change project (next
                  (emit (reify logged) actor
                    (.plainStore address (truncate address (Expr.eval (finiteRegs thd) value)))
                    none (Addr.sources (finiteRegSources thd) loc ++
                      Expr.sources (finiteRegSources thd) value))
                  actor { reifyThread thd with
                    todo := .stmt file line (.plainStore loc value) :: tail } tail) =
                finiteNext
                  (finiteEmit logged actor
                    (.plainStore address (truncate address (Expr.eval (finiteRegs thd) value)))
                    none (Addr.sources (finiteRegSources thd) loc ++
                      Expr.sources (finiteRegSources thd) value))
                  actor { thd with
                    todo := .stmt file line (.plainStore loc value) :: tail } tail
              rw [project_next,
                project_emit_reify (p := logged) (actor := actor)
                  (action := .plainStore address (truncate address (Expr.eval (finiteRegs thd) value)))
                  (rf := none) (deps := Addr.sources (finiteRegSources thd) loc ++
                    Expr.sources (finiteRegSources thd) value)]
              exact congrArg
                (fun nextThread => finiteNext (finiteEmit logged actor
                  (.plainStore address (truncate address (Expr.eval (finiteRegs thd) value)))
                  none (Addr.sources (finiteRegSources thd) loc ++
                    Expr.sources (finiteRegSources thd) value)) actor nextThread tail)
                (project_reifyThread { thd with
                  todo := .stmt file line (.plainStore loc value) :: tail })
            case fetchAdd loc amount subtract =>
              simp only [readChoice_reify]
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) loc
              let finiteRead := finiteReadChoice p address choice
              let value' := if subtract then
                (finiteRead.fst + 4294967296 - amount) % 4294967296
                else (finiteRead.fst + amount) % 4294967296
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.fetchAdd loc amount subtract)) }
              change project (next
                  (emit (reify logged) actor (.rmw address .seqCst finiteRead.fst value')
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor { reifyThread thd with
                    todo := .stmt file line (.fetchAdd loc amount subtract) :: tail } tail) =
                finiteNext
                  (finiteEmit logged actor (.rmw address .seqCst finiteRead.fst value')
                    finiteRead.snd (Addr.sources (finiteRegSources thd) loc))
                  actor { thd with
                    todo := .stmt file line (.fetchAdd loc amount subtract) :: tail } tail
              rw [project_next,
                project_emit_reify (p := logged) (actor := actor)
                  (action := .rmw address .seqCst finiteRead.fst value')
                  (rf := finiteRead.snd) (deps := Addr.sources (finiteRegSources thd) loc)]
              exact congrArg
                (fun nextThread => finiteNext (finiteEmit logged actor
                  (.rmw address .seqCst finiteRead.fst value') finiteRead.snd
                  (Addr.sources (finiteRegSources thd) loc)) actor nextThread tail)
                (project_reifyThread { thd with
                  todo := .stmt file line (.fetchAdd loc amount subtract) :: tail })
            case cas dst loc expected desired =>
              let thd := p.threads[actor]
              let address := Addr.eval (fun r => thd.regs[witnessRegIndex r]) loc
              let finiteRead := finiteReadChoice p address choice
              have threadProjection :
                  projectThread
                      (setReg { reifyThread thd with
                          todo := .stmt file line (.cas dst loc expected desired) :: tail }
                        dst
                        (if finiteRead.fst =
                            Expr.eval (fun r => thd.regs[witnessRegIndex r]) expected then 1 else 0)
                        [p.candidate.events.size]) =
                    finiteSetReg { thd with
                        todo := .stmt file line (.cas dst loc expected desired) :: tail }
                      dst
                      (if finiteRead.fst =
                          Expr.eval (fun r => thd.regs[witnessRegIndex r]) expected then 1 else 0)
                      [p.candidate.events.size] := by
                simpa [reifyThread] using
                  project_setReg_reifyThread
                    { thd with todo := .stmt file line (.cas dst loc expected desired) :: tail }
                    dst
                    (if finiteRead.fst =
                        Expr.eval (fun r => thd.regs[witnessRegIndex r]) expected then 1 else 0)
                    [p.candidate.events.size]
              simp only [readChoice_reify]
              unfold finiteRegs finiteRegSources
              dsimp only [thd, address, finiteRead] at threadProjection ⊢
              simp only [reifyThread] at threadProjection
              rw [project_next, project_emit_logged_reify]
              simp only [reify]
              rw [threadProjection]
              unfold finiteNext finiteSetThread
              rfl
            case fence =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .fence) }
              let nextThread := { thd with
                todo := .stmt file line .fence :: tail }
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line .fence :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next (emit (reify logged) actor (.fence .seqCst))
                  actor { reifyThread thd with
                    todo := .stmt file line .fence :: tail } tail) =
                finiteNext (finiteEmit logged actor (.fence .seqCst)) actor nextThread tail
              rw [project_next, project_emit_reify, threadProjection]
            case signalFence =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .signalFence) }
              let nextThread := { thd with
                todo := .stmt file line .signalFence :: tail }
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line .signalFence :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next (emit (reify logged) actor (.signalFence .seqCst))
                  actor { reifyThread thd with
                    todo := .stmt file line .signalFence :: tail } tail) =
                finiteNext (finiteEmit logged actor (.signalFence .seqCst)) actor nextThread tail
              rw [project_next, project_emit_reify, threadProjection]
            case lock mutex =>
              simp only
              unfold finiteRegs finiteRegSources
              let thd := p.threads[actor]
              let mutexId := mutex.eval (finiteRegs thd)
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.lock mutex)) }
              have lockEq :
                  (reify p).locks (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) =
                  finiteLock p (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) := rfl
              simp only [lockEq]
              by_cases free : finiteLock p (mutex.eval (fun r =>
                  p.threads[actor].regs[witnessRegIndex r])) = none
              · simp only [free, if_true]
                let sourceOut := emit (reify logged) actor (.lock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                let finiteOut := finiteEmit logged actor (.lock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                have emitted : project sourceOut = finiteOut := by
                  dsimp only [sourceOut, finiteOut]
                  exact project_emit_reify logged actor (.lock mutexId) none
                    (mutex.sources (finiteRegSources thd))
                have lockProjection :
                    project { sourceOut with
                        locks := replace (reify p).locks mutexId (some actor) } =
                      { finiteOut with locks := finiteNatSet p.locks mutexId (some actor) } := by
                  change { project sourceOut with
                      locks := Vector.ofFn (fun i =>
                        replace (fun k => if h : k < 7 then p.locks[k]'h else none)
                          mutexId (some actor) i.val) } = _
                  rw [emitted, natVector_replace]
                let sourceThread := { reifyThread thd with
                  todo := .stmt file line (.lock mutex) :: tail }
                let finiteThread := { thd with
                  todo := .stmt file line (.lock mutex) :: tail }
                have threadProjection : projectThread sourceThread = finiteThread := by
                  exact projectThread_todo thd _
                change project (next { sourceOut with
                    locks := replace (reify p).locks mutexId (some actor) }
                  actor sourceThread tail) =
                    finiteNext { finiteOut with
                      locks := finiteNatSet p.locks mutexId (some actor) }
                      actor finiteThread tail
                rw [project_next, lockProjection, threadProjection]
              · simp only [free, if_false]
                exact project_reify p
            case unlock mutex =>
              simp only
              unfold finiteRegs finiteRegSources
              let thd := p.threads[actor]
              let mutexId := mutex.eval (finiteRegs thd)
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.unlock mutex)) }
              have lockEq :
                  (reify p).locks (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) =
                  finiteLock p (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) := rfl
              simp only [lockEq]
              by_cases owned : finiteLock p (mutex.eval (fun r =>
                  p.threads[actor].regs[witnessRegIndex r])) = some actor
              · simp only [owned, if_true]
                let sourceOut := emit (reify logged) actor (.unlock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                let finiteOut := finiteEmit logged actor (.unlock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                have emitted : project sourceOut = finiteOut := by
                  dsimp only [sourceOut, finiteOut]
                  exact project_emit_reify logged actor (.unlock mutexId) none
                    (mutex.sources (finiteRegSources thd))
                have lockProjection :
                    project { sourceOut with locks := replace (reify p).locks mutexId none } =
                      { finiteOut with locks := finiteNatSet p.locks mutexId none } := by
                  change { project sourceOut with
                      locks := Vector.ofFn (fun i =>
                        replace (fun k => if h : k < 7 then p.locks[k]'h else none)
                          mutexId none i.val) } = _
                  rw [emitted, natVector_replace]
                let sourceThread := { reifyThread thd with
                  todo := .stmt file line (.unlock mutex) :: tail }
                let finiteThread := { thd with
                  todo := .stmt file line (.unlock mutex) :: tail }
                have threadProjection : projectThread sourceThread = finiteThread := by
                  exact projectThread_todo thd _
                change project (next { sourceOut with
                    locks := replace (reify p).locks mutexId none }
                  actor sourceThread tail) =
                    finiteNext { finiteOut with
                      locks := finiteNatSet p.locks mutexId none }
                      actor finiteThread tail
                rw [project_next, lockProjection, threadProjection]
              · simp only [owned, if_false]
                exact project_reify p
            case condWait cond mutex =>
              simp only
              unfold finiteRegs finiteRegSources
              let thd := p.threads[actor]
              let mutexId := mutex.eval (finiteRegs thd)
              let conditionId := cond.eval (finiteRegs thd)
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.condWait cond mutex)) }
              have lockEq :
                  (reify p).locks (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) =
                  finiteLock p (mutex.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r])) := rfl
              simp only [lockEq]
              by_cases owned : finiteLock p (mutex.eval (fun r =>
                  p.threads[actor].regs[witnessRegIndex r])) = some actor
              · simp only [owned, if_true]
                let sourceOut := emit (reify logged) actor (.unlock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                let finiteOut := finiteEmit logged actor (.unlock mutexId) none
                  (mutex.sources (finiteRegSources thd))
                have emitted : project sourceOut = finiteOut := by
                  dsimp only [sourceOut, finiteOut]
                  exact project_emit_reify logged actor (.unlock mutexId) none
                    (mutex.sources (finiteRegSources thd))
                have lockProjection :
                    project { sourceOut with locks := replace (reify p).locks mutexId none } =
                      { finiteOut with locks := finiteNatSet p.locks mutexId none } := by
                  change { project sourceOut with
                      locks := Vector.ofFn (fun i =>
                        replace (fun k => if h : k < 7 then p.locks[k]'h else none)
                          mutexId none i.val) } = _
                  rw [emitted, natVector_replace]
                let sourceThread := { reifyThread thd with
                  todo := tail, parked := some (conditionId, mutexId) }
                let finiteThread := { thd with
                  todo := tail, parked := some (conditionId, mutexId) }
                have threadProjection : projectThread sourceThread = finiteThread := by
                  exact projectThread_todo_parked thd tail _
                change project (setThread { sourceOut with
                    locks := replace (reify p).locks mutexId none }
                  actor sourceThread) =
                    finiteSetThread { finiteOut with
                      locks := finiteNatSet p.locks mutexId none }
                      actor finiteThread
                rw [project_setThread, lockProjection, threadProjection]
              · simp only [owned, if_false]
                exact project_reify p
            case broadcast cond =>
              simp only
              let thd := p.threads[actor]
              let conditionId := cond.eval (finiteRegs thd)
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.broadcast cond)) }
              let sourceOut := { reify logged with
                conditions := replace (reify p).conditions conditionId
                  ((reify p).conditions conditionId + 1) }
              let finiteOut := { logged with
                conditions := finiteNatSet p.conditions conditionId (finiteCondition p conditionId + 1) }
              have outProjection : project sourceOut = finiteOut := by
                change { project (reify logged) with
                    conditions := Vector.ofFn (fun i =>
                      replace (fun k => if h : k < 5 then p.conditions[k]'h else 0)
                        conditionId (finiteCondition p conditionId + 1) i.val) } = _
                rw [project_reify, natVector_replace]
              let sourceThread := { reifyThread thd with
                todo := .stmt file line (.broadcast cond) :: tail }
              let finiteThread := { thd with
                todo := .stmt file line (.broadcast cond) :: tail }
              have threadProjection : projectThread sourceThread = finiteThread := by
                exact projectThread_todo thd _
              change project (next sourceOut actor sourceThread tail) =
                finiteNext finiteOut actor finiteThread tail
              rw [project_next, outProjection]
              exact congrArg (fun nextThread =>
                finiteNext finiteOut actor nextThread tail) threadProjection
            case signal cond =>
              simp only
              let thd := p.threads[actor]
              let conditionId := cond.eval (finiteRegs thd)
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.signal cond)) }
              let sourceOut := { reify logged with
                conditions := replace (reify p).conditions conditionId
                  ((reify p).conditions conditionId + 1) }
              let finiteOut := { logged with
                conditions := finiteNatSet p.conditions conditionId (finiteCondition p conditionId + 1) }
              have outProjection : project sourceOut = finiteOut := by
                change { project (reify logged) with
                    conditions := Vector.ofFn (fun i =>
                      replace (fun k => if h : k < 5 then p.conditions[k]'h else 0)
                        conditionId (finiteCondition p conditionId + 1) i.val) } = _
                rw [project_reify, natVector_replace]
              let sourceThread := { reifyThread thd with
                todo := .stmt file line (.signal cond) :: tail }
              let finiteThread := { thd with
                todo := .stmt file line (.signal cond) :: tail }
              have threadProjection : projectThread sourceThread = finiteThread := by
                exact projectThread_todo thd _
              change project (next sourceOut actor sourceThread tail) =
                finiteNext finiteOut actor finiteThread tail
              rw [project_next, outProjection]
              exact congrArg (fun nextThread =>
                finiteNext finiteOut actor nextThread tail) threadProjection
            case protect page enabled =>
              simp only
              let thd := p.threads[actor]
              let pageId := Expr.eval (finiteRegs thd) page
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.protect page enabled)) }
              let sourceOut := { reify logged with
                pageProtected := if choice.protectSucceeds then
                  replace (reify p).pageProtected pageId enabled else (reify p).pageProtected
                os := p.os ++ [OSEvent.protection actor.val pageId enabled choice.protectSucceeds] }
              let finiteOut := { logged with
                pageProtected := if choice.protectSucceeds then
                  finiteNatSet p.pageProtected pageId enabled else p.pageProtected
                os := p.os ++ [OSEvent.protection actor.val pageId enabled choice.protectSucceeds] }
              have outProjection : project sourceOut = finiteOut := by
                cases success : choice.protectSucceeds with
                | false =>
                    dsimp only [sourceOut, finiteOut]
                    simp only [success, Bool.false_eq_true, if_false]
                    change { project (reify logged) with
                      pageProtected := Vector.ofFn (fun i =>
                        if h : i.val < 4 then p.pageProtected[i.val]'h else false)
                      os := p.os ++ [OSEvent.protection actor.val pageId enabled false] } =
                        { logged with
                          pageProtected := p.pageProtected
                          os := p.os ++ [OSEvent.protection actor.val pageId enabled false] }
                    rw [project_reify, natVector_roundtrip]
                | true =>
                    dsimp only [sourceOut, finiteOut]
                    simp only [success, if_true]
                    change { project (reify logged) with
                      pageProtected := Vector.ofFn (fun i =>
                        replace (fun k => if h : k < 4 then p.pageProtected[k]'h else false)
                          pageId enabled i.val)
                      os := p.os ++ [OSEvent.protection actor.val pageId enabled true] } =
                        { logged with
                          pageProtected := finiteNatSet p.pageProtected pageId enabled
                          os := p.os ++ [OSEvent.protection actor.val pageId enabled true] }
                    rw [project_reify, natVector_replace]
              let sourceThread := { reifyThread thd with
                todo := .stmt file line (.protect page enabled) :: tail }
              let finiteThread := { thd with
                todo := .stmt file line (.protect page enabled) :: tail }
              have threadProjection : projectThread sourceThread = finiteThread := by
                exact projectThread_todo thd _
              change project (next sourceOut actor sourceThread tail) =
                finiteNext finiteOut actor finiteThread tail
              rw [project_next, outProjection]
              exact congrArg (fun nextThread =>
                finiteNext finiteOut actor nextThread tail) threadProjection
            case readPage dst page =>
              simp only
              unfold finiteRegs finiteRegSources
              let thd := p.threads[actor]
              let pageId := Expr.eval (finiteRegs thd) page
              let faulted := finitePageProtected p pageId
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.readPage dst page)) }
              have pageEq :
                  (reify p).pageProtected (Expr.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r]) page) =
                  finitePageProtected p (Expr.eval (fun r =>
                    p.threads[actor].regs[witnessRegIndex r]) page) := rfl
              simp only [pageEq]
              by_cases faults : finitePageProtected p (Expr.eval (fun r =>
                  p.threads[actor].regs[witnessRegIndex r]) page) = true
              · simp only [faults, if_true]
                let sourceOut := { reify logged with
                  os := p.os ++ [OSEvent.pageRead actor.val pageId true
                    (thd.controlSources ++ Expr.sources (finiteRegSources thd) page)] }
                let out := { logged with
                  os := p.os ++ [OSEvent.pageRead actor.val pageId true
                    (thd.controlSources ++ Expr.sources (finiteRegSources thd) page)] }
                have outProjection : project sourceOut = out := by
                  change project (reify out) = out
                  exact project_reify out
                let sourceThread := { reifyThread thd with
                  todo := .stmt file line (.readPage dst page) :: tail
                  fault := some pageId }
                let finiteThread := { thd with
                  todo := .stmt file line (.readPage dst page) :: tail
                  fault := some pageId }
                have baseProjection := projectThread_todo thd
                  (.stmt file line (.readPage dst page) :: tail)
                have threadProjection := projectThread_fault _ _ baseProjection (some pageId)
                change project (setThread sourceOut actor sourceThread) =
                  finiteSetThread out actor finiteThread
                rw [project_setThread, outProjection]
                exact congrArg (finiteSetThread out actor) threadProjection
              · simp only [faults, Bool.false_eq_true, if_false]
                let sourceOut := { reify logged with
                  os := p.os ++ [OSEvent.pageRead actor.val pageId false
                    (thd.controlSources ++ Expr.sources (finiteRegSources thd) page)] }
                let out := { logged with
                  os := p.os ++ [OSEvent.pageRead actor.val pageId false
                    (thd.controlSources ++ Expr.sources (finiteRegSources thd) page)] }
                have outProjection : project sourceOut = out := by
                  change project (reify out) = out
                  exact project_reify out
                let sourceSet := setReg
                  { reifyThread thd with todo := .stmt file line (.readPage dst page) :: tail }
                  dst 0
                let finiteSet := finiteSetReg
                  { thd with todo := .stmt file line (.readPage dst page) :: tail } dst 0
                have regProjection : projectThread sourceSet = finiteSet := by
                  dsimp only [sourceSet, finiteSet]
                  simpa [reifyThread] using project_setReg_reifyThread
                    { thd with todo := .stmt file line (.readPage dst page) :: tail } dst 0
                let sourcePermit := decide ((reify p).memory
                  (.gcState p.threads[actor].regs[witnessRegIndex .ptls]) = 0)
                let permit := decide (finiteMemory p (.gcState (finiteRegs thd .ptls)) = 0)
                have permitEq : sourcePermit = permit := rfl
                have threadProjection :
                    projectThread { sourceSet with criticalPermit := sourcePermit } =
                      { finiteSet with criticalPermit := permit } := by
                  rw [permitEq]
                  exact projectThread_criticalPermit sourceSet finiteSet regProjection permit
                change project (next sourceOut actor
                    { sourceSet with criticalPermit := sourcePermit } tail) =
                  finiteNext out actor { finiteSet with criticalPermit := permit } tail
                rw [project_next, outProjection]
                exact congrArg (fun nextThread => finiteNext out actor nextThread tail) threadProjection
            case external name =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.external name)) }
              let nextThread := { thd with
                todo := .stmt file line (.external name) :: tail }
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line (.external name) :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next (reify logged) actor
                  { reifyThread thd with
                    todo := .stmt file line (.external name) :: tail } tail) =
                finiteNext logged actor nextThread tail
              rw [project_next, project_reify, threadProjection]
            case milestone field value =>
              simp only
              let thd := p.threads[actor]
              let address := Addr.eval (finiteRegs thd) field
              let stored := Expr.eval (finiteRegs thd) value
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line (.milestone field value)) }
              let sourceOut := { reify logged with
                memory := replace (reify p).memory address stored }
              let finiteOut := { logged with
                memory := finiteLocationSet p.memory address stored }
              let nextThread := { thd with
                todo := .stmt file line (.milestone field value) :: tail }
              have outProjection : project sourceOut = finiteOut := by
                change { project (reify logged) with
                    memory := Vector.ofFn (fun i =>
                      replace (witnessLookup p.memory 0)
                        address stored witnessLocations[i]) } = finiteOut
                rw [project_reify, locationVector_replace]
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line (.milestone field value) :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next sourceOut actor
                  { reifyThread thd with
                    todo := .stmt file line (.milestone field value) :: tail } tail) =
                finiteNext finiteOut actor nextThread tail
              rw [project_next, outProjection, threadProjection]
            case critical =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .critical) }
              by_cases permitted : p.threads[actor].criticalPermit = true
              · simp only [permitted, if_true]
                let out := { logged with
                  criticalDuringGC := p.criticalDuringGC || p.collectionActive }
                let nextThread := { thd with
                  todo := .stmt file line .critical :: tail }
                rw [project_next]
                have outProjection :
                    project { reify p with
                      sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)]
                      criticalDuringGC := (reify p).criticalDuringGC ||
                        (reify p).collectionActive } = out := by
                  change project (reify out) = out
                  exact project_reify out
                rw [outProjection]
                have readyFields :
                    (p.threads[actor].aborted = false ∧ p.threads[actor].parked = none) ∧
                      p.threads[actor].fault = none := by simpa using ready
                rcases readyFields with ⟨⟨abortedEq, parkedEq⟩, faultEq⟩
                apply congrArg (fun nextThread => finiteNext out actor nextThread tail)
                have thdTodo : thd.todo = .stmt file line .critical :: tail := by
                  simpa [thd] using todoEq
                have restored : { thd with todo := .stmt file line .critical :: tail } = thd :=
                  witnessThread_setTodo_eq thd _ thdTodo
                have combined := (projectThread_todo thd
                  (.stmt file line .critical :: tail)).trans restored
                dsimp only [thd] at combined ⊢
                simp only [reifyThread] at combined
                rw [permitted] at combined
                exact combined
              · simp only [permitted, Bool.false_eq_true, if_false]
                let nextThread := { thd with
                  todo := .stmt file line .critical :: tail, aborted := true }
                rw [project_setThread]
                have loggedProjection :
                    project { reify p with
                      sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)]
                      criticalDuringGC := (reify p).criticalDuringGC ||
                        ((reify p).collectionActive &&
                          sourceTouchesRoots file line .critical) } = logged := by
                  change project (reify logged) = logged
                  exact project_reify logged
                rw [loggedProjection]
                have readyFields :
                    (p.threads[actor].aborted = false ∧ p.threads[actor].parked = none) ∧
                      p.threads[actor].fault = none := by simpa using ready
                rcases readyFields with ⟨⟨abortedEq, parkedEq⟩, faultEq⟩
                apply congrArg (finiteSetThread logged actor)
                have thdTodo : thd.todo = .stmt file line .critical :: tail := by
                  simpa [thd] using todoEq
                have restored :
                    { thd with todo := .stmt file line .critical :: tail, aborted := true } =
                      { thd with aborted := true } :=
                  witnessThread_setTodo_aborted_eq thd _ thdTodo
                have combined := (projectThread_todo_aborted thd
                  (.stmt file line .critical :: tail)).trans restored
                dsimp only [thd] at combined ⊢
                simp only [reifyThread] at combined
                have permitFalse : p.threads[actor].criticalPermit = false :=
                  Bool.eq_false_iff.2 permitted
                rw [permitFalse, todoEq] at combined
                exact combined
            case gcBody =>
              simp only
              let thd := p.threads[actor]
              let out := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                collectionActive := true
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .gcBody) }
              let nextThread := { thd with todo := .stmt file line .gcBody :: tail }
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line .gcBody :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next (reify out) actor
                  { reifyThread thd with todo := .stmt file line .gcBody :: tail } tail) =
                finiteNext out actor nextThread tail
              rw [project_next, project_reify, threadProjection]
            case endGCBody =>
              simp only
              let thd := p.threads[actor]
              let out := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                collectionActive := false
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .endGCBody) }
              let nextThread := { thd with todo := .stmt file line .endGCBody :: tail }
              have threadProjection :
                  projectThread { reifyThread thd with
                    todo := .stmt file line .endGCBody :: tail } = nextThread := by
                simpa [nextThread, reifyThread] using project_reifyThread nextThread
              change project (next (reify out) actor
                  { reifyThread thd with todo := .stmt file line .endGCBody :: tail } tail) =
                finiteNext out actor nextThread tail
              rw [project_next, project_reify, threadProjection]
            case abort =>
              simp only
              let thd := p.threads[actor]
              let logged := { p with
                sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
                criticalDuringGC := p.criticalDuringGC ||
                  (p.collectionActive && sourceTouchesRoots file line .abort) }
              let nextThread := { thd with
                todo := .stmt file line .abort :: tail, aborted := true }
              rw [project_setThread]
              have loggedProjection :
                  project { reify p with
                    sourceTrace := (reify p).sourceTrace ++ [(actor.val, file, line)]
                    criticalDuringGC := (reify p).criticalDuringGC ||
                      ((reify p).collectionActive && sourceTouchesRoots file line .abort) } = logged := by
                change project (reify logged) = logged
                exact project_reify logged
              rw [loggedProjection]
              have readyFields :
                  (p.threads[actor].aborted = false ∧ p.threads[actor].parked = none) ∧
                    p.threads[actor].fault = none := by simpa using ready
              rcases readyFields with ⟨⟨abortedEq, parkedEq⟩, faultEq⟩
              apply congrArg (finiteSetThread logged actor)
              have thdTodo : thd.todo = .stmt file line .abort :: tail := by
                simpa [thd] using todoEq
              have restored : { thd with todo := .stmt file line .abort :: tail, aborted := true } =
                  { thd with aborted := true } :=
                witnessThread_setTodo_aborted_eq thd _ thdTodo
              have combined := (projectThread_todo_aborted thd
                (.stmt file line .abort :: tail)).trans restored
              dsimp only [thd] at combined ⊢
              rw [todoEq] at combined
              exact combined

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem project_wake_reify (p : WitnessProjection) (actor : Fin 3) :
    project (wake (reify p) actor) = finiteWake p actor := by
  unfold wake finiteWake
  have sourceThread : (reify p).threads actor = reifyThread p.threads[actor] := rfl
  rw [sourceThread]
  simp only [reifyThread]
  cases parkedEq : p.threads[actor].parked with
  | none => simpa only [parkedEq] using project_reify p
  | some parked =>
      obtain ⟨condition, mutex⟩ := parked
      simp only
      have lockEq : (reify p).locks mutex = finiteLock p mutex := rfl
      rw [lockEq]
      by_cases free : finiteLock p mutex = none
      · simp only [free, if_true]
        let sourceOut := emit (reify p) actor (.lock mutex)
        let finiteOut := finiteEmit p actor (.lock mutex)
        have emitted : project sourceOut = finiteOut := by
          dsimp only [sourceOut, finiteOut]
          exact project_emit_reify p actor (.lock mutex) none []
        have lockProjection :
            project { sourceOut with
                locks := replace (reify p).locks mutex (some actor) } =
              { finiteOut with locks := finiteNatSet p.locks mutex (some actor) } := by
          change
            { project sourceOut with
                locks := Vector.ofFn (fun i =>
                  replace (fun k => if h : k < 7 then p.locks[k]'h else none)
                    mutex (some actor) i.val) } =
              { finiteOut with locks := finiteNatSet p.locks mutex (some actor) }
          rw [emitted, natVector_replace]
        have threadProjection :
            projectThread { reifyThread p.threads[actor] with parked := none } =
              { p.threads[actor] with parked := none } := by
          simpa [reifyThread] using
            project_reifyThread { p.threads[actor] with parked := none }
        rw [project_setThread, lockProjection]
        change
          finiteSetThread { finiteOut with
              locks := finiteNatSet p.locks mutex (some actor) } actor
            (projectThread { reifyThread p.threads[actor] with parked := none }) =
          finiteSetThread { finiteOut with
              locks := finiteNatSet p.locks mutex (some actor) } actor
            { p.threads[actor] with parked := none }
        exact congrArg
          (finiteSetThread { finiteOut with
            locks := finiteNatSet p.locks mutex (some actor) } actor)
          threadProjection
      · simp only [free, if_false]
        exact project_reify p

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem project_deliver_reify (p : WitnessProjection) (actor : Fin 3) :
    project (deliver (reify p) actor) = finiteDeliver p actor := by
  unfold deliver finiteDeliver
  have sourceThread : (reify p).threads actor = reifyThread p.threads[actor] := rfl
  rw [sourceThread]
  simp only [reifyThread]
  cases faultEq : p.threads[actor].fault with
  | none => simpa only [faultEq] using project_reify p
  | some page =>
      simp only
      have memoryEq (loc : Loc) : (reify p).memory loc = finiteMemory p loc := rfl
      have invalid : ¬(finiteMemory p
            (.handlersReady (finiteRegs p.threads[actor] .ptls)) = 1 ∧
          finiteMemory p
            (.gcState (finiteRegs p.threads[actor] .ptls)) ≠ 1) := by
        unfold finiteRegs
        simp [finiteMemory, finiteLocationGet, witnessLocationIndex]
      have sourceInvalid : ¬((reify p).memory
            (.handlersReady p.threads[actor].regs[witnessRegIndex .ptls]) = 1 ∧
          (reify p).memory
            (.gcState p.threads[actor].regs[witnessRegIndex .ptls]) ≠ 1) := by
        simpa only [memoryEq, finiteRegs] using invalid
      simp only [sourceInvalid, invalid, if_false]
      let nextThread := { p.threads[actor] with fault := some page, aborted := true }
      simpa [nextThread, reifyThread] using project_setThread_reify p actor nextThread

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem project_advance_reify (p : WitnessProjection) (cmd : Scheduled 3) :
    project (advance (reify p) cmd) = finiteAdvance p cmd := by
  cases cmd with
  | source actor choice => exact project_step_reify p actor choice
  | wake actor => exact project_wake_reify p actor
  | deliver actor => exact project_deliver_reify p actor

end JuliaLean.CRuntime.WorldStop
