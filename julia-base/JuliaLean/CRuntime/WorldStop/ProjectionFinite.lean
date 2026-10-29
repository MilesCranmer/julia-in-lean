import JuliaLean.CRuntime.WorldStop.Projection

namespace JuliaLean.CRuntime.WorldStop

open Memory

def finiteVectorSet (values : Vector α n) (index : Fin n) (value : α) : Vector α n :=
  Vector.ofFn fun i => if i = index then value else values[i]

def finiteNatGet (values : Vector α n) (outside : α) (index : Nat) : α :=
  if h : index < n then values[index]'h else outside

def finiteNatSet (values : Vector α n) (index : Nat) (value : α) : Vector α n :=
  if h : index < n then finiteVectorSet values ⟨index, h⟩ value else values

def finiteLocationGet (values : Vector α 22) (outside : α) (loc : Loc) : α :=
  match witnessLocationIndex loc with
  | some i => values[i]
  | none => outside

def finiteLocationSet (values : Vector α 22) (loc : Loc) (value : α) : Vector α 22 :=
  match witnessLocationIndex loc with
  | some i => finiteVectorSet values i value
  | none => values

def finiteRegs (thd : WitnessThread) (reg : Reg) : Nat :=
  thd.regs[witnessRegIndex reg]

def finiteRegSources (thd : WitnessThread) (reg : Reg) : List Nat :=
  thd.regSources[witnessRegIndex reg]

def finiteSetReg (thd : WitnessThread) (dst : Reg) (value : Nat)
    (sources : List Nat := []) : WitnessThread :=
  let value := match localWidth dst with
    | some bits => value % (2 ^ bits)
    | none => value
  { thd with
    regs := finiteVectorSet thd.regs (witnessRegIndex dst) value
    regSources := finiteVectorSet thd.regSources (witnessRegIndex dst) sources }

def finiteSetThread (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) : WitnessProjection :=
  { p with threads := finiteVectorSet p.threads actor thd }

def finiteMemory (p : WitnessProjection) (loc : Loc) : Nat :=
  finiteLocationGet p.memory 0 loc

def finiteLatest (p : WitnessProjection) (loc : Loc) : Option Nat :=
  finiteLocationGet p.latest none loc

def finiteMOClock (p : WitnessProjection) (loc : Loc) : Nat :=
  finiteLocationGet p.moClock 0 loc

def finitePageProtected (p : WitnessProjection) (page : Nat) : Bool :=
  finiteNatGet p.pageProtected false page

def finiteLock (p : WitnessProjection) (mutex : Nat) : Option (Fin 3) :=
  finiteNatGet p.locks none mutex

def finiteCondition (p : WitnessProjection) (condition : Nat) : Nat :=
  finiteNatGet p.conditions 0 condition

def finiteReadChoice (p : WitnessProjection) (loc : Loc) (choice : Choice) : Nat × Option Nat :=
  match choice.read with
  | .current => (finiteMemory p loc, finiteLatest p loc)
  | .chosen value source => (value, source)

/-- Finite projection of `emit`, `Source.lean:674-691`. -/
def finiteEmit (p : WitnessProjection) (actor : Fin 3)
    (action : Memory.Action Loc Nat) (rf : Option Nat := none)
    (deps : List Nat := []) : WitnessProjection :=
  let writes := action.writeValue.isSome
  let atomicWrite := writes && !action.isPlain
  let mo := if atomicWrite then finiteMOClock p (action.location.getD .gcRunning) + 1 else 0
  let event : Memory.Event Loc Nat :=
    { thread := actor.val, action := action, readFrom := rf, mo := mo
      sc := p.scClock, dependsOn := p.threads[actor].controlSources ++ deps }
  let p' := { p with
    candidate := p.candidate.append event
    scClock := p.scClock + if action.isSC then 1 else 0 }
  match action.location, action.writeValue with
  | some loc, some value =>
      { p' with
        memory := finiteLocationSet p.memory loc (truncate loc value)
        latest := finiteLocationSet p.latest loc (some (p'.candidate.events.size - 1))
        moClock := if atomicWrite then finiteLocationSet p.moClock loc mo else p.moClock }
  | _, _ => p'

def finiteNext (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) (tail : List Command) : WitnessProjection :=
  finiteSetThread p actor { thd with todo := tail }

def finiteReturnThread (p : WitnessProjection) (actor : Fin 3)
    (thd : WitnessThread) : WitnessProjection :=
  match thd.calls with
  | [] => finiteSetThread p actor { thd with todo := [] }
  | todo :: calls =>
      let handlerReturn := thd.inHandler && thd.handlerDepth == some calls.length
      { (finiteSetThread p actor { thd with
          todo := todo, calls := calls
          inHandler := if handlerReturn then false else thd.inHandler
          handlerDepth := if handlerReturn then none else thd.handlerDepth }) with
        os := if handlerReturn then p.os ++ [.returnFromHandler actor.val] else p.os }

def finiteOpSupported (thd : WitnessThread) : Op → Bool
  | .load _ loc _ | .store loc _ _ | .plainLoad _ loc | .plainStore loc _
  | .fetchAdd loc _ _ | .cas _ loc _ _ | .milestone loc _ =>
      decide (WitnessTracked (loc.eval (finiteRegs thd)))
  | .lock mutex | .unlock mutex => decide (mutex.eval (finiteRegs thd) < 7)
  | .condWait cond mutex =>
      decide (cond.eval (finiteRegs thd) < 5) && decide (mutex.eval (finiteRegs thd) < 7)
  | .broadcast cond | .signal cond => decide (cond.eval (finiteRegs thd) < 5)
  | .protect page _ => decide (page.eval (finiteRegs thd) < 4)
  | .readPage _ page => decide (page.eval (finiteRegs thd) < 4) &&
      decide (WitnessTracked (.gcState (finiteRegs thd .ptls)))
  | _ => true

def finiteSupported (p : WitnessProjection) : Scheduled 3 → Bool
  | .source actor _ =>
      match p.threads[actor].todo with
      | .stmt _ _ op :: _ => finiteOpSupported p.threads[actor] op
      | _ => true
  | .wake actor =>
      match p.threads[actor].parked with
      | none => true
      | some (_, mutex) => decide (mutex < 7)
  | .deliver _ => false

/-- Finite projection of `step`, `Source.lean:728-835`. -/
def finiteStep (p : WitnessProjection) (actor : Fin 3)
    (choice : Choice := {}) : WitnessProjection :=
  let thd := p.threads[actor]
  if thd.aborted || thd.parked.isSome || thd.fault.isSome then p else
  match thd.todo with
  | [] => finiteReturnThread p actor thd
  | .ret file line :: _ =>
      finiteReturnThread { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor thd
  | .call file line proc :: tail =>
      finiteSetThread { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor { thd with todo := program proc, calls := tail :: thd.calls }
  | .branch file line test yes no :: tail =>
      finiteNext { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor
        { thd with
          controlSources := thd.controlSources ++ test.sources (finiteRegSources thd) }
        ((if test.eval (finiteRegs thd) ≠ 0 then yes else no) ++ tail)
  | .whileDo file line prelude test body :: tail =>
      finiteNext p actor thd (prelude ++ [.testLoop file line prelude test body] ++ tail)
  | .testLoop file line prelude test body :: tail =>
      finiteNext { p with sourceTrace := p.sourceTrace ++ [(actor.val, file, line)] }
        actor
        { thd with
          controlSources := thd.controlSources ++ test.sources (finiteRegSources thd) }
        (if test.eval (finiteRegs thd) ≠ 0 then
          body ++ [.whileDo file line prelude test body] ++ tail else tail)
  | .stmt file line op :: tail =>
      let logged := { p with
        sourceTrace := p.sourceTrace ++ [(actor.val, file, line)]
        criticalDuringGC := p.criticalDuringGC ||
          (p.collectionActive && sourceTouchesRoots file line op) }
      let eval := Expr.eval (finiteRegs thd)
      let addr := Addr.eval (finiteRegs thd)
      let deps := Expr.sources (finiteRegSources thd)
      let addrDeps := Addr.sources (finiteRegSources thd)
      match op with
      | .assign dst value =>
          finiteNext logged actor (finiteSetReg thd dst (eval value) (deps value)) tail
      | .load dst loc order =>
          let (value, rf) := finiteReadChoice p (addr loc) choice
          let out := finiteEmit logged actor (.load (addr loc) order value) rf (addrDeps loc)
          finiteNext out actor (finiteSetReg thd dst value [p.candidate.events.size]) tail
      | .store loc order value =>
          let thd := if addr loc = .gcState (finiteRegs thd .ptls) then
              { thd with criticalPermit := false } else thd
          finiteNext
            (finiteEmit logged actor (.store (addr loc) order (truncate (addr loc) (eval value)))
              none (addrDeps loc ++ deps value)) actor thd tail
      | .plainLoad dst loc =>
          let (value, rf) := finiteReadChoice p (addr loc) choice
          let out := finiteEmit logged actor (.plainLoad (addr loc) value) rf (addrDeps loc)
          finiteNext out actor (finiteSetReg thd dst value [p.candidate.events.size]) tail
      | .plainStore loc value =>
          finiteNext
            (finiteEmit logged actor (.plainStore (addr loc) (truncate (addr loc) (eval value)))
              none (addrDeps loc ++ deps value)) actor thd tail
      | .fetchAdd loc amount subtract =>
          let (value, rf) := finiteReadChoice p (addr loc) choice
          let value' := if subtract then (value + 4294967296 - amount) % 4294967296
            else (value + amount) % 4294967296
          finiteNext
            (finiteEmit logged actor (.rmw (addr loc) .seqCst value value') rf (addrDeps loc))
            actor thd tail
      | .cas dst loc expected desired =>
          let (value, rf) := finiteReadChoice p (addr loc) choice
          let out := finiteEmit logged actor
            (.cas (addr loc) .seqCst .seqCst (eval expected) (eval desired) value) rf
            (addrDeps loc ++ deps expected ++ deps desired)
          finiteNext out actor
            (finiteSetReg thd dst (if value = eval expected then 1 else 0)
              [p.candidate.events.size]) tail
      | .fence => finiteNext (finiteEmit logged actor (.fence .seqCst)) actor thd tail
      | .signalFence =>
          finiteNext (finiteEmit logged actor (.signalFence .seqCst)) actor thd tail
      | .lock mutex =>
          let m := mutex.eval (finiteRegs thd)
          if finiteLock p m = none then
            let out := finiteEmit logged actor (.lock m) none
              (mutex.sources (finiteRegSources thd))
            finiteNext { out with locks := finiteNatSet p.locks m (some actor) } actor thd tail
          else p
      | .unlock mutex =>
          let m := mutex.eval (finiteRegs thd)
          if finiteLock p m = some actor then
            let out := finiteEmit logged actor (.unlock m) none
              (mutex.sources (finiteRegSources thd))
            finiteNext { out with locks := finiteNatSet p.locks m none } actor thd tail
          else p
      | .condWait cond mutex =>
          let m := mutex.eval (finiteRegs thd)
          if finiteLock p m = some actor then
            let out := finiteEmit logged actor (.unlock m) none
              (mutex.sources (finiteRegSources thd))
            finiteSetThread { out with locks := finiteNatSet p.locks m none } actor
              { thd with todo := tail, parked := some (cond.eval (finiteRegs thd), m) }
          else p
      | .broadcast cond | .signal cond =>
          let k := cond.eval (finiteRegs thd)
          finiteNext { logged with
            conditions := finiteNatSet p.conditions k (finiteCondition p k + 1) }
            actor thd tail
      | .protect page enabled =>
          let page := eval page
          finiteNext { logged with
            pageProtected := if choice.protectSucceeds then
              finiteNatSet p.pageProtected page enabled else p.pageProtected
            os := p.os ++ [.protection actor.val page enabled choice.protectSucceeds] }
            actor thd tail
      | .readPage dst pageExpr =>
          let page := eval pageExpr
          let faulted := finitePageProtected p page
          let out := { logged with
            os := p.os ++ [.pageRead actor.val page faulted
              (thd.controlSources ++ deps pageExpr)] }
          if faulted then finiteSetThread out actor { thd with fault := some page }
          else finiteNext out actor
            { (finiteSetReg thd dst 0) with
              criticalPermit := decide (finiteMemory p (.gcState (finiteRegs thd .ptls)) = 0) }
            tail
      | .external _ => finiteNext logged actor thd tail
      | .milestone field value =>
          finiteNext { logged with
            memory := finiteLocationSet p.memory (addr field) (eval value) } actor thd tail
      | .critical =>
          if thd.criticalPermit then
            finiteNext { logged with
              criticalDuringGC := p.criticalDuringGC || p.collectionActive } actor thd tail
          else finiteSetThread logged actor { thd with aborted := true }
      | .gcBody => finiteNext { logged with collectionActive := true } actor thd tail
      | .endGCBody => finiteNext { logged with collectionActive := false } actor thd tail
      | .abort => finiteSetThread logged actor { thd with aborted := true }

/-- Finite projection of `wake`, `Source.lean:839-847`. -/
def finiteWake (p : WitnessProjection) (actor : Fin 3) : WitnessProjection :=
  let thd := p.threads[actor]
  match thd.parked with
  | none => p
  | some (_, mutex) =>
      if finiteLock p mutex = none then
        let out := finiteEmit p actor (.lock mutex)
        finiteSetThread { out with locks := finiteNatSet p.locks mutex (some actor) }
          actor { thd with parked := none }
      else p

def finiteDeliver (p : WitnessProjection) (actor : Fin 3) : WitnessProjection :=
  let thd := p.threads[actor]
  match thd.fault with
  | none => p
  | some page =>
      if finiteMemory p (.handlersReady (finiteRegs thd .ptls)) = 1 ∧
          finiteMemory p (.gcState (finiteRegs thd .ptls)) ≠ 1 then
        finiteSetThread { p with os := p.os ++ [.delivery actor.val page] } actor
          { thd with
            todo := program .setGCAndWait
            calls := thd.todo :: thd.calls
            fault := none
            inHandler := true
            handlerDepth := some thd.calls.length }
      else finiteSetThread p actor { thd with aborted := true }

def finiteAdvance (p : WitnessProjection) : Scheduled 3 → WitnessProjection
  | .source actor choice => finiteStep p actor choice
  | .wake actor => finiteWake p actor
  | .deliver actor => finiteDeliver p actor

private theorem witnessRegIndex_witnessRegs :
    ∀ i : Fin 31, witnessRegIndex witnessRegs[i] = i := by decide

private theorem witnessVector_roundtrip (values : Vector α 31) :
    Vector.ofFn (fun i => values[witnessRegIndex witnessRegs[i]]) = values := by
  apply Vector.ext
  intro i
  intro hi
  simp only [Vector.getElem_ofFn]
  have indexEq := witnessRegIndex_witnessRegs ⟨i, hi⟩
  exact congrArg (fun index : Fin 31 => values[index]) indexEq

theorem project_reifyThread (thd : WitnessThread) :
    projectThread (reifyThread thd) = thd := by
  cases thd
  unfold projectThread reifyThread
  rw [witnessVector_roundtrip, witnessVector_roundtrip]

end JuliaLean.CRuntime.WorldStop
