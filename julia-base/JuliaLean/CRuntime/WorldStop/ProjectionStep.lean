import JuliaLean.CRuntime.WorldStop.ProjectionFiniteProof

namespace JuliaLean.CRuntime.WorldStop

private def opSupported (thd : Thread) : Op → Bool
  | .load _ loc _ | .store loc _ _ | .plainLoad _ loc | .plainStore loc _
  | .fetchAdd loc _ _ | .cas _ loc _ _ | .milestone loc _ =>
      decide (WitnessTracked (loc.eval thd.regs))
  | .lock mutex | .unlock mutex => decide (mutex.eval thd.regs < 7)
  | .condWait cond mutex =>
      decide (cond.eval thd.regs < 5) && decide (mutex.eval thd.regs < 7)
  | .broadcast cond | .signal cond => decide (cond.eval thd.regs < 5)
  | .protect page _ => decide (page.eval thd.regs < 4)
  | .readPage _ page => decide (page.eval thd.regs < 4) &&
      decide (WitnessTracked (.gcState (thd.regs .ptls)))
  | _ => true

private def sourceSupported (s : Machine 3) : Scheduled 3 → Bool
  | .source actor _ =>
      match (s.threads actor).todo with
      | .stmt _ _ op :: _ => opSupported (s.threads actor) op
      | _ => true
  | .wake actor =>
      match (s.threads actor).parked with
      | none => true
      | some (_, mutex) => decide (mutex < 7)
  | .deliver _ => false

private theorem sourceSupported_reify (p : WitnessProjection) (cmd : Scheduled 3) :
    sourceSupported (reify p) cmd = finiteSupported p cmd := by
  cases cmd with
  | source actor choice =>
      simp only [sourceSupported, finiteSupported, reify, reifyThread,
        Vector.getElem_ofFn]
      cases p.threads[actor].todo with
      | nil => rfl
      | cons command tail =>
          cases command with
          | stmt file line op => cases op <;> rfl
          | branch file line test yes no => rfl
          | whileDo file line prelude test body => rfl
          | testLoop file line prelude test body => rfl
          | call file line proc => rfl
          | ret file line => rfl
  | wake actor =>
      change (match p.threads[actor].parked with
        | none => true
        | some (_, mutex) => decide (mutex < 7)) = _
      rfl
  | deliver actor => rfl

/-- Every source memory access and OS index is retained by the finite tables.
Handler delivery requires initialization metadata outside these runtime tables. -/
def witnessSupported (p : WitnessProjection) (cmd : Scheduled 3) : Bool :=
  finiteSupported p cmd

def witnessStep (p : WitnessProjection) (cmd : Scheduled 3) : WitnessProjection :=
  finiteAdvance p cmd

private theorem agreement_setThread {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (thd : Thread) :
    WitnessAgreement (setThread s actor thd) (setThread t actor thd) :=
  { h with threads := by simp only [setThread, h.threads] }

private theorem agreement_next {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (thd : Thread) (tail : List Command) :
    WitnessAgreement (next s actor thd tail) (next t actor thd tail) :=
  agreement_setThread h actor _

private theorem agreement_trace {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (file : String) (line : Nat) :
    WitnessAgreement { s with sourceTrace := s.sourceTrace ++ [(actor.val, file, line)] }
      { t with sourceTrace := t.sourceTrace ++ [(actor.val, file, line)] } :=
  { h with sourceTrace := by rw [h.sourceTrace] }

private theorem agreement_returnThread {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (thd : Thread) :
    WitnessAgreement (returnThread s actor thd) (returnThread t actor thd) := by
  rcases h with ⟨hm, ht, hp, hl, hc, hr, ho, hs, he, hos, htr, ha, hcr⟩
  unfold returnThread
  cases thd.calls <;> constructor <;> intros <;> simp_all [setThread]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
private theorem agreement_step {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (choice : Choice)
    (supported : sourceSupported t (.source actor choice) = true) :
    WitnessAgreement (step s actor choice) (step t actor choice) := by
  have hmo₀ := h.moClock .gcRunning (by decide : WitnessTracked .gcRunning)
  have readEqual (loc : Loc) (tracked : WitnessTracked loc) :
      readChoice s loc choice = readChoice t loc choice := by
    cases hread : choice.read with
    | current => simp [readChoice, hread, h.memory loc tracked, h.latest loc tracked]
    | chosen value source => simp [readChoice, hread]
  unfold step
  simp only [h.threads]
  split
  · exact h
  · cases todoEq : (t.threads actor).todo with
    | nil =>
        simpa only [todoEq, h.threads] using
          agreement_returnThread h actor (t.threads actor)
    | cons command tail =>
        cases command with
        | ret file line =>
            simpa only [todoEq, h.threads] using
              agreement_returnThread (agreement_trace h actor file line) actor
                (t.threads actor)
        | call file line proc =>
            let thd := t.threads actor
            simpa only [thd, todoEq, h.threads] using
              agreement_setThread (agreement_trace h actor file line) actor
                { thd with todo := program proc, calls := tail :: thd.calls }
        | branch file line test yes no =>
            let thd := t.threads actor
            simpa only [thd, todoEq, h.threads] using
              agreement_next (agreement_trace h actor file line) actor
                { thd with controlSources := thd.controlSources ++ test.sources thd.regSources }
                ((if test.eval thd.regs ≠ 0 then yes else no) ++ tail)
        | whileDo file line prelude test body =>
            let thd := t.threads actor
            simpa only [thd, todoEq, h.threads] using
              agreement_next h actor thd
                (prelude ++ [.testLoop file line prelude test body] ++ tail)
        | testLoop file line prelude test body =>
            let thd := t.threads actor
            simpa only [thd, todoEq, h.threads] using
              agreement_next (agreement_trace h actor file line) actor
                { thd with controlSources := thd.controlSources ++ test.sources thd.regSources }
                (if test.eval thd.regs ≠ 0 then
                  body ++ [.whileDo file line prelude test body] ++ tail else tail)
        | stmt file line op =>
            have footprint : opSupported (t.threads actor) op = true := by
              simpa only [sourceSupported, todoEq] using supported
            cases op
            all_goals
              simp only [opSupported, Bool.and_eq_true, decide_eq_true_eq] at footprint
              rcases h with ⟨hm, ht, hp, hl, hc, hr, ho, hs, he, hos, htr, ha, hcr⟩
              simp_all [next, setThread, emit, Memory.Action.location,
                Memory.Action.writeValue, Memory.Action.isPlain]
            all_goals
              repeat first | apply WitnessAgreement.mk | intro _ | split
            all_goals try dsimp only
            all_goals repeat first | split
            all_goals first
              | rfl
              | assumption
              | exact hm _ (by assumption)
              | exact hp _ (by assumption)
              | exact hl _ (by assumption)
              | exact hc _ (by assumption)
              | exact hr _ (by assumption)
              | exact ho _ (by assumption)
              | exact hs
              | exact he
              | exact hos
              | exact htr
              | exact ha
              | exact hcr
              | (try simp_all [replace])

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
private theorem agreement_wake {s t : Machine 3} (h : WitnessAgreement s t)
    (actor : Fin 3) (supported : sourceSupported t (.wake actor) = true) :
    WitnessAgreement (wake s actor) (wake t actor) := by
  have hmo₀ := h.moClock .gcRunning (by decide : WitnessTracked .gcRunning)
  simp only [wake, h.threads]
  cases parkedEq : (t.threads actor).parked with
  | none =>
      exact h
  | some parked =>
      obtain ⟨cond, mutex⟩ := parked
      have bounded : mutex < 7 := by simpa [sourceSupported, parkedEq] using supported
      have hlock := h.locks mutex bounded
      simp only
      rw [hlock]
      by_cases free : t.locks mutex = none
      · simp [free]
        rcases h with ⟨hm, ht, hp, hl, hc, hr, ho, hs, he, hos, htr, ha, hcr⟩
        simp_all [setThread, emit, Memory.Action.location,
          Memory.Action.writeValue, Memory.Action.isPlain]
        all_goals repeat first | apply WitnessAgreement.mk | intro _
        all_goals try dsimp only
        all_goals first
          | rfl
          | assumption
          | exact hm _ (by assumption)
          | exact hp _ (by assumption)
          | exact hl _ (by assumption)
          | exact hc _ (by assumption)
          | exact hr _ (by assumption)
          | exact ho _ (by assumption)
          | exact hs
          | exact he
          | exact hos
          | exact htr
          | exact ha
          | exact hcr
          | (try simp_all [replace])
      · simpa [free] using h

private theorem agreement_advance {s t : Machine 3} (h : WitnessAgreement s t)
    (cmd : Scheduled 3) (supported : sourceSupported t cmd = true) :
    WitnessAgreement (advance s cmd) (advance t cmd) := by
  cases cmd with
  | source actor choice => exact agreement_step h actor choice supported
  | wake actor => exact agreement_wake h actor supported
  | deliver actor => simp [sourceSupported] at supported

theorem project_advance (s : Machine 3) (cmd : Scheduled 3)
    (supported : witnessSupported (project s) cmd = true) :
    project (advance s cmd) = witnessStep (project s) cmd := by
  have sourceSupport : sourceSupported (reify (project s)) cmd = true := by
    rw [sourceSupported_reify]
    exact supported
  calc
    project (advance s cmd) = project (advance (reify (project s)) cmd) :=
      (agreement_advance (reify_project_agreement s) cmd sourceSupport).project_eq
    _ = finiteAdvance (project s) cmd := project_advance_reify (project s) cmd

def projectedRun (p : WitnessProjection) : List (Scheduled 3) → WitnessProjection
  | [] => p
  | cmd :: rest => projectedRun (witnessStep p cmd) rest

def witnessRunSupported (p : WitnessProjection) : List (Scheduled 3) → Bool
  | [] => true
  | cmd :: rest => witnessSupported p cmd && witnessRunSupported (witnessStep p cmd) rest

set_option maxHeartbeats 3000000 in
theorem project_run (s : Machine 3) (schedule : List (Scheduled 3))
    (supported : witnessRunSupported (project s) schedule = true) :
    project (run s schedule) = projectedRun (project s) schedule := by
  induction schedule generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
      simp only [witnessRunSupported] at supported
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp supported
      simp only [run, projectedRun]
      rw [← project_advance s cmd head]
      exact ih (advance s cmd) (by rwa [project_advance s cmd head])

set_option maxHeartbeats 3000000 in
theorem projectedRun_append (p : WitnessProjection) (front back : List (Scheduled 3)) :
    projectedRun p (front ++ back) = projectedRun (projectedRun p front) back := by
  induction front generalizing p with
  | nil => rfl
  | cons cmd rest ih =>
      rw [List.cons_append, projectedRun, projectedRun]
      exact ih (witnessStep p cmd)

set_option maxHeartbeats 3000000 in
theorem witnessRunSupported_append (p : WitnessProjection) (front back : List (Scheduled 3))
    (first : witnessRunSupported p front = true)
    (second : witnessRunSupported (projectedRun p front) back = true) :
    witnessRunSupported p (front ++ back) = true := by
  induction front generalizing p with
  | nil => exact second
  | cons cmd rest ih =>
      rw [witnessRunSupported] at first
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp first
      have second' :
          witnessRunSupported (projectedRun (witnessStep p cmd) rest) back = true := by
        simpa only [projectedRun] using second
      rw [List.cons_append, witnessRunSupported, head, Bool.true_and]
      exact ih (witnessStep p cmd) tail second'

end JuliaLean.CRuntime.WorldStop
