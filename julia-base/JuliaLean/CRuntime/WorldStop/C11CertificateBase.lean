import JuliaLean.CRuntime.WorldStop.Candidate

namespace JuliaLean.CRuntime.WorldStop

open Memory

def coherentAgainst (c : Memory.Candidate Loc Nat) (relation : c.Id → c.Id → Bool) : Prop :=
  (∀ i : c.Id, relation i i = false) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true → ∀ b : c.Id,
    c.isAtomicWrite b = true → c.sameLocation a b = true →
    c.modificationBefore a b = false → relation a b = false) ∧
  (∀ write : c.Id, c.isAtomicWrite write = true → ∀ read : c.Id,
    c.isAtomicRead read = true → c.sameLocation write read = true →
    relation write read = true → ∀ source : c.Id,
    c.readSource read source = true → (c.event write).mo ≤ (c.event source).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → ∀ write : c.Id,
    c.isAtomicWrite write = true → c.sameLocation read write = true →
    relation read write = true → ∀ source : c.Id,
    c.readSource read source = true → (c.event source).mo < (c.event write).mo) ∧
  (∀ a : c.Id, c.isAtomicRead a = true → ∀ b : c.Id,
    c.isAtomicRead b = true → c.sameLocation a b = true →
    relation a b = true → ∀ x : c.Id, c.readSource a x = true →
    ∀ y : c.Id, c.readSource b y = true → (c.event x).mo ≤ (c.event y).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → ∀ source : c.Id,
    c.readSource read source = true → relation read source = false)

def scAgainst (c : Memory.Candidate Loc Nat) (relation : c.Id → c.Id → Bool) : Prop :=
  (∀ a : c.Id, (c.event a).action.isSC = true →
    ∀ b : c.Id, (c.event b).action.isSC = true →
    (relation a b = true ∨ c.modificationBefore a b = true) →
      (c.event a).sc < (c.event b).sc) ∧
  (∀ read : c.Id, (c.event read).action.isSC = true → c.isAtomicRead read = true →
    ∀ source : c.Id, c.readSource read source = true →
      (if (c.event source).action.isSC then
        (c.event source).sc < (c.event read).sc ∧
        ∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
          c.sameLocation a read = true → (c.event a).sc < (c.event read).sc →
            (c.event a).sc ≤ (c.event source).sc
       else ∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
         c.sameLocation a read = true → (c.event a).sc < (c.event read).sc →
           relation source a = false)) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true → (c.event a).action.isSC = true →
    ∀ read : c.Id, c.isAtomicRead read = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      (c.event a).sc < (c.event x).sc → c.sequencedBefore x read = true →
        (c.event a).mo ≤ (c.event source).mo) ∧
  (∀ read : c.Id, c.isAtomicRead read = true → (c.event read).action.isSC = true →
    ∀ a : c.Id, c.isAtomicWrite a = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      c.sequencedBefore a x = true → (c.event x).sc < (c.event read).sc →
        (c.event a).mo ≤ (c.event source).mo) ∧
  (∀ a : c.Id, c.isAtomicWrite a = true →
    ∀ read : c.Id, c.isAtomicRead read = true → c.sameLocation a read = true →
    ∀ source : c.Id, c.readSource read source = true →
    ∀ x : c.Id, (c.event x).action.isFence = true → (c.event x).action.isSC = true →
      c.sequencedBefore a x = true →
    ∀ y : c.Id, (c.event y).action.isFence = true → (c.event y).action.isSC = true →
      c.sequencedBefore y read = true → (c.event x).sc < (c.event y).sc →
        (c.event a).mo ≤ (c.event source).mo)

def raceAgainst (c : Memory.Candidate Loc Nat) (relation : c.Id → c.Id → Bool) : Prop :=
  ∀ a b : c.Id, a ≠ b → c.sameLocation a b = true →
    ((c.event a).action.isPlain = true ∨ (c.event b).action.isPlain = true) →
    (c.isWrite a = true ∨ c.isWrite b = true) →
    relation a b = true ∨ relation b a = true

def eventEarlier (c : Memory.Candidate Loc Nat) (a b : c.Id) : Bool :=
  decide (a.val < b.val)

def ChronologicalCertificate (c : Memory.Candidate Loc Nat) : Prop :=
  c.WellFormed ∧
  (∀ a b : c.Id, c.hbEdge a b = true → a.val < b.val) ∧
  coherentAgainst c (eventEarlier c) ∧ c.RMWAtomicity ∧
  scAgainst c (eventEarlier c) ∧ c.MutexValid ∧
  (∀ read source : c.Id, c.readSource read source = true → source.val < read.val) ∧
  (∀ read : c.Id, ∀ dep ∈ (c.event read).dependsOn, dep < read.val) ∧
  raceAgainst c c.hbEdge ∧
  (∀ read source : c.Id, (c.event read).action.isPlain = true → c.isRead read = true →
    c.readSource read source = true → c.hbEdge source read = true ∧
      ∀ other : c.Id, c.isWrite other = true → c.sameLocation read other = true →
        ¬(eventEarlier c source other = true ∧ eventEarlier c other read = true))

set_option synthInstance.maxSize 65536 in
instance (c : Memory.Candidate Loc Nat) : Decidable (ChronologicalCertificate c) := by
  unfold ChronologicalCertificate coherentAgainst scAgainst raceAgainst
    Memory.Candidate.WellFormed Memory.Candidate.ReadFromTyped
    Memory.Candidate.RMWAtomicity Memory.Candidate.MutexValid
  infer_instance

theorem chronologicalCertificate_defined (c : Memory.Candidate Loc Nat)
    (certificate : ChronologicalCertificate c) : c.Defined := by
  rcases certificate with ⟨wf, edges, co, rmw, sc, mutex, rfForward, depsForward, races, ordinary⟩
  have hbForward (a b : c.Id) (h : c.happensBefore a b = true) : a.val < b.val :=
    Memory.Candidate.closure_rank (fun i : c.Id => i.val) edges h
  have hbSubset (a b : c.Id) (h : c.happensBefore a b = true) :
      eventEarlier c a b = true := by
    simp [eventEarlier, hbForward a b h]
  have hbFalse (a b : c.Id) (h : eventEarlier c a b = false) :
      c.happensBefore a b = false := by
    cases actual : c.happensBefore a b with
    | false => rfl
    | true =>
      have impossible := hbSubset a b actual
      rw [h] at impossible
      cases impossible
  have coherent : c.Coherent := by
    change coherentAgainst c c.happensBefore
    rcases co with ⟨irreflexive, writes, wr, rw, reads, reverseRF⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      exact hbFalse a a (irreflexive a)
    · intro a ha b hb same order
      exact hbFalse a b (writes a ha b hb same order)
    · intro write hw read hr same hb source rf
      exact wr write hw read hr same (hbSubset write read hb) source rf
    · intro read hr write hw same hb source rf
      exact rw read hr write hw same (hbSubset read write hb) source rf
    · intro a ha b hb same order x hx y hy
      exact reads a ha b hb same (hbSubset a b order) x hx y hy
    · intro read atomic source rf
      exact hbFalse read source (reverseRF read atomic source rf)
  have sequentiallyConsistent : c.SCConsistent := by
    change scAgainst c c.happensBefore
    rcases sc with ⟨orders, loads, writeFence, readFence, fences⟩
    refine ⟨?_, ?_, writeFence, readFence, fences⟩
    · intro a ha b hb order
      apply orders a ha b hb
      rcases order with before | modification
      · exact Or.inl (hbSubset a b before)
      · exact Or.inr modification
    · intro read hr atomic source rf
      have h := loads read hr atomic source rf
      cases sourceSC : (c.event source).action.isSC with
      | false =>
        simp [sourceSC] at h ⊢
        intro a ha hsc same before
        exact hbFalse source a (h a ha hsc same before)
      | true => simpa [sourceSC] using h
  have justified : c.Justified := by
    apply Memory.Candidate.justified_of_forward
    intro a b edge
    simp only [Memory.Candidate.justificationEdge, Bool.or_eq_true_iff, or_assoc] at edge
    rcases edge with rf | dependency | writes
    · exact rfForward b a rf
    · exact depsForward b a.val (of_decide_eq_true dependency)
    · simp only [Bool.and_eq_true_iff, and_assoc] at writes
      exact hbForward a b writes.2.2.2
  have raceFree : c.RaceFree := by
    intro a b distinct same plain write
    rcases races a b distinct same plain write with forward | reverse
    · exact Or.inl (Memory.Candidate.happensBefore_of_hbEdge forward)
    · exact Or.inr (Memory.Candidate.happensBefore_of_hbEdge reverse)
  have visible : c.OrdinaryVisible := by
    intro read source plain reading rf
    rcases ordinary read source plain reading rf with ⟨edge, last⟩
    refine ⟨Memory.Candidate.happensBefore_of_hbEdge edge, ?_⟩
    intro other write same between
    exact last other write same
      ⟨hbSubset source other between.1, hbSubset other read between.2⟩
  exact ⟨⟨wf, coherent, rmw, sequentiallyConsistent, mutex, justified⟩, raceFree, visible⟩

theorem candidate_defined_true (c : Memory.Candidate Loc Nat) (h : c.Defined) :
    c.defined = true := by
  simpa [Memory.Candidate.defined, Memory.Candidate.consistent,
    Memory.Candidate.dataRaceFree, Memory.Candidate.Defined, Bool.and_eq_true, and_assoc] using h

end JuliaLean.CRuntime.WorldStop
