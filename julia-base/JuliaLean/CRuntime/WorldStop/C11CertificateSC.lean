import JuliaLean.CRuntime.WorldStop.C11CertificateAtomic

namespace JuliaLean.CRuntime.WorldStop

open Memory
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false
namespace SD
abbrev scIds := C11CertificateData.scIds
abbrev scReadFromPairs := C11CertificateData.scReadFromPairs
abbrev atomicWriteIds := C11CertificateData.atomicWriteIds
abbrev readFromPairs := C11CertificateData.readFromPairs
abbrev readFromPairBlocks := C11CertificateData.readFromPairBlocks
abbrev scFenceIds := C11CertificateData.scFenceIds
end SD

def scWrite48 : canonicalCandidate.Id := certificateId 48 (by decide)
def scFence55 : canonicalCandidate.Id := certificateId 55 (by decide)

theorem sc_sequencedBefore_forward (first second : canonicalCandidate.Id)
    (edge : canonicalCandidate.sequencedBefore first second = true) :
    first.val < second.val := by
  simp only [Memory.Candidate.sequencedBefore, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at edge
  exact edge.2

theorem canonicalCandidate_uniqueSC :
    ∀ i j : canonicalCandidate.Id,
      (canonicalCandidate.event i).action.isSC = true →
      (canonicalCandidate.event j).action.isSC = true →
      (canonicalCandidate.event i).sc = (canonicalCandidate.event j).sc → i = j := by
  intro i j scI scJ sameRank
  have memberI := (isSC_iff_mem i).mp scI
  have memberJ := (isSC_iff_mem j).mp scJ
  have rankI := scRank_of_sc i scI
  have rankJ := scRank_of_sc j scJ
  simp [C11CertificateData.scIds] at memberI
  simp [C11CertificateData.scIds] at memberJ
  rcases memberI with valueI | valueI | valueI <;>
    rcases memberJ with valueJ | valueJ | valueJ <;>
    apply Fin.ext <;>
    simp [C11CertificateData.scRank, valueI, valueJ] at rankI rankJ <;>
    omega

theorem scAtomicWrite_eq_48 (event : canonicalCandidate.Id)
    (writing : canonicalCandidate.isAtomicWrite event = true)
    (sc : (canonicalCandidate.event event).action.isSC = true) : event = scWrite48 := by
  have writeMember := (isAtomicWrite_iff_mem event).mp writing
  have scMember := (isSC_iff_mem event).mp sc
  have value : event.val = 48 := by
    simp [C11CertificateData.atomicWriteIds] at writeMember
    simp [C11CertificateData.scIds] at scMember
    omega
  apply Fin.ext
  exact value

theorem scFence_eq_55 (event : canonicalCandidate.Id)
    (fence : (canonicalCandidate.event event).action.isFence = true) :
    event = scFence55 := by
  have member := (isFence_iff_mem event).mp fence
  have value : event.val = 55 := by
    simpa [C11CertificateData.scFenceIds] using member
  apply Fin.ext
  exact value

def scReadFromCoverageCheck : Bool :=
  SD.readFromPairs.all fun pair =>
    decide (pair.1 ∈ SD.scIds → pair ∈ SD.scReadFromPairs)

def scReadFromBoundsCheck : Bool := pairBoundsCheck SD.scReadFromPairs

theorem scReadFromCoverageCheck_true : scReadFromCoverageCheck = true := by decide
theorem scReadFromBoundsCheck_true : scReadFromBoundsCheck = true := by decide

theorem sc_readFrom_pair (read source : canonicalCandidate.Id)
    (sc : (canonicalCandidate.event read).action.isSC = true)
    (rf : canonicalCandidate.readSource read source = true) :
    (read.val, source.val) ∈ SD.scReadFromPairs := by
  have pairMember := (readSource_iff_mem read source).mp rf
  have readMember := (isSC_iff_mem read).mp sc
  have check := scReadFromCoverageCheck_true
  unfold scReadFromCoverageCheck at check
  have row := (List.all_eq_true.mp check) (read.val, source.val) pairMember
  exact (of_decide_eq_true row) readMember

theorem gcRunning_atomicRead_eq_48 (read : canonicalCandidate.Id)
    (atomic : canonicalCandidate.isAtomicRead read = true)
    (same : canonicalCandidate.sameLocation scWrite48 read = true) :
    read = scWrite48 := by
  have writeLocation : (canonicalCandidate.event scWrite48).action.location =
      some .gcRunning :=
    (gcRunningLocation_iff scWrite48).mpr (by decide)
  simp only [Memory.Candidate.sameLocation, Bool.and_eq_true, beq_iff_eq] at same
  have readLocation : (canonicalCandidate.event read).action.location =
      some .gcRunning := by
    rw [← same.2]
    exact writeLocation
  have locationMember := (gcRunningLocation_iff read).mp readLocation
  have readMember := (isAtomicRead_iff_mem read).mp atomic
  simp [C11CertificateData.gcRunningAccessIds] at locationMember
  simp [C11CertificateData.atomicReadIds] at readMember
  have value : read.val = 48 := by omega
  apply Fin.ext
  exact value

theorem canonicalCandidate_sc :
    scAgainst canonicalCandidate (eventEarlier canonicalCandidate) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro first scFirst second scSecond order
    have firstMember := (isSC_iff_mem first).mp scFirst
    have secondMember := (isSC_iff_mem second).mp scSecond
    have rankFirst := scRank_of_sc first scFirst
    have rankSecond := scRank_of_sc second scSecond
    rcases order with earlier | modification
    · have idOrder : first.val < second.val := by
        simpa [eventEarlier] using earlier
      simp [C11CertificateData.scIds] at firstMember secondMember
      rcases firstMember with firstId | firstId | firstId <;>
        rcases secondMember with secondId | secondId | secondId <;>
        simp [C11CertificateData.scRank, firstId, secondId] at rankFirst rankSecond <;>
        omega
    · simp only [Memory.Candidate.modificationBefore, Bool.and_eq_true,
        decide_eq_true_eq] at modification
      rcases modification with ⟨⟨⟨firstWriting, secondWriting⟩, _⟩, lower⟩
      have firstEq := scAtomicWrite_eq_48 first firstWriting scFirst
      have secondEq := scAtomicWrite_eq_48 second secondWriting scSecond
      subst first
      subst second
      exact (Nat.lt_irrefl _ lower).elim
  · intro read readSC atomic source rf
    have pairMember := sc_readFrom_pair read source readSC rf
    have sourceNotSC : (canonicalCandidate.event source).action.isSC = false := by
      cases sourceSC : (canonicalCandidate.event source).action.isSC with
      | false => rfl
      | true =>
        have sourceMember := (isSC_iff_mem source).mp sourceSC
        simp [C11CertificateData.scReadFromPairs,
          C11CertificateData.scIds] at pairMember sourceMember
        omega
    rw [sourceNotSC]
    intro event writing eventSC same before
    have eventEq := scAtomicWrite_eq_48 event writing eventSC
    subst event
    simp [C11CertificateData.scReadFromPairs] at pairMember
    rcases pairMember with firstPair | secondPair
    · have readValue := firstPair.1
      have sourceValue := firstPair.2
      have readEq : read = certificateId 31 (by decide) := Fin.ext readValue
      have sourceEq : source = certificateId 12 (by decide) := Fin.ext sourceValue
      rw [readEq] at same
      rw [sourceEq]
      have impossible : canonicalCandidate.sameLocation scWrite48
          (certificateId 31 (by decide)) = false := by decide
      rw [impossible] at same
      contradiction
    · have readValue := secondPair.1
      have sourceValue := secondPair.2
      have readEq : read = certificateId 48 (by decide) := Fin.ext readValue
      have sourceEq : source = certificateId 0 (by decide) := Fin.ext sourceValue
      rw [readEq] at before
      rw [sourceEq]
      have sameEvent : certificateId 48 (by decide) = scWrite48 := by apply Fin.ext; rfl
      rw [sameEvent] at before
      exact (Nat.lt_irrefl _ before).elim
  · intro event writing eventSC read atomic same source rf fence fenceAction fenceSC rank before
    have eventEq := scAtomicWrite_eq_48 event writing eventSC
    have fenceEq := scFence_eq_55 fence fenceAction
    subst event
    subst fence
    have readEq := gcRunning_atomicRead_eq_48 read atomic same
    subst read
    have impossible := sc_sequencedBefore_forward
      scFence55 scWrite48 before
    change (55 : Nat) < 48 at impossible
    omega
  · intro read atomic readSC event writing same source rf fence fenceAction fenceSC before rank
    have fenceEq := scFence_eq_55 fence fenceAction
    subst fence
    have readMember := (isSC_iff_mem read).mp readSC
    have atomicMember := (isAtomicRead_iff_mem read).mp atomic
    have readRank := scRank_of_sc read readSC
    have fenceRank := scRank_of_sc scFence55 (by decide)
    change (canonicalCandidate.event scFence55).sc = 2 at fenceRank
    simp [C11CertificateData.scIds] at readMember
    simp [C11CertificateData.atomicReadIds] at atomicMember
    rcases readMember with readId | readId | readId <;>
      simp [C11CertificateData.scRank, readId] at readRank <;>
      omega
  · intro event writing read atomic same source rf first firstFence firstSC beforeFirst
      second secondFence secondSC beforeSecond rank
    have firstEq := scFence_eq_55 first firstFence
    have secondEq := scFence_eq_55 second secondFence
    subst first
    subst second
    exact (Nat.lt_irrefl _ rank).elim

end JuliaLean.CRuntime.WorldStop
