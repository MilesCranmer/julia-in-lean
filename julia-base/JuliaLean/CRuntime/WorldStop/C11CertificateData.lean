import JuliaLean.CRuntime.WorldStop.Candidate

namespace JuliaLean.CRuntime.WorldStop.C11CertificateData

open Memory

def initializerIds : List Nat := List.range 20

def concurrentIds : List Nat := (List.range 68).map (fun id => id + 20)

def allEventIds : List Nat := List.range 88

def atomicReadIds : List Nat :=
  [20, 21, 23, 26, 31, 32, 34, 35, 37, 40, 42, 43, 45, 47, 48, 49,
   56, 58, 61, 62, 64, 65, 67, 68, 69, 70, 71, 73, 76, 77, 80]

def atomicWriteIds : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
   18, 19, 27, 30, 38, 44, 48, 78, 81, 82]

def plainReadIds : List Nat := [22, 28, 50, 52, 60, 63, 66, 72, 83]

def plainWriteIds : List Nat := [29, 51, 53, 57, 59, 84]

def readIds : List Nat := atomicReadIds ++ plainReadIds

def plainAccessIds : List Nat := plainReadIds ++ plainWriteIds

def writeIds : List Nat := atomicWriteIds ++ plainWriteIds

def accessIds : List Nat :=
  (((atomicReadIds ++ atomicWriteIds) ++ plainReadIds) ++ plainWriteIds).eraseDups

def accessIdBlocks : List (List Nat) :=
  (List.range 19).map fun block => (accessIds.drop (block * 4)).take 4

def nonInitAtomicWriteIds : List Nat := [27, 30, 38, 44, 48, 78, 81, 82]

def readFromPairs : List (Nat × Nat) :=
  [(20, 2), (21, 3), (22, 15), (23, 11), (26, 10), (28, 19),
   (31, 12), (32, 13), (34, 27), (35, 5), (37, 6), (40, 8),
   (42, 1), (43, 4), (45, 44), (47, 9), (48, 0), (49, 1),
   (50, 17), (52, 18), (56, 2), (58, 3), (60, 14), (61, 44),
   (62, 44), (63, 15), (64, 5), (65, 5), (66, 16), (67, 38),
   (68, 38), (69, 1), (70, 2), (71, 3), (72, 15), (73, 11),
   (76, 27), (77, 5), (80, 30), (83, 29)]

def readFromPairBlocks : List (List (Nat × Nat)) :=
  (List.range 10).map fun block => (readFromPairs.drop (block * 4)).take 4

def atomicInitializerPairs : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6),
   (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13),
   (14, 14), (15, 15), (16, 16), (17, 17), (18, 18), (19, 19),
   (20, 2), (21, 3), (23, 11), (26, 10), (27, 10), (30, 7),
   (31, 12), (32, 13), (34, 10), (35, 5), (37, 6), (38, 6), (40, 8),
   (42, 1), (43, 4), (44, 4), (45, 4), (47, 9), (48, 0), (49, 1),
   (56, 2), (58, 3), (61, 4), (62, 4), (64, 5), (65, 5), (67, 6),
   (68, 6), (69, 1), (70, 2), (71, 3), (73, 11), (76, 10), (77, 5),
   (78, 5), (80, 7), (81, 7), (82, 10)]

def scIds : List Nat := [31, 48, 55]

def scReadFromPairs : List (Nat × Nat) := [(31, 12), (48, 0)]

def scAtomicWriteIds : List Nat := [48]

def scFenceIds : List Nat := [55]

def successfulRMWIds : List Nat := [48]

def scRank : Nat → Nat
  | 31 => 0
  | 48 => 1
  | 55 => 2
  | _ => 0

def gcRunningAccessIds : List Nat := [0, 48]

def eventLocation : Nat → Option Loc
  | 0 => some .gcRunning
  | 1 => some .disableCounter
  | 2 => some .nThreads
  | 3 => some .allTLS
  | 4 => some (.gcState 1)
  | 5 => some (.gcState 2)
  | 6 => some (.gcState 3)
  | 7 => some (.safepoint 2)
  | 8 => some (.safepoint 3)
  | 9 => some (.suspendCount 1)
  | 10 => some (.suspendCount 2)
  | 11 => some (.currentTask 2)
  | 12 => some .threadedRegion
  | 13 => some .ioLoopTid
  | 14 => some (.tlsSlot 1 0)
  | 15 => some (.tlsSlot 1 1)
  | 16 => some (.tlsSlot 1 2)
  | 17 => some (.pageCount 1)
  | 18 => some (.pageCount 2)
  | 19 => some (.pageCount 3)
  | 20 => some .nThreads
  | 21 => some .allTLS
  | 22 => some (.tlsSlot 1 1)
  | 23 => some (.currentTask 2)
  | 26 => some (.suspendCount 2)
  | 27 => some (.suspendCount 2)
  | 28 => some (.pageCount 3)
  | 29 => some (.pageCount 3)
  | 30 => some (.safepoint 2)
  | 31 => some .threadedRegion
  | 32 => some .ioLoopTid
  | 34 => some (.suspendCount 2)
  | 35 => some (.gcState 2)
  | 37 => some (.gcState 3)
  | 38 => some (.gcState 3)
  | 40 => some (.safepoint 3)
  | 42 => some .disableCounter
  | 43 => some (.gcState 1)
  | 44 => some (.gcState 1)
  | 45 => some (.gcState 1)
  | 47 => some (.suspendCount 1)
  | 48 => some .gcRunning
  | 49 => some .disableCounter
  | 50 => some (.pageCount 1)
  | 51 => some (.pageCount 1)
  | 52 => some (.pageCount 2)
  | 53 => some (.pageCount 2)
  | 56 => some .nThreads
  | 57 => some .gcNThreads
  | 58 => some .allTLS
  | 59 => some .gcAllTLS
  | 60 => some (.tlsSlot 1 0)
  | 61 => some (.gcState 1)
  | 62 => some (.gcState 1)
  | 63 => some (.tlsSlot 1 1)
  | 64 => some (.gcState 2)
  | 65 => some (.gcState 2)
  | 66 => some (.tlsSlot 1 2)
  | 67 => some (.gcState 3)
  | 68 => some (.gcState 3)
  | 69 => some .disableCounter
  | 70 => some .nThreads
  | 71 => some .allTLS
  | 72 => some (.tlsSlot 1 1)
  | 73 => some (.currentTask 2)
  | 76 => some (.suspendCount 2)
  | 77 => some (.gcState 2)
  | 78 => some (.gcState 2)
  | 80 => some (.safepoint 2)
  | 81 => some (.safepoint 2)
  | 82 => some (.suspendCount 2)
  | 83 => some (.pageCount 3)
  | 84 => some (.pageCount 3)
  | _ => none

def eventMO : Nat → Nat
  | 27 | 30 | 38 | 44 | 48 | 78 => 1
  | 81 | 82 => 2
  | _ => 0

def eventThread (id : Nat) : Nat :=
  if id < 20 then 0
  else if id < 42 then 2
  else if id < 70 then 0
  else if id < 77 then 2
  else if id < 81 then 1
  else if id < 87 then 2
  else 1

def lockMutex : Nat → Nat
  | 24 | 46 | 74 => 0
  | 25 | 75 => 6
  | _ => 0

def unlockMutex : Nat → Nat
  | 33 | 85 => 6
  | 36 | 54 | 86 => 0
  | _ => 0

def mutexPartnerPairs : List (Nat × Nat) :=
  [(24, 36), (25, 33), (46, 54), (74, 86), (75, 85)]

def unlockForLock : Nat → Nat
  | 24 => 36
  | 25 => 33
  | 46 => 54
  | 74 => 86
  | 75 => 85
  | _ => 0

def lockForUnlock : Nat → Nat
  | 33 => 25
  | 36 => 24
  | 54 => 46
  | 85 => 75
  | 86 => 74
  | _ => 0

def mutexIds : List Nat := [0, 6]

def lockIds : List Nat := [24, 25, 46, 74, 75]

def unlockIds : List Nat := [33, 36, 54, 85, 86]

def ordinaryConflictPairs : List (Nat × Nat) :=
  [(14, 60), (15, 22), (15, 63), (15, 72), (16, 66), (17, 50),
   (17, 51), (18, 52), (18, 53), (19, 28), (19, 29), (19, 83),
   (19, 84), (28, 29), (28, 84), (29, 83), (29, 84), (50, 51),
   (52, 53), (83, 84)]

def dependencyEventIds : List Nat :=
  (List.range 21).map (fun i => i + 21) ++
  (List.range 34).map (fun i => i + 43) ++
  (List.range 9).map (fun i => i + 79)

def dependencySourceIds : List Nat :=
  [20, 21, 22, 23, 26, 28, 31, 32, 34, 35, 37, 42, 47, 48, 49, 50,
   52, 56, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 70, 71, 72, 73,
   76, 77, 83]

def synchronizesWithPairs : List (Nat × Nat) :=
  [(33, 75), (36, 46), (38, 68), (44, 62), (54, 74)]

set_option maxHeartbeats 2000000 in
theorem canonicalCandidate_eventCount : canonicalCandidate.events.size = 88 := by decide

theorem event48_atomicRead : 48 ∈ atomicReadIds := by decide

theorem event48_readFrom0 : (48, 0) ∈ readFromPairs := by decide

theorem event38_synchronizesWith68 : (38, 68) ∈ synchronizesWithPairs := by decide

theorem events19_83_conflict : (19, 83) ∈ ordinaryConflictPairs := by decide

theorem initializerIds_exact (id : Nat) : id ∈ initializerIds ↔ id < 20 := by
  simp [initializerIds]

theorem concurrentIds_exact (id : Nat) : id ∈ concurrentIds ↔ 20 ≤ id ∧ id < 88 := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    have sourceBound := List.mem_range.mp sourceMember
    omega
  · intro bounds
    apply List.mem_map.mpr
    refine ⟨id - 20, List.mem_range.mpr ?_, ?_⟩
    · omega
    · omega

end JuliaLean.CRuntime.WorldStop.C11CertificateData
