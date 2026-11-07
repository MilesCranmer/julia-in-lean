import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- `FormatMessage`, `base/libc.jl:395-410`: `FormatMessageW` returns the
number of UTF-16 units in its allocated result and Julia allocates the same
number of destination units. -/
def formatMessageAccesses (returnedLength : Nat) : List Access :=
  [span0 returnedLength 0 returnedLength, span0 returnedLength 0 returnedLength]

def FormatMessageInBounds : Prop :=
  ∀ n, accessesSafe (formatMessageAccesses n)

theorem formatMessageInBounds_proven : FormatMessageInBounds := by
  intro n
  simp [formatMessageAccesses, accessesSafe, Access.safe, span0]

/-- `uv_os_get_group`, `base/libc.jl:581-603`, returns a null-terminated
pointer array.  Julia loads position `length(members)+1` and stops on the
sentinel.  `some` represents a member pointer and `none` the sentinel. -/
def groupMemberAccesses (capacity : Nat) : List (Option Unit) → Nat → List Access
  | [], _ => []
  | none :: _, k => [at0 capacity k]
  | some _ :: rest, k => at0 capacity k :: groupMemberAccesses capacity rest (k + 1)

def groupMembers (members : Nat) : List (Option Unit) :=
  List.replicate members (some ()) ++ [none]

def GroupMembersInBounds : Prop :=
  ∀ members, accessesSafe (groupMemberAccesses (members + 1) (groupMembers members) 0)

private theorem groupMemberAccesses_safe (capacity : Nat) (xs : List (Option Unit)) (k : Nat)
    (h : k + xs.length ≤ capacity) : accessesSafe (groupMemberAccesses capacity xs k) := by
  induction xs generalizing k with
  | nil => simp [groupMemberAccesses, accessesSafe]
  | cons head rest ih =>
      cases head with
      | none =>
          simp only [List.length_cons] at h
          simp only [groupMemberAccesses, accessesSafe, List.mem_singleton, forall_eq,
            Access.safe, at0]
          omega
      | some _ =>
          simp only [List.length_cons] at h
          simp only [groupMemberAccesses, accessesSafe, List.mem_cons, forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            omega
          · apply ih
            omega

theorem groupMembersInBounds_proven : GroupMembersInBounds := by
  intro members
  apply groupMemberAccesses_safe
  simp [groupMembers]

def LibcBuffersInBounds : Prop := FormatMessageInBounds ∧ GroupMembersInBounds

theorem libcBuffersInBounds_proven : LibcBuffersInBounds :=
  ⟨formatMessageInBounds_proven, groupMembersInBounds_proven⟩

end JuliaLean.MemSafety.G1
