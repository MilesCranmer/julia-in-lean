import JuliaLean.IOBuffers.Props

/-!
Counterexamples to the refuted `IOBuffer` properties. Each is replayed by
`repro/<id>.jl`.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

theorem reachable_mk (c : Ctor) (ops : List Op) (hc : c.ok) (ho : ∀ o ∈ ops, Op.ok o)
    (hw : (ops.map Op.weight).sum ≤ bound) (io0 : IOBuf) (hb : c.build = .ok io0) :
    Reachable (finalState ops io0) :=
  ⟨c, ops, io0, hc, hb, ho, hw, rfl⟩

/-- `IOBuffer()`. -/
abbrev ctorDefault : Ctor := .empty (some true) (some true) none (some true) (2 ^ 63 - 1) none

theorem ctorDefault_ok : ctorDefault.ok := ⟨by decide, by decide, fun _ hs => nomatch hs⟩

/-- `PipeBuffer()`. -/
abbrev ctorPipe : Ctor := .pipe (.mem []) (2 ^ 63 - 1)

theorem ctorPipe_ok : ctorPipe.ok := ⟨by simp [DataArg.ok], by decide, by decide⟩

theorem ops_ok_of {ops : List Op} (h : ops.all (fun o => match o with
    | .writeBytes bs => decide (bs.length ≤ bound) | .readN n => decide (isInt n)
    | .readBang n => decide (n ≤ bound) | .readbytes n => decide (isInt n)
    | .truncate n => decide (isInt n) | .copyline _ _ => false | _ => true) = true) :
    ∀ o ∈ ops, Op.ok o := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  cases o <;> simp_all [Op.ok] <;> exact this

/-- `truncate(io, 3)` with the mark at 3 clears the mark. -/
theorem truncateKeepsMark_refuted : ¬ TruncateKeepsMark := by
  intro h
  have hr := reachable_mk ctorDefault [.writeBytes [97, 98, 99, 100, 101, 102], .seek 3, .mark]
    ctorDefault_ok (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl 3 (by decide) rfl (by decide) (by decide)
  revert this; decide

/-- `take!` on a `PipeBuffer` after `closewrite` throws `ErrorException`. -/
theorem takeReadOnly_refuted : ¬ TakeReadOnly := by
  intro h
  have hr := reachable_mk ctorPipe [.writeBytes [97, 98, 99], .closewrite]
    ctorPipe_ok (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl rfl rfl
  revert this; decide

/-- `take!(IOBuffer("abc"))` after reading one byte leaves the position at 1. -/
theorem takeResets_refuted : ¬ TakeResets := by
  intro h
  have hr := reachable_mk (.str [97, 98, 99]) [.readByte]
    (by simp [Ctor.ok, bound]) (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl rfl ⟨_, rfl⟩
  revert this; decide

/-- A marked `PipeBuffer`: `takestring!` returns the bytes read since the mark too. -/
theorem takestringEqTake_refuted : ¬ TakestringEqTake := by
  intro h
  have hr := reachable_mk ctorPipe [.writeBytes [97, 98, 99, 100, 101, 102], .mark, .readN 2]
    ctorPipe_ok (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl _ rfl
  revert this; decide

/-- `readuntil` on `IOBuffer(read=false)` returns data. -/
theorem readUntilUnreadable_refuted : ¬ ReadUntilUnreadable := by
  intro h
  have hr := reachable_mk (.empty (some false) (some true) none (some true) (2 ^ 63 - 1) none)
    [.writeBytes [97, 98, 10, 99, 100], .seekstart]
    ⟨by decide, by decide, fun _ hs => nomatch hs⟩
    (ops_ok_of (by decide)) (by decide) _ rfl
  obtain ⟨⟨_, hm⟩, _⟩ := h _ hr rfl 10 false
  change (Except.ok _ : Except IOErr (List UInt8)) = _ at hm
  nomatch hm

/-- `peek(io, Int8)` after `mark` removes the mark. -/
theorem peekKeepsMark_refuted : ¬ PeekKeepsMark := by
  intro h
  have hr := reachable_mk (.str [97, 98, 99]) [.mark, .readByte]
    (by simp [Ctor.ok, bound]) (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl (by decide)
  revert this; decide

/-- `copyline` of an empty line into the start of `"QQQQ"` writes `"\n"`. -/
theorem copylineMiddle_refuted : ¬ CopylineMiddle := by
  intro h
  have hr := reachable_mk ctorDefault [.writeBytes [81, 81, 81, 81], .seekstart]
    ctorDefault_ok (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl rfl rfl (by decide) (by decide) [10] (by decide) (by decide)
  revert this; decide

/-- `copyline` from an exhausted stream into `"a\n"` deletes the `"\n"`. -/
theorem copylineAtEnd_refuted : ¬ CopylineAtEnd := by
  intro h
  have hr := reachable_mk ctorDefault [.writeBytes [97, 10]]
    ctorDefault_ok (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl rfl (Or.inr (by decide)) (by decide) [] (by decide) (by decide)
  revert this; decide

/-- `IOBuffer(view(zeros(UInt8, 4), 1:4); write=true)`: writing 5 bytes throws `MethodError`. -/
theorem writeNoMethodError_refuted : ¬ WriteNoMethodError := by
  intro h
  have hr := reachable_mk (.data (.other [0, 0, 0, 0]) none (some true) none none (2 ^ 63 - 1)) []
    ⟨by simp [DataArg.ok, bound], by decide, by decide⟩ (ops_ok_of (by decide)) (by decide) _ rfl
  have := h _ hr rfl [104, 101, 108, 108, 111] (by decide) "get_used_span"
  revert this; decide

/-- `PipeBuffer(UInt8[]; maxsize=UInt(10))` throws `TypeError`. -/
theorem pipeBufferMaxsizeInteger_refuted : ¬ PipeBufferMaxsizeInteger := by
  intro h
  obtain ⟨_, hio⟩ := h .u64 10 (by decide) (by decide) (by decide) (by decide)
  change (Except.error _ : Except IOErr IOBuf) = _ at hio
  nomatch hio

end JuliaLean.IOBuffers
