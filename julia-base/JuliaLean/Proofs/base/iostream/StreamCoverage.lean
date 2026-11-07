import JuliaLean.base.iostream

namespace JuliaLean.Streams

open JuliaLean

def IOStreamLifecycleCoverage : Prop := ∀ s n delta mode bytes readable writable,
  ioCtor readable writable = ⟨[], 0, true, readable, writable⟩ ∧
  ioPointerModel n = n ∧
  (ioTruncate s n).data = (if n ≤ s.data.length then s.data.take n
    else s.data ++ List.replicate (n - s.data.length) 0) ∧
  (ioTruncate s n).position = min s.position n ∧
  ioSkip s delta = { s with position := (max 0 ((s.position : Int) + delta)).toNat } ∧
  ioClose s = { s with isopen := false } ∧
  ioBytesAvailable s = s.data.length - s.position ∧
  ioEof s = decide (ioBytesAvailable s = 0) ∧
  ioSeek s n = { s with position := n } ∧
  ioSeekEnd s = { s with position := s.data.length } ∧
  (match ioWrite s bytes with | .ok (count, _) => count = bytes.length ∨ count = 0 | .error _ => True) ∧
  parseOpenMode mode = match mode with
    | "r" => some .r | "r+" => some .rplus | "w" => some .w
    | "w+" => some .wplus | "a" => some .a | "a+" => some .aplus | _ => none

def IOStreamReadCoverage : Prop := ∀ s n d keep,
  ioReadN s n =
    (let bytes := (s.data.drop s.position).take n
     (bytes, { s with position := s.position + bytes.length })) ∧
  ioReadAvailable s = ioReadN s (s.data.length - s.position) ∧
  ioTake s = (s.data, { s with data := [], position := 0 }) ∧
  ioReadUntil s d keep =
    (let r := splitUntil d (s.data.drop s.position)
     let bytes := if r.found && keep then r.before ++ [d] else r.before
     let consumed := r.before.length + if r.found then 1 else 0
     (bytes, { s with position := s.position + consumed })) ∧
  ioReadline s keep =
    (let r := ioReadUntil s 10 keep
     if keep then r else (stripTrailingCR r.1, r.2)) ∧
  ioReadExact s n =
    (let r := ioReadN s n
     if r.1.length = n then .ok r else .error .eofError) ∧
  ioPeek s = match s.data[s.position]? with | some b => .ok b | none => .error .eofError

theorem ioStreamLifecycleCoverage_proven : IOStreamLifecycleCoverage := by
  simp [IOStreamLifecycleCoverage, ioCtor, ioPointerModel, ioTruncate, ioSkip,
    ioClose, ioBytesAvailable, ioEof, ioSeek, ioSeekEnd, ioWrite, parseOpenMode]
  intro s bytes
  by_cases hw : s.writable <;> by_cases ho : s.isopen <;> simp [hw, ho] <;>
    split <;> simp_all
theorem ioStreamReadCoverage_proven : IOStreamReadCoverage := by
  simp [IOStreamReadCoverage, ioReadN, ioReadAvailable, ioTake, ioReadUntil,
    ioReadline, ioReadExact, ioPeek]
  intro s
  cases s.data[s.position]? <;> rfl

end JuliaLean.Streams
