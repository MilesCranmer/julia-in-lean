import JuliaLean.Core

namespace JuliaLean.MemSafety.G5

/-! ## `base/toml/parser.jl` -/

/-- A byte range recorded by `parse_string_continue` at parser.jl:1383-1413.
The scanner cursor ensures that every chunk lies in `l.str`. -/
structure TomlChunk (sourceLength : Nat) where
  start : Nat
  length : Nat
  sourceFits : start + length ≤ sourceLength

/-- The relevant Parser fields passed from public `parse` and `tryparse` paths
to `take_chunks`. -/
structure TomlChunkState where
  sourceLength : Nat
  chunks : List (TomlChunk sourceLength)

structure CopySpan where
  sourceStart : Nat
  destStart : Nat
  count : Nat

/-- The copy loop at parser.jl:1447-1459. `destStart` is the source's
one-based `offset` normalized to a zero-based byte offset. -/
def takeChunkCopiesFrom {sourceLength : Nat} :
    Nat → List (TomlChunk sourceLength) → List CopySpan
  | _, [] => []
  | dest, chunk :: rest =>
    ⟨chunk.start, dest, chunk.length⟩ ::
      takeChunkCopiesFrom (dest + chunk.length) rest

def takeChunkCopies (state : TomlChunkState) : List CopySpan :=
  takeChunkCopiesFrom 0 state.chunks

def takeChunkDestinationLength (state : TomlChunkState) : Nat :=
  (state.chunks.map (·.length)).sum

/-- Each source span is within `l.str`; each destination span is within the
string allocated from `sum(length, l.chunks)`. -/
def TomlTakeChunksAccessesInBounds : Prop :=
  ∀ state span, span ∈ takeChunkCopies state →
    span.sourceStart + span.count ≤ state.sourceLength ∧
    span.destStart + span.count ≤ takeChunkDestinationLength state

private theorem takeChunkCopiesFrom_safe {sourceLength : Nat} :
    ∀ (chunks : List (TomlChunk sourceLength)) dest span,
      span ∈ takeChunkCopiesFrom dest chunks →
      span.sourceStart + span.count ≤ sourceLength ∧
      span.destStart + span.count ≤
        dest + (chunks.map (fun chunk : TomlChunk sourceLength => chunk.length)).sum
  | [], _, _, h => by simp [takeChunkCopiesFrom] at h
  | chunk :: rest, dest, span, h => by
      simp only [takeChunkCopiesFrom, List.mem_cons] at h
      rcases h with rfl | h
      · constructor
        · exact chunk.sourceFits
        · simp
      · have ih := takeChunkCopiesFrom_safe rest (dest + chunk.length) span h
        constructor
        · exact ih.1
        · simp only [List.map_cons, List.sum_cons]
          omega

theorem tomlTakeChunksAccessesInBounds : TomlTakeChunksAccessesInBounds := by
  intro state span h
  have hs := takeChunkCopiesFrom_safe state.chunks 0 span h
  simpa [takeChunkCopies, takeChunkDestinationLength] using hs


end JuliaLean.MemSafety.G5
