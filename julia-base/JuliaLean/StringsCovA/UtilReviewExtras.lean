import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.UtilRebuilt
import JuliaLean.StringUtil.Pad

namespace JuliaLean.StringsCovA.UtilReviewExtras

open JuliaLean JuliaLean.Strings JuliaLean.Registry

inductive IOEvent where
  | mark | readChar | readBytes (count : Nat) | reset | convertString | delegate
  deriving Repr, DecidableEq

structure IOResult where
  result : Bool
  events : List IOEvent
  remaining : List UInt8
  deriving Repr, DecidableEq

def startsCharsIO (unread : List UInt8) (decoded : UInt32) (chars : List UInt32) : IOResult :=
  ⟨chars.contains decoded, [.mark, .readChar, .reset], unread⟩

def P93 : Prop := ∀ unread decoded chars,
  let output := startsCharsIO unread decoded chars
  output.events = [.mark, .readChar, .reset] ∧ output.remaining = unread ∧
    output.result = chars.contains decoded
theorem p93 : P93 := by unfold P93; intros; exact ⟨rfl, rfl, rfl⟩

def startsUtf8IO (unread pre : List UInt8) : IOResult :=
  let count := pre.length
  ⟨unread.take count == pre, [.mark, .readBytes count, .reset], unread⟩

def P99 : Prop := ∀ unread pre,
  let output := startsUtf8IO unread pre
  output.events = [.mark, .readBytes pre.length, .reset] ∧ output.remaining = unread ∧
    output.result = (unread.take pre.length == pre)
theorem p99 : P99 := by unfold P99; intros; exact ⟨rfl, rfl, rfl⟩

def startsAbstractIO (toString : A → List UInt8) (unread : List UInt8) (pre : A) : IOResult :=
  let concrete := toString pre
  let delegated := startsUtf8IO unread concrete
  { delegated with events := [.convertString, .delegate] ++ delegated.events }

def P105 : Prop := ∀ (A : Type) toString unread (pre : A),
  (startsAbstractIO toString unread pre).events =
    [.convertString, .delegate, .mark, .readBytes (toString pre).length, .reset] ∧
  (startsAbstractIO toString unread pre).remaining = unread
theorem p105 : P105 := by unfold P105; intros; exact ⟨rfl, rfl⟩

structure EndsCharsResult where
  checkedEmpty : Bool
  readLast : Bool
  result : Bool
  deriving Repr, DecidableEq

def endsChars (source chars : List UInt32) : EndsCharsResult :=
  match source with
  | [] => ⟨true, false, false⟩
  | _ :: _ => ⟨true, true, chars.contains (source.reverse.headD 0)⟩

def P67 : Prop := ∀ source chars,
  (endsChars source chars).checkedEmpty = true ∧
  ((endsChars source chars).readLast = true ↔ source ≠ [])
theorem p67 : P67 := by
  unfold P67
  intro source chars
  cases source <;> simp [endsChars]

structure CharSlice where
  source : List UInt32
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq

def chopPrefixChar (source : List UInt32) (character : UInt32) : CharSlice :=
  if source.isEmpty then ⟨source, 0, source.length⟩
  else if source.headD 0 == character then ⟨source, 1, source.length⟩
  else ⟨source, 0, source.length⟩

def P290 : Prop := ∀ source character,
  (chopPrefixChar source character).source = source ∧
  ((chopPrefixChar source character).start = 1 ↔
    ∃ rest, source = character :: rest)
theorem p290 : P290 := by
  unfold P290 chopPrefixChar
  intro source character
  cases source <;> simp
  split <;> simp_all

def chopSuffixChar (source : List UInt32) (character : UInt32) : CharSlice :=
  match source.getLast? with
  | none => ⟨source, 0, source.length⟩
  | some last => if last == character then ⟨source, 0, source.length - 1⟩
      else ⟨source, 0, source.length⟩

def P344 : Prop := ∀ source character,
  (chopSuffixChar source character).source = source ∧
  (chopSuffixChar source character).stop ≤ source.length
theorem p344 : P344 := by
  unfold P344
  intro source character
  cases h : source.getLast? with
  | none => simp [chopSuffixChar, h]
  | some last =>
      simp [chopSuffixChar, h]
      split <;> simp

def padRemainderModel (pad : JStr) (stop : JInt64) : JSub :=
  ⟨pad, ix 0, stop⟩
def P516 : Prop := ∀ pad stop,
  (padRemainderModel pad stop).str = pad ∧ (padRemainderModel pad stop).ncu = stop
theorem p516 : P516 := by unfold P516; intros; exact ⟨rfl, rfl⟩

def P526 : Prop := ∀ cw source width pad,
  (width - ix (JuliaLean.StringUtil.textwidth cw source)).val ≤ 0 →
    JuliaLean.StringUtil.Pad.lpadStr cw source width pad = .ok source
theorem p526 : P526 := by
  unfold P526 JuliaLean.StringUtil.Pad.lpadStr
  intros; simp_all

def P566 : Prop := ∀ cw source width pad,
  (width - ix (JuliaLean.StringUtil.textwidth cw source)).val ≤ 0 →
    JuliaLean.StringUtil.Pad.rpadStr cw source width pad = .ok source
theorem p566 : P566 := by
  unfold P566 JuliaLean.StringUtil.Pad.rpadStr
  intros; simp_all

def P609 : Prop := ∀ cw source replacement width,
  JuliaLean.StringUtil.truncBoundaries cw source replacement width .right true = .ok none →
    JuliaLean.StringUtil.rtruncate cw source replacement width = .ok source
theorem p609 : P609 := by
  unfold P609 JuliaLean.StringUtil.rtruncate
  intros; simp_all

def P642 : Prop := ∀ cw source replacement width,
  JuliaLean.StringUtil.truncBoundaries cw source replacement width .left true = .ok none →
    JuliaLean.StringUtil.ltruncate cw source replacement width = .ok source
theorem p642 : P642 := by
  unfold P642 JuliaLean.StringUtil.ltruncate
  intros; simp_all

def P676 : Prop := ∀ cw source replacement width prefer,
  JuliaLean.StringUtil.truncBoundaries cw source replacement width .center prefer = .ok none →
    JuliaLean.StringUtil.ctruncate cw source replacement width prefer = .ok source
theorem p676 : P676 := by
  unfold P676 JuliaLean.StringUtil.ctruncate
  intros; simp_all

def P687 : Prop := ∀ cw source width,
  JuliaLean.StringUtil.checkTextwidth cw source width = true ↔
    JuliaLean.StringUtil.checkLoop cw width (chars source) (ix 0) = true
theorem p687 : P687 := by unfold P687 JuliaLean.StringUtil.checkTextwidth; intros; rfl

def P697 : Prop := ∀ cw source replacement width mode prefer,
  width.val < 0 →
  JuliaLean.StringUtil.truncBoundaries cw source replacement width mode prefer =
    .error (.jl (.argumentError s!"maxwidth {width.val} should be non-negative"))
theorem p697 : P697 := by
  unfold P697 JuliaLean.StringUtil.truncBoundaries
  intros; simp_all

def P814 : Prop := ∀ source size state,
  state.val > (ncodeunits source).val →
  Strings.partitionIterate source size state = .ok none
theorem p814 : P814 := by
  unfold P814 Strings.partitionIterate
  intros; simp_all

def splitWhitespace (source : JStr) (limit : JInt64) (keepempty : Bool) :=
  UtilRebuilt.eachsplitWhitespace source limit keepempty
def P964 : Prop := ∀ source limit keepempty,
  (splitWhitespace source limit keepempty).source = source ∧
  (splitWhitespace source limit keepempty).limit = limit ∧
  (splitWhitespace source limit keepempty).keepempty = keepempty
theorem p964 : P964 := by unfold P964; intros; exact ⟨rfl, rfl, rfl⟩

def rsplitWhitespace (source : JStr) (limit : JInt64) (keepempty : Bool) :=
  UtilRebuilt.eachrsplitWhitespace source limit keepempty
def P1007 : Prop := ∀ source limit keepempty,
  (rsplitWhitespace source limit keepempty).source = source ∧
  (rsplitWhitespace source limit keepempty).limit = limit ∧
  (rsplitWhitespace source limit keepempty).keepempty = keepempty
theorem p1007 : P1007 := by unfold P1007; intros; exact ⟨rfl, rfl, rfl⟩

def P1035 : Prop := ∀ source pairs count,
  count.val < 0 → JuliaLean.StringUtil.replaceN source pairs count =
    .error (.jl (.domainError "`count` must be non-negative."))
theorem p1035 : P1035 := by
  unfold P1035
  intro source pairs count hneg
  have hzero : count.val ≠ 0 := by omega
  simp [JuliaLean.StringUtil.replaceN, JuliaLean.StringUtil.replaceInit, hzero, hneg]

inductive FinishEvent where | replaceOnce | freePatterns | writeRest
  deriving Repr, DecidableEq
def finishEvents (iterations : Nat) : List FinishEvent :=
  List.replicate iterations .replaceOnce ++ [.freePatterns, .writeRest]
def P1053 : Prop := ∀ iterations,
  finishEvents iterations = List.replicate iterations .replaceOnce ++ [.freePatterns, .writeRest]
theorem p1053 : P1053 := by
  unfold P1053 finishEvents; intros; rfl

def P1068 : Prop := ∀ source pairs count,
  count.val = 0 → JuliaLean.StringUtil.replaceN source pairs count = .ok (source.bytes, 0)
theorem p1068 : P1068 := by
  unfold P1068 JuliaLean.StringUtil.replaceN
  intros; simp_all

def replaceIOWrapper (toString : A → JStr) (toCount : C → JInt64)
    (engine : List UInt8 → JStr → P → JInt64 → R)
    (io : List UInt8) (source : A) (pairs : P) (count : C) : R :=
  engine io (toString source) pairs (toCount count)
def P1183 : Prop := ∀ (A C P R : Type) toString toCount engine io (source : A) (pairs : P) (count : C),
  replaceIOWrapper (R := R) toString toCount engine io source pairs count =
    engine io (toString source) pairs (toCount count)
theorem p1183 : P1183 := by unfold P1183; intros; rfl

def replaceStringWrapper (toString : A → JStr) (toCount : C → JInt64)
    (engine : JStr → P → JInt64 → R) (source : A) (pairs : P) (count : C) : R :=
  engine (toString source) pairs (toCount count)
def P1186 : Prop := ∀ (A C P R : Type) toString toCount engine (source : A) (pairs : P) (count : C),
  replaceStringWrapper (R := R) toString toCount engine source pairs count =
    engine (toString source) pairs (toCount count)
theorem p1186 : P1186 := by unfold P1186; intros; rfl

def P1240 : Prop := ∀ source,
  (ncodeunits source).val ≠ (length source).val →
  JuliaLean.StringUtil.hex2bytes source =
    .error (JuliaLean.StringUtil.argErr "input string must consist of hexadecimal characters only")
theorem p1240 : P1240 := by
  unfold P1240 JuliaLean.StringUtil.hex2bytes
  intros; simp_all

def P1277 : Prop := ∀ character,
  JuliaLean.StringUtil.numberFromHexChar character =
    match Strings.codepoint character with
    | .error error => .error error
    | .ok codepoint => if codepoint ≤ 0xff then
        JuliaLean.StringUtil.numberFromHexByte codepoint.toUInt8
      else .error (.jl (.inexactError "UInt8"))
theorem p1277 : P1277 := by
  unfold P1277 JuliaLean.StringUtil.numberFromHexChar
  intros; rfl

def P1278 : Prop := ∀ byte,
  (byte ≥ 0x30 && byte ≤ 0x39) = true →
    JuliaLean.StringUtil.numberFromHexByte byte = .ok (byte - 0x30)
theorem p1278 : P1278 := by
  unfold P1278 JuliaLean.StringUtil.numberFromHexByte
  intro byte h
  simp at h
  simp [h.1, h.2]

def entry (id : String) (line : String) (fn statement : String) (prop theoremName : Lean.Name) : Entry := {
  id := id, juliaFile := "base/strings/util.jl", juliaFns := [fn], statement := statement,
  source := "base/strings/util.jl:" ++ line, status := .proven, prop := prop, thm := some theoremName
}

def entries : List Entry := []

end JuliaLean.StringsCovA.UtilReviewExtras
