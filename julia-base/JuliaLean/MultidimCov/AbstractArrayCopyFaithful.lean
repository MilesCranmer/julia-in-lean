import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayCopyFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

inductive Outcome (α : Type) where
  | returned (value : α)
  | thrown (failure : Failure)
  | diverged
  deriving Repr, DecidableEq

instance : Monad Outcome where
  pure := .returned
  bind value next := match value with
    | .returned result => next result
    | .thrown failure => .thrown failure
    | .diverged => .diverged

def liftResult : JResult α → Outcome α
  | .ok value => .returned value
  | .error failure => .thrown failure

inductive Iteration (α : Type) where
  | done
  | yielded (value : α) (rest : Iteration α)
  | failed (failure : Failure)
  | diverges
  deriving Repr, DecidableEq

def fromIteration : Iteration α → Outcome (Option (α × Iteration α))
  | .done => .returned none
  | .yielded value rest => .returned (some (value, rest))
  | .failed failure => .thrown failure
  | .diverges => .diverged

def copyLockstep (set : D → I → V → Outcome D) :
    D → Iteration I → Iteration V → Outcome D
  | dest, _, .done => .returned dest
  | _, _, .failed failure => .thrown failure
  | _, _, .diverges => .diverged
  | _, .done, .yielded _ _ =>
      .thrown (.argument (.literal "destination has fewer elements than required"))
  | _, .failed failure, .yielded _ _ => .thrown failure
  | _, .diverges, .yielded _ _ => .diverged
  | dest, .yielded index indices, .yielded value values => do
      let next ← set dest index value
      copyLockstep set next indices values

/-- Iterable-to-array `copyto!`, lines 941-951. -/
def m941 (eachindex : D → Outcome (Iteration I)) (iterate : S → Outcome (Iteration V))
    (set : D → I → V → Outcome D) (dest : D) (src : S) : Outcome D := do
  let indices ← eachindex dest
  let values ← iterate src
  copyLockstep set dest indices values
def P941 : Prop := ∀ {D I S V : Type} (eachindex : D → Outcome (Iteration I))
    (iterate : S → Outcome (Iteration V)) (set : D → I → V → Outcome D) dest src,
  m941 eachindex iterate set dest src = do
    let indices ← eachindex dest
    let values ← iterate src
    copyLockstep set dest indices values
theorem p941 : P941 := by unfold P941; intros; rfl

def writeSequential (set : D → Int → V → Outcome D) :
    D → Int → Iteration V → Outcome D
  | dest, _, .done => .returned dest
  | _, _, .failed failure => .thrown failure
  | _, _, .diverges => .diverged
  | dest, index, .yielded value rest => do
      let next ← set dest index value
      writeSequential set next (index + 1) rest

/-- `copyto!(dest,dstart,src)`, lines 953-971. -/
def m953 (toInt : IntegerValue → Outcome Int) (hasLength : S → Outcome Bool)
    (destLength : D → Outcome Int) (sourceLength : S → Outcome Int)
    (lastindex : D → Outcome Int) (checkbounds : D → Int → Outcome Unit)
    (iterate : S → Outcome (Iteration V)) (set : D → Int → V → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) : Outcome D := do
  let index ← toInt dstart
  let sized ← hasLength src
  if sized then
    let lengthDest ← destLength dest
    if 0 < lengthDest then
      let count ← sourceLength src
      if count = 0 then return dest
      checkbounds dest index
      let final ← lastindex dest
      if ¬(count ≤ final - index + 1) then .thrown .bounds
      else writeSequential set dest index (← iterate src)
    else writeSequential set dest index (← iterate src)
  else writeSequential set dest index (← iterate src)
def P953 : Prop := ∀ {D S V : Type} (toInt : IntegerValue → Outcome Int)
    (hasLength : S → Outcome Bool) (destLength : D → Outcome Int)
    (sourceLength : S → Outcome Int) (lastindex : D → Outcome Int)
    (checkbounds : D → Int → Outcome Unit) (iterate : S → Outcome (Iteration V))
    (set : D → Int → V → Outcome D) (dest : D) dstart (src : S),
  m953 toInt hasLength destLength sourceLength lastindex checkbounds iterate set dest dstart src = do
    let index ← toInt dstart
    let sized ← hasLength src
    if sized then
      let lengthDest ← destLength dest
      if 0 < lengthDest then
        let count ← sourceLength src
        if count = 0 then return dest
        checkbounds dest index
        let final ← lastindex dest
        if ¬(count ≤ final - index + 1) then .thrown .bounds
        else writeSequential set dest index (← iterate src)
      else writeSequential set dest index (← iterate src)
    else writeSequential set dest index (← iterate src)
theorem p953 : P953 := by unfold P953; intros; rfl

def skipValues : Nat → Nat → Iteration V → Outcome (Nat × Iteration V)
  | 0, skipped, values => .returned (skipped, values)
  | _ + 1, _, .failed failure => .thrown failure
  | _ + 1, _, .diverges => .diverged
  | _ + 1, skipped, .done => .returned (skipped, .done)
  | count + 1, skipped, .yielded _ rest => skipValues count (skipped + 1) rest

/-- `copyto!(dest,dstart,src,sstart)`, lines 974-1000. -/
def m974 (toInt : IntegerValue → Outcome Int) (iterate : S → Outcome (Iteration V))
    (set : D → Int → V → Outcome D) (dest : D) (dstart : IntegerValue)
    (src : S) (sstart : IntegerValue) : Outcome D :=
  if sstart.value < 1 then
    .thrown (.argument (lazyAppend [.literal "source start offset (", .integer sstart.value,
      .literal ") is < 1"]))
  else do
    let values ← iterate src
    let skipped ← skipValues (sstart.value - 1).toNat 0 values
    match skipped.2 with
    | .done =>
        .thrown (.argument (lazyAppend [.literal "source has fewer elements than required, ",
          .literal "expected at least ", .integer sstart.value, .literal ", got ",
          .integer skipped.1]))
    | .failed failure => .thrown failure
    | .diverges => .diverged
    | .yielded value rest =>
        let index ← toInt dstart
        writeSequential set dest index (.yielded value rest)
def P974 : Prop := ∀ {D S V : Type} (toInt : IntegerValue → Outcome Int)
    (iterate : S → Outcome (Iteration V)) (set : D → Int → V → Outcome D)
    (dest : D) dstart (src : S) sstart,
  m974 toInt iterate set dest dstart src sstart =
    if sstart.value < 1 then
      .thrown (.argument (lazyAppend [.literal "source start offset (", .integer sstart.value,
        .literal ") is < 1"]))
    else do
      let values ← iterate src
      let skipped ← skipValues (sstart.value - 1).toNat 0 values
      match skipped.2 with
      | .done =>
          .thrown (.argument (lazyAppend [.literal "source has fewer elements than required, ",
            .literal "expected at least ", .integer sstart.value, .literal ", got ",
            .integer skipped.1]))
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .yielded value rest =>
          let index ← toInt dstart
          writeSequential set dest index (.yielded value rest)
theorem p974 : P974 := by unfold P974; intros; rfl

def writeBounded (set : D → Int → V → Outcome D) :
    D → Int → Nat → Iteration V → Outcome (D × Nat)
  | dest, _, 0, _ => .returned (dest, 0)
  | dest, _, _, .done => .returned (dest, 0)
  | _, _, _, .failed failure => .thrown failure
  | _, _, _, .diverges => .diverged
  | dest, index, count + 1, .yielded value rest => do
      let next ← set dest index value
      let result ← writeBounded set next (index + 1) count rest
      .returned (result.1, result.2 + 1)

/-- Counted iterable `copyto!`, lines 1003-1037. -/
def m1003 (toInt : IntegerValue → Outcome Int) (linearIndices : D → Outcome (List Int))
    (iterate : S → Outcome (Iteration V)) (set : D → Int → V → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) (sstart count : IntegerValue) : Outcome D :=
  if count.value < 0 then
    .thrown (.argument (lazyAppend [.literal "tried to copy n=", .integer count.value,
      .literal ", elements, but n should be non-negative"]))
  else if count.value = 0 then .returned dest
  else do
    let indices ← linearIndices dest
    if sstart.value < 1 then
      .thrown (.argument (lazyAppend [.literal "source start offset (", .integer sstart.value,
        .literal ") is < 1"]))
    else if ¬(indices.contains dstart.value &&
      count.value ≤ (indices.getLast?.getD 0) - dstart.value + 1) then .thrown .bounds
    else
      let destinationStart ← toInt dstart
      let n ← toInt count
      let values ← iterate src
      let skipped ← skipValues (sstart.value - 1).toNat 0 values
      match skipped.2 with
      | .done =>
          .thrown (.argument (lazyAppend [.literal "source has fewer elements than required, ",
            .literal "expected at least ", .integer sstart.value, .literal ", got ",
            .integer skipped.1]))
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .yielded value rest => do
          let firstWrite ← set dest destinationStart value
          let copied ← writeBounded set firstWrite (destinationStart + 1) (n - 1).toNat rest
          if copied.2 < (n - 1).toNat then .thrown .bounds else .returned copied.1
def P1003 : Prop := ∀ {D S V : Type} (toInt : IntegerValue → Outcome Int)
    (linearIndices : D → Outcome (List Int)) (iterate : S → Outcome (Iteration V))
    (set : D → Int → V → Outcome D)
    (dest : D) dstart (src : S) sstart count,
  m1003 toInt linearIndices iterate set dest dstart src sstart count =
  if count.value < 0 then
    .thrown (.argument (lazyAppend [.literal "tried to copy n=", .integer count.value,
      .literal ", elements, but n should be non-negative"]))
  else if count.value = 0 then .returned dest
  else do
    let indices ← linearIndices dest
    if sstart.value < 1 then
      .thrown (.argument (lazyAppend [.literal "source start offset (", .integer sstart.value,
        .literal ") is < 1"]))
    else if ¬(indices.contains dstart.value &&
      count.value ≤ (indices.getLast?.getD 0) - dstart.value + 1) then .thrown .bounds
    else
      let destinationStart ← toInt dstart
      let n ← toInt count
      let values ← iterate src
      let skipped ← skipValues (sstart.value - 1).toNat 0 values
      match skipped.2 with
      | .done =>
          .thrown (.argument (lazyAppend [.literal "source has fewer elements than required, ",
            .literal "expected at least ", .integer sstart.value, .literal ", got ",
            .integer skipped.1]))
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .yielded value rest => do
          let firstWrite ← set dest destinationStart value
          let copied ← writeBounded set firstWrite (destinationStart + 1) (n - 1).toNat rest
          if copied.2 < (n - 1).toNat then .thrown .bounds else .returned copied.1
theorem p1003 : P1003 := by unfold P1003; intros; rfl

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq

/-- Array-to-array `copyto!`, lines 1072-1080. -/
def m1072 (isEmpty : S → Outcome Bool) (isBitArray : D → Bool)
    (copyBitArray : D → S → Outcome D) (unalias : D → S → Outcome S)
    (indexStyleDest : D → IndexStyle) (indexStyleSrc : S → IndexStyle)
    (copyUnaliased : IndexStyle → D → IndexStyle → S → Outcome D)
    (dest : D) (src : S) : Outcome D := do
  if ← isEmpty src then return dest
  if isBitArray dest then copyBitArray dest src
  else
    let source ← unalias dest src
    copyUnaliased (indexStyleDest dest) dest (indexStyleSrc source) source
def P1072 : Prop := ∀ {D S : Type} isEmpty isBitArray copyBitArray unalias
    indexStyleDest indexStyleSrc copyUnaliased (dest : D) (src : S),
  m1072 isEmpty isBitArray copyBitArray unalias indexStyleDest indexStyleSrc
    copyUnaliased dest src = do
      if ← isEmpty src then return dest
      if isBitArray dest then copyBitArray dest src
      else
        let source ← unalias dest src
        copyUnaliased (indexStyleDest dest) dest (indexStyleSrc source) source
theorem p1072 : P1072 := by unfold P1072; intros; rfl

/-- Styled array-to-array `copyto!`, lines 1082-1086. -/
def m1082 (isEmpty : S → Outcome Bool) (unalias : D → S → Outcome S)
    (copyUnaliased : IndexStyle → D → IndexStyle → S → Outcome D)
    (destStyle : IndexStyle) (dest : D) (srcStyle : IndexStyle) (src : S) : Outcome D := do
  if ← isEmpty src then return dest
  let source ← unalias dest src
  copyUnaliased destStyle dest srcStyle source
def P1082 : Prop := ∀ {D S : Type} isEmpty unalias copyUnaliased destStyle
    (dest : D) srcStyle (src : S),
  m1082 isEmpty unalias copyUnaliased destStyle dest srcStyle src = do
    if ← isEmpty src then return dest
    let source ← unalias dest src
    copyUnaliased destStyle dest srcStyle source
theorem p1082 : P1082 := by unfold P1082; intros; rfl

def copyLinear (iterateIndices : LS → D → (D → Int → Outcome D) → Outcome D)
    (read : S → Int → Outcome V) (write : D → Int → V → Outcome D)
    (add : Int → Int → Outcome Int) (delta : Int) (dest : D) (src : S)
    (indices : LS) : Outcome D :=
  iterateIndices indices dest fun current index => do
    let value ← read src index
    let destinationIndex ← add index delta
    write current destinationIndex value

/-- `copyto_unaliased!`, lines 1088-1123. Linear-index iteration remains
incremental, so index-iterator failures and divergence occur between reads and writes. -/
def m1088 (isEmpty : S → Outcome Bool)
    (linearIndicesDest : D → Outcome LD) (linearIndicesSrc : S → Outcome LS)
    (firstDest : LD → Outcome Int) (firstSrc lastSrc : LS → Outcome Int)
    (subtract add : Int → Int → Outcome Int) (checkbounds : LD → Int → Outcome Bool)
    (iterateSrcValues : S → Outcome (Iteration V))
    (iterateSrcIndices : LS → D → (D → Int → Outcome D) → Outcome D)
    (iteratorsEqual : D → S → Outcome Bool)
    (copyShared copyDual : D → S → Outcome D)
    (readLinear : S → Int → Outcome V) (writeLinear : D → Int → V → Outcome D)
    (destStyle srcStyle : IndexStyle) (dest : D) (src : S) : Outcome D := do
  if ← isEmpty src then return dest
  let destIndices ← linearIndicesDest dest
  let srcIndices ← linearIndicesSrc src
  let destinationFirst ← firstDest destIndices
  let sourceFirst ← firstSrc srcIndices
  let delta ← subtract destinationFirst sourceFirst
  let lowIndex ← add sourceFirst delta
  let sourceLast ← lastSrc srcIndices
  let highIndex ← add sourceLast delta
  let low ← checkbounds destIndices lowIndex
  let high ← checkbounds destIndices highIndex
  if ¬(low && high) then .thrown .bounds
  else match destStyle, srcStyle with
    | .linear, .linear =>
        copyLinear iterateSrcIndices readLinear writeLinear add delta dest src srcIndices
    | .linear, .cartesian =>
        writeSequential writeLinear dest destinationFirst (← iterateSrcValues src)
    | .cartesian, _ =>
        if ← iteratorsEqual dest src then copyShared dest src else copyDual dest src
def P1088 : Prop := ∀ {D S LD LS V : Type} (isEmpty : S → Outcome Bool)
    (linearIndicesDest : D → Outcome LD) (linearIndicesSrc : S → Outcome LS)
    (firstDest : LD → Outcome Int) (firstSrc lastSrc : LS → Outcome Int)
    (subtract add : Int → Int → Outcome Int) (checkbounds : LD → Int → Outcome Bool)
    (iterateSrcValues : S → Outcome (Iteration V))
    (iterateSrcIndices : LS → D → (D → Int → Outcome D) → Outcome D)
    (iteratorsEqual : D → S → Outcome Bool) (copyShared copyDual : D → S → Outcome D)
    (readLinear : S → Int → Outcome V) (writeLinear : D → Int → V → Outcome D)
    destStyle srcStyle (dest : D) (src : S),
  m1088 isEmpty linearIndicesDest linearIndicesSrc firstDest firstSrc lastSrc subtract add
    checkbounds iterateSrcValues iterateSrcIndices iteratorsEqual copyShared copyDual
    readLinear writeLinear destStyle srcStyle dest src = do
      if ← isEmpty src then return dest
      let destIndices ← linearIndicesDest dest
      let srcIndices ← linearIndicesSrc src
      let destinationFirst ← firstDest destIndices
      let sourceFirst ← firstSrc srcIndices
      let delta ← subtract destinationFirst sourceFirst
      let lowIndex ← add sourceFirst delta
      let sourceLast ← lastSrc srcIndices
      let highIndex ← add sourceLast delta
      let low ← checkbounds destIndices lowIndex
      let high ← checkbounds destIndices highIndex
      if ¬(low && high) then .thrown .bounds
      else match destStyle, srcStyle with
        | .linear, .linear =>
            copyLinear iterateSrcIndices readLinear writeLinear add delta dest src srcIndices
        | .linear, .cartesian =>
            writeSequential writeLinear dest destinationFirst (← iterateSrcValues src)
        | .cartesian, _ =>
            if ← iteratorsEqual dest src then copyShared dest src else copyDual dest src
theorem p1088 : P1088 := by unfold P1088; intros; rfl

/-- Three-argument array `copyto!`, lines 1125-1127. -/
def m1125 (linearIndices : S → Outcome (List Int)) (length : S → Outcome IntegerValue)
    (copyFive : D → IntegerValue → S → IntegerValue → IntegerValue → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) : Outcome D := do
  let indices ← linearIndices src
  let count ← length src
  copyFive dest dstart src ⟨indices.head?.getD 1⟩ count
def P1125 : Prop := ∀ {D S : Type} linearIndices length copyFive
    (dest : D) dstart (src : S), m1125 linearIndices length copyFive dest dstart src = do
      let indices ← linearIndices src
      let count ← length src
      copyFive dest dstart src ⟨indices.head?.getD 1⟩ count
theorem p1125 : P1125 := by unfold P1125; intros; rfl

/-- Four-argument array `copyto!`, lines 1129-1133. -/
def m1129 (linearIndices : S → Outcome (List Int))
    (checkbounds : List Int → IntegerValue → Outcome Bool)
    (copyFive : D → IntegerValue → S → IntegerValue → IntegerValue → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) (sstart : IntegerValue) : Outcome D := do
  let indices ← linearIndices src
  if ¬(← checkbounds indices sstart) then .thrown .bounds
  else copyFive dest dstart src sstart ⟨indices.getLast?.getD 0 - sstart.value + 1⟩
def P1129 : Prop := ∀ {D S : Type} linearIndices checkbounds copyFive
    (dest : D) dstart (src : S) sstart,
  m1129 linearIndices checkbounds copyFive dest dstart src sstart = do
    let indices ← linearIndices src
    if ¬(← checkbounds indices sstart) then .thrown .bounds
    else copyFive dest dstart src sstart ⟨indices.getLast?.getD 0 - sstart.value + 1⟩
theorem p1129 : P1129 := by unfold P1129; intros; rfl

def copyCount (read : S → Int → Outcome V) (write : D → Int → V → Outcome D) :
    D → S → Int → Int → Nat → Outcome D
  | dest, _, _, _, 0 => .returned dest
  | dest, src, di, si, count + 1 => do
      let value ← read src si
      let next ← write dest di value
      copyCount read write next src (di + 1) (si + 1) count

/-- Five-argument array `copyto!`, lines 1135-1152. -/
def m1135 (linearDest : D → Outcome (List Int)) (linearSrc : S → Outcome (List Int))
    (checkbounds : List Int → IntegerValue → Outcome Bool) (toInt : IntegerValue → Outcome Int)
    (unalias : D → S → Outcome S) (read : S → Int → Outcome V)
    (write : D → Int → V → Outcome D) (dest : D) (dstart : IntegerValue)
    (src : S) (sstart count : IntegerValue) : Outcome D :=
  if count.value = 0 then .returned dest
  else if count.value < 0 then .thrown (.argument (.literal "n should be non-negative"))
  else do
    let destIndices ← linearDest dest
    let srcIndices ← linearSrc src
    let destFirst ← checkbounds destIndices dstart
    if ¬(destFirst && count.value ≤ destIndices.getLast?.getD 0 - dstart.value + 1) then .thrown .bounds
    let srcFirst ← checkbounds srcIndices sstart
    if ¬(srcFirst && count.value ≤ srcIndices.getLast?.getD 0 - sstart.value + 1) then .thrown .bounds
    let di ← toInt dstart
    let si ← toInt sstart
    let n ← toInt count
    let source ← unalias dest src
    copyCount read write dest source di si n.toNat
def P1135 : Prop := ∀ {D S V : Type} (linearDest : D → Outcome (List Int))
    (linearSrc : S → Outcome (List Int)) (checkbounds : List Int → IntegerValue → Outcome Bool)
    (toInt : IntegerValue → Outcome Int) (unalias : D → S → Outcome S)
    (read : S → Int → Outcome V) (write : D → Int → V → Outcome D)
    (dest : D) dstart (src : S) sstart count,
  m1135 linearDest linearSrc checkbounds toInt unalias read write dest dstart src sstart count =
  if count.value = 0 then .returned dest
  else if count.value < 0 then .thrown (.argument (.literal "n should be non-negative"))
  else do
    let destIndices ← linearDest dest
    let srcIndices ← linearSrc src
    let destFirst ← checkbounds destIndices dstart
    if ¬(destFirst && count.value ≤ destIndices.getLast?.getD 0 - dstart.value + 1) then
      .thrown .bounds
    let srcFirst ← checkbounds srcIndices sstart
    if ¬(srcFirst && count.value ≤ srcIndices.getLast?.getD 0 - sstart.value + 1) then
      .thrown .bounds
    let di ← toInt dstart
    let si ← toInt sstart
    let n ← toInt count
    let source ← unalias dest src
    copyCount read write dest source di si n.toNat
theorem p1135 : P1135 := by unfold P1135; intros; rfl

structure RangeOps (R : Type) where
  length : R → Outcome Int
  first : R → Outcome Int
  step : R → Outcome Int
  values : R → Outcome (List Int)

def copyRegion (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D)
    (rowStep colStep : Unit → Outcome Int) :
    D → S → Int → List Int → Int → List Int → Outcome D
  | dest, _, _, [], _, _ => .returned dest
  | dest, src, destColumn, sourceColumn :: sourceColumns, destRow, sourceRows => do
      let next ← sourceRows.foldlM (fun state sourceRow => do
        let value ← read src sourceRow sourceColumn
        let out ← write state.1 state.2 destColumn value
        let step ← rowStep ()
        .returned (out, state.2 + step)) (dest, destRow)
      let step ← colStep ()
      copyRegion read write rowStep colStep next.1 src (destColumn + step)
        sourceColumns destRow sourceRows

/-- Matrix-region `copyto!`, lines 1159-1182. -/
def m1159 (destOps : RangeOps RD) (srcOps : RangeOps RS)
    (checkDest : D → RD → RD → Outcome Unit) (checkSrc : S → RS → RS → Outcome Unit)
    (unalias : D → S → Outcome S) (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D) (dest : D) (destRows destCols : RD)
    (src : S) (srcRows srcCols : RS) : Outcome D := do
  let drLength ← destOps.length destRows
  let srLength ← srcOps.length srcRows
  if drLength != srLength then
    let actualSource ← srcOps.length srcRows
    let actualDest ← destOps.length destRows
    .thrown (.argument (lazyAppend [.literal "source and destination must have same size (got ",
      .integer actualSource, .literal " and ", .integer actualDest, .literal ")"]))
  let dcLength ← destOps.length destCols
  let scLength ← srcOps.length srcCols
  if dcLength != scLength then
    let actualSource ← srcOps.length srcCols
    let actualDest ← destOps.length destCols
    .thrown (.argument (lazyAppend [.literal "source and destination must have same size (got ",
      .integer actualSource, .literal " and ", .integer actualDest, .literal ")"]))
  checkDest dest destRows destCols
  checkSrc src srcRows srcCols
  let source ← unalias dest src
  copyRegion read write (fun _ => destOps.step destRows) (fun _ => destOps.step destCols)
    dest source (← destOps.first destCols) (← srcOps.values srcCols)
    (← destOps.first destRows) (← srcOps.values srcRows)
def P1159 : Prop := ∀ {D S RD RS V : Type} (destOps : RangeOps RD) (srcOps : RangeOps RS)
    (checkDest : D → RD → RD → Outcome Unit) (checkSrc : S → RS → RS → Outcome Unit)
    (unalias : D → S → Outcome S) (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D)
    (dest : D) destRows destCols (src : S) srcRows srcCols,
  m1159 destOps srcOps checkDest checkSrc unalias read write dest destRows destCols src srcRows srcCols = do
    let drLength ← destOps.length destRows
    let srLength ← srcOps.length srcRows
    if drLength != srLength then
      let actualSource ← srcOps.length srcRows
      let actualDest ← destOps.length destRows
      .thrown (.argument (lazyAppend [.literal "source and destination must have same size (got ",
        .integer actualSource, .literal " and ", .integer actualDest, .literal ")"]))
    let dcLength ← destOps.length destCols
    let scLength ← srcOps.length srcCols
    if dcLength != scLength then
      let actualSource ← srcOps.length srcCols
      let actualDest ← destOps.length destCols
      .thrown (.argument (lazyAppend [.literal "source and destination must have same size (got ",
        .integer actualSource, .literal " and ", .integer actualDest, .literal ")"]))
    checkDest dest destRows destCols
    checkSrc src srcRows srcCols
    let source ← unalias dest src
    copyRegion read write (fun _ => destOps.step destRows) (fun _ => destOps.step destCols)
      dest source (← destOps.first destCols) (← srcOps.values srcCols)
      (← destOps.first destRows) (← srcOps.values srcRows)
theorem p1159 : P1159 := by unfold P1159; intros; rfl

/-- `_checkaxs`, line 1184. -/
def m1184 (equal : A → A → Bool) (asAny : A → AnyValue) (destAxes srcAxes : A) : JResult Unit :=
  if equal destAxes srcAxes then .ok ()
  else .error (.dimensionMismatch (lazyAppend [.literal "axes must agree, got ",
    .dynamic (asAny destAxes), .literal " and ", .dynamic (asAny srcAxes)]))
def P1184 : Prop := ∀ {A : Type} equal asAny (dest src : A),
  m1184 equal asAny dest src = if equal dest src then .ok ()
  else .error (.dimensionMismatch (lazyAppend [.literal "axes must agree, got ",
    .dynamic (asAny dest), .literal " and ", .dynamic (asAny src)]))
theorem p1184 : P1184 := by unfold P1184; intros; rfl

/-- `copyto_axcheck!`, lines 1186-1189. -/
def m1186 (axes : A → JResult X) (check : X → X → JResult Unit)
    (copyto : A → A → JResult A) (dest src : A) : JResult A := do
  let destAxes ← axes dest
  let srcAxes ← axes src
  check destAxes srcAxes
  copyto dest src
def P1186 : Prop := ∀ {A X : Type} (axes : A → JResult X)
    (check : X → X → JResult Unit) (copyto : A → A → JResult A) (dest src : A),
  m1186 axes check copyto dest src = do
    let destAxes ← axes dest
    let srcAxes ← axes src
    check destAxes srcAxes
    copyto dest src
theorem p1186 : P1186 := by unfold P1186; intros; rfl

/-- `_one`, lines 1222-1234. -/
def m1222 (axes : M → JResult (R × C)) (lengthRows : R → JResult Nat)
    (lengthCols : C → JResult Nat) (zero : V → JResult V)
    (assertType : V → JResult V) (requireOneBased : M → JResult Unit)
    (similar : M → JResult D) (fill : D → V → JResult D)
    (iterateRows : R → D → (D → I → JResult D) → JResult D)
    (set : D → I → I → V → JResult D) (unit : V) (matrix : M) : JResult D := do
  let matrixAxes ← axes matrix
  let rowsLength ← lengthRows matrixAxes.1
  let colsLength ← lengthCols matrixAxes.2
  if rowsLength != colsLength then
    .error (.dimensionMismatch (.literal "multiplicative identity defined only for square matrices"))
  else
    let zeroValue ← assertType (← zero unit)
    requireOneBased matrix
    let dest ← similar matrix
    let cleared ← fill dest zeroValue
    iterateRows matrixAxes.1 cleared (fun out index => set out index index unit)
def P1222 : Prop := ∀ {M R C I V D : Type} (axes : M → JResult (R × C))
    (lengthRows : R → JResult Nat) (lengthCols : C → JResult Nat)
    (zero : V → JResult V) (assertType : V → JResult V)
    (requireOneBased : M → JResult Unit) (similar : M → JResult D)
    (fill : D → V → JResult D)
    (iterateRows : R → D → (D → I → JResult D) → JResult D)
    (set : D → I → I → V → JResult D) unit matrix,
  m1222 axes lengthRows lengthCols zero assertType requireOneBased similar fill iterateRows
    set unit matrix = do
      let matrixAxes ← axes matrix
      let rowsLength ← lengthRows matrixAxes.1
      let colsLength ← lengthCols matrixAxes.2
      if rowsLength != colsLength then
        .error (.dimensionMismatch (.literal "multiplicative identity defined only for square matrices"))
      else
        let zeroValue ← assertType (← zero unit)
        requireOneBased matrix
        let dest ← similar matrix
        let cleared ← fill dest zeroValue
        iterateRows matrixAxes.1 cleared (fun out index => set out index index unit)
theorem p1222 : P1222 := by unfold P1222; intros; rfl

/-- Tuple-state array iteration, lines 1251-1255. -/
def m1251 (iterate : State → Outcome (Option (I × Next)))
    (getindex : A → I → Outcome V) (rebuild : State → Next → State)
    (array : A) (state : State) : Outcome (Option (V × State)) := do
  match ← iterate state with
  | none => .returned none
  | some (index, next) =>
      let value ← getindex array index
      .returned (some (value, rebuild state next))
def P1251 : Prop := ∀ {State I Next A V : Type}
    (iterate : State → Outcome (Option (I × Next))) (getindex : A → I → Outcome V)
    (rebuild : State → Next → State) (array : A) state,
  m1251 iterate getindex rebuild array state = do
    match ← iterate state with
    | none => .returned none
    | some (index, next) =>
        let value ← getindex array index
        .returned (some (value, rebuild state next))
theorem p1251 : P1251 := by unfold P1251; intros; rfl

/-- Integer-state array iteration, lines 1256-1259. -/
def m1256 (checkbounds : A → IntegerValue → Outcome Bool)
    (getindex : A → IntegerValue → Outcome V) (one : IntegerValue → Outcome IntegerValue)
    (add : IntegerValue → IntegerValue → Outcome IntegerValue)
    (array : A) (state : IntegerValue) : Outcome (Option (V × IntegerValue)) := do
  if ¬(← checkbounds array state) then return none
  let value ← getindex array state
  let increment ← one state
  let next ← add state increment
  .returned (some (value, next))
def P1256 : Prop := ∀ {A V : Type} (checkbounds : A → IntegerValue → Outcome Bool)
    (getindex : A → IntegerValue → Outcome V) (one : IntegerValue → Outcome IntegerValue)
    (add : IntegerValue → IntegerValue → Outcome IntegerValue) (array : A) state,
  m1256 checkbounds getindex one add array state = do
    if ¬(← checkbounds array state) then return none
    let value ← getindex array state
    let increment ← one state
    let next ← add state increment
    .returned (some (value, next))
theorem p1256 : P1256 := by unfold P1256; intros; rfl

/-- Type-map of StepRange, line 1267. -/
def m1267 (start step : R → JResult A) (last : R → JResult A)
    (convert : A → JResult B) (construct : B → B → B → JResult O) (range : R) : JResult O := do
  let convertedStart ← convert (← start range)
  let convertedStep ← convert (← step range)
  let convertedLast ← convert (← last range)
  construct convertedStart convertedStep convertedLast
def P1267 : Prop := ∀ {R A B O : Type} (start step last : R → JResult A)
    (convert : A → JResult B) (construct : B → B → B → JResult O) range,
  m1267 start step last convert construct range = do
    let convertedStart ← convert (← start range)
    let convertedStep ← convert (← step range)
    let convertedLast ← convert (← last range)
    construct convertedStart convertedStep convertedLast
theorem p1267 : P1267 := by unfold P1267; intros; rfl

/-- Type-map of UnitRange, line 1268. -/
def m1268 (start last : R → JResult A) (convert : A → JResult B)
    (construct : B → B → JResult O) (range : R) : JResult O := do
  let convertedStart ← convert (← start range)
  let convertedLast ← convert (← last range)
  construct convertedStart convertedLast
def P1268 : Prop := ∀ {R A B O : Type} (start last : R → JResult A)
    (convert : A → JResult B) (construct : B → B → JResult O) range,
  m1268 start last convert construct range = do
    let convertedStart ← convert (← start range)
    let convertedLast ← convert (← last range)
    construct convertedStart convertedLast
theorem p1268 : P1268 := by unfold P1268; intros; rfl

/-- Type-map of LinRange, lines 1270-1272. -/
def m1270 (start stop : R → JResult A) (length : R → JResult Nat)
    (convert : A → JResult B) (construct : B → B → Nat → JResult O) (range : R) : JResult O := do
  let convertedStart ← convert (← start range)
  let convertedStop ← convert (← stop range)
  let count ← length range
  construct convertedStart convertedStop count
def P1270 : Prop := ∀ {R A B O : Type} (start stop : R → JResult A)
    (length : R → JResult Nat) (convert : A → JResult B)
    (construct : B → B → Nat → JResult O) range,
  m1270 start stop length convert construct range = do
    let convertedStart ← convert (← start range)
    let convertedStop ← convert (← stop range)
    let count ← length range
    construct convertedStart convertedStop count
theorem p1270 : P1270 := by unfold P1270; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-copy-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayCopyFaithful
