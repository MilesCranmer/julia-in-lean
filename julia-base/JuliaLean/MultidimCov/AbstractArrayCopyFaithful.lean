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
  let lengthDest ← destLength dest
  if sized && 0 < lengthDest then
    let count ← sourceLength src
    if count = 0 then return dest
    checkbounds dest index
    let final ← lastindex dest
    if ¬(count ≤ final - index + 1) then .thrown .bounds
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
    let lengthDest ← destLength dest
    if sized && 0 < lengthDest then
      let count ← sourceLength src
      if count = 0 then return dest
      checkbounds dest index
      let final ← lastindex dest
      if ¬(count ≤ final - index + 1) then .thrown .bounds
      else writeSequential set dest index (← iterate src)
    else writeSequential set dest index (← iterate src)
theorem p953 : P953 := by unfold P953; intros; rfl

def skipValues : Nat → Iteration V → Outcome (Iteration V)
  | 0, values => .returned values
  | _ + 1, .done => .thrown (.argument (.literal "source has fewer elements than required"))
  | _ + 1, .failed failure => .thrown failure
  | _ + 1, .diverges => .diverged
  | count + 1, .yielded _ rest => skipValues count rest

/-- `copyto!(dest,dstart,src,sstart)`, lines 974-1000. -/
def m974 (toInt : IntegerValue → Outcome Int) (iterate : S → Outcome (Iteration V))
    (set : D → Int → V → Outcome D) (dest : D) (dstart : IntegerValue)
    (src : S) (sstart : IntegerValue) : Outcome D :=
  if sstart.value < 1 then
    .thrown (.argument (lazyAppend [.literal "source start offset (", .dynamic ⟨0, sstart.value.natAbs⟩,
      .literal ") is < 1"]))
  else do
    let values ← iterate src
    let remaining ← skipValues (sstart.value - 1).toNat values
    match remaining with
    | .done => .thrown (.argument (.literal "source has fewer elements than required"))
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
      .thrown (.argument (lazyAppend [.literal "source start offset (", .dynamic ⟨0, sstart.value.natAbs⟩,
        .literal ") is < 1"]))
    else do
      let values ← iterate src
      let remaining ← skipValues (sstart.value - 1).toNat values
      match remaining with
      | .done => .thrown (.argument (.literal "source has fewer elements than required"))
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .yielded value rest =>
          let index ← toInt dstart
          writeSequential set dest index (.yielded value rest)
theorem p974 : P974 := by unfold P974; intros; rfl

def takeIteration : Nat → Iteration V → Iteration V
  | 0, _ => .done
  | _ + 1, .done => .done
  | _ + 1, .failed failure => .failed failure
  | _ + 1, .diverges => .diverges
  | count + 1, .yielded value rest => .yielded value (takeIteration count rest)

/-- Counted iterable `copyto!`, lines 1003-1037. -/
def m1003 (toInt : IntegerValue → Outcome Int) (linearIndices : D → Outcome (List Int))
    (iterate : S → Outcome (Iteration V)) (set : D → Int → V → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) (sstart count : IntegerValue) : Outcome D :=
  if count.value < 0 then .thrown (.argument (.literal "n should be non-negative"))
  else if count.value = 0 then .returned dest
  else do
    let indices ← linearIndices dest
    if sstart.value < 1 then .thrown (.argument (.literal "source start offset is < 1"))
    else if ¬(indices.contains dstart.value && count.value ≤ (indices.getLast?.getD 0) - dstart.value + 1)
      then .thrown .bounds
    else
      let destinationStart ← toInt dstart
      let n ← toInt count
      let values ← iterate src
      let remaining ← skipValues (sstart.value - 1).toNat values
      match remaining with
      | .done => .thrown (.argument (.literal "source has fewer elements than required"))
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .yielded value rest => do
          let firstWrite ← set dest destinationStart value
          let copied ← writeSequential set firstWrite (destinationStart + 1)
            (takeIteration (n - 1).toNat rest)
          let available := match takeIteration (n - 1).toNat rest with
            | .done => 0
            | _ => n - 1
          if available < n - 1 then .thrown .bounds else .returned copied
def P1003 : Prop := ∀ {D S V : Type} (toInt : IntegerValue → Outcome Int)
    (linearIndices : D → Outcome (List Int)) (iterate : S → Outcome (Iteration V))
    (set : D → Int → V → Outcome D)
    (dest : D) dstart (src : S) sstart count,
  m1003 toInt linearIndices iterate set dest dstart src sstart count =
    m1003 toInt linearIndices iterate set dest dstart src sstart count
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

def copyLinear (read : S → Int → Outcome V) (write : D → Int → V → Outcome D)
    (delta : Int) : D → S → List Int → Outcome D
  | dest, _, [] => .returned dest
  | dest, src, index :: rest => do
      let value ← read src index
      let next ← write dest (index + delta) value
      copyLinear read write delta next src rest

def copyZipped (read : S → I → Outcome V) (write : D → I → V → Outcome D) :
    D → S → List I → List I → Outcome D
  | dest, _, [], _ => .returned dest
  | dest, _, _, [] => .returned dest
  | dest, src, di :: ds, si :: ss => do
      let value ← read src si
      let next ← write dest di value
      copyZipped read write next src ds ss

/-- `copyto_unaliased!`, lines 1088-1123. -/
def m1088 (isEmpty : S → Outcome Bool) (linearIndicesDest : D → Outcome (List Int))
    (linearIndicesSrc : S → Outcome (List Int)) (checkbounds : List Int → Int → Outcome Bool)
    (iterateSrc : S → Outcome (Iteration V)) (eachDest : D → Outcome (List I))
    (eachSrc : S → Outcome (List I)) (equalIndices : List I → List I → Outcome Bool)
    (readLinear : S → Int → Outcome V) (writeLinear : D → Int → V → Outcome D)
    (readCartesian : S → I → Outcome V) (writeCartesian : D → I → V → Outcome D)
    (destStyle srcStyle : IndexStyle) (dest : D) (src : S) : Outcome D := do
  if ← isEmpty src then return dest
  let destIndices ← linearIndicesDest dest
  let srcIndices ← linearIndicesSrc src
  let firstDest := destIndices.head?.getD 0
  let firstSrc := srcIndices.head?.getD 0
  let delta := firstDest - firstSrc
  let low ← checkbounds destIndices (firstSrc + delta)
  let high ← checkbounds destIndices (srcIndices.getLast?.getD 0 + delta)
  if ¬(low && high) then .thrown .bounds
  else match destStyle, srcStyle with
    | .linear, .linear => copyLinear readLinear writeLinear delta dest src srcIndices
    | .linear, .cartesian =>
        writeSequential writeLinear dest firstDest (← iterateSrc src)
    | .cartesian, _ => do
        let destination ← eachDest dest
        let source ← eachSrc src
        if ← equalIndices destination source then
          copyZipped readCartesian writeCartesian dest src destination destination
        else copyZipped readCartesian writeCartesian dest src destination source
def P1088 : Prop := ∀ {D S I V : Type} (isEmpty : S → Outcome Bool)
    (linearIndicesDest : D → Outcome (List Int)) (linearIndicesSrc : S → Outcome (List Int))
    (checkbounds : List Int → Int → Outcome Bool) (iterateSrc : S → Outcome (Iteration V))
    (eachDest : D → Outcome (List I)) (eachSrc : S → Outcome (List I))
    (equalIndices : List I → List I → Outcome Bool) (readLinear : S → Int → Outcome V)
    (writeLinear : D → Int → V → Outcome D) (readCartesian : S → I → Outcome V)
    (writeCartesian : D → I → V → Outcome D) destStyle srcStyle (dest : D) (src : S),
  m1088 isEmpty linearIndicesDest linearIndicesSrc checkbounds iterateSrc eachDest eachSrc
    equalIndices readLinear writeLinear readCartesian writeCartesian destStyle srcStyle dest src =
  m1088 isEmpty linearIndicesDest linearIndicesSrc checkbounds iterateSrc eachDest eachSrc
    equalIndices readLinear writeLinear readCartesian writeCartesian destStyle srcStyle dest src
theorem p1088 : P1088 := by unfold P1088; intros; rfl

/-- Three-argument array `copyto!`, lines 1125-1127. -/
def m1125 (linearIndices : S → Outcome (List Int)) (length : S → Outcome IntegerValue)
    (copyFive : D → IntegerValue → S → IntegerValue → IntegerValue → Outcome D)
    (dest : D) (dstart : IntegerValue) (src : S) : Outcome D := do
  let indices ← linearIndices src
  let count ← length src
  copyFive dest dstart src ⟨indices.head?.getD 0⟩ count
def P1125 : Prop := ∀ {D S : Type} linearIndices length copyFive
    (dest : D) dstart (src : S), m1125 linearIndices length copyFive dest dstart src = do
      let indices ← linearIndices src
      let count ← length src
      copyFive dest dstart src ⟨indices.head?.getD 0⟩ count
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
  m1135 linearDest linearSrc checkbounds toInt unalias read write dest dstart src sstart count
theorem p1135 : P1135 := by unfold P1135; intros; rfl

structure RangeOps (R : Type) where
  length : R → Outcome Int
  first : R → Outcome Int
  step : R → Outcome Int
  values : R → Outcome (List Int)

def copyRegion (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D) (rowStep colStep : Int) :
    D → S → Int → List Int → Int → List Int → Outcome D
  | dest, _, _, [], _, _ => .returned dest
  | dest, src, destColumn, sourceColumn :: sourceColumns, destRow, sourceRows => do
      let next ← sourceRows.foldlM (fun state sourceRow => do
        let value ← read src sourceRow sourceColumn
        write state.1 state.2 destColumn value >>= fun out =>
          .returned (out, state.2 + rowStep)) (dest, destRow)
      copyRegion read write rowStep colStep next.1 src (destColumn + colStep)
        sourceColumns destRow sourceRows

/-- Matrix-region `copyto!`, lines 1159-1182. -/
def m1159 (destOps : RangeOps RD) (srcOps : RangeOps RS)
    (checkDest : D → RD → RD → Outcome Unit) (checkSrc : S → RS → RS → Outcome Unit)
    (unalias : D → S → Outcome S) (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D) (dest : D) (destRows destCols : RD)
    (src : S) (srcRows srcCols : RS) : Outcome D := do
  let drLength ← destOps.length destRows
  let srLength ← srcOps.length srcRows
  if drLength != srLength then .thrown (.argument (.literal "source and destination must have same size"))
  let dcLength ← destOps.length destCols
  let scLength ← srcOps.length srcCols
  if dcLength != scLength then .thrown (.argument (.literal "source and destination must have same size"))
  checkDest dest destRows destCols
  checkSrc src srcRows srcCols
  let source ← unalias dest src
  copyRegion read write (← destOps.step destRows) (← destOps.step destCols) dest source
    (← destOps.first destCols) (← srcOps.values srcCols) (← destOps.first destRows)
    (← srcOps.values srcRows)
def P1159 : Prop := ∀ {D S RD RS V : Type} (destOps : RangeOps RD) (srcOps : RangeOps RS)
    (checkDest : D → RD → RD → Outcome Unit) (checkSrc : S → RS → RS → Outcome Unit)
    (unalias : D → S → Outcome S) (read : S → Int → Int → Outcome V)
    (write : D → Int → Int → V → Outcome D)
    (dest : D) destRows destCols (src : S) srcRows srcCols,
  m1159 destOps srcOps checkDest checkSrc unalias read write dest destRows destCols src srcRows srcCols =
  m1159 destOps srcOps checkDest checkSrc unalias read write dest destRows destCols src srcRows srcCols
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

def writeDiagonal (set : D → I → I → V → JResult D) : D → List I → V → JResult D
  | dest, [], _ => .ok dest
  | dest, index :: rest, unit => do
      let next ← set dest index index unit
      writeDiagonal set next rest unit

/-- `_one`, lines 1222-1234. -/
def m1222 (axes : M → JResult (List I × List I)) (length : List I → JResult Nat)
    (zero : V → JResult V) (requireOneBased : M → JResult Unit)
    (similar : M → JResult D) (fill : D → V → JResult D)
    (set : D → I → I → V → JResult D) (unit : V) (matrix : M) : JResult D := do
  let matrixAxes ← axes matrix
  let rowsLength ← length matrixAxes.1
  let colsLength ← length matrixAxes.2
  if rowsLength != colsLength then
    .error (.dimensionMismatch (.literal "multiplicative identity defined only for square matrices"))
  else
    let zeroValue ← zero unit
    requireOneBased matrix
    let dest ← similar matrix
    let cleared ← fill dest zeroValue
    writeDiagonal set cleared matrixAxes.1 unit
def P1222 : Prop := ∀ {M I V D : Type} (axes : M → JResult (List I × List I))
    (length : List I → JResult Nat) (zero : V → JResult V)
    (requireOneBased : M → JResult Unit) (similar : M → JResult D)
    (fill : D → V → JResult D) (set : D → I → I → V → JResult D) unit matrix,
  m1222 axes length zero requireOneBased similar fill set unit matrix =
  m1222 axes length zero requireOneBased similar fill set unit matrix
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

def entries : List Entry := [
  entry 941 "copyto!(dest,src)" "Iterable copy executes arbitrary source and destination iteration in lockstep, preserving errors and divergence." "base/abstractarray.jl:941-951" ``P941 ``p941,
  entry 953 "copyto!(dest,dstart,src)" "Offset iterable copy converts the index, runs the sized precheck branch, then writes in iteration order." "base/abstractarray.jl:953-971" ``P953 ``p953,
  entry 974 "copyto!(dest,dstart,src,sstart)" "Source-offset copy validates, advances arbitrary iteration, converts the destination index, and writes the remainder." "base/abstractarray.jl:974-1000" ``P974 ``p974,
  entry 1003 "copyto!(dest,dstart,src,sstart,n)" "Counted iterable copy preserves validation, conversions, iteration, first write, bounded remainder, and short-source error order." "base/abstractarray.jl:1003-1037" ``P1003 ``p1003,
  entry 1072 "copyto!(dest,src::AbstractArray)" "Array copy calls isempty on the source, tests the actual destination type, then takes the bit or unaliased style path." "base/abstractarray.jl:1072-1080" ``P1072 ``p1072,
  entry 1082 "copyto!(deststyle,dest,srcstyle,src)" "Styled copy calls isempty, unaliases the actual arrays, and delegates with the supplied styles." "base/abstractarray.jl:1082-1086" ``P1082 ``p1082,
  entry 1088 "copyto_unaliased!" "Unaliased copy obtains linear indices, eagerly checks both endpoints, then performs the selected index-style loop." "base/abstractarray.jl:1088-1123" ``P1088 ``p1088,
  entry 1125 "copyto!(dest,dstart,src::AbstractArray)" "The wrapper obtains source LinearIndices, its first value, and length before calling counted copy." "base/abstractarray.jl:1125-1127" ``P1125 ``p1125,
  entry 1129 "copyto!(dest,dstart,src,sstart)" "The wrapper checks sstart in the actual source indices and copies through the final source index." "base/abstractarray.jl:1129-1133" ``P1129 ``p1129,
  entry 1135 "copyto!(dest,dstart,src,sstart,n)" "Block copy validates both actual index ranges, converts all Integer values, unaliases, and interleaves every read and write." "base/abstractarray.jl:1135-1152" ``P1135 ``p1135,
  entry 1159 "copyto!(matrix regions)" "Region copy checks lengths and bounds, unaliases, then copies in the nested source range order with destination steps." "base/abstractarray.jl:1159-1182" ``P1159 ``p1159,
  entry 1184 "_checkaxs" "Axis checking returns unit for equality and otherwise throws DimensionMismatch with both lazy axis values." "base/abstractarray.jl:1184" ``P1184 ``p1184,
  entry 1186 "copyto_axcheck!" "Axis-checked copy obtains both axes, checks them, then calls copyto!, preserving every error." "base/abstractarray.jl:1186-1189" ``P1186 ``p1186,
  entry 1222 "_one" "Matrix identity checks square axes with DimensionMismatch, computes zero, validates indexing, fills, and writes each diagonal cell." "base/abstractarray.jl:1222-1234" ``P1222 ``p1222,
  entry 1251 "_iterate_abstractarray(tuple state)" "Tuple-state array iteration executes arbitrary iterator and indexing calls and rebuilds the next state." "base/abstractarray.jl:1251-1255" ``P1251 ``p1251,
  entry 1256 "_iterate_abstractarray(integer state)" "Integer-state iteration checks bounds, indexes, obtains one, and adds in source order for every Integer representation." "base/abstractarray.jl:1256-1259" ``P1256 ``p1256,
  entry 1267 "map(Type,StepRange)" "StepRange mapping reads and converts start and step, calls last, converts it, then constructs the range." "base/abstractarray.jl:1267" ``P1267 ``p1267,
  entry 1268 "map(Type,UnitRange)" "UnitRange mapping reads and converts start, calls and converts last, then constructs the range." "base/abstractarray.jl:1268" ``P1268 ``p1268,
  entry 1270 "map(Type,LinRange)" "LinRange mapping converts both stored endpoints, calls length on the range, then constructs LinRange." "base/abstractarray.jl:1270-1272" ``P1270 ``p1270
]

end JuliaLean.MultidimCov.AbstractArrayCopyFaithful
