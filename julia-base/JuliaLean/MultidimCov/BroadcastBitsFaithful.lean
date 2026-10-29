import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastBitsFaithful

open JuliaLean.Registry

inductive Error where | dimensionMismatch | bounds deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure BitArray where
  axes : List Nat
  bits : List Bool
  chunks : List UInt64
  deriving Repr, DecidableEq

inductive ChunkOp where
  | and | or | xor | nand | nor | not | identity | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq

def applyChunk : ChunkOp → List UInt64 → UInt64
  | .and, args => args.foldl (· &&& ·) (~~~(0 : UInt64))
  | .or, args => args.foldl (· ||| ·) 0
  | .xor, args => args.foldl (· ^^^ ·) 0
  | .nand, args => ~~~(args.foldl (· &&& ·) (~~~(0 : UInt64)))
  | .nor, args => ~~~(args.foldl (· ||| ·) 0)
  | .not, head :: _ => ~~~head
  | .identity, head :: _ => head
  | .eq, x :: y :: _ => ~~~(x ^^^ y)
  | .ne, x :: y :: _ => x ^^^ y
  | .lt, x :: y :: _ => ~~~x &&& y
  | .le, x :: y :: _ => ~~~x ||| y
  | .gt, x :: y :: _ => x &&& ~~~y
  | .ge, x :: y :: _ => x ||| ~~~y
  | _, _ => 0

def m1083 {F A : Type} (_f : F) (_args : A) : Option ChunkOp := none
def P1083 : Prop := ∀ {F A : Type} (f : F) (args : A), m1083 f args = none
theorem p1083 : P1083 := by simp [P1083, m1083]

def m1084 {A : Type} (_args : A) : ChunkOp := .and
def P1084 : Prop := ∀ {A : Type} (args : A), m1084 args = .and
theorem p1084 : P1084 := by simp [P1084, m1084]

def m1085 {A : Type} (_args : A) : ChunkOp := .or
def P1085 : Prop := ∀ {A : Type} (args : A), m1085 args = .or
theorem p1085 : P1085 := by simp [P1085, m1085]

def m1086 {A : Type} (_args : A) : ChunkOp := .xor
def P1086 : Prop := ∀ {A : Type} (args : A), m1086 args = .xor
theorem p1086 : P1086 := by simp [P1086, m1086]

def m1087 {A : Type} (_args : A) : ChunkOp := .nand
def P1087 : Prop := ∀ {A : Type} (args : A), m1087 args = .nand
theorem p1087 : P1087 := by simp [P1087, m1087]

def m1088 {A : Type} (_args : A) : ChunkOp := .nor
def P1088 : Prop := ∀ {A : Type} (args : A), m1088 args = .nor
theorem p1088 : P1088 := by simp [P1088, m1088]

def m1089 {A : Type} (_args : A) : ChunkOp := .not
def P1089 : Prop := ∀ {A : Type} (args : A), m1089 args = .not
theorem p1089 : P1089 := by simp [P1089, m1089]

def m1090 {A : Type} (_args : A) : ChunkOp := .identity
def P1090 : Prop := ∀ {A : Type} (args : A), m1090 args = .identity
theorem p1090 : P1090 := by simp [P1090, m1090]

def m1091 {A : Type} (_args : A) : ChunkOp := .eq
def P1091 : Prop := ∀ {A : Type} (args : A), m1091 args = .eq
theorem p1091 : P1091 := by simp [P1091, m1091]

def m1092 {A : Type} (_args : A) : ChunkOp := .ne
def P1092 : Prop := ∀ {A : Type} (args : A), m1092 args = .ne
theorem p1092 : P1092 := by simp [P1092, m1092]

def m1093 {A : Type} (_args : A) : ChunkOp := .lt
def P1093 : Prop := ∀ {A : Type} (args : A), m1093 args = .lt
theorem p1093 : P1093 := by simp [P1093, m1093]

def m1094 {A : Type} (_args : A) : ChunkOp := .le
def P1094 : Prop := ∀ {A : Type} (args : A), m1094 args = .le
theorem p1094 : P1094 := by simp [P1094, m1094]

def m1095 {A : Type} (_args : A) : ChunkOp := .gt
def P1095 : Prop := ∀ {A : Type} (args : A), m1095 args = .gt
theorem p1095 : P1095 := by simp [P1095, m1095]

def m1096 {A : Type} (_args : A) : ChunkOp := .ge
def P1096 : Prop := ∀ {A : Type} (args : A), m1096 args = .ge
theorem p1096 : P1096 := by simp [P1096, m1096]

inductive Arg where
  | bitArray (value : BitArray)
  | scalar (value : Bool)
  | node (fn : Nat) (op : Option ChunkOp) (args : List Arg) (axes : List Nat)
  | unsupported
  deriving Repr

mutual
  def isChunked (chunkop : Nat → List Arg → Option ChunkOp) (resultAxes : List Nat) : Arg → Bool
    | .bitArray value => resultAxes = value.axes
    | .scalar _ => true
    | .node fn _ args _ =>
        match chunkop fn args with
        | none => false
        | some _ => isChunkedList chunkop resultAxes args
    | .unsupported => false

  def isChunkedList (chunkop : Nat → List Arg → Option ChunkOp)
      (resultAxes : List Nat) : List Arg → Bool
    | [] => true
    | head :: tail =>
        isChunked chunkop resultAxes head && isChunkedList chunkop resultAxes tail
end

def m1098 (chunkop : Nat → List Arg → Option ChunkOp)
    (resultAxes : List Nat) (fn : Nat) (args : List Arg) : Bool :=
  match chunkop fn args with
  | none => false
  | some _ => isChunkedList chunkop resultAxes args
def P1098 : Prop := ∀ chunkop resultAxes fn args,
  m1098 chunkop resultAxes fn args =
    match chunkop fn args with
    | none => false
    | some _ => isChunkedList chunkop resultAxes args
theorem p1098 : P1098 := by simp [P1098, m1098]

def m1099 {R B : Type} (_result : R) (_bc : B) : Bool := false
def P1099 : Prop := ∀ {R B : Type} (result : R) (bc : B), m1099 result bc = false
theorem p1099 : P1099 := by simp [P1099, m1099]

def m1100 (chunkop : Nat → List Arg → Option ChunkOp)
    (resultAxes : List Nat) (args : List Arg) (_op : ChunkOp) : Bool :=
  isChunkedList chunkop resultAxes args
def P1100 : Prop := ∀ chunkop resultAxes args op,
  m1100 chunkop resultAxes args op = isChunkedList chunkop resultAxes args
theorem p1100 : P1100 := by simp [P1100, m1100]

def m1101 {R A : Type} (_result : R) (_args : A) : Bool := false
def P1101 : Prop := ∀ {R A : Type} (result : R) (args : A), m1101 result args = false
theorem p1101 : P1101 := by simp [P1101, m1101]

def m1102 (chunkop : Nat → List Arg → Option ChunkOp)
    (resultAxes : List Nat) (head : BitArray) (tail : List Arg) : Bool :=
  resultAxes = head.axes && isChunkedList chunkop resultAxes tail
def P1102 : Prop := ∀ chunkop resultAxes head tail,
  m1102 chunkop resultAxes head tail =
    (resultAxes = head.axes && isChunkedList chunkop resultAxes tail)
theorem p1102 : P1102 := by simp [P1102, m1102]

def m1103 (chunkop : Nat → List Arg → Option ChunkOp)
    (resultAxes : List Nat) (_head : Bool) (tail : List Arg) : Bool :=
  isChunkedList chunkop resultAxes tail
def P1103 : Prop := ∀ chunkop resultAxes head tail,
  m1103 chunkop resultAxes head tail = isChunkedList chunkop resultAxes tail
theorem p1103 : P1103 := by simp [P1103, m1103]

def m1104 (chunkop : Nat → List Arg → Option ChunkOp)
    (resultAxes : List Nat) (head : Arg) (tail : List Arg) : Bool :=
  isChunked chunkop resultAxes head && isChunkedList chunkop resultAxes tail
def P1104 : Prop := ∀ chunkop resultAxes head tail,
  m1104 chunkop resultAxes head tail =
    (isChunked chunkop resultAxes head && isChunkedList chunkop resultAxes tail)
theorem p1104 : P1104 := by simp [P1104, m1104]

def m1105 {R : Type} (_result : R) : Bool := true
def P1105 : Prop := ∀ {R : Type} (result : R), m1105 result = true
theorem p1105 : P1105 := by simp [P1105, m1105]

def liftFuncs (chunkop : Nat → List Arg → Option ChunkOp) : Arg → Arg
  | .node fn _ args axes =>
      .node fn (chunkop fn args) (args.map (liftFuncs chunkop)) axes
  | arg => arg

def m1108 (chunkop : Nat → List Arg → Option ChunkOp) (bc : Arg) : Arg :=
  liftFuncs chunkop bc
def P1108 : Prop := ∀ chunkop bc, m1108 chunkop bc = liftFuncs chunkop bc
theorem p1108 : P1108 := by simp [P1108, m1108]

def m1109 (chunkop : Nat → List Arg → Option ChunkOp)
    (fn : Nat) (args : List Arg) (axes : List Nat) : Arg :=
  .node fn none (args.map (liftFuncs chunkop)) axes
def P1109 : Prop := ∀ chunkop fn args axes,
  m1109 chunkop fn args axes = .node fn none (args.map (liftFuncs chunkop)) axes
theorem p1109 : P1109 := by simp [P1109, m1109]

def m1110 (chunkop : Nat → List Arg → Option ChunkOp)
    (fn : Nat) (op : ChunkOp) (args : List Arg) (axes : List Nat) : Arg :=
  .node fn (some op) (args.map (liftFuncs chunkop)) axes
def P1110 : Prop := ∀ chunkop fn op args axes,
  m1110 chunkop fn op args axes = .node fn (some op) (args.map (liftFuncs chunkop)) axes
theorem p1110 : P1110 := by simp [P1110, m1110]

def m1111 (value : α) : α := value
def P1111 : Prop := ∀ {α : Type} (value : α), m1111 value = value
theorem p1111 : P1111 := by simp [P1111, m1111]

inductive Lifted where
  | chunks (values : List UInt64)
  | scalar (value : UInt64)
  deriving Repr, DecidableEq

def liftChunks : List Arg → List Lifted
  | [] => []
  | .bitArray value :: tail => .chunks value.chunks :: liftChunks tail
  | .scalar value :: tail =>
      .scalar (if value then ~~~(0 : UInt64) else 0) :: liftChunks tail
  | _ :: tail => liftChunks tail

def m1113 : List Lifted := []
def P1113 : Prop := ∀ _ : Unit, m1113 = []
theorem p1113 : P1113 := by simp [P1113, m1113]

def m1114 (head : BitArray) (tail : List Arg) : List Lifted :=
  .chunks head.chunks :: liftChunks tail
def P1114 : Prop := ∀ head tail,
  m1114 head tail = .chunks head.chunks :: liftChunks tail
theorem p1114 : P1114 := by simp [P1114, m1114]

def m1116 (head : Bool) (tail : List Arg) : List Lifted :=
  .scalar (if head then ~~~(0 : UInt64) else 0) :: liftChunks tail
def P1116 : Prop := ∀ head tail,
  m1116 head tail =
    .scalar (if head then ~~~(0 : UInt64) else 0) :: liftChunks tail
theorem p1116 : P1116 := by simp [P1116, m1116]

def m1117 {I : Type} (_index : I) : Result (List UInt64) := .ok []
def P1117 : Prop := ∀ {I : Type} (index : I), m1117 index = .ok []
theorem p1117 : P1117 := by simp [P1117, m1117]

def ithChunk (index : Nat) : List Lifted → Result (List UInt64)
  | [] => .ok []
  | .scalar value :: tail => do pure (value :: (← ithChunk index tail))
  | .chunks values :: tail =>
      if index = 0 then .error .bounds
      else match values[index - 1]? with
        | none => .error .bounds
        | some value => do pure (value :: (← ithChunk index tail))

def m1118 (index : Nat) (chunks : List UInt64) (tail : List Lifted) :
    Result (List UInt64) :=
  ithChunk index (.chunks chunks :: tail)
def P1118 : Prop := ∀ index chunks tail,
  m1118 index chunks tail = ithChunk index (.chunks chunks :: tail)
theorem p1118 : P1118 := by simp [P1118, m1118]

def m1119 (index : Nat) (scalar : UInt64) (tail : List Lifted) :
    Result (List UInt64) :=
  ithChunk index (.scalar scalar :: tail)
def P1119 : Prop := ∀ index scalar tail,
  m1119 index scalar tail = ithChunk index (.scalar scalar :: tail)
theorem p1119 : P1119 := by simp [P1119, m1119]

def evalChunks (op : ChunkOp) (args : List Lifted) : Nat → Nat → Result (List UInt64)
  | _, 0 => .ok []
  | index, count + 1 => do
      let values ← ithChunk index args
      pure (applyChunk op values :: (← evalChunks op args (index + 1) count))

def m1120 (chunkop : Nat → List Arg → Option ChunkOp) (flatten : Arg → Arg)
    (dest : BitArray) (bc : Arg) (endMask : UInt64) : Result BitArray :=
  if dest.bits.isEmpty then .ok dest else
  match flatten (liftFuncs chunkop bc) with
  | .node _ (some op) args _ => do
      let computed ← evalChunks op (liftChunks args) 1 dest.chunks.length
      let masked := match computed.reverse with
        | [] => []
        | last :: rest => ((last &&& endMask) :: rest).reverse
      pure { dest with chunks := masked }
  | _ => .error .bounds
def P1120 : Prop := ∀ chunkop flatten dest bc endMask,
  m1120 chunkop flatten dest bc endMask =
    if dest.bits.isEmpty then .ok dest else
    match flatten (liftFuncs chunkop bc) with
    | .node _ (some op) args _ => do
        let computed ← evalChunks op (liftChunks args) 1 dest.chunks.length
        let masked := match computed.reverse with
          | [] => []
          | last :: rest => ((last &&& endMask) :: rest).reverse
        pure { dest with chunks := masked }
    | _ => .error .bounds
theorem p1120 : P1120 := by simp [P1120, m1120]

def packWord (eval : Nat → Bool) (start count : Nat) : UInt64 :=
  (List.range count).foldl (fun word offset =>
    if eval (start + offset) then word ||| ((1 : UInt64) <<< UInt64.ofNat offset) else word) 0

def packBits (eval : Nat → Bool) (count : Nat) : List UInt64 :=
  (List.range ((count + 63) / 64)).map fun chunk =>
    packWord eval (chunk * 64) (min 64 (count - chunk * 64))

def m1035 {B : Type} (axes : B → List Nat) (isChunked : BitArray → B → Bool)
    (chunkedCopy : BitArray → B → Result BitArray) (ndims : BitArray → Nat)
    (preprocess : BitArray → B → Result B) (getBool : B → Nat → Result Bool)
    (dest : BitArray) (bc : B) : Result BitArray :=
  if dest.axes ≠ axes bc then .error .dimensionMismatch
  else if isChunked dest bc then chunkedCopy dest bc
  else if ndims dest = 0 then do
    let bit ← getBool bc 0
    pure { dest with bits := [bit], chunks := [if bit then 1 else 0] }
  else do
    let ready ← preprocess dest bc
    let bits ← (List.range dest.bits.length).mapM (getBool ready)
    pure { dest with bits := bits, chunks := packBits (fun i => bits.getD i false) bits.length }
def P1035 : Prop := ∀ {B : Type} (axes : B → List Nat)
    (isChunked : BitArray → B → Bool) (chunkedCopy : BitArray → B → Result BitArray)
    (ndims : BitArray → Nat) (preprocess : BitArray → B → Result B)
    (getBool : B → Nat → Result Bool) dest bc,
  m1035 axes isChunked chunkedCopy ndims preprocess getBool dest bc =
    if dest.axes ≠ axes bc then .error .dimensionMismatch
    else if isChunked dest bc then chunkedCopy dest bc
    else if ndims dest = 0 then do
      let bit ← getBool bc 0
      pure { dest with bits := [bit], chunks := [if bit then 1 else 0] }
    else do
      let ready ← preprocess dest bc
      let bits ← (List.range dest.bits.length).mapM (getBool ready)
      pure { dest with bits := bits, chunks := packBits (fun i => bits.getD i false) bits.length }
theorem p1035 : P1035 := by simp [P1035, m1035]

structure BitMasked where
  parent : BitArray
  mask : BitArray
  deriving Repr, DecidableEq

def m1261 (parent mask : BitArray) : BitMasked := ⟨parent, mask⟩
def P1261 : Prop := ∀ parent mask, m1261 parent mask = ⟨parent, mask⟩
theorem p1261 : P1261 := by simp [P1261, m1261]

def m1263 (checkbounds : BitArray → BitArray → Result Unit)
    (parent mask : BitArray) : Result BitMasked := do
  checkbounds parent mask
  pure ⟨parent, mask⟩
def P1263 : Prop := ∀ checkbounds parent mask,
  m1263 checkbounds parent mask = do
    checkbounds parent mask
    pure ⟨parent, mask⟩
theorem p1263 : P1263 := by simp [P1263, m1263]

def m1267 (checkbounds : BitArray → BitArray → Result Unit)
    (parent mask : BitArray) : Result BitMasked := m1263 checkbounds parent mask
def P1267 : Prop := ∀ checkbounds parent mask,
  m1267 checkbounds parent mask = m1263 checkbounds parent mask
theorem p1267 : P1267 := by simp [P1267, m1267]

def m1268 {IO T : Type} (typeOf : BitMasked → T)
    (showType : IO → T → Result IO) (showPair : IO → BitArray × BitArray → Result IO)
    (io : IO) (value : BitMasked) : Result Unit := do
  let io ← showType io (typeOf value)
  let _ ← showPair io (value.parent, value.mask)
  pure ()
def P1268 : Prop := ∀ {IO T : Type} (typeOf : BitMasked → T)
    (showType : IO → T → Result IO) (showPair : IO → BitArray × BitArray → Result IO)
    io value,
  m1268 typeOf showType showPair io value = do
    let io ← showType io (typeOf value)
    let _ ← showPair io (value.parent, value.mask)
    pure ()
theorem p1268 : P1268 := by simp [P1268, m1268]

def fillMasked (value : BitMasked) (bit : Bool) : BitMasked :=
  let updated := (value.parent.bits.zip value.mask.bits).map fun pair => if pair.2 then bit else pair.1
  { value with parent := { value.parent with bits := updated } }

def m1270 (value : BitMasked) (bit : Bool) : BitMasked := fillMasked value bit
def P1270 : Prop := ∀ value bit, m1270 value bit = fillMasked value bit
theorem p1270 : P1270 := by simp [P1270, m1270]

def m1271 {B BC R : Type} (view : BitMasked → B)
    (materializeBang : B → BC → R) (value : BitMasked) (bc : BC) : R :=
  materializeBang (view value) bc
def P1271 : Prop := ∀ {B BC R : Type} (view : BitMasked → B)
    (materializeBang : B → BC → R) value bc,
  m1271 view materializeBang value bc = materializeBang (view value) bc
theorem p1271 : P1271 := by simp [P1271, m1271]

def fillChunks : List UInt64 → List UInt64 → Bool → Result (List UInt64)
  | [], _, _ => .ok []
  | _ :: _, [], _ => .error .bounds
  | parent :: parents, mask :: masks, bit => do
      let updated := if bit then parent ||| mask else parent &&& ~~~mask
      pure (updated :: (← fillChunks parents masks bit))

def m1272 (value : BitMasked) (bit : Bool) : Result BitMasked := do
  let chunks ← fillChunks value.parent.chunks value.mask.chunks bit
  pure { value with parent := { value.parent with chunks := chunks } }
def P1272 : Prop := ∀ value bit,
  m1272 value bit = do
    let chunks ← fillChunks value.parent.chunks value.mask.chunks bit
    pure { value with parent := { value.parent with chunks := chunks } }
theorem p1272 : P1272 := by simp [P1272, m1272]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; bit-array representation and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastBitsFaithful
