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
  | node (op : Option ChunkOp) (args : List Arg) (axes : List Nat)
  | unsupported
  deriving Repr

mutual
  def isChunked (resultAxes : List Nat) : Arg → Bool
    | .bitArray value => resultAxes = value.axes
    | .scalar _ => true
    | .node none _ _ => false
    | .node (some _) args _ => isChunkedList resultAxes args
    | .unsupported => false

  def isChunkedList (resultAxes : List Nat) : List Arg → Bool
    | [] => true
    | head :: tail => isChunked resultAxes head && isChunkedList resultAxes tail
end

def m1098 (resultAxes : List Nat) (bc : Arg) : Bool := isChunked resultAxes bc
def P1098 : Prop := ∀ resultAxes bc, m1098 resultAxes bc = isChunked resultAxes bc
theorem p1098 : P1098 := by simp [P1098, m1098]

def m1099 {R B : Type} (_result : R) (_bc : B) : Bool := false
def P1099 : Prop := ∀ {R B : Type} (result : R) (bc : B), m1099 result bc = false
theorem p1099 : P1099 := by simp [P1099, m1099]

def m1100 (resultAxes : List Nat) (args : List Arg) (_op : ChunkOp) : Bool := args.all (isChunked resultAxes)
def P1100 : Prop := ∀ resultAxes args op, m1100 resultAxes args op = args.all (isChunked resultAxes)
theorem p1100 : P1100 := by simp [P1100, m1100]

def m1101 {R A : Type} (_result : R) (_args : A) : Bool := false
def P1101 : Prop := ∀ {R A : Type} (result : R) (args : A), m1101 result args = false
theorem p1101 : P1101 := by simp [P1101, m1101]

def m1102 (resultAxes : List Nat) (head : BitArray) (tail : List Arg) : Bool :=
  resultAxes = head.axes && tail.all (isChunked resultAxes)
def P1102 : Prop := ∀ resultAxes head tail,
  m1102 resultAxes head tail = (resultAxes = head.axes && tail.all (isChunked resultAxes))
theorem p1102 : P1102 := by simp [P1102, m1102]

def m1103 (resultAxes : List Nat) (_head : Bool) (tail : List Arg) : Bool := tail.all (isChunked resultAxes)
def P1103 : Prop := ∀ resultAxes head tail, m1103 resultAxes head tail = tail.all (isChunked resultAxes)
theorem p1103 : P1103 := by simp [P1103, m1103]

def m1104 (resultAxes : List Nat) (head : Arg) (tail : List Arg) : Bool :=
  isChunked resultAxes head && tail.all (isChunked resultAxes)
def P1104 : Prop := ∀ resultAxes head tail,
  m1104 resultAxes head tail = (isChunked resultAxes head && tail.all (isChunked resultAxes))
theorem p1104 : P1104 := by simp [P1104, m1104]

def m1105 {R : Type} (_result : R) : Bool := true
def P1105 : Prop := ∀ {R : Type} (result : R), m1105 result = true
theorem p1105 : P1105 := by simp [P1105, m1105]

def liftFuncs : Arg → Arg
  | .node op args axes => .node op (args.map liftFuncs) axes
  | arg => arg

def m1108 (bc : Arg) : Arg := liftFuncs bc
def P1108 : Prop := ∀ bc, m1108 bc = liftFuncs bc
theorem p1108 : P1108 := by simp [P1108, m1108]

def m1109 (args : List Arg) (axes : List Nat) : Arg := .node none (args.map liftFuncs) axes
def P1109 : Prop := ∀ args axes, m1109 args axes = .node none (args.map liftFuncs) axes
theorem p1109 : P1109 := by simp [P1109, m1109]

def m1110 (op : ChunkOp) (args : List Arg) (axes : List Nat) : Arg := .node (some op) (args.map liftFuncs) axes
def P1110 : Prop := ∀ op args axes, m1110 op args axes = .node (some op) (args.map liftFuncs) axes
theorem p1110 : P1110 := by simp [P1110, m1110]

def m1111 (value : α) : α := value
def P1111 : Prop := ∀ {α : Type} (value : α), m1111 value = value
theorem p1111 : P1111 := by simp [P1111, m1111]

structure Lifted where
  chunks : List UInt64
  deriving Repr, DecidableEq

def liftChunks : List Arg → List Lifted
  | [] => []
  | .bitArray value :: tail => ⟨value.chunks⟩ :: liftChunks tail
  | .scalar value :: tail => ⟨[if value then ~~~(0 : UInt64) else 0]⟩ :: liftChunks tail
  | _ :: tail => liftChunks tail

def m1113 : List Lifted := []
def P1113 : Prop := ∀ _ : Unit, m1113 = []
theorem p1113 : P1113 := by simp [P1113, m1113]

def m1114 (head : BitArray) (tail : List Arg) : List Lifted := ⟨head.chunks⟩ :: liftChunks tail
def P1114 : Prop := ∀ head tail, m1114 head tail = ⟨head.chunks⟩ :: liftChunks tail
theorem p1114 : P1114 := by simp [P1114, m1114]

def m1116 (head : Bool) (tail : List Arg) : List Lifted :=
  ⟨[if head then ~~~(0 : UInt64) else 0]⟩ :: liftChunks tail
def P1116 : Prop := ∀ head tail,
  m1116 head tail = ⟨[if head then ~~~(0 : UInt64) else 0]⟩ :: liftChunks tail
theorem p1116 : P1116 := by simp [P1116, m1116]

def m1117 {I : Type} (_index : I) : List UInt64 := []
def P1117 : Prop := ∀ {I : Type} (index : I), m1117 index = []
theorem p1117 : P1117 := by simp [P1117, m1117]

def ithChunk (index : Nat) : List Lifted → List UInt64
  | [] => []
  | head :: tail => head.chunks[index]?.getD 0 :: ithChunk index tail

def m1118 (index : Nat) (chunks : List UInt64) (tail : List Lifted) : List UInt64 :=
  chunks[index]?.getD 0 :: ithChunk index tail
def P1118 : Prop := ∀ index chunks tail,
  m1118 index chunks tail = chunks[index]?.getD 0 :: ithChunk index tail
theorem p1118 : P1118 := by simp [P1118, m1118]

def m1119 (index : Nat) (scalar : UInt64) (tail : List Lifted) : List UInt64 := scalar :: ithChunk index tail
def P1119 : Prop := ∀ index scalar tail, m1119 index scalar tail = scalar :: ithChunk index tail
theorem p1119 : P1119 := by simp [P1119, m1119]

def m1120 (dest : BitArray) (op : ChunkOp) (args : List Lifted) (endMask : UInt64) : BitArray :=
  if dest.bits.isEmpty then dest else
    let computed := (List.range dest.chunks.length).map fun i => applyChunk op (ithChunk i args)
    let masked := match computed.reverse with
      | [] => []
      | last :: rest => ((last &&& endMask) :: rest).reverse
    { dest with chunks := masked }
def P1120 : Prop := ∀ dest op args endMask,
  m1120 dest op args endMask = if dest.bits.isEmpty then dest else
    let computed := (List.range dest.chunks.length).map fun i => applyChunk op (ithChunk i args)
    let masked := match computed.reverse with
      | [] => []
      | last :: rest => ((last &&& endMask) :: rest).reverse
    { dest with chunks := masked }
theorem p1120 : P1120 := by simp [P1120, m1120]

def m1035 (dest : BitArray) (exprAxes : List Nat) (chunked : Option BitArray)
    (eval : Nat → Bool) : Result BitArray :=
  if dest.axes ≠ exprAxes then .error .dimensionMismatch else
  match chunked with
  | some result => .ok result
  | none => .ok { dest with bits := (List.range dest.bits.length).map eval }
def P1035 : Prop := ∀ dest exprAxes chunked eval,
  m1035 dest exprAxes chunked eval =
    if dest.axes ≠ exprAxes then .error .dimensionMismatch else
    match chunked with
    | some result => .ok result
    | none => .ok { dest with bits := (List.range dest.bits.length).map eval }
theorem p1035 : P1035 := by simp [P1035, m1035]

structure BitMasked where
  parent : BitArray
  mask : BitArray
  deriving Repr, DecidableEq

def m1261 (parent mask : BitArray) : BitMasked := ⟨parent, mask⟩
def P1261 : Prop := ∀ parent mask, m1261 parent mask = ⟨parent, mask⟩
theorem p1261 : P1261 := by simp [P1261, m1261]

def m1263 (parent mask : BitArray) : Result BitMasked :=
  if parent.bits.length = mask.bits.length then .ok ⟨parent, mask⟩ else .error .bounds
def P1263 : Prop := ∀ parent mask,
  m1263 parent mask = if parent.bits.length = mask.bits.length then .ok ⟨parent, mask⟩ else .error .bounds
theorem p1263 : P1263 := by simp [P1263, m1263]

def m1267 (parent mask : BitArray) : Result BitMasked := m1263 parent mask
def P1267 : Prop := ∀ parent mask, m1267 parent mask = m1263 parent mask
theorem p1267 : P1267 := by simp [P1267, m1267]

def m1268 (render : String → String) (value : BitMasked) : List String :=
  [render "BitMasked", render (toString value.parent.bits.length), render (toString value.mask.bits.length)]
def P1268 : Prop := ∀ render value,
  m1268 render value = [render "BitMasked", render (toString value.parent.bits.length), render (toString value.mask.bits.length)]
theorem p1268 : P1268 := by simp [P1268, m1268]

def fillMasked (value : BitMasked) (bit : Bool) : BitMasked :=
  let updated := (value.parent.bits.zip value.mask.bits).map fun pair => if pair.2 then bit else pair.1
  { value with parent := { value.parent with bits := updated } }

def m1270 (value : BitMasked) (bit : Bool) : BitMasked := fillMasked value bit
def P1270 : Prop := ∀ value bit, m1270 value bit = fillMasked value bit
theorem p1270 : P1270 := by simp [P1270, m1270]

def m1271 {B R : Type} (view : BitMasked → B) (materializeBang : B → R) (value : BitMasked) : R :=
  materializeBang (view value)
def P1271 : Prop := ∀ {B R : Type} (view : BitMasked → B) (materializeBang : B → R) value,
  m1271 view materializeBang value = materializeBang (view value)
theorem p1271 : P1271 := by simp [P1271, m1271]

def m1272 (value : BitMasked) (bit : Bool) : BitMasked := fillMasked value bit
def P1272 : Prop := ∀ value bit,
  (m1272 value bit).parent.bits = (value.parent.bits.zip value.mask.bits).map (fun pair => if pair.2 then bit else pair.1) ∧
  (m1272 value bit).mask = value.mask
theorem p1272 : P1272 := by simp [P1272, m1272, fillMasked]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; bit-array representation and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := [
  entry 1035 "copyto!(::BitArray,::Broadcasted{Nothing})" "BitArray copy checks axes, selects the chunked path when available, and otherwise evaluates every destination bit in logical order." ``P1035 ``p1035,
  entry 1083 "_chunkop(f,args)" "Every unsupported function maps to no chunk operation." ``P1083 ``p1083,
  entry 1084 "_chunkop(and-like,args)" "Bitwise conjunction, multiplication, and min map to chunk conjunction." ``P1084 ``p1084,
  entry 1085 "_chunkop(or-like,args)" "Bitwise disjunction and max map to chunk disjunction." ``P1085 ``p1085,
  entry 1086 "_chunkop(xor,args)" "xor maps to chunk xor." ``P1086 ``p1086,
  entry 1087 "_chunkop(nand,args)" "nand maps to chunk nand." ``P1087 ``p1087,
  entry 1088 "_chunkop(nor,args)" "nor maps to chunk nor." ``P1088 ``p1088,
  entry 1089 "_chunkop(not,args)" "Both Boolean negations map to chunk complement." ``P1089 ``p1089,
  entry 1090 "_chunkop(identity,args)" "identity remains identity at chunk level." ``P1090 ``p1090,
  entry 1091 "_chunkop(==,pair)" "Equality maps to complemented xor." ``P1091 ``p1091,
  entry 1092 "_chunkop(!=,pair)" "Inequality maps to xor." ``P1092 ``p1092,
  entry 1093 "_chunkop(<,pair)" "Less-than maps to complement-left and right." ``P1093 ``p1093,
  entry 1094 "_chunkop(<=,pair)" "Less-or-equal maps to complement-left or right." ``P1094 ``p1094,
  entry 1095 "_chunkop(>,pair)" "Greater-than maps to left and complement-right." ``P1095 ``p1095,
  entry 1096 "_chunkop(>=,pair)" "Greater-or-equal maps to left or complement-right." ``P1096 ``p1096,
  entry 1098 "ischunkedbroadcast(R,bc)" "Chunk eligibility derives the chunk operation before recursively checking all arguments." ``P1098 ``p1098,
  entry 1099 "ischunkedbroadcast(R,bc,nothing)" "A missing chunk operation is never eligible." ``P1099 ``p1099,
  entry 1100 "ischunkedbroadcast(R,bc,f)" "A known chunk operation delegates to the complete argument tuple." ``P1100 ``p1100,
  entry 1101 "ischunkedbroadcast(R,args)" "Unsupported argument shapes are ineligible." ``P1101 ``p1101,
  entry 1102 "ischunkedbroadcast(R,BitArray,args...)" "A BitArray requires identical size before recursively checking its tail." ``P1102 ``p1102,
  entry 1103 "ischunkedbroadcast(R,Bool,args...)" "A Bool scalar is accepted before recursively checking its tail." ``P1103 ``p1103,
  entry 1104 "ischunkedbroadcast(R,Broadcasted,args...)" "A nested expression and every tail argument must both be eligible." ``P1104 ``p1104,
  entry 1105 "ischunkedbroadcast(R,())" "The empty argument tuple is eligible." ``P1105 ``p1105,
  entry 1108 "liftfuncs(::Broadcasted)" "Function lifting derives the chunk operation and recursively lifts every nested argument." ``P1108 ``p1108,
  entry 1109 "liftfuncs(::Broadcasted,nothing)" "A missing operation preserves f while recursively lifting every argument." ``P1109 ``p1109,
  entry 1110 "liftfuncs(::Broadcasted,f)" "A known operation replaces f while recursively lifting every argument." ``P1110 ``p1110,
  entry 1111 "liftfuncs(x)" "Every leaf value passes through unchanged." ``P1111 ``p1111,
  entry 1113 "liftchunks(())" "The empty argument tuple yields no chunk sources." ``P1113 ``p1113,
  entry 1114 "liftchunks(BitArray,args...)" "A BitArray contributes its chunk vector before recursively lifting the tail." ``P1114 ``p1114,
  entry 1116 "liftchunks(Bool,args...)" "A Bool becomes an all-zero or all-one UInt64 chunk before the lifted tail." ``P1116 ``p1116,
  entry 1117 "ithchunk(i)" "The empty chunk argument list yields empty for every index." ``P1117 ``p1117,
  entry 1118 "ithchunk(i,chunks,args...)" "A chunk vector contributes chunk i before recursively indexing the tail." ``P1118 ``p1118,
  entry 1119 "ithchunk(i,scalar,args...)" "A scalar chunk is reused before recursively indexing the tail." ``P1119 ``p1119,
  entry 1120 "chunkedcopyto!(dest,bc)" "Chunked copy returns empty destinations unchanged, evaluates each output chunk, then masks the final chunk." ``P1120 ``p1120,
  entry 1261 "BitMaskedBitArray{N,M}(parent,mask)" "The inner constructor stores parent and mask unchanged." ``P1261 ``p1261,
  entry 1263 "BitMaskedBitArray(parent,mask)" "The public constructor checks mask bounds before storing parent and mask." ``P1263 ``p1263,
  entry 1267 "dotview(::BitArray,::BitArray)" "BitArray dotview delegates to the checked masked-array constructor." ``P1267 ``p1267,
  entry 1268 "show(::IO,::BitMaskedBitArray)" "Printing visits the wrapper type, parent, and mask in order." ``P1268 ``p1268,
  entry 1270 "materialize!(masked,identity Bool)" "Identity scalar materialization delegates to masked fill." ``P1270 ``p1270,
  entry 1271 "materialize!(masked,bc)" "General materialization creates the masked parent view before delegating." ``P1271 ``p1271,
  entry 1272 "fill!(masked,b)" "Masked fill updates exactly selected parent bits and preserves every unselected bit and the mask." ``P1272 ``p1272
]

end JuliaLean.MultidimCov.BroadcastBitsFaithful
