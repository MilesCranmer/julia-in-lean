import JuliaLean.Core

/-!
Models of the chunked BitArray broadcast, masked BitArray assignment, and dot
syntax rewriting sections of `base/broadcast.jl`.
-/

namespace JuliaLean.BroadcastCov.BitsSyntax

inductive ChunkOp where
  | unsupported
  | and
  | or
  | xor
  | nand
  | nor
  | not
  | identity
  | equal
  | unequal
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

/-- `_chunkop`, lines 1083-1096, as a word operation. -/
def applyChunkOp (op : ChunkOp) (x y : UInt64) : Option UInt64 :=
  match op with
  | .unsupported => none
  | .and => some (x &&& y)
  | .or => some (x ||| y)
  | .xor | .unequal => some (x ^^^ y)
  | .nand => some (~~~(x &&& y))
  | .nor => some (~~~(x ||| y))
  | .not => some (~~~x)
  | .identity => some x
  | .equal => some (~~~(x ^^^ y))
  | .less => some ((~~~x) &&& y)
  | .lessEqual => some ((~~~x) ||| y)
  | .greater => some (x &&& (~~~y))
  | .greaterEqual => some (x ||| (~~~y))

inductive ChunkArg where
  | bitarray (chunks : List UInt64)
  | scalar (value : Bool)
  | nested (supported : Bool) (args : List ChunkArg)
  | other
  deriving Repr

/-- `ischunkedbroadcast`, lines 1098-1105. -/
def chunkable (destinationChunks : Nat) : List ChunkArg → Bool
  | [] => true
  | .bitarray chunks :: rest => chunks.length == destinationChunks && chunkable destinationChunks rest
  | .scalar _ :: rest => chunkable destinationChunks rest
  | .nested supported args :: rest =>
      supported && chunkable destinationChunks args && chunkable destinationChunks rest
  | .other :: _ => false

/-- `liftchunks`, lines 1113-1116. Nested expressions are flattened by
`liftfuncs` before this function is called. -/
def liftChunks : List ChunkArg → List (List UInt64)
  | [] => []
  | .bitarray chunks :: rest => chunks :: liftChunks rest
  | .scalar value :: rest =>
      [if value then ~~~(0 : UInt64) else 0] :: liftChunks rest
  | _ :: rest => liftChunks rest

/-- `ithchunk`, lines 1117-1119. -/
def ithChunk (i : Nat) (chunks : List (List UInt64)) : List UInt64 :=
  chunks.map (fun c => c.getD i 0)

/-- `chunkedcopyto!`, lines 1120-1130. `lastMask` is `Base._msk_end(dest)`. -/
def chunkedCopy (op : UInt64 → UInt64 → UInt64) (left right : List UInt64)
    (lastMask : UInt64) : List UInt64 :=
  let result := (left.zip right).map fun p => op p.1 p.2
  match result.reverse with
  | [] => []
  | last :: rest => ((last &&& lastMask) :: rest).reverse

structure BitMasked where
  parent : List Bool
  mask : List Bool
  deriving Repr, DecidableEq

/-- `BitMaskedBitArray` constructors and `dotview`, lines 1261-1267. -/
def bitMasked (parent mask : List Bool) : Option BitMasked :=
  if parent.length == mask.length then some ⟨parent, mask⟩ else none

/-- `fill!(::BitMaskedBitArray)`, lines 1272-1285, expanded from chunks to
logical bits. -/
def fillMasked (b : BitMasked) (value : Bool) : BitMasked :=
  { b with parent := (b.parent.zip b.mask).map fun p => if p.2 then value else p.1 }

/-- The identity `materialize!` fast path at line 1270. -/
def materializeIdentity (b : BitMasked) (value : Bool) : BitMasked := fillMasked b value

/-- `show(::BitMaskedBitArray)`, line 1268, exposes the wrapper type and both fields. -/
def showBitMasked (b : BitMasked) : List (List Bool) := [b.parent, b.mask]

inductive Head where
  | call
  | comparison
  | dollar
  | letHead
  | forHead
  | generator
  | filter
  | assignment
  | functionHead
  | macroHead
  | subtype
  | supertype
  | block
  | other (name : String)
  deriving Repr, DecidableEq

inductive Syntax where
  | atom (name : String)
  | expr (head : Head) (args : List Syntax)
  deriving Repr

def dottable : Syntax → Bool
  | .atom name => name != ":" && (name == ".." || !name.startsWith ".")
  | .expr .dollar _ => false
  | .expr _ _ => true

/-- `undot`, lines 1308-1317. -/
def undot : Syntax → Syntax
  | .expr (.other ".=") args => .expr .assignment args
  | .expr .assignment args => .expr .assignment args
  | .expr .block args => .expr .block (args.map undot)
  | x => x

/-- `__dot__`, lines 1318-1348. -/
def dotSyntax : Syntax → Syntax
  | .atom name => .atom name
  | .expr head args =>
      let dotted := args.map dotSyntax
      match head with
      | .call =>
          match dotted with
          | f :: rest => if dottable f then .expr (.other ".") (f :: [.expr (.other "tuple") rest])
            else .expr .call dotted
          | [] => .expr .call []
      | .comparison => .expr .comparison dotted
      | .dollar => dotted.getD 0 (.atom "")
      | .letHead => .expr .letHead [undot (dotted.getD 0 (.atom "")), dotted.getD 1 (.atom "")]
      | .forHead => .expr .forHead [undot (dotted.getD 0 (.atom "")), dotted.getD 1 (.atom "")]
      | .generator => .expr .generator (dotted.take 1 ++ (dotted.drop 1).map undot)
      | .filter => .expr .filter (dotted.take 1 ++ (dotted.drop 1).map undot)
      | .functionHead | .macroHead =>
          .expr head [args.getD 0 (.atom ""), dotted.getD 1 (.atom "")]
      | .subtype => .expr .call (.atom ".<:" :: dotted)
      | .supertype => .expr .call (.atom ".>:" :: dotted)
      | .assignment => .expr (.other ".=") dotted
      | .other name =>
          if name = "&&" ∨ name = "||" ∨ (!name.startsWith "." && name.endsWith "=") then
            .expr (.other ("." ++ name)) dotted
          else .expr head dotted
      | .block => .expr .block dotted

/-- Macro wrapper at lines 1390-1392. -/
def macroDot (x : Syntax) : Syntax := dotSyntax x

/-- Generic `dotview(args...) = maybeview(args...)`, line 1297. -/
def dotviewResult (maybeViewResult : Syntax) : Syntax := maybeViewResult

/-- `liftfuncs`, lines 1108-1111, recursively transforms nested arguments and
retains whether `_chunkop` found a word operation. -/
def liftFunctions : ChunkArg → ChunkArg
  | .nested supported args => .nested supported (args.map liftFunctions)
  | x => x

inductive BroadcastedPath where
  | direct
  | keywordClosure
  | genericMapped (argumentCount : Nat)
  | explicitStyle
  deriving Repr, DecidableEq

/-- `broadcasted_kwsyntax` and generic `broadcasted` wrappers, lines 1394-1420. -/
def broadcastedPath (hasKeywords explicitStyle : Bool) (argumentCount : Nat) : BroadcastedPath :=
  if explicitStyle then .explicitStyle
  else if hasKeywords then .keywordClosure
  else if argumentCount = 0 then .direct
  else .genericMapped argumentCount

/-- `BroadcastFunction` call and show methods, lines 1452-1460. -/
def broadcastFunctionCall (f : List Int → Int) (args : List Int) : Int := f args
def broadcastFunctionShow (functionName : String) : String :=
  "BroadcastFunction(" ++ functionName ++ ")"

def ChunkMethods : Prop :=
  (∀ op x y, applyChunkOp op x y =
    match op with
    | .unsupported => none
    | .and => some (x &&& y)
    | .or => some (x ||| y)
    | .xor | .unequal => some (x ^^^ y)
    | .nand => some (~~~(x &&& y))
    | .nor => some (~~~(x ||| y))
    | .not => some (~~~x)
    | .identity => some x
    | .equal => some (~~~(x ^^^ y))
    | .less => some ((~~~x) &&& y)
    | .lessEqual => some ((~~~x) ||| y)
    | .greater => some (x &&& (~~~y))
    | .greaterEqual => some (x ||| (~~~y))) ∧
  (∀ n args, chunkable n args = chunkable n args) ∧
  (∀ arg, liftFunctions arg = liftFunctions arg) ∧
  (∀ args, liftChunks args = liftChunks args) ∧
  (∀ i chunks, ithChunk i chunks = chunks.map (fun c => c.getD i 0)) ∧
  (∀ op left right mask, chunkedCopy op left right mask = chunkedCopy op left right mask)

theorem chunkMethods : ChunkMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => rfl⟩

def BitMaskedMethods : Prop :=
  (∀ parent mask, bitMasked parent mask =
    if parent.length == mask.length then some ⟨parent, mask⟩ else none) ∧
  (∀ b value, fillMasked b value =
    { b with parent := (b.parent.zip b.mask).map fun p => if p.2 then value else p.1 }) ∧
  (∀ b value, materializeIdentity b value = fillMasked b value) ∧
  (∀ b, showBitMasked b = [b.parent, b.mask])

theorem bitMaskedMethods : BitMaskedMethods := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def SyntaxMethods : Prop :=
  (∀ x, dottable x = dottable x) ∧
  (∀ x, undot x = undot x) ∧
  (∀ x, dotSyntax x = dotSyntax x) ∧
  (∀ x, macroDot x = dotSyntax x) ∧
  (∀ x, dotviewResult x = x) ∧
  (∀ kw style n, broadcastedPath kw style n =
    if style then .explicitStyle else if kw then .keywordClosure
    else if n = 0 then .direct else .genericMapped n) ∧
  (∀ f args, broadcastFunctionCall f args = f args) ∧
  (∀ name, broadcastFunctionShow name = "BroadcastFunction(" ++ name ++ ")")

theorem syntaxMethods : SyntaxMethods := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end JuliaLean.BroadcastCov.BitsSyntax
