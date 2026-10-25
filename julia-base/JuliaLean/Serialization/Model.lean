import JuliaLean.Serialization.Tags

/-!
# Model of `stdlib/Serialization/src/Serialization.jl` (master `bbfa0ce4150`)

Values (`V`) are first-occurrence trees: a mutable object (a `Vector`, an `Expr`,
a `Base.RefValue{Any}`, or a `String` object longer than seven bytes) that the
serializer has already written is the node `back k`, where `k` is the slot the
serializer's cycle table (`s.cycle_table`, `:28`) assigned to it. This is exactly
what `serialize_cycle` (`:253-262`) looks up: the tree records the result of the
identity lookup instead of the heap. Symbols and types are interned in Julia, so
the encoder state keeps their tables explicitly, keyed by name and by type.

The decoder mirrors `handle_deserialize` (`:1048-1159`) on a byte list; its
backreference table is `s.backref_table` (`:29`).
-/

namespace JuliaLean.Serialization

open JuliaLean

/-- Errors: Julia exceptions, plus `unmodelled` for formats outside the model and
`fuel` for running out of recursion budget. -/
inductive SErr where
  | jl (e : JlError)
  /-- `EOFError`. -/
  | eof
  /-- `ErrorException` from `error(...)`. -/
  | errorEx (msg : String)
  /-- `TypeError` from a failed `::T` assertion or a field of the wrong type. -/
  | typeError
  /-- `MethodError` (`write(io, x)` without a method, `base/io.jl:897`). -/
  | methodError (fn : String)
  | unmodelled (what : String)
  | fuel
  deriving Repr, DecidableEq

/-! ### Little-endian integers -/

/-- The `n` low bytes of `m`, least significant first (`write(io, x)` of an
`n`-byte bits value on a little-endian machine). -/
def le : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, m => UInt8.ofNat (m % 256) :: le n (m / 256)

/-- The value of a little-endian byte string. -/
def unle : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * unle bs

/-- Number of bytes of a `BitInteger` type. -/
def nbytes (t : IntTy) : Nat := t.bits / 8

/-- The two's-complement bit pattern of `x` in `t`. -/
def intBits (t : IntTy) (x : Int) : Nat := (x % (2 ^ t.bits : Int)).toNat

/-- `reinterpret(T, u)` for a `t.bits`-bit pattern `u`. -/
def ofBits (t : IntTy) (u : Nat) : Int :=
  if t.signed ∧ 2 ^ (t.bits - 1) ≤ u then (u : Int) - 2 ^ t.bits else u

/-- `TAGS` index of a `BitInteger` type (`:47`). -/
def intTag : IntTy → Nat
  | .i8 => 2 | .u8 => 3 | .i16 => 4 | .u16 => 5 | .i32 => 6
  | .u32 => 7 | .i64 => 8 | .u64 => 9 | .i128 => 10 | .u128 => 11

/-- `Float16`, `Float32`, `Float64`. -/
inductive FTy where
  | f16 | f32 | f64
  deriving Repr, DecidableEq

def FTy.tag : FTy → Nat
  | .f16 => 12 | .f32 => 13 | .f64 => 14

def FTy.nbytes : FTy → Nat
  | .f16 => 2 | .f32 => 4 | .f64 => 8

/-! ### Values -/

/-- Values of the modelled types. A `Char` is its `UInt32` bit pattern (`c < 2^32`),
a float its bit pattern, a `Symbol`/`String` its bytes. -/
inductive V where
  | int (t : IntTy) (x : Int)
  | flt (w : FTy) (bits : Nat)
  | bool (b : Bool)
  | char (c : Nat)
  | nothing
  | sym (name : Bytes)
  | str (s : Bytes)
  | tup (xs : List V)
  | expr (head : Bytes) (args : List V)
  /-- `Vector{Any}`; `none` is `#undef`. -/
  | anyvec (xs : List (Option V))
  /-- `Vector{T}` for a `BitInteger` type `T`. -/
  | ivec (t : IntTy) (xs : List Int)
  | bvec (xs : List Bool)
  /-- `Base.RefValue{Any}`; `none` is an undefined `x` field. -/
  | refv (x : Option V)
  /-- `UnitRange{Int64}` with fields `start`, `stop`. -/
  | urange (lo hi : Int)
  /-- `NamedTuple{names, Tuple{typeof.(xs)...}}` with scalar, `String` or `Symbol` fields. -/
  | ntup (names : List Bytes) (xs : List V)
  /-- A further reference to the mutable object at slot `k`. -/
  | back (k : Nat)
  deriving Repr, Inhabited

mutual
/-- Structural equality of values (Lean cannot derive `DecidableEq` for `V`). -/
def V.beq : V → V → Bool
  | .int t x, .int t' x' => t == t' && x == x'
  | .flt w b, .flt w' b' => w == w' && b == b'
  | .bool a, .bool b => a == b
  | .char a, .char b => a == b
  | .nothing, .nothing => true
  | .sym a, .sym b => a == b
  | .str a, .str b => a == b
  | .tup a, .tup b => V.beqList a b
  | .expr h a, .expr h' b => h == h' && V.beqList a b
  | .anyvec a, .anyvec b => V.beqOptList a b
  | .ivec t a, .ivec t' b => t == t' && a == b
  | .bvec a, .bvec b => a == b
  | .refv a, .refv b => V.beqOpt a b
  | .urange a b, .urange c d => a == c && b == d
  | .ntup n a, .ntup n' b => n == n' && V.beqList a b
  | .back a, .back b => a == b
  | _, _ => false

def V.beqList : List V → List V → Bool
  | [], [] => true
  | x :: xs, y :: ys => V.beq x y && V.beqList xs ys
  | _, _ => false

def V.beqOpt : Option V → Option V → Bool
  | none, none => true
  | some x, some y => V.beq x y
  | _, _ => false

def V.beqOptList : List (Option V) → List (Option V) → Bool
  | [], [] => true
  | x :: xs, y :: ys => V.beqOpt x y && V.beqOptList xs ys
  | _, _ => false
end

instance : BEq V := ⟨V.beq⟩

/-- Types the model serializes. `tagged n` is `TAGS[n]`. -/
inductive Ty where
  | tagged (n : Nat)
  | refAny
  | urange
  | ntup (names : List Bytes) (fts : List Nat)
  | tuple (fts : List Nat)
  deriving Repr, DecidableEq

/-- `TAGS` index of `typeof(x)` for the scalar, `String` and `Symbol` values that may
be `NamedTuple` fields. -/
def typeTag : V → Option Nat
  | .int t _ => some (intTag t)
  | .flt w _ => some w.tag
  | .bool _ => some BOOL_TYPE_TAG
  | .char _ => some CHAR_TAG
  | .str _ => some STRING_TAG
  | .sym _ => some SYMBOL_TAG
  | _ => none

/-! ### Encoder -/

/-- What occupies a slot: an interned symbol, an interned type, or a mutable object.
These are also the entries of the deserializer's `s.backref_table`. -/
inductive Key where
  | sym (name : Bytes)
  | ty (t : Ty)
  | obj
  deriving Repr, DecidableEq

/-- Serializer state: `s.counter` and `s.cycle_table` as a list of (key, slot) pairs,
newest first. Symbols and types are looked up by key; a mutable object is looked up
by identity, which the value tree records as `back k`. -/
structure ES where
  counter : Nat
  tab : List (Key × Nat)
  deriving Repr

def ES.init : ES := ⟨0, []⟩

/-- `_setcycle!(s, x, s.counter); s.counter += 1` (`:259-260`). -/
def ES.register (es : ES) (k : Key) : ES := ⟨es.counter + 1, (k, es.counter) :: es.tab⟩

/-- `_emit_backref(io, offs)`, `:239-251`. -/
def emitBackref (k : Nat) : Bytes :=
  if k ≤ 65535 then UInt8.ofNat SHORTBACKREF_TAG :: le 2 k
  else if k ≤ 2 ^ 31 - 1 then UInt8.ofNat BACKREF_TAG :: le 4 k
  else UInt8.ofNat LONGBACKREF_TAG :: le 8 k

/-- `write_as_tag(s, tag)`, `:194-198`. -/
def writeAsTag (t : Nat) : Bytes :=
  if t < VALUE_TAGS then [0, UInt8.ofNat t] else [UInt8.ofNat t]

/-- `serialize(s, n::Int32)`, `:801-809`. -/
def serInt32 (n : Int) : Bytes :=
  if 0 ≤ n ∧ n ≤ 32 then [UInt8.ofNat (ZERO32_TAG + n.toNat)]
  else UInt8.ofNat INT32_TAG :: le 4 (intBits .i32 n)

/-- `serialize(s, n::Int64)`, `:811-822`. -/
def serInt64 (n : Int) : Bytes :=
  if 0 ≤ n ∧ n ≤ 32 then [UInt8.ofNat (ZERO64_TAG + n.toNat)]
  else if -2 ^ 31 ≤ n ∧ n ≤ 2 ^ 31 - 1 then UInt8.ofNat SHORTINT64_TAG :: le 4 (intBits .i32 n)
  else UInt8.ofNat INT64_TAG :: le 8 (intBits .i64 n)

/-- `serialize` of a `BitInteger`: `:801-822` for `Int32`/`Int64`, the `@eval`
methods `:824-829` (tag, then the raw bytes) for the other eight types. -/
def serInt (t : IntTy) (x : Int) : Bytes :=
  match t with
  | .i32 => serInt32 x
  | .i64 => serInt64 x
  | _ => UInt8.ofNat (intTag t) :: le (nbytes t) (intBits t x)

/-- `bswap(reinterpret(UInt32, c))` on the bit pattern `c < 2^32`. -/
def bswap32 (c : Nat) : Nat :=
  (c / 2 ^ 24 % 256) + (c / 2 ^ 16 % 256) * 2 ^ 8 + (c / 2 ^ 8 % 256) * 2 ^ 16 + (c % 256) * 2 ^ 24

/-- The loop of `write(io::IO, c::Char)`, `base/io.jl:973-979`: write the low byte
of `u`, shift right by 8, stop once `u` is zero (at most four bytes). -/
def charLoop : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, u => UInt8.ofNat (u % 256) :: (if u / 256 = 0 then [] else charLoop k (u / 256))

/-- `write(io, c::Char)`, `base/io.jl:973-979`. -/
def writeChar (c : Nat) : Bytes := charLoop 4 (bswap32 c)

/-- The run-length loop of `serialize_array_data` for `Bool` arrays, `:337-349`. -/
def rleGo (last : Bool) (count : Nat) : List Bool → Bytes
  | [] => [UInt8.ofNat ((if last then 128 else 0) + count)]
  | x :: xs =>
    if x != last || count == 127 then UInt8.ofNat ((if last then 128 else 0) + count) :: rleGo x 1 xs
    else rleGo last (count + 1) xs

/-- `serialize_array_data(s, a)` for `eltype(a) === Bool`, `:334-349`. -/
def rle : List Bool → Bytes
  | [] => []
  | x :: xs => rleGo x 1 xs

/-- `serialize(s, x::Symbol)`, `:313-332`: a table symbol is its tag; a name longer
than seven bytes goes through `serialize_cycle`. -/
def serSym (es : ES) (name : Bytes) : Bytes × ES :=
  match sertagSym name with
  | some t => (writeAsTag t, es)
  | none =>
    let len := name.length
    let hdr : Bytes := if len ≤ 255 then [UInt8.ofNat SYMBOL_TAG, UInt8.ofNat len]
      else UInt8.ofNat LONGSYMBOL_TAG :: le 4 len
    if len > 7 then
      match es.tab.lookup (.sym name) with
      | some k => (emitBackref k, es)
      | none => (hdr ++ name, es.register (.sym name))
    else (hdr ++ name, es)

/-- `serialize(s, m::Module)` for `Base` and `Core`, `:481-498`: `MODULE_TAG`, then
`serialize_mod_names` (the UUID `nothing` and the root name), then `()`. -/
def serModule (es : ES) (name : Bytes) : Bytes × ES :=
  let (b, es) := serSym es name
  (UInt8.ofNat MODULE_TAG :: UInt8.ofNat NOTHING_TAG :: b ++ [UInt8.ofNat EMPTYTUPLE_TAG], es)

/-- `serialize(s, T)` for a type with a tag (`:781-783`, `write_as_tag`). -/
def serTagType (t : Nat) : Bytes := writeAsTag t

/-- `serialize_type_data(s, t)` for a non-wrapper `DataType` in `Base` or `Core`,
`:751-779`: cycle lookup, `DATATYPE_TAG`, the name, the module, then the parameter
count as `Int32` and the parameters. `params` writes the parameters. -/
def serTypeData (es : ES) (T : Ty) (name modName : Bytes) (np : Nat)
    (params : ES → Bytes × ES) : Bytes × ES :=
  match es.tab.lookup (.ty T) with
  | some k => (emitBackref k, es)
  | none =>
    let es := es.register (.ty T)
    let (bn, es) := serSym es name
    let (bm, es) := serModule es modName
    let (bp, es) := params es
    (UInt8.ofNat DATATYPE_TAG :: bn ++ bm ++ le 4 np ++ bp, es)

/-- `serialize(s, Tuple{T...})` for tagged field types: `Tuple{}` has a tag;
otherwise `serialize_type_data` with name `:Tuple` in `Core` (`:781-792`). -/
def serTupleType (es : ES) (fts : List Nat) : Bytes × ES :=
  if fts = [] then (serTagType EMPTYTUPLE_TYPE_TAG, es)
  else serTypeData es (.tuple fts) nameTuple nameCore fts.length
    (fun es => ((fts.map serTagType).flatten, es))

/-- A fresh slot for a mutable object (`serialize_cycle` not finding it). -/
def ES.newObj (es : ES) : ES := es.register .obj

/-- Serialize symbols in order. -/
def serSyms (es : ES) : List Bytes → Bytes × ES
  | [] => ([], es)
  | n :: ns =>
    let (b1, es) := serSym es n
    let (b2, es) := serSyms es ns
    (b1 ++ b2, es)

/-- `serialize(s, names)` for the `Tuple` of `Symbol`s that is a `NamedTuple`'s
first parameter (`:289-303`). -/
def serNames (es : ES) (names : List Bytes) : Bytes × ES :=
  if names = [] then ([UInt8.ofNat EMPTYTUPLE_TAG], es)
  else
    let l := names.length
    let hdr : Bytes := if l ≤ 255 then [UInt8.ofNat TUPLE_TAG, UInt8.ofNat l]
      else UInt8.ofNat LONGTUPLE_TAG :: le 4 l
    let (b, es) := serSyms es names
    (hdr ++ b, es)

mutual
/-- `serialize(s, x)` (`:284-889`) for the modelled values. -/
def ser (es : ES) : V → Bytes × ES
  | .int t x => (serInt t x, es)
  | .flt w b => (UInt8.ofNat w.tag :: le w.nbytes b, es)
  | .bool b => ([UInt8.ofNat (if b then TRUE_TAG else FALSE_TAG)], es)
  | .char c => ([UInt8.ofNat CHAR_TAG] ++ writeChar c, es)
  | .nothing => (writeAsTag NOTHING_TAG, es)
  | .sym name => serSym es name
  | .str s =>
    let len := s.length
    let hdr : Bytes := if len ≤ 255 then [UInt8.ofNat STRING_TAG, UInt8.ofNat len]
      else UInt8.ofNat LONGSTRING_TAG :: le 8 len
    if len > 7 then (UInt8.ofNat SHARED_REF_TAG :: hdr ++ s, es.newObj)
    else (hdr ++ s, es)
  | .tup xs =>
    if xs = [] then ([UInt8.ofNat EMPTYTUPLE_TAG], es)
    else
      let l := xs.length
      let hdr : Bytes := if l ≤ 255 then [UInt8.ofNat TUPLE_TAG, UInt8.ofNat l]
        else UInt8.ofNat LONGTUPLE_TAG :: le 4 l
      let (b, es) := serList es xs
      (hdr ++ b, es)
  | .expr head args =>
    let es := es.newObj
    let l := args.length
    let hdr : Bytes := if l ≤ 255 then [UInt8.ofNat EXPR_TAG, UInt8.ofNat l]
      else UInt8.ofNat LONGEXPR_TAG :: le 4 l
    let (bh, es) := serSym es head
    let (ba, es) := serList es args
    (hdr ++ bh ++ ba, es)
  | .anyvec xs =>
    let es := es.newObj
    let (b, es) := serOptList es xs
    (UInt8.ofNat ARRAY_TAG :: UInt8.ofNat ANY_TAG :: serInt64 xs.length ++ b, es)
  | .ivec t xs =>
    let es := es.newObj
    let elty : Bytes := if t = .u8 then [] else serTagType (intTag t)
    (UInt8.ofNat ARRAY_TAG :: elty ++ serInt64 xs.length ++
      (xs.map fun x => le (nbytes t) (intBits t x)).flatten, es)
  | .bvec xs =>
    let es := es.newObj
    (UInt8.ofNat ARRAY_TAG :: UInt8.ofNat BOOL_TYPE_TAG :: serInt64 xs.length ++ rle xs, es)
  | .refv x =>
    let es := es.newObj
    let (bt, es) := serTypeData es .refAny nameRefValue nameBase 1
      (fun es => (serTagType ANY_TAG, es))
    let (bx, es) := serOpt es x
    (UInt8.ofNat REF_OBJECT_TAG :: bt ++ bx, es)
  | .urange lo hi =>
    let (bt, es) := serTypeData es .urange nameUnitRange nameBase 1
      (fun es => (serTagType INT64_TAG, es))
    (UInt8.ofNat OBJECT_TAG :: bt ++ serInt64 lo ++ serInt64 hi, es)
  | .ntup names xs =>
    let fts := xs.map fun x => (typeTag x).getD 0
    let (bt, es) := serTypeData es (.ntup names fts) nameNamedTuple nameCore 2
      (fun es =>
        let (b1, es) := serNames es names
        let (b2, es) := serTupleType es fts
        (b1 ++ b2, es))
    let (bx, es) := serList es xs
    (UInt8.ofNat OBJECT_TAG :: bt ++ bx, es)
  | .back k => (emitBackref k, es)

/-- Serialize a list of values in order. -/
def serList (es : ES) : List V → Bytes × ES
  | [] => ([], es)
  | x :: xs =>
    let (b1, es) := ser es x
    let (b2, es) := serList es xs
    (b1 ++ b2, es)

/-- A possibly undefined element or field: `UNDEFREF_TAG` for `#undef`. -/
def serOpt (es : ES) : Option V → Bytes × ES
  | none => ([UInt8.ofNat UNDEFREF_TAG], es)
  | some x => ser es x

/-- Elements of a `Vector{Any}` (`_serialize_non_bits_elements!`, `:355-364`). -/
def serOptList (es : ES) : List (Option V) → Bytes × ES
  | [] => ([], es)
  | x :: xs =>
    let (b1, es) := serOpt es x
    let (b2, es) := serOptList es xs
    (b1 ++ b2, es)
end

/-- `ser_version`, `:92`. -/
abbrev serVersion : Nat := 31

/-- `writeheader(s)`, `:906-920`, on a little-endian 64-bit machine. -/
def header : Bytes :=
  [UInt8.ofNat HEADER_TAG, 0x4a, 0x4c, UInt8.ofNat serVersion, 0x04, 0, 0, 0]

/-- `serialize(io, x)`, `:980-984`: a fresh `Serializer`, the header, then `x`. -/
def serialize (x : V) : Bytes := header ++ (ser ES.init x).1

/-! ### Decoder -/

/-- Modules reachable by `deserialize_module`. -/
inductive Md where
  | base | core
  deriving Repr, DecidableEq

/-- What `deserialize(s)` returns. -/
inductive Obj where
  | v (x : V)
  | ty (t : Ty)
  | md (m : Md)
  deriving Repr

/-- Deserializer state: unread input, `s.counter`, `s.backref_table` (whose entries
are the `Key`s of the slots), `s.pending_refs`, `s.version`. -/
structure DS where
  io : Bytes
  counter : Nat
  table : Nat → Option Key
  pending : List Nat
  version : Nat

def DS.init (io : Bytes) : DS := ⟨io, 0, fun _ => none, [], serVersion⟩

/-- The decoder monad. -/
def Dm (α : Type) : Type := DS → Except SErr (α × DS)

@[inline] def Dm.pure {α : Type} (a : α) : Dm α := fun s => .ok (a, s)
@[inline] def Dm.bind {α β : Type} (m : Dm α) (k : α → Dm β) : Dm β := fun s =>
  match m s with
  | .ok (a, s') => k a s'
  | .error e => .error e

instance : Monad Dm where
  pure := Dm.pure
  bind := Dm.bind

def fail {α : Type} (e : SErr) : Dm α := fun _ => .error e

def getS : Dm DS := fun s => .ok (s, s)
def setS (s : DS) : Dm Unit := fun _ => .ok ((), s)

/-- `read(io, UInt8)`. -/
def readU8 : Dm UInt8 := fun s =>
  match s.io with
  | [] => .error .eof
  | b :: bs => .ok (b, { s with io := bs })

/-- `n` bytes (`read!`, `unsafe_read`): `EOFError` when fewer remain. -/
def readN (n : Nat) : Dm Bytes := fun s =>
  if n ≤ s.io.length then .ok (s.io.take n, { s with io := s.io.drop n })
  else .error .eof

/-- `read(io, T)` for an `n`-byte bits type: the little-endian value. -/
def readLE (n : Nat) : Dm Nat := do
  let bs ← readN n
  pure (unle bs)

/-- `read(io, T)` for a `BitInteger` type `T`. -/
def readInt (t : IntTy) : Dm Int := do
  let u ← readLE (nbytes t)
  pure (ofBits t u)

/-- `_setbackref!(s, slot, x)`, `:207-213`. -/
def setBackref (slot : Nat) (e : Key) : Dm Unit := fun s =>
  .ok ((), { s with table := fun j => if j = slot then some e else s.table j })

/-- `slot = s.counter; s.counter += 1`. -/
def newSlot : Dm Nat := fun s => .ok (s.counter, { s with counter := s.counter + 1 })

/-- `resolve_ref_immediately(s, x)`, `:1039-1043`. -/
def resolveNow (e : Key) : Dm Unit := do
  let k ← newSlot
  setBackref k e

/-- The value of a backreference entry. -/
def ofEntry (k : Nat) : Key → Obj
  | .sym n => .v (.sym n)
  | .ty t => .ty t
  | .obj => .v (.back k)

/-- `_getbackref(s, id)`, `:226-231`: an error unless the slot is assigned. -/
def getBackref (id : Int) : Dm Obj := fun s =>
  if id < 0 then .error (.errorEx "Inconsistent Serializer state")
  else match s.table id.toNat with
    | some e => .ok (ofEntry id.toNat e, s)
    | none => .error (.errorEx "Inconsistent Serializer state")

/-- `leading_ones(b::UInt8)`. -/
def leadingOnes8 (b : Nat) : Nat :=
  if b < 128 then 0 else if b < 192 then 1 else if b < 224 then 2 else if b < 240 then 3
  else if b < 248 then 4 else if b < 252 then 5 else if b < 254 then 6 else if b < 255 then 7
  else 8

/-- The loop of `read(io, ::Type{Char})`, `base/io.jl:1097-1103`: positions
`s = 16, 8, 0` (`steps` left), while `s ≥ l`, not at EOF, and the next byte is a
continuation byte (`peek(io) & 0xc0 == 0x80`). -/
def readCharLoop : Nat → Nat → Nat → Nat → Dm Nat
  | 0, _, _, c => pure c
  | k + 1, s, l, c => fun st =>
    if l ≤ s then
      match st.io with
      | [] => .ok (c, st)
      | b :: bs =>
        if b &&& 0xc0 = 0x80 then readCharLoop k (s - 8) l (c + b.toNat * 2 ^ s) { st with io := bs }
        else .ok (c, st)
    else .ok (c, st)

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1106`. -/
def readChar : Dm Nat := do
  let b0 ← readU8
  let lo := leadingOnes8 b0.toNat
  let c := b0.toNat * 2 ^ 24
  if 2 ≤ lo ∧ lo ≤ 4 then readCharLoop 3 16 (8 * (4 - lo)) c
  else pure c

/-- The run-length loop of `deserialize_array` for `Bool`, `:1542-1552`: read a byte,
store `count = b & 0x7f` copies of `b >> 7 != 0`; `A[i]` past the end throws. -/
def rleRead (n : Nat) : Nat → List Bool → Dm (List Bool)
  | 0, _ => fail (.unmodelled "run-length loop budget")
  | fuel + 1, acc => do
    if n ≤ acc.length then pure acc
    else
      let b ← readU8
      let v := decide (b.toNat ≥ 128)
      let count := b.toNat % 128
      if acc.length + count > n then fail (.jl .boundsError)
      else rleRead n fuel (acc ++ List.replicate count v)

/-- `Symbol(str)` for bytes read from the stream (`:1161-1169`): `Symbol` rejects NUL. -/
def mkSymbol (bs : Bytes) : Dm V :=
  if bs.contains 0 then fail (.jl (.argumentError "Symbol name may not contain \\0"))
  else pure (.sym bs)

/-- `deserialize_symbol(s, len)`, `:1161-1169`. -/
def deserSymbol (len : Int) : Dm Obj := do
  if len < 0 then fail (.jl (.argumentError "negative length"))
  else
    let bs ← readN len.toNat
    let sym ← mkSymbol bs
    if len > 7 then resolveNow (.sym bs)
    pure (.v sym)

/-- `deserialize_string(s, len)`, `:1844-1848`. -/
def deserString (len : Int) : Dm Obj := do
  if len < 0 then fail (.unmodelled "negative string length")
  else
    let bs ← readN len.toNat
    pure (.v (.str bs))

/-- A value of the model, or `unmodelled` for a type or module in value position. -/
def asV : Obj → Dm V
  | .v x => pure x
  | _ => fail (.unmodelled "type or module value")

/-- `x::Symbol`. -/
def asSym : Obj → Dm Bytes
  | .v (.sym n) => pure n
  | _ => fail .typeError

/-- Read `n` values with `d`. -/
def readMany {α : Type} (d : Dm α) : Nat → Dm (List α)
  | 0 => pure []
  | n + 1 => do
    let x ← d
    let xs ← readMany d n
    pure (x :: xs)

/-- The `#undef`-aware element/field loop (`deserialize_fillarray!`, `:1566-1574`, and
the mutable branch of `deserialize(s, t::DataType)`, `:1858-1863`): read a tag; unless
it is `UNDEFREF_TAG`, `handle_deserialize` it. -/
def readOpt (h : Nat → Dm Obj) : Dm (Option V) := do
  let tag ← readU8
  if tag.toNat = UNDEFREF_TAG then pure none
  else
    let o ← h tag.toNat
    let x ← asV o
    pure (some x)

/-- `root_module(PkgId(name))` for the modules of the model. -/
def rootModule (name : Bytes) : Dm Md :=
  if name = nameBase then pure .base
  else if name = nameCore then pure .core
  else fail (.unmodelled "root module")

/-- `deserialize_module(s)`, `:1184-1206` (no submodules). -/
def deserModule (d : Dm Obj) : Dm Obj := do
  let mkey ← d
  match mkey with
  | .v (.tup _) => fail (.unmodelled "old module format")
  | .v .nothing =>
    let n ← d
    let name ← asSym n
    let m ← rootModule name
    let mname ← d
    match mname with
    | .v (.tup []) => pure (.md m)
    | _ => fail (.unmodelled "submodule")
  | _ => fail (.unmodelled "module uuid")

/-- `getglobal(mod, name)` for the generic types of the model. -/
inductive Global where
  | refValue | unitRange | namedTuple | tuple

def getGlobal : Md → Bytes → Dm Global
  | .base, n => if n = nameRefValue then pure .refValue
      else if n = nameUnitRange then pure .unitRange
      else fail (.unmodelled "global")
  | .core, n => if n = nameNamedTuple then pure .namedTuple
      else if n = nameTuple then pure .tuple
      else fail (.unmodelled "global")

/-- The tags of a list of tagged types (`TAGS[n]` read as types), if all are. -/
def taggedOf : List Obj → Option (List Nat)
  | [] => some []
  | .ty (.tagged n) :: ps => (taggedOf ps).map (n :: ·)
  | _ :: _ => none

/-- The names of a tuple of symbols, if all are symbols. -/
def symsOf : List V → Option (List Bytes)
  | [] => some []
  | .sym n :: xs => (symsOf xs).map (n :: ·)
  | _ :: _ => none

/-- The names of a `NamedTuple` type parameter. -/
def asNames : Obj → Dm (List Bytes)
  | .v (.tup xs) => match symsOf xs with
    | some ns => pure ns
    | none => fail (.unmodelled "NamedTuple names")
  | _ => fail (.unmodelled "NamedTuple names")

/-- The field types of a `Tuple{...}` type parameter. -/
def asTupleTy : Obj → Dm (List Nat)
  | .ty (.tagged 75) => pure []
  | .ty (.tuple fts) => pure fts
  | _ => fail (.unmodelled "NamedTuple types")

/-- Read one type parameter, which must be the tagged type `want`. -/
def readParam (d : Dm Obj) (want : Nat) (t : Ty) : Dm Ty := do
  let p ← d
  match p with
  | .ty (.tagged n) => if n = want then pure t else fail (.unmodelled "type parameter")
  | _ => fail (.unmodelled "type parameter")

/-- The parameters of `deserialize_datatype`, `:1760-1781`: `np` parameters for
`Tuple`, else `t = t{deserialize(s)}` once per parameter. -/
def readParams (d : Dm Obj) (g : Global) (np : Int) : Dm Ty :=
  match g with
  | .tuple => do
    let ps ← readMany d np.toNat
    match taggedOf ps with
    | some fts => pure (if fts = [] then Ty.tagged EMPTYTUPLE_TYPE_TAG else Ty.tuple fts)
    | none => fail (.unmodelled "type parameter")
  | .refValue =>
    if np = 1 then readParam d ANY_TAG .refAny
    else fail (.unmodelled "parameters")
  | .unitRange =>
    if np = 1 then readParam d INT64_TAG .urange
    else fail (.unmodelled "parameters")
  | .namedTuple =>
    if np = 2 then do
      let p1 ← d
      let names ← asNames p1
      let p2 ← d
      let fts ← asTupleTy p2
      if names.length = fts.length then pure (Ty.ntup names fts)
      else fail (.unmodelled "NamedTuple arity")
    else fail (.unmodelled "parameters")

/-- The module of a type reference (`deserialize(s)::Module`). -/
def asMod : Obj → Dm Md
  | .md m => pure m
  | _ => fail .typeError

/-- `deserialize_datatype(s, false)`, `:1747-1785`, for the generic types of the
model; none of them is a `DataType` without parameters (`:1757`). -/
def deserDatatype (d : Dm Obj) : Dm Obj := do
  let slot ← newSlot
  let n ← d
  let name ← asSym n
  let mo ← d
  let m ← asMod mo
  let g ← getGlobal m name
  let np ← readInt .i32
  if np = 0 then fail (.unmodelled "unwrap_unionall")
  else do
    let t ← readParams d g np
    setBackref slot (.ty t)
    pure (.ty t)

/-- A field value of the declared type (`jl_new_structv` checks field types). -/
def checkField (ft : Nat) (x : V) : Dm V :=
  if typeTag x = some ft then pure x else fail .typeError

/-- All fields defined. -/
def allSome : List (Option V) → Option (List V)
  | [] => some []
  | some x :: xs => (allSome xs).map (x :: ·)
  | none :: _ => none

/-- Every field has its declared type. -/
def fieldsOk : List Nat → List V → Bool
  | ft :: fts, x :: xs => typeTag x == some ft && fieldsOk fts xs
  | _, _ => true

/-- `deserialize(s, t::DataType)` for the struct types of the model, `:1851-1881`.
`mutableSlot` is the slot `REF_OBJECT_TAG` pushed. -/
def deserStruct (h : Nat → Dm Obj) : Ty → Dm Obj
  | .refAny => do
    -- mutable: `deserialize_cycle` pops the pending slot before reading the field
    let s ← getS
    match s.pending with
    | [] => fail (.unmodelled "empty pending_refs")
    | slot :: rest =>
      setS { s with pending := rest }
      setBackref slot .obj
      let x ← readOpt h
      pure (.v (.refv x))
  | .urange => do
    let a ← readOpt h
    let b ← readOpt h
    match a, b with
    | some a, some b => do
      let a ← checkField INT64_TAG a
      let b ← checkField INT64_TAG b
      match a, b with
      | .int .i64 lo, .int .i64 hi => pure (.v (.urange lo hi))
      | _, _ => fail .typeError
    | _, _ => fail (.unmodelled "undefined immutable field")
  | .ntup names fts => do
    let xs ← readMany (readOpt h) fts.length
    match allSome xs with
    | some xs => if fieldsOk fts xs then pure (.v (.ntup names xs)) else fail .typeError
    | none => fail (.unmodelled "undefined immutable field")
  | _ => fail (.unmodelled "struct type")

/-- Decode an element type tag to a vector kind: `none` for `UInt8` (no `elty`). -/
inductive ArrKind where
  | any | bool | int (t : IntTy)

/-- The `n` consecutive `nb`-byte elements of the bytes `read!` filled in. -/
def chunks (nb : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | n + 1, bs => bs.take nb :: chunks nb n (bs.drop nb)

def intTyOfTag : Nat → Option IntTy
  | 2 => some .i8 | 3 => some .u8 | 4 => some .i16 | 5 => some .u16 | 6 => some .i32
  | 7 => some .u32 | 8 => some .i64 | 9 => some .u64 | 10 => some .i128 | 11 => some .u128
  | _ => none

/-- The length of a 1-dimensional array, `d1::Union{Int32,Int64}`. -/
def asLen : Obj → Dm (Option Int)
  | .v (.int .i64 n) => pure (some n)
  | .v (.int .i32 n) => pure (some n)
  | _ => pure none

/-- The element type of a 1-dimensional array (`:1520-1527`): an element type is
written before the length, except for `UInt8`. -/
def arrKind (d : Dm Obj) : Obj → Dm (ArrKind × Obj)
  | .ty (.tagged n) => do
    let d1 ← d
    if n = ANY_TAG then pure (ArrKind.any, d1)
    else if n = BOOL_TYPE_TAG then pure (ArrKind.bool, d1)
    else match intTyOfTag n with
      | some t => pure (ArrKind.int t, d1)
      | none => fail (.unmodelled "element type")
  | o => pure (ArrKind.int .u8, o)

/-- The elements of a vector of length `n` (`:1528-1564`). -/
def arrBody (h : Nat → Dm Obj) (slot : Nat) : ArrKind → Int → Dm Obj
  | .int t, n => do
    setBackref slot .obj
    let bs ← readN (n.toNat * nbytes t)
    pure (.v (.ivec t ((chunks (nbytes t) n.toNat bs).map fun c => ofBits t (unle c))))
  | .bool, n => do
    let xs ← (if n.toNat > 0 then do
        let s ← getS
        rleRead n.toNat (s.io.length + 1) []
      else pure [])
    setBackref slot .obj
    pure (.v (.bvec xs))
  | .any, n => do
    setBackref slot .obj
    let xs ← readMany (readOpt h) n.toNat
    pure (.v (.anyvec xs))

/-- `deserialize_array(s)`, `:1517-1564`, for 1-dimensional `Vector{Any}`,
`Vector{Bool}` and `Vector{T}` with `T` a `BitInteger`. -/
def deserArray (d : Dm Obj) (h : Nat → Dm Obj) : Dm Obj := do
  let slot ← newSlot
  let d1 ← d
  let kd ← arrKind d d1
  let len ← asLen kd.2
  match len with
  | none => fail (.unmodelled "multidimensional array")
  | some n =>
    if n < 0 then fail (.jl (.argumentError "negative array length"))
    else arrBody h slot kd.1 n

/-- `deserialize_expr(s, len)`, `:1623-1669` (`current_module[]` is `nothing` at top
level, so a `:method` head is kept). -/
def deserExpr (d : Dm Obj) (len : Int) : Dm Obj := do
  resolveNow .obj
  let ho ← d
  let head ← asSym ho
  let args ← readMany (do let o ← d; asV o) len.toNat
  pure (.v (.expr head args))

/-- `deserialize_tuple(s, len)`, `:1171-1177`. -/
def deserTuple (d : Dm Obj) (len : Nat) : Dm Obj := do
  let xs ← readMany (do let o ← d; asV o) len
  pure (.v (.tup xs))

/-- `readheader(s)`, `:922-954` (tag already read), on a little-endian machine. -/
def readHeader : Dm Unit := do
  let m1 ← readU8
  let m2 ← readU8
  if m1 ≠ 0x4a ∨ m2 ≠ 0x4c then fail (.errorEx "Unsupported serialization format")
  else
    let version ← readU8
    let flags ← readU8
    let _ ← readU8
    let _ ← readU8
    let _ ← readU8
    let endianflag := flags.toNat % 4
    let wordflag := flags.toNat / 4 % 4
    if wordflag > 1 then fail (.errorEx "Unknown word size flag in header")
    else if endianflag > 1 then fail (.errorEx "Unknown endianness flag in header")
    else if endianflag ≠ 0 then fail (.errorEx "Serialized byte order mismatch")
    else if version.toNat > serVersion then
      fail (.errorEx "Cannot read stream serialized with a newer version of Julia")
    else do
      let s ← getS
      setS { s with version := version.toNat }

/-- `desertag(b)` for value tags `b ≥ VALUE_TAGS` and for `0`-prefixed type tags. -/
def desertag (b : Nat) : Dm Obj :=
  if b = 0 then fail (.unmodelled "TAGS[0]")
  else if b < VALUE_TAGS then pure (.ty (.tagged b))
  else if b = EMPTYTUPLE_TAG then pure (.v (.tup []))
  else if b = 74 then fail (.unmodelled "svec()")
  else if b < FALSE_TAG then pure (.ty (.tagged b))
  else if b = FALSE_TAG then pure (.v (.bool false))
  else if b = TRUE_TAG then pure (.v (.bool true))
  else if b = NOTHING_TAG then pure (.v .nothing)
  else if b < ZERO32_TAG then pure (.v (.sym (symOfTag b)))
  else if b < ZERO64_TAG then pure (.v (.int .i32 (b - ZERO32_TAG)))
  else if b ≤ 255 then pure (.v (.int .i64 (b - ZERO64_TAG)))
  else fail (.unmodelled "tag")

/-- `handle_deserialize(s, b)`, `:1048-1159`, with recursion budget `f`; `d` is a
nested `deserialize(s)` and `h` a nested `handle_deserialize`. -/
def handle : Nat → Nat → Dm Obj
  | 0, _ => fail .fuel
  | f + 1, b =>
    let h : Nat → Dm Obj := handle f
    let d : Dm Obj := do
      let b ← readU8
      h b.toNat
    if b = 0 then do
      let b' ← readU8
      desertag b'.toNat
    else if b ≥ VALUE_TAGS then desertag b
    else if b = TUPLE_TAG then do
      let n ← readU8
      deserTuple d n.toNat
    else if b = SHORTBACKREF_TAG then do
      let id ← readLE 2
      getBackref id
    else if b = BACKREF_TAG then do
      let id ← readInt .i32
      getBackref id
    else if b = ARRAY_TAG then deserArray d h
    else if b = DATATYPE_TAG then deserDatatype d
    else if b = FULL_DATATYPE_TAG then fail (.unmodelled "FULL_DATATYPE_TAG")
    else if b = WRAPPER_DATATYPE_TAG then fail (.unmodelled "WRAPPER_DATATYPE_TAG")
    else if b = OBJECT_TAG then do
      let t ← d
      match t with
      | .ty t => deserStruct h t
      | _ => fail .typeError
    else if b = REF_OBJECT_TAG then do
      let slot ← newSlot
      let s ← getS
      setS { s with pending := slot :: s.pending }
      let t ← d
      match t with
      | .ty t => deserStruct h t
      | _ => fail .typeError
    else if b = SHARED_REF_TAG then do
      let slot ← newSlot
      let o ← d
      setBackref slot .obj
      pure o
    else if b = SYMBOL_TAG then do
      let n ← readU8
      deserSymbol n.toNat
    else if b = SHORTINT64_TAG then do
      let x ← readInt .i32
      pure (.v (.int .i64 x))
    else if b = EXPR_TAG then do
      let n ← readU8
      deserExpr d n.toNat
    else if b = MODULE_TAG then deserModule d
    else if b = STRING_TAG then do
      let n ← readU8
      deserString n.toNat
    else if b = LONGSTRING_TAG then do
      let n ← readInt .i64
      deserString n
    else if b = LONGTUPLE_TAG then do
      let n ← readInt .i32
      if n < 0 then fail (.unmodelled "negative tuple length") else deserTuple d n.toNat
    else if b = LONGEXPR_TAG then do
      let n ← readInt .i32
      deserExpr d n
    else if b = LONGBACKREF_TAG then do
      let id ← readInt .i64
      getBackref id
    else if b = LONGSYMBOL_TAG then do
      let n ← readInt .i32
      deserSymbol n
    else if b = HEADER_TAG then do
      readHeader
      d
    else if 2 ≤ b ∧ b ≤ 11 then do
      let t := (intTyOfTag b).getD .i8
      let x ← readInt t
      pure (.v (.int t x))
    else if b = 12 then do let x ← readLE 2; pure (.v (.flt .f16 x))
    else if b = 13 then do let x ← readLE 4; pure (.v (.flt .f32 x))
    else if b = 14 then do let x ← readLE 8; pure (.v (.flt .f64 x))
    else if b = CHAR_TAG then do
      let c ← readChar
      pure (.v (.char c))
    else fail (.unmodelled "tag")

/-- `deserialize(s)`, `:1024-1026`: read a tag byte and handle it. -/
def deser (f : Nat) : Dm Obj := do
  let b ← readU8
  handle f b.toNat

/-- `deserialize(io)`, `:1012`, with a recursion budget larger than the input:
every nested `deserialize` call reads at least one byte first. Returns the value and
the unread bytes (the stream position). -/
def deserialize (io : Bytes) : Except SErr (Obj × Bytes) :=
  match deser (io.length + 1) (DS.init io) with
  | .ok (o, s) => .ok (o, s.io)
  | .error e => .error e

end JuliaLean.Serialization
