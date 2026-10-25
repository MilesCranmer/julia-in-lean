import JuliaLean.Serialization.Model

/-!
# Properties of `stdlib/Serialization`

`serialize` promises that `deserialize` reads back a value "as identical as
possible to the original" (`Serialization.jl:959-961`): equal for every value,
`===` for bits values, one object for two references to the same mutable object,
cycles restored, and the stream left just after the value.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-! ### Well-formed values -/

/-- Bytes of a `Char` bit pattern, most significant first. -/
def cbyte (c : Nat) (i : Nat) : Nat := c / 2 ^ (24 - 8 * i) % 256

/-- A UTF-8 continuation byte, `0b10xxxxxx`. -/
def isContN (b : Nat) : Prop := 128 ≤ b ∧ b < 192

/-- A `Char` whose bytes form a complete sequence: a lead byte announcing `n` bytes
(two to four leading ones) followed by exactly `n - 1` continuation bytes, or any
other first byte alone. Iterating a `String` produces such `Char`s except for
sequences cut short by the end of the string or a non-continuation byte, such as
`"\xc0"[1]`. -/
def CharWF (c : Nat) : Prop :=
  c < 2 ^ 32 ∧
  let lo := leadingOnes8 (cbyte c 0)
  if lo = 2 then isContN (cbyte c 1) ∧ cbyte c 2 = 0 ∧ cbyte c 3 = 0
  else if lo = 3 then isContN (cbyte c 1) ∧ isContN (cbyte c 2) ∧ cbyte c 3 = 0
  else if lo = 4 then isContN (cbyte c 1) ∧ isContN (cbyte c 2) ∧ isContN (cbyte c 3)
  else cbyte c 1 = 0 ∧ cbyte c 2 = 0 ∧ cbyte c 3 = 0

/-- A valid `Symbol` name: no NUL byte (`Symbol` rejects it) and an `Int32` length. -/
def SymWF (n : Bytes) : Prop := 0 ∉ n ∧ n.length < 2 ^ 31

/-- `t.min ≤ x ≤ t.max`. -/
def InRange (t : IntTy) (x : Int) : Prop := t.min ≤ x ∧ x ≤ t.max

/-- State after the type data of `Base.RefValue{Any}`. -/
def refTypeES (es : ES) : ES :=
  (serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))).2

/-- State after the type data of `NamedTuple{names, Tuple{fts...}}`. -/
def ntupTypeES (es : ES) (names : List Bytes) (fts : List Nat) : ES :=
  (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2
    (fun es =>
      let (b1, es) := serNames es names
      let (b2, es) := serTupleType es fts
      (b1 ++ b2, es))).2

mutual
/-- `x` is a value of its Julia type, written by a serializer in state `es`: integers
in range, bit patterns of the right width, complete `Char`s, `Int32`/`Int64` lengths,
and `back k` only for a mutable object already written at slot `k`. -/
def WF (es : ES) : V → Prop
  | .int t x => InRange t x
  | .flt w b => b < 256 ^ w.nbytes
  | .bool _ => True
  | .char c => CharWF c
  | .nothing => True
  | .sym n => SymWF n
  | .str s => s.length < 2 ^ 63
  | .tup xs => xs.length < 2 ^ 31 ∧ WFList es xs
  | .expr h args => SymWF h ∧ args.length < 2 ^ 31 ∧ WFList (serSym es.newObj h).2 args
  | .anyvec xs => xs.length < 2 ^ 63 ∧ WFOptList es.newObj xs
  | .ivec t xs => xs.length < 2 ^ 63 ∧ ∀ x ∈ xs, InRange t x
  | .bvec xs => xs.length < 2 ^ 63
  | .refv x => WFOpt (refTypeES es.newObj) x
  | .urange lo hi => InRange .i64 lo ∧ InRange .i64 hi
  | .ntup names xs => names.length = xs.length ∧ names.Nodup ∧ (∀ n ∈ names, SymWF n) ∧
      names.length < 2 ^ 31 ∧ (∀ x ∈ xs, (typeTag x).isSome) ∧
      WFList (ntupTypeES es names (xs.map fun x => (typeTag x).getD 0)) xs
  | .back k => (Key.obj, k) ∈ es.tab

def WFList (es : ES) : List V → Prop
  | [] => True
  | x :: xs => WF es x ∧ WFList (ser es x).2 xs

def WFOpt (es : ES) : Option V → Prop
  | none => True
  | some x => WF es x

def WFOptList (es : ES) : List (Option V) → Prop
  | [] => True
  | x :: xs => WFOpt es x ∧ WFOptList (serOpt es x).2 xs
end

/-- The serializer's slot assignment: the key registered at slot `k`. -/
def encTable (es : ES) (k : Nat) : Option Key :=
  (es.tab.find? fun p => p.2 == k).map Prod.fst

/-- `deserialize(io)` returning the final deserializer state. -/
def deserializeState (io : Bytes) : Except SErr (Obj × DS) :=
  deser (io.length + 1) (DS.init io)

/-! ### Round trip -/

/-- `deserialize(serialize(x))` returns `x` for every well-formed value of the model
(integers of all ten widths, floats by bit pattern, `Bool`, `Char`, `nothing`,
symbols, strings, tuples, `Expr`, `Vector{Any}` with `#undef`, `Vector{T}` for bits
integers, `Vector{Bool}`, `Base.RefValue{Any}`, `UnitRange{Int64}`, `NamedTuple`s,
shared and cyclic references), and leaves the stream just after the value. The
serializer's slot counter is an `Int`, so at most `2^63` slots are used. -/
def RoundTrip : Prop :=
  ∀ x : V, WF ES.init x → (ser ES.init x).2.counter ≤ 2 ^ 63 → ∀ rest : Bytes,
    deserialize (serialize x ++ rest) = .ok (.v x, rest)

/-- The deserializer gives every slot the same occupant as the serializer: after
reading `serialize(x)`, `s.counter` and every entry of `s.backref_table` agree with
the serializer's `s.counter` and `s.cycle_table`. Together with the round trip this
means each `back k` in the result denotes the object the serializer wrote at slot `k`:
shared mutable objects stay shared and cycles are restored. -/
def SlotAgreement : Prop :=
  ∀ x : V, WF ES.init x → (ser ES.init x).2.counter ≤ 2 ^ 63 → ∀ rest : Bytes, ∃ s : DS,
    deserializeState (serialize x ++ rest) = .ok (.v x, s) ∧ s.io = rest ∧
    s.counter = (ser ES.init x).2.counter ∧ ∀ k, s.table k = encTable (ser ES.init x).2 k

/-- A `(Char, Int32)` tuple round-trips for every `Char` bit pattern. -/
def CharRoundTrip : Prop :=
  ∀ c : Nat, c < 2 ^ 32 → ∀ n : Int, InRange .i32 n →
    deserialize (serialize (.tup [.char c, .int .i32 n])) = .ok (.v (.tup [.char c, .int .i32 n]), [])

/-- A backreference to an assigned slot `k < 2^63` (`_emit_backref`, `:239-251`) reads
back that slot's entry and nothing more, across the `UInt16`/`Int32`/`Int64` forms. -/
def BackrefDecode : Prop :=
  ∀ k : Nat, k < 2 ^ 63 → ∀ (s : DS) (e : Key) (rest : Bytes),
    s.table k = some e → s.io = emitBackref k ++ rest →
    deser 1 s = .ok (ofEntry k e, { s with io := rest })

/-- `readheader` accepts a stream header of every format version up to `ser_version`
and rejects newer versions (`:948-951`). -/
def HeaderVersions : Prop :=
  ∀ ver : Nat, ver < 256 → ∀ x : V, WF ES.init x → (ser ES.init x).2.counter ≤ 2 ^ 63 →
    ∀ rest : Bytes,
    deserialize ([UInt8.ofNat HEADER_TAG, 0x4a, 0x4c, UInt8.ofNat ver, 0x04, 0, 0, 0] ++
        (ser ES.init x).1 ++ rest) =
      if ver ≤ serVersion then .ok (.v x, rest)
      else .error (.errorEx "Cannot read stream serialized with a newer version of Julia")

/-! ### Primitive types -/

/-- A primitive type: a `BitInteger` type of Base, or a user `primitive type` of
`nbytes` bytes. -/
inductive PrimTy where
  | base (t : IntTy)
  | user (name : Bytes) (nbytes : Nat)

def PrimTy.nbytes : PrimTy → Nat
  | .base t => Serialization.nbytes t
  | .user _ n => n

/-- `write(io, x)` for a primitive value with bit pattern `u`: Base's methods for its
bit types (`base/io.jl`), else the fallback `write(io::IO, x) = throw(MethodError(...))`
(`base/io.jl:897`). -/
def writePrim : PrimTy → Nat → Except SErr Bytes
  | .base t, u => .ok (le (nbytes t) u)
  | .user _ _, _ => .error (.methodError "write")

/-- `read(io, T)` for a primitive type (`base/io.jl:1009-1016`, fallback `:1345`). -/
def readPrim : PrimTy → Bytes → Except SErr (Nat × Bytes)
  | .base t, bs => if nbytes t ≤ bs.length then .ok (unle (bs.take (nbytes t)), bs.drop (nbytes t))
      else .error .eof
  | .user _ _, _ => .error (.errorEx "The IO stream does not support reading objects of type")

/-- The primitive branch of `serialize_any` (`:869-871`): after the type, the value
is written with `write(s.io, x)`; `deserialize(s, t::DataType)` (`:1853-1854`) reads
it with `read(s.io, t)`. -/
def primRoundTrip (P : PrimTy) (u : Nat) : Except SErr Nat := do
  let b ← writePrim P u
  let (v, _) ← readPrim P b
  pure v

/-- Every value of a primitive type round-trips through its `serialize_any` branch. -/
def PrimitiveRoundTrip : Prop :=
  ∀ (P : PrimTy) (u : Nat), u < 256 ^ P.nbytes → primRoundTrip P u = .ok u

end JuliaLean.Serialization
