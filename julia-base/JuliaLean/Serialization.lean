import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Serialization.Model
import JuliaLean.Serialization.Props
import JuliaLean.Serialization.Refutations
import JuliaLean.Serialization.Validation
import JuliaLean.Serialization.Basic
import JuliaLean.Serialization.Proofs

namespace JuliaLean.Serialization

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "serialization-roundtrip", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["serialize(::IO, x)", "deserialize(::IO)", "serialize_cycle", "writetag", "write_as_tag",
      "serialize(::AbstractSerializer, ::Symbol)", "serialize(::AbstractSerializer, ::String)",
      "serialize(::AbstractSerializer, ::Tuple)", "serialize(::AbstractSerializer, ::Expr)",
      "serialize(::AbstractSerializer, ::Array)", "serialize_any", "serialize_type_data", "handle_deserialize",
      "deserialize_array", "deserialize_datatype", "deserialize(::AbstractSerializer, ::DataType)"]
    statement := "deserialize(serialize(x)) returns x and leaves the stream just after it, for integers of all ten widths, floats (bit patterns), Bool, complete Chars, nothing, Symbols and Strings of any length, Tuples, Expr, Vector{Any} with #undef, bits-integer Vectors, Vector{Bool}, Base.RefValue{Any}, UnitRange{Int64}, NamedTuples of scalars, and shared and cyclic references."
    source := "serialize docstring, Serialization.jl:959-961", status := .proven
    prop := ``RoundTrip, thm := some ``roundTrip_proof
    notes := "Covers the 255/256-byte String/Symbol/Tuple/Expr header boundaries, the 7/8-byte String/Symbol sharing boundary, and all three backreference widths. Model differentially checked against Julia (Validation.lean)." },
  { id := "serialization-slot-agreement", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["serialize_cycle", "_setcycle!", "deserialize_cycle", "resolve_ref_immediately", "_setbackref!", "_getbackref"]
    statement := "After deserialize(serialize(x)), the deserializer's counter and backref_table agree with the serializer's counter and cycle_table, so every back-reference denotes the object written at that slot (sharing and cycles are restored)."
    source := "invariant (serialize_cycle / deserialize_cycle pair up slots)", status := .proven
    prop := ``SlotAgreement, thm := some ``slotAgreement_proof },
  { id := "serialization-backref-decode", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["_emit_backref", "handle_deserialize", "_getbackref"]
    statement := "For every slot k < 2^63 holding an entry, the bytes _emit_backref writes for k decode to that entry and nothing more, at the UInt16 / Int32 / Int64 boundaries 65535/65536 and typemax(Int32)/typemax(Int32)+1."
    source := "invariant (SHORTBACKREF_TAG / BACKREF_TAG / LONGBACKREF_TAG)", status := .proven
    prop := ``BackrefDecode, thm := some ``backrefDecode_proof },
  { id := "serialization-header-versions", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["writeheader", "readheader"]
    statement := "A stream whose header carries format version v is read back when v <= ser_version and rejected with \"Cannot read stream serialized with a newer version of Julia\" when v > ser_version."
    source := "readheader, Serialization.jl:922-954; writeheader docstring :891-905", status := .proven
    prop := ``HeaderVersions, thm := some ``headerVersions_proof },
  -- refuted
  { id := "serialization-char-malformed", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["serialize(::AbstractSerializer, ::Char)", "handle_deserialize", "write(::IO, ::Char)", "read(::IO, ::Type{Char})"]
    statement := "For every Char bit pattern c and Int32 n, deserialize(serialize((c, n))) == (c, n) and consumes exactly the serialized bytes."
    source := "serialize docstring, Serialization.jl:959-961; base/char.jl:18-19 (Char encodes invalid byte streams losslessly)", status := .refuted
    prop := ``CharRoundTrip, thm := some ``charRoundTrip_refuted
    issue := "none found (queries: serialize Char invalid, serialize malformed Char, deserialize Char EOFError, Serialization invalid Char, read(io, Char) continuation, Serialization Char, serialize Char, deserialize Char)"
    notes := "('\\xc0', Int32(1)): write(io, '\\xc0') emits one byte and read(io, Char) also takes the tag byte 0xbf of Int32(1), so deserialize throws EOFError; with 42 serialized after it, the first deserialize returns ('\\xc0\\xbf', 42). Same on 1.13.2." },
  { id := "serialization-primitive-type", juliaFile := "stdlib/Serialization/src/Serialization.jl"
    juliaFns := ["serialize_any", "deserialize(::AbstractSerializer, ::DataType)"]
    statement := "Every value of a primitive type round-trips through the primitive branch of serialize_any and deserialize."
    source := "serialize docstring, Serialization.jl:959-961 (\"Write an arbitrary value\")", status := .refuted
    prop := ``PrimitiveRoundTrip, thm := some ``primitiveRoundTrip_refuted
    issue := "none found (queries: serialize primitive type write MethodError, serialize custom primitive type, Serialization primitive type, isprimitivetype serialize); related #53544 (closed)"
    notes := "primitive type Bits32 32 end: serialize(io, x) throws MethodError: no method matching write(::IOBuffer, ::Bits32) (base/io.jl:897); Vector{Bits32} works because arrays are written raw. Same on 1.13.2." }
]

end JuliaLean.Serialization
