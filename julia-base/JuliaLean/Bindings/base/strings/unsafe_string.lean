import JuliaLean.base.pointer
import JuliaLean.base.strings.string

namespace JuliaLean.Bindings.base.strings.unsafe_string

/-- Bind `unsafe_string(::Ptr{UInt8})` to the modeled `jl_cstr_to_string` runtime. -/
def unsafeStringNulUInt8Bound (ops : JuliaLean.base.strings.string.StringPointerPrimitive)
    (pointer : JuliaLean.base.pointer.Ptr (JuliaLean.JInt .u8)) :
    JuliaLean.base.strings.string.CStringOutcome (List UInt8) :=
  JuliaLean.base.strings.string.unsafeStringNul
    (JuliaLean.base.pointer.convertPtrType JuliaLean.base.pointer.C_NULL)
    ops.jlCstrToString pointer

/-- Bind `unsafe_string(::Ptr{Int8})` through the C ABI's `Ptr{UInt8}` argument. -/
def unsafeStringNulInt8Bound (ops : JuliaLean.base.strings.string.StringPointerPrimitive)
    (pointer : JuliaLean.base.pointer.Ptr (JuliaLean.JInt .i8)) :
    JuliaLean.base.strings.string.CStringOutcome (List UInt8) :=
  JuliaLean.base.strings.string.unsafeStringNul
    (JuliaLean.base.pointer.convertPtrType JuliaLean.base.pointer.C_NULL)
    (fun pointer => ops.jlCstrToString (JuliaLean.base.pointer.convertPtrType pointer))
    pointer

end JuliaLean.Bindings.base.strings.unsafe_string
