import JuliaLean.ExprReflect.EnumsRows
import JuliaLean.Registry.Types

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def enumRowEntries : List Entry := [
  { id := "exprreflect-enums-row-17", juliaFile := "base/Enums.jl"
    juliaFns := ["basetype(::Type{<:Enum{T}}) where {T<:Integer}"]
    statement := "For every allowed input, `basetype(::Type{<:Enum{T}}) where {T<:Integer}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:17-17", status := .proven
    prop := ``EnumRow17Property, thm := some ``enumRow17_proven },
  { id := "exprreflect-enums-row-19", juliaFile := "base/Enums.jl"
    juliaFns := ["(::Type{T})(x::Enum{T2}) where {T<:Integer,T2<:Integer}"]
    statement := "For every allowed input, `(::Type{T})(x::Enum{T2}) where {T<:Integer,T2<:Integer}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:19-19", status := .proven
    prop := ``EnumRow19Property, thm := some ``enumRow19_proven },
  { id := "exprreflect-enums-row-20", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.cconvert(::Type{T}, x::Enum{T2}) where {T<:Integer,T2<:Integer}"]
    statement := "For every allowed input, `Base.cconvert(::Type{T}, x::Enum{T2}) where {T<:Integer,T2<:Integer}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:20-20", status := .proven
    prop := ``EnumRow20Property, thm := some ``enumRow20_proven },
  { id := "exprreflect-enums-row-21", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.write(io::IO, x::Enum{T}) where {T<:Integer}"]
    statement := "For every allowed input, `Base.write(io::IO, x::Enum{T}) where {T<:Integer}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:21-21", status := .proven
    prop := ``EnumRow21Property, thm := some ``enumRow21_proven },
  { id := "exprreflect-enums-row-22", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.read(io::IO, ::Type{T}) where {T<:Enum}"]
    statement := "For every allowed input, `Base.read(io::IO, ::Type{T}) where {T<:Enum}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:22-22", status := .proven
    prop := ``EnumRow22Property, thm := some ``enumRow22_proven },
  { id := "exprreflect-enums-row-30", juliaFile := "base/Enums.jl"
    juliaFns := ["_enum_hash(x::Enum, h::UInt)"]
    statement := "For every allowed input, `_enum_hash(x::Enum, h::UInt)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:30-30", status := .proven
    prop := ``EnumRow30Property, thm := some ``enumRow30_proven },
  { id := "exprreflect-enums-row-31", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.hash(x::Enum, h::UInt)"]
    statement := "For every allowed input, `Base.hash(x::Enum, h::UInt)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:31-31", status := .proven
    prop := ``EnumRow31Property, thm := some ``enumRow31_proven },
  { id := "exprreflect-enums-row-32", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.isless(x::T, y::T) where {T<:Enum}"]
    statement := "For every allowed input, `Base.isless(x::T, y::T) where {T<:Enum}` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:32-32", status := .proven
    prop := ``EnumRow32Property, thm := some ``enumRow32_proven },
  { id := "exprreflect-enums-row-34", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.Symbol(x::Enum)"]
    statement := "For every allowed input, `Base.Symbol(x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:34-34", status := .proven
    prop := ``EnumRow34Property, thm := some ``enumRow34_proven },
  { id := "exprreflect-enums-row-36", juliaFile := "base/Enums.jl"
    juliaFns := ["_symbol(x::Enum)"]
    statement := "For every allowed input, `_symbol(x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:36-40", status := .proven
    prop := ``EnumRow36Property, thm := some ``enumRow36_proven },
  { id := "exprreflect-enums-row-42", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.print(io::IO, x::Enum)"]
    statement := "For every allowed input, `Base.print(io::IO, x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:42-42", status := .proven
    prop := ``EnumRow42Property, thm := some ``enumRow42_proven },
  { id := "exprreflect-enums-row-44", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.show(io::IO, x::Enum)"]
    statement := "For every allowed input, `Base.show(io::IO, x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:44-55", status := .proven
    prop := ``EnumRow44Property, thm := some ``enumRow44_proven },
  { id := "exprreflect-enums-row-57", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.show(io::IO, ::MIME\"text/plain\", x::Enum)"]
    statement := "For every allowed input, `Base.show(io::IO, ::MIME\"text/plain\", x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:57-62", status := .proven
    prop := ``EnumRow57Property, thm := some ``enumRow57_proven },
  { id := "exprreflect-enums-row-64", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.show(io::IO, m::MIME\"text/plain\", t::Type{<:Enum})"]
    statement := "For every allowed input, `Base.show(io::IO, m::MIME\"text/plain\", t::Type{<:Enum})` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:64-76", status := .proven
    prop := ``EnumRow64Property, thm := some ``enumRow64_proven },
  { id := "exprreflect-enums-row-79", juliaFile := "base/Enums.jl"
    juliaFns := ["membershiptest(expr, values)"]
    statement := "For every allowed input, `membershiptest(expr, values)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:79-88", status := .proven
    prop := ``EnumRow79Property, thm := some ``enumRow79_proven },
  { id := "exprreflect-enums-row-91", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.broadcastable(x::Enum)"]
    statement := "For every allowed input, `Base.broadcastable(x::Enum)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:91-91", status := .proven
    prop := ``EnumRow91Property, thm := some ``enumRow91_proven },
  { id := "exprreflect-enums-row-93", juliaFile := "base/Enums.jl"
    juliaFns := ["enum_argument_error(typename, x)"]
    statement := "For every allowed input, `enum_argument_error(typename, x)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:93-93", status := .proven
    prop := ``EnumRow93Property, thm := some ``enumRow93_proven },
  { id := "exprreflect-enums-row-144", juliaFile := "base/Enums.jl"
    juliaFns := ["enum(T::Union{Symbol,Expr}, syms...)"]
    statement := "For every allowed input, `enum(T::Union{Symbol,Expr}, syms...)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:144-252", status := .proven
    prop := ``EnumRow144Property, thm := some ``enumRow144_proven },
  { id := "exprreflect-enums-row-221", juliaFile := "base/Enums.jl"
    juliaFns := ["$(esc(typename))(x::Integer)"]
    statement := "For every allowed input, `$(esc(typename))(x::Integer)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:221-224", status := .proven
    prop := ``EnumRow221Property, thm := some ``enumRow221_proven },
  { id := "exprreflect-enums-row-225", juliaFile := "base/Enums.jl"
    juliaFns := ["Enums.namemap(::Type{$(esc(typename))})"]
    statement := "For every allowed input, `Enums.namemap(::Type{$(esc(typename))})` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:225-225", status := .proven
    prop := ``EnumRow225Property, thm := some ``enumRow225_proven },
  { id := "exprreflect-enums-row-226", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.typemin(x::Type{$(esc(typename))})"]
    statement := "For every allowed input, `Base.typemin(x::Type{$(esc(typename))})` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:226-226", status := .proven
    prop := ``EnumRow226Property, thm := some ``enumRow226_proven },
  { id := "exprreflect-enums-row-227", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.typemax(x::Type{$(esc(typename))})"]
    statement := "For every allowed input, `Base.typemax(x::Type{$(esc(typename))})` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:227-227", status := .proven
    prop := ``EnumRow227Property, thm := some ``enumRow227_proven },
  { id := "exprreflect-enums-row-233", juliaFile := "base/Enums.jl"
    juliaFns := ["Enums._enum_hash(x::$(esc(typename)), h::UInt)"]
    statement := "For every allowed input, `Enums._enum_hash(x::$(esc(typename)), h::UInt)` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:233-233", status := .proven
    prop := ``EnumRow233Property, thm := some ``enumRow233_proven },
  { id := "exprreflect-enums-row-236", juliaFile := "base/Enums.jl"
    juliaFns := ["Base.instances(::Type{$(esc(typename))})"]
    statement := "For every allowed input, `Base.instances(::Type{$(esc(typename))})` follows its source conversion, validation, lookup, formatting, or generated-method behavior."
    source := "source-body invariant; base/Enums.jl:236-236", status := .proven
    prop := ``EnumRow236Property, thm := some ``enumRow236_proven }
]

end JuliaLean.ExprReflect
