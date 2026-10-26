import JuliaLean.BigNumsCov.MpfrFaithful.Arithmetic
import JuliaLean.BigNumsCov.MpfrFaithful.Compare
import JuliaLean.BigNumsCov.MpfrFaithful.Conversions
import JuliaLean.BigNumsCov.MpfrFaithful.Formatting
import JuliaLean.BigNumsCov.MpfrFaithful.Math
import JuliaLean.BigNumsCov.MpfrFaithful.Precision
import JuliaLean.BigNumsCov.MpfrFaithful.Setup
import JuliaLean.BigNumsCov.MpfrFaithful.Storage

import JuliaLean.Registry.Types

namespace JuliaLean.BigNumsCov.MpfrFaithful

open JuliaLean.Registry

/-- Method-specific entries replacing rows rejected by the fixed coverage review. -/
def entries : List Entry := [
  { id := "bignumscov-mpfr-44", juliaFile := "base/mpfr.jl"
    juliaFns := ["version()"]
    statement := "The version method at base/mpfr.jl:44-44 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:44-44", status := .proven
    prop := ``Version44, thm := some ``version44_proven },
  { id := "bignumscov-mpfr-45", juliaFile := "base/mpfr.jl"
    juliaFns := ["patches()"]
    statement := "The patches method at base/mpfr.jl:45-45 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:45-45", status := .proven
    prop := ``Patches45, thm := some ``patches45_proven },
  { id := "bignumscov-mpfr-47", juliaFile := "base/mpfr.jl"
    juliaFns := ["__init__()"]
    statement := "The __init__ method at base/mpfr.jl:47-56 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:47-56", status := .proven
    prop := ``Init47, thm := some ``init47_proven },
  { id := "bignumscov-mpfr-75", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Nearest})"]
    statement := "The convert method at base/mpfr.jl:75-75 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:75-75", status := .proven
    prop := ``Convert75, thm := some ``convert75_proven },
  { id := "bignumscov-mpfr-76", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:ToZero})"]
    statement := "The convert method at base/mpfr.jl:76-76 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:76-76", status := .proven
    prop := ``Convert76, thm := some ``convert76_proven },
  { id := "bignumscov-mpfr-77", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Up})"]
    statement := "The convert method at base/mpfr.jl:77-77 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:77-77", status := .proven
    prop := ``Convert77, thm := some ``convert77_proven },
  { id := "bignumscov-mpfr-78", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Down})"]
    statement := "The convert method at base/mpfr.jl:78-78 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:78-78", status := .proven
    prop := ``Convert78, thm := some ``convert78_proven },
  { id := "bignumscov-mpfr-79", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:FromZero})"]
    statement := "The convert method at base/mpfr.jl:79-79 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:79-79", status := .proven
    prop := ``Convert79, thm := some ``convert79_proven },
  { id := "bignumscov-mpfr-81", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{RoundingMode}, r::MPFRRoundingMode)"]
    statement := "The convert method at base/mpfr.jl:81-95 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:81-95", status := .proven
    prop := ``Convert81, thm := some ``convert81_proven },
  { id := "bignumscov-mpfr-110", juliaFile := "base/mpfr.jl"
    juliaFns := ["tie_breaker_is_to_even(::MPFRRoundingMode)"]
    statement := "The tie_breaker_is_to_even method at base/mpfr.jl:110-110 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:110-110", status := .proven
    prop := ``TieBreaker110, thm := some ``tieBreaker110_proven },
  { id := "bignumscov-mpfr-149", juliaFile := "base/mpfr.jl"
    juliaFns := ["_BigFloat(d::Memory{Limb})"]
    statement := "The _BigFloat method at base/mpfr.jl:149-152 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:149-152", status := .proven
    prop := ``BigFloat149, thm := some ``bigFloat149_proven },
  { id := "bignumscov-mpfr-154", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:154-171 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:154-171", status := .proven
    prop := ``BigFloat154, thm := some ``bigFloat154_proven },
  { id := "bignumscov-mpfr-183", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.getproperty(x::BigFloat, s::Symbol)"]
    statement := "The Base.getproperty method at base/mpfr.jl:183-197 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:183-197", status := .proven
    prop := ``Getproperty183, thm := some ``getproperty183_proven },
  { id := "bignumscov-mpfr-201", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.setproperty!(x::BigFloat, s::Symbol, v)"]
    statement := "The Base.setproperty! method at base/mpfr.jl:201-211 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:201-211", status := .proven
    prop := ``Setproperty201, thm := some ``setproperty201_proven },
  { id := "bignumscov-mpfr-214", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ptr{BigFloat})"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:214-214 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:214-214", status := .proven
    prop := ``UnsafeConvert214, thm := some ``unsafeConvert214_proven },
  { id := "bignumscov-mpfr-215", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ref{BigFloat})"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:215-215 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:215-215", status := .proven
    prop := ``UnsafeConvert215, thm := some ``unsafeConvert215_proven },
  { id := "bignumscov-mpfr-216", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::BigFloat)"]
    statement := "The Base.cconvert method at base/mpfr.jl:216-216 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:216-216", status := .proven
    prop := ``Cconvert216, thm := some ``cconvert216_proven },
  { id := "bignumscov-mpfr-217", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::Number)"]
    statement := "The Base.cconvert method at base/mpfr.jl:217-217 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:217-217", status := .proven
    prop := ``Cconvert217, thm := some ``cconvert217_proven },
  { id := "bignumscov-mpfr-218", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::Ref{BigFloat})"]
    statement := "The Base.cconvert method at base/mpfr.jl:218-218 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:218-218", status := .proven
    prop := ``Cconvert218, thm := some ``cconvert218_proven },
  { id := "bignumscov-mpfr-219", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::BigFloatData)"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:219-228 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:219-228", status := .proven
    prop := ``UnsafeConvert219, thm := some ``unsafeConvert219_proven },
  { id := "bignumscov-mpfr-229", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ptr{Limb}}, fd::BigFloatData)"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:229-229 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:229-229", status := .proven
    prop := ``UnsafeConvert229, thm := some ``unsafeConvert229_proven },
  { id := "bignumscov-mpfr-230", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.setindex!(fd::BigFloatData, v, i)"]
    statement := "The Base.setindex! method at base/mpfr.jl:230-235 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:230-235", status := .proven
    prop := ``Setindex230, thm := some ``setindex230_proven },
  { id := "bignumscov-mpfr-236", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.getindex(fd::BigFloatData, i)"]
    statement := "The Base.getindex method at base/mpfr.jl:236-240 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:236-240", status := .proven
    prop := ``Getindex236, thm := some ``getindex236_proven },
  { id := "bignumscov-mpfr-241", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.length(fd::BigFloatData)"]
    statement := "The Base.length method at base/mpfr.jl:241-241 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:241-241", status := .proven
    prop := ``Length241, thm := some ``length241_proven },
  { id := "bignumscov-mpfr-242", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.copyto!(fd::BigFloatData, limbs)"]
    statement := "The Base.copyto! method at base/mpfr.jl:242-242 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:242-242", status := .proven
    prop := ``Copyto242, thm := some ``copyto242_proven },
  { id := "bignumscov-mpfr-247", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding_raw(::Type{BigFloat}, r::MPFRRoundingMode)"]
    statement := "The setrounding_raw method at base/mpfr.jl:247-247 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:247-247", status := .proven
    prop := ``SetroundingRaw247, thm := some ``setroundingRaw247_proven },
  { id := "bignumscov-mpfr-248", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding_raw(f::Function, ::Type{BigFloat}, r::MPFRRoundingMode)"]
    statement := "The setrounding_raw method at base/mpfr.jl:248-250 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:248-250", status := .proven
    prop := ``SetroundingRaw248, thm := some ``setroundingRaw248_proven },
  { id := "bignumscov-mpfr-252", juliaFile := "base/mpfr.jl"
    juliaFns := ["rounding(::Type{BigFloat})"]
    statement := "The rounding method at base/mpfr.jl:252-252 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:252-252", status := .proven
    prop := ``Rounding252, thm := some ``rounding252_proven },
  { id := "bignumscov-mpfr-253", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding(::Type{BigFloat}, r::RoundingMode)"]
    statement := "The setrounding method at base/mpfr.jl:253-253 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:253-253", status := .proven
    prop := ``Setrounding253, thm := some ``setrounding253_proven },
  { id := "bignumscov-mpfr-254", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding(f::Function, ::Type{BigFloat}, r::RoundingMode)"]
    statement := "The setrounding method at base/mpfr.jl:254-255 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:254-255", status := .proven
    prop := ``Setrounding254, thm := some ``setrounding254_proven },
  { id := "bignumscov-mpfr-299", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen(::Type{Float64})"]
    statement := "The widen method at base/mpfr.jl:299-299 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:299-299", status := .proven
    prop := ``Widen299, thm := some ``widen299_proven },
  { id := "bignumscov-mpfr-300", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen(::Type{BigFloat})"]
    statement := "The widen method at base/mpfr.jl:300-300 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:300-300", status := .proven
    prop := ``Widen300, thm := some ``widen300_proven },
  { id := "bignumscov-mpfr-302", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:302-311 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:302-311", status := .proven
    prop := ``BigFloat302, thm := some ``bigFloat302_proven },
  { id := "bignumscov-mpfr-313", juliaFile := "base/mpfr.jl"
    juliaFns := ["_duplicate(x::BigFloat)"]
    statement := "The _duplicate method at base/mpfr.jl:313-317 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:313-317", status := .proven
    prop := ``Duplicate313, thm := some ``duplicate313_proven },
  { id := "bignumscov-mpfr-322", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::($fC), r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:322-326 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:322-326", status := .proven
    prop := ``BigFloat322, thm := some ``bigFloat322_proven },
  { id := "bignumscov-mpfr-330", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Float64, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:330-372 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:330-372", status := .proven
    prop := ``BigFloat330, thm := some ``bigFloat330_proven },
  { id := "bignumscov-mpfr-374", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::BigInt, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:374-378 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:374-378", status := .proven
    prop := ``BigFloat374, thm := some ``bigFloat374_proven },
  { id := "bignumscov-mpfr-380", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Integer; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:380-381 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:380-381", status := .proven
    prop := ``BigFloat380, thm := some ``bigFloat380_proven },
  { id := "bignumscov-mpfr-382", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Integer, r::MPFRRoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:382-383 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:382-383", status := .proven
    prop := ``BigFloat382, thm := some ``bigFloat382_proven },
  { id := "bignumscov-mpfr-385", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{Bool,Int8,Int16,Int32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:385-386 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:385-386", status := .proven
    prop := ``BigFloat385, thm := some ``bigFloat385_proven },
  { id := "bignumscov-mpfr-387", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{UInt8,UInt16,UInt32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:387-388 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:387-388", status := .proven
    prop := ``BigFloat387, thm := some ``bigFloat387_proven },
  { id := "bignumscov-mpfr-390", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{Float16,Float32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:390-391 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:390-391", status := .proven
    prop := ``BigFloat390, thm := some ``bigFloat390_proven },
  { id := "bignumscov-mpfr-393", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Rational, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:393-400 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:393-400", status := .proven
    prop := ``BigFloat393, thm := some ``bigFloat393_proven },
  { id := "bignumscov-mpfr-401", juliaFile := "base/mpfr.jl"
    juliaFns := ["_opposite_round(r::MPFRRoundingMode)"]
    statement := "The _opposite_round method at base/mpfr.jl:401-405 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:401-405", status := .proven
    prop := ``Opposite401, thm := some ``opposite401_proven },
  { id := "bignumscov-mpfr-407", juliaFile := "base/mpfr.jl"
    juliaFns := ["tryparse(::Type{BigFloat}, s::AbstractString; base::Integer=0, precision::Integer=_precision_with_base_2(BigFloat), rounding::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The tryparse method at base/mpfr.jl:407-412 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:407-412", status := .proven
    prop := ``Tryparse407, thm := some ``tryparse407_proven },
  { id := "bignumscov-mpfr-414", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::AbstractString, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:414-415 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:414-415", status := .proven
    prop := ``BigFloat414, thm := some ``bigFloat414_proven },
  { id := "bignumscov-mpfr-417", juliaFile := "base/mpfr.jl"
    juliaFns := ["Rational(x::BigFloat)"]
    statement := "The Rational method at base/mpfr.jl:417-417 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:417-417", status := .proven
    prop := ``Rational417, thm := some ``rational417_proven },
  { id := "bignumscov-mpfr-418", juliaFile := "base/mpfr.jl"
    juliaFns := ["AbstractFloat(x::BigInt)"]
    statement := "The AbstractFloat method at base/mpfr.jl:418-418 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:418-418", status := .proven
    prop := ``AbstractFloat418, thm := some ``abstractFloat418_proven },
  { id := "bignumscov-mpfr-420", juliaFile := "base/mpfr.jl"
    juliaFns := ["float(::Type{BigInt})"]
    statement := "The float method at base/mpfr.jl:420-420 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:420-420", status := .proven
    prop := ``Float420, thm := some ``float420_proven },
  { id := "bignumscov-mpfr-422", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Real, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:422-423 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:422-423", status := .proven
    prop := ``BigFloat422, thm := some ``bigFloat422_proven },
  { id := "bignumscov-mpfr-424", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::AbstractString, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:424-425 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:424-425", status := .proven
    prop := ``BigFloat424, thm := some ``bigFloat424_proven },
  { id := "bignumscov-mpfr-428", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(T, x::BigFloat, r::RoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:428-428 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:428-428", status := .proven
    prop := ``Unchecked428, thm := some ``unchecked428_proven },
  { id := "bignumscov-mpfr-430", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{Int64}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:430-432 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:430-432", status := .proven
    prop := ``Unchecked430, thm := some ``unchecked430_proven },
  { id := "bignumscov-mpfr-434", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{UInt64}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:434-436 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:434-436", status := .proven
    prop := ``Unchecked434, thm := some ``unchecked434_proven },
  { id := "bignumscov-mpfr-438", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{BigInt}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:438-442 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:438-442", status := .proven
    prop := ``Unchecked438, thm := some ``unchecked438_proven },
  { id := "bignumscov-mpfr-444", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{T}, x::BigFloat, r::MPFRRoundingMode) where T<:Union{Signed, Unsigned}"]
    statement := "The _unchecked_cast method at base/mpfr.jl:444-447 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:444-447", status := .proven
    prop := ``Unchecked444, thm := some ``unchecked444_proven },
  { id := "bignumscov-mpfr-449", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode}) where T<:Union{Signed, Unsigned}"]
    statement := "The round method at base/mpfr.jl:449-456 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:449-456", status := .proven
    prop := ``Round449, thm := some ``round449_proven },
  { id := "bignumscov-mpfr-458", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{BigInt}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode})"]
    statement := "The round method at base/mpfr.jl:458-463 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:458-463", status := .proven
    prop := ``Round458, thm := some ``round458_proven },
  { id := "bignumscov-mpfr-465", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat, r::RoundingMode) where T<:Union{Signed, Unsigned}"]
    statement := "The round method at base/mpfr.jl:465-466 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:465-466", status := .proven
    prop := ``Invoke465, thm := some ``invoke465_proven },
  { id := "bignumscov-mpfr-467", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{BigInt}, x::BigFloat, r::RoundingMode)"]
    statement := "The round method at base/mpfr.jl:467-468 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:467-468", status := .proven
    prop := ``Invoke467, thm := some ``invoke467_proven },
  { id := "bignumscov-mpfr-471", juliaFile := "base/mpfr.jl"
    juliaFns := ["unsafe_trunc(::Type{T}, x::BigFloat) where {T<:Integer}"]
    statement := "The unsafe_trunc method at base/mpfr.jl:471-471 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:471-471", status := .proven
    prop := ``Unsafe471, thm := some ``unsafe471_proven },
  { id := "bignumscov-mpfr-472", juliaFile := "base/mpfr.jl"
    juliaFns := ["unsafe_trunc(::Type{BigInt}, x::BigFloat)"]
    statement := "The unsafe_trunc method at base/mpfr.jl:472-472 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:472-472", status := .proven
    prop := ``Unsafe472, thm := some ``unsafe472_proven },
  { id := "bignumscov-mpfr-474", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat) where T<:Integer"]
    statement := "The round method at base/mpfr.jl:474-474 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:474-474", status := .proven
    prop := ``Round474, thm := some ``round474_proven },
  { id := "bignumscov-mpfr-476", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{Integer}, x::BigFloat, r::RoundingMode)"]
    statement := "The round method at base/mpfr.jl:476-476 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:476-476", status := .proven
    prop := ``Round476, thm := some ``round476_proven },
  { id := "bignumscov-mpfr-477", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{Integer}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The round method at base/mpfr.jl:477-477 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:477-477", status := .proven
    prop := ``Round477, thm := some ``round477_proven },
  { id := "bignumscov-mpfr-479", juliaFile := "base/mpfr.jl"
    juliaFns := ["Bool(x::BigFloat)"]
    statement := "The Bool method at base/mpfr.jl:479-483 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:479-483", status := .proven
    prop := ``Bool479, thm := some ``bool479_proven },
  { id := "bignumscov-mpfr-484", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigInt(x::BigFloat)"]
    statement := "The BigInt method at base/mpfr.jl:484-487 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:484-487", status := .proven
    prop := ``BigInt484, thm := some ``bigInt484_proven },
  { id := "bignumscov-mpfr-489", juliaFile := "base/mpfr.jl"
    juliaFns := ["(::Type{T})(x::BigFloat) where T<:Integer"]
    statement := "The (::Type{T}) method at base/mpfr.jl:489-492 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:489-492", status := .proven
    prop := ``Convert489, thm := some ``convert489_proven },
  { id := "bignumscov-mpfr-494", juliaFile := "base/mpfr.jl"
    juliaFns := ["to_ieee754(::Type{T}, x::BigFloat, rm) where {T<:AbstractFloat}"]
    statement := "The to_ieee754 method at base/mpfr.jl:494-548 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:494-548", status := .proven
    prop := ``ToIeee494, thm := some ``toIeee494_proven },
  { id := "bignumscov-mpfr-550", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float16(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float16 method at base/mpfr.jl:550-550 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:550-550", status := .proven
    prop := ``Float550, thm := some ``float550_proven },
  { id := "bignumscov-mpfr-551", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float32(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float32 method at base/mpfr.jl:551-551 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:551-551", status := .proven
    prop := ``Float551, thm := some ``float551_proven },
  { id := "bignumscov-mpfr-552", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float64(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float64 method at base/mpfr.jl:552-552 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:552-552", status := .proven
    prop := ``Float552, thm := some ``float552_proven },
  { id := "bignumscov-mpfr-553", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float16(x::BigFloat, r::RoundingMode)"]
    statement := "The Float16 method at base/mpfr.jl:553-553 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:553-553", status := .proven
    prop := ``Float553, thm := some ``float553_proven },
  { id := "bignumscov-mpfr-554", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float32(x::BigFloat, r::RoundingMode)"]
    statement := "The Float32 method at base/mpfr.jl:554-554 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:554-554", status := .proven
    prop := ``Float554, thm := some ``float554_proven },
  { id := "bignumscov-mpfr-555", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float64(x::BigFloat, r::RoundingMode)"]
    statement := "The Float64 method at base/mpfr.jl:555-555 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:555-555", status := .proven
    prop := ``Float555, thm := some ``float555_proven },
  { id := "bignumscov-mpfr-557", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigFloat}, ::Type{<:Real})"]
    statement := "The promote_rule method at base/mpfr.jl:557-557 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:557-557", status := .proven
    prop := ``Promote557, thm := some ``promote557_proven },
  { id := "bignumscov-mpfr-558", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigInt}, ::Type{<:AbstractFloat})"]
    statement := "The promote_rule method at base/mpfr.jl:558-558 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:558-558", status := .proven
    prop := ``Promote558, thm := some ``promote558_proven },
  { id := "bignumscov-mpfr-559", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigFloat}, ::Type{<:AbstractFloat})"]
    statement := "The promote_rule method at base/mpfr.jl:559-559 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:559-559", status := .proven
    prop := ``Promote559, thm := some ``promote559_proven },
  { id := "bignumscov-mpfr-561", juliaFile := "base/mpfr.jl"
    juliaFns := ["big(::Type{<:AbstractFloat})"]
    statement := "The big method at base/mpfr.jl:561-561 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:561-561", status := .proven
    prop := ``Big561, thm := some ``big561_proven },
  { id := "bignumscov-mpfr-563", juliaFile := "base/mpfr.jl"
    juliaFns := ["big(x::AbstractFloat)"]
    statement := "The big method at base/mpfr.jl:563-563 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:563-563", status := .proven
    prop := ``Big563, thm := some ``big563_proven },
  { id := "bignumscov-mpfr-565", juliaFile := "base/mpfr.jl"
    juliaFns := ["Rational{BigInt}(x::AbstractFloat)"]
    statement := "The Rational{BigInt} method at base/mpfr.jl:565-571 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:565-571", status := .proven
    prop := ``Rational565, thm := some ``rational565_proven },
  { id := "bignumscov-mpfr-589", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::CulongMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:589-589 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:589-589", status := .proven
    prop := ``Reverse589, thm := some ``reverse589_proven },
  { id := "bignumscov-mpfr-597", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::ClongMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:597-597 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:597-597", status := .proven
    prop := ``Reverse597, thm := some ``reverse597_proven },
  { id := "bignumscov-mpfr-605", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::CdoubleMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:605-605 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:605-605", status := .proven
    prop := ``Reverse605, thm := some ``reverse605_proven },
  { id := "bignumscov-mpfr-613", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::BigInt, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:613-613 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:613-613", status := .proven
    prop := ``Reverse613, thm := some ``reverse613_proven },
  { id := "bignumscov-mpfr-678", juliaFile := "base/mpfr.jl"
    juliaFns := ["inv(x::BigFloat)"]
    statement := "The inv method at base/mpfr.jl:678-678 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:678-678", status := .proven
    prop := ``Inv678, thm := some ``inv678_proven },
  { id := "bignumscov-mpfr-686", juliaFile := "base/mpfr.jl"
    juliaFns := ["muladd(x::BigFloat, y::BigFloat, z::BigFloat)"]
    statement := "The muladd method at base/mpfr.jl:686-686 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:686-686", status := .proven
    prop := ``Muladd686, thm := some ``muladd686_proven },
  { id := "bignumscov-mpfr-690", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, y::BigFloat)"]
    statement := "The div method at base/mpfr.jl:690-695 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:690-695", status := .proven
    prop := ``Div690, thm := some ``div690_proven },
  { id := "bignumscov-mpfr-698", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::CulongMax)"]
    statement := "The div method at base/mpfr.jl:698-703 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:698-703", status := .proven
    prop := ``Div698, thm := some ``div698_proven },
  { id := "bignumscov-mpfr-704", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::CulongMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:704-709 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:704-709", status := .proven
    prop := ``Div704, thm := some ``div704_proven },
  { id := "bignumscov-mpfr-712", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::ClongMax)"]
    statement := "The div method at base/mpfr.jl:712-717 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:712-717", status := .proven
    prop := ``Div712, thm := some ``div712_proven },
  { id := "bignumscov-mpfr-718", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::ClongMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:718-723 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:718-723", status := .proven
    prop := ``Div718, thm := some ``div718_proven },
  { id := "bignumscov-mpfr-726", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::CdoubleMax)"]
    statement := "The div method at base/mpfr.jl:726-731 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:726-731", status := .proven
    prop := ``Div726, thm := some ``div726_proven },
  { id := "bignumscov-mpfr-732", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::CdoubleMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:732-737 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:732-737", status := .proven
    prop := ``Div732, thm := some ``div732_proven },
  { id := "bignumscov-mpfr-740", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::BigInt)"]
    statement := "The div method at base/mpfr.jl:740-745 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:740-745", status := .proven
    prop := ``Div740, thm := some ``div740_proven },
  { id := "bignumscov-mpfr-781", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt(x::BigFloat)"]
    statement := "The sqrt method at base/mpfr.jl:781-787 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:781-787", status := .proven
    prop := ``Sqrt781, thm := some ``sqrt781_proven },
  { id := "bignumscov-mpfr-789", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt(x::BigInt)"]
    statement := "The sqrt method at base/mpfr.jl:789-789 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:789-789", status := .proven
    prop := ``Sqrt789, thm := some ``sqrt789_proven },
  { id := "bignumscov-mpfr-815", juliaFile := "base/mpfr.jl"
    juliaFns := ["^(x::BigFloat, y::Integer)"]
    statement := "The ^ method at base/mpfr.jl:815-815 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:815-815", status := .proven
    prop := ``Power815, thm := some ``power815_proven },
  { id := "bignumscov-mpfr-816", juliaFile := "base/mpfr.jl"
    juliaFns := ["^(x::BigFloat, y::Unsigned)"]
    statement := "The ^ method at base/mpfr.jl:816-816 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:816-816", status := .proven
    prop := ``Power816, thm := some ``power816_proven },
  { id := "bignumscov-mpfr-826", juliaFile := "base/mpfr.jl"
    juliaFns := ["sincos_fast(v::BigFloat)"]
    statement := "The sincos_fast method at base/mpfr.jl:826-831 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:826-831", status := .proven
    prop := ``SincosFast826, thm := some ``sincosFast826_proven },
  { id := "bignumscov-mpfr-832", juliaFile := "base/mpfr.jl"
    juliaFns := ["sincos(v::BigFloat)"]
    statement := "The sincos method at base/mpfr.jl:832-832 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:832-832", status := .proven
    prop := ``Sincos832, thm := some ``sincos832_proven },
  { id := "bignumscov-mpfr-835", juliaFile := "base/mpfr.jl"
    juliaFns := ["big_ln2()"]
    statement := "The big_ln2 method at base/mpfr.jl:835-839 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:835-839", status := .proven
    prop := ``BigLn2835, thm := some ``bigLn2835_proven },
  { id := "bignumscov-mpfr-841", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Clong)"]
    statement := "The ldexp method at base/mpfr.jl:841-845 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:841-845", status := .proven
    prop := ``Ldexp841, thm := some ``ldexp841_proven },
  { id := "bignumscov-mpfr-846", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Culong)"]
    statement := "The ldexp method at base/mpfr.jl:846-850 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:846-850", status := .proven
    prop := ``Ldexp846, thm := some ``ldexp846_proven },
  { id := "bignumscov-mpfr-851", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::ClongMax)"]
    statement := "The ldexp method at base/mpfr.jl:851-851 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:851-851", status := .proven
    prop := ``Ldexp851, thm := some ``ldexp851_proven },
  { id := "bignumscov-mpfr-852", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::CulongMax)"]
    statement := "The ldexp method at base/mpfr.jl:852-852 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:852-852", status := .proven
    prop := ``Ldexp852, thm := some ``ldexp852_proven },
  { id := "bignumscov-mpfr-853", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Integer)"]
    statement := "The ldexp method at base/mpfr.jl:853-853 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:853-853", status := .proven
    prop := ``Ldexp853, thm := some ``ldexp853_proven },
  { id := "bignumscov-mpfr-855", juliaFile := "base/mpfr.jl"
    juliaFns := ["factorial(x::BigFloat)"]
    statement := "The factorial method at base/mpfr.jl:855-863 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:855-863", status := .proven
    prop := ``Factorial855, thm := some ``factorial855_proven },
  { id := "bignumscov-mpfr-872", juliaFile := "base/mpfr.jl"
    juliaFns := ["$f(x::BigFloat)"]
    statement := "The $f method at base/mpfr.jl:872-881 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:872-881", status := .proven
    prop := ``Logarithm872, thm := some ``logarithm872_proven },
  { id := "bignumscov-mpfr-884", juliaFile := "base/mpfr.jl"
    juliaFns := ["log1p(x::BigFloat)"]
    statement := "The log1p method at base/mpfr.jl:884-893 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:884-893", status := .proven
    prop := ``Log1p884, thm := some ``log1p884_proven },
  { id := "bignumscov-mpfr-897", juliaFile := "base/mpfr.jl"
    juliaFns := ["minmax(x::BigFloat, y::BigFloat)"]
    statement := "The minmax method at base/mpfr.jl:897-901 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:897-901", status := .proven
    prop := ``Minmax897, thm := some ``minmax897_proven },
  { id := "bignumscov-mpfr-903", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base._extrema_rf(x::NTuple{2,BigFloat}, y::NTuple{2,BigFloat})"]
    statement := "The Base._extrema_rf method at base/mpfr.jl:903-910 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:903-910", status := .proven
    prop := ``Extrema903, thm := some ``extrema903_proven },
  { id := "bignumscov-mpfr-912", juliaFile := "base/mpfr.jl"
    juliaFns := ["modf(x::BigFloat)"]
    statement := "The modf method at base/mpfr.jl:912-917 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:912-917", status := .proven
    prop := ``Modf912, thm := some ``modf912_proven },
  { id := "bignumscov-mpfr-932", juliaFile := "base/mpfr.jl"
    juliaFns := ["rem2pi(x::BigFloat, r::RoundingMode)"]
    statement := "The rem2pi method at base/mpfr.jl:932-932 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:932-932", status := .proven
    prop := ``Rem2pi932, thm := some ``rem2pi932_proven },
  { id := "bignumscov-mpfr-946", juliaFile := "base/mpfr.jl"
    juliaFns := ["($f)(x::BigFloat)"]
    statement := "The $f method at base/mpfr.jl:946-952 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:946-952", status := .proven
    prop := ``CheckedUnary946, thm := some ``checkedUnary946_proven },
  { id := "bignumscov-mpfr-966", juliaFile := "base/mpfr.jl"
    juliaFns := ["($(Symbol(f,:d)))(x::BigFloat)"]
    statement := "The $(Symbol(f,:d)) method at base/mpfr.jl:966-972 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:966-972", status := .proven
    prop := ``Degree966, thm := some ``degree966_proven },
  { id := "bignumscov-mpfr-973", juliaFile := "base/mpfr.jl"
    juliaFns := ["($(Symbol(:a,f,:d)))(x::BigFloat)"]
    statement := "The $(Symbol(:a,f,:d)) method at base/mpfr.jl:973-979 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:973-979", status := .proven
    prop := ``Degree973, thm := some ``degree973_proven },
  { id := "bignumscov-mpfr-982", juliaFile := "base/mpfr.jl"
    juliaFns := ["atand(y::BigFloat, x::BigFloat)"]
    statement := "The atand method at base/mpfr.jl:982-986 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:982-986", status := .proven
    prop := ``Atand982, thm := some ``atand982_proven },
  { id := "bignumscov-mpfr-990", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:990-990 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:990-990", status := .proven
    prop := ``Equal990, thm := some ``equal990_proven },
  { id := "bignumscov-mpfr-991", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:991-991 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:991-991", status := .proven
    prop := ``LessEqual991, thm := some ``lessEqual991_proven },
  { id := "bignumscov-mpfr-992", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:992-992 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:992-992", status := .proven
    prop := ``Less992, thm := some ``less992_proven },
  { id := "bignumscov-mpfr-994", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::BigInt)"]
    statement := "The cmp method at base/mpfr.jl:994-997 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:994-997", status := .proven
    prop := ``Cmp994, thm := some ``cmp994_proven },
  { id := "bignumscov-mpfr-998", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::ClongMax)"]
    statement := "The cmp method at base/mpfr.jl:998-1001 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:998-1001", status := .proven
    prop := ``Cmp998, thm := some ``cmp998_proven },
  { id := "bignumscov-mpfr-1002", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::CulongMax)"]
    statement := "The cmp method at base/mpfr.jl:1002-1005 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1002-1005", status := .proven
    prop := ``Cmp1002, thm := some ``cmp1002_proven },
  { id := "bignumscov-mpfr-1006", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::Integer)"]
    statement := "The cmp method at base/mpfr.jl:1006-1006 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1006-1006", status := .proven
    prop := ``Cmp1006, thm := some ``cmp1006_proven },
  { id := "bignumscov-mpfr-1007", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::Integer, y::BigFloat)"]
    statement := "The cmp method at base/mpfr.jl:1007-1007 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1007-1007", status := .proven
    prop := ``Cmp1007, thm := some ``cmp1007_proven },
  { id := "bignumscov-mpfr-1009", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::CdoubleMax)"]
    statement := "The cmp method at base/mpfr.jl:1009-1013 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1009-1013", status := .proven
    prop := ``Cmp1009, thm := some ``cmp1009_proven },
  { id := "bignumscov-mpfr-1014", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::CdoubleMax, y::BigFloat)"]
    statement := "The cmp method at base/mpfr.jl:1014-1014 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1014-1014", status := .proven
    prop := ``Cmp1014, thm := some ``cmp1014_proven },
  { id := "bignumscov-mpfr-1016", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::Integer)"]
    statement := "The == method at base/mpfr.jl:1016-1016 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1016-1016", status := .proven
    prop := ``Eq1016, thm := some ``eq1016_proven },
  { id := "bignumscov-mpfr-1017", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::Integer, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:1017-1017 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1017-1017", status := .proven
    prop := ``Eq1017, thm := some ``eq1017_proven },
  { id := "bignumscov-mpfr-1018", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::CdoubleMax)"]
    statement := "The == method at base/mpfr.jl:1018-1018 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1018-1018", status := .proven
    prop := ``Eq1018, thm := some ``eq1018_proven },
  { id := "bignumscov-mpfr-1019", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::CdoubleMax, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:1019-1019 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1019-1019", status := .proven
    prop := ``Eq1019, thm := some ``eq1019_proven },
  { id := "bignumscov-mpfr-1021", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::Integer)"]
    statement := "The < method at base/mpfr.jl:1021-1021 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1021-1021", status := .proven
    prop := ``Lt1021, thm := some ``lt1021_proven },
  { id := "bignumscov-mpfr-1022", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::Integer, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:1022-1022 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1022-1022", status := .proven
    prop := ``Lt1022, thm := some ``lt1022_proven },
  { id := "bignumscov-mpfr-1023", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::CdoubleMax)"]
    statement := "The < method at base/mpfr.jl:1023-1023 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1023-1023", status := .proven
    prop := ``Lt1023, thm := some ``lt1023_proven },
  { id := "bignumscov-mpfr-1024", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::CdoubleMax, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:1024-1024 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1024-1024", status := .proven
    prop := ``Lt1024, thm := some ``lt1024_proven },
  { id := "bignumscov-mpfr-1026", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::Integer)"]
    statement := "The <= method at base/mpfr.jl:1026-1026 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1026-1026", status := .proven
    prop := ``Le1026, thm := some ``le1026_proven },
  { id := "bignumscov-mpfr-1027", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::Integer, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:1027-1027 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1027-1027", status := .proven
    prop := ``Le1027, thm := some ``le1027_proven },
  { id := "bignumscov-mpfr-1028", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::CdoubleMax)"]
    statement := "The <= method at base/mpfr.jl:1028-1028 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1028-1028", status := .proven
    prop := ``Le1028, thm := some ``le1028_proven },
  { id := "bignumscov-mpfr-1029", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::CdoubleMax, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:1029-1029 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1029-1029", status := .proven
    prop := ``Le1029, thm := some ``le1029_proven },
  { id := "bignumscov-mpfr-1033", juliaFile := "base/mpfr.jl"
    juliaFns := ["signbit(x::BigFloat)"]
    statement := "The signbit method at base/mpfr.jl:1033-1033 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1033-1033", status := .proven
    prop := ``Signbit1033, thm := some ``signbit1033_proven },
  { id := "bignumscov-mpfr-1035", juliaFile := "base/mpfr.jl"
    juliaFns := ["sign(x::BigFloat)"]
    statement := "The sign method at base/mpfr.jl:1035-1039 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1035-1039", status := .proven
    prop := ``Sign1035, thm := some ``sign1035_proven },
  { id := "bignumscov-mpfr-1041", juliaFile := "base/mpfr.jl"
    juliaFns := ["_precision_with_base_2(x::BigFloat)"]
    statement := "The _precision_with_base_2 method at base/mpfr.jl:1041-1043 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1041-1043", status := .proven
    prop := ``Precision1041, thm := some ``precision1041_proven },
  { id := "bignumscov-mpfr-1044", juliaFile := "base/mpfr.jl"
    juliaFns := ["precision(x::BigFloat; base::Integer=2)"]
    statement := "The precision method at base/mpfr.jl:1044-1044 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1044-1044", status := .proven
    prop := ``Precision1044, thm := some ``precision1044_proven },
  { id := "bignumscov-mpfr-1047", juliaFile := "base/mpfr.jl"
    juliaFns := ["_convert_precision_from_base(precision::Integer, base::Integer)"]
    statement := "The _convert_precision_from_base method at base/mpfr.jl:1047-1048 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1047-1048", status := .proven
    prop := ``ConvertPrecision1047, thm := some ``convertPrecision1047_proven },
  { id := "bignumscov-mpfr-1050", juliaFile := "base/mpfr.jl"
    juliaFns := ["_precision_with_base_2(::Type{BigFloat})"]
    statement := "The _precision_with_base_2 method at base/mpfr.jl:1050-1051 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1050-1051", status := .proven
    prop := ``TypePrecision1050, thm := some ``typePrecision1050_proven },
  { id := "bignumscov-mpfr-1069", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(::Type{BigFloat}, precision::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1069-1074 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1069-1074", status := .proven
    prop := ``Setprecision1069, thm := some ``setprecision1069_proven },
  { id := "bignumscov-mpfr-1076", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(precision::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1076-1076 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1076-1076", status := .proven
    prop := ``Setprecision1076, thm := some ``setprecision1076_proven },
  { id := "bignumscov-mpfr-1078", juliaFile := "base/mpfr.jl"
    juliaFns := ["maxintfloat(x::BigFloat)"]
    statement := "The maxintfloat method at base/mpfr.jl:1078-1078 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1078-1078", status := .proven
    prop := ``Maxint1078, thm := some ``maxint1078_proven },
  { id := "bignumscov-mpfr-1079", juliaFile := "base/mpfr.jl"
    juliaFns := ["maxintfloat(::Type{BigFloat})"]
    statement := "The maxintfloat method at base/mpfr.jl:1079-1079 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1079-1079", status := .proven
    prop := ``Maxint1079, thm := some ``maxint1079_proven },
  { id := "bignumscov-mpfr-1081", juliaFile := "base/mpfr.jl"
    juliaFns := ["copysign(x::BigFloat, y::BigFloat)"]
    statement := "The copysign method at base/mpfr.jl:1081-1085 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1081-1085", status := .proven
    prop := ``Copysign1081, thm := some ``copysign1081_proven },
  { id := "bignumscov-mpfr-1087", juliaFile := "base/mpfr.jl"
    juliaFns := ["exponent(x::BigFloat)"]
    statement := "The exponent method at base/mpfr.jl:1087-1093 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1087-1093", status := .proven
    prop := ``Exponent1087, thm := some ``exponent1087_proven },
  { id := "bignumscov-mpfr-1095", juliaFile := "base/mpfr.jl"
    juliaFns := ["frexp(x::BigFloat)"]
    statement := "The frexp method at base/mpfr.jl:1095-1100 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1095-1100", status := .proven
    prop := ``Frexp1095, thm := some ``frexp1095_proven },
  { id := "bignumscov-mpfr-1102", juliaFile := "base/mpfr.jl"
    juliaFns := ["significand(x::BigFloat)"]
    statement := "The significand method at base/mpfr.jl:1102-1109 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1102-1109", status := .proven
    prop := ``Significand1102, thm := some ``significand1102_proven },
  { id := "bignumscov-mpfr-1121", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(x::BigFloat, ::RoundingMode{$(QuoteNode(R))})"]
    statement := "The round method at base/mpfr.jl:1121-1125 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1121-1125", status := .proven
    prop := ``Round1121, thm := some ``round1121_proven },
  { id := "bignumscov-mpfr-1129", juliaFile := "base/mpfr.jl"
    juliaFns := ["isinf(x::BigFloat)"]
    statement := "The isinf method at base/mpfr.jl:1129-1131 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1129-1131", status := .proven
    prop := ``Isinf1129, thm := some ``isinf1129_proven },
  { id := "bignumscov-mpfr-1133", juliaFile := "base/mpfr.jl"
    juliaFns := ["isnan(x::BigFloat)"]
    statement := "The isnan method at base/mpfr.jl:1133-1135 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1133-1135", status := .proven
    prop := ``Isnan1133, thm := some ``isnan1133_proven },
  { id := "bignumscov-mpfr-1141", juliaFile := "base/mpfr.jl"
    juliaFns := ["iszero(x::BigFloat)"]
    statement := "The iszero method at base/mpfr.jl:1141-1141 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1141-1141", status := .proven
    prop := ``Iszero1141, thm := some ``iszero1141_proven },
  { id := "bignumscov-mpfr-1142", juliaFile := "base/mpfr.jl"
    juliaFns := ["isone(x::BigFloat)"]
    statement := "The isone method at base/mpfr.jl:1142-1142 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1142-1142", status := .proven
    prop := ``Isone1142, thm := some ``isone1142_proven },
  { id := "bignumscov-mpfr-1148", juliaFile := "base/mpfr.jl"
    juliaFns := ["typemax(::Type{BigFloat})"]
    statement := "The typemax method at base/mpfr.jl:1148-1148 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1148-1148", status := .proven
    prop := ``Typemax1148, thm := some ``typemax1148_proven },
  { id := "bignumscov-mpfr-1149", juliaFile := "base/mpfr.jl"
    juliaFns := ["typemin(::Type{BigFloat})"]
    statement := "The typemin method at base/mpfr.jl:1149-1149 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1149-1149", status := .proven
    prop := ``Typemin1149, thm := some ``typemin1149_proven },
  { id := "bignumscov-mpfr-1151", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat!(x::BigFloat, n::Integer=1)"]
    statement := "The nextfloat! method at base/mpfr.jl:1151-1157 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1151-1157", status := .proven
    prop := ``Nextfloat1151, thm := some ``nextfloat1151_proven },
  { id := "bignumscov-mpfr-1159", juliaFile := "base/mpfr.jl"
    juliaFns := ["prevfloat!(x::BigFloat, n::Integer=1)"]
    statement := "The prevfloat! method at base/mpfr.jl:1159-1165 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1159-1165", status := .proven
    prop := ``Prevfloat1159, thm := some ``prevfloat1159_proven },
  { id := "bignumscov-mpfr-1167", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat(x::BigFloat, n::Integer=1)"]
    statement := "The nextfloat method at base/mpfr.jl:1167-1167 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1167-1167", status := .proven
    prop := ``Nextfloat1167, thm := some ``nextfloat1167_proven },
  { id := "bignumscov-mpfr-1168", juliaFile := "base/mpfr.jl"
    juliaFns := ["prevfloat(x::BigFloat, n::Integer=1)"]
    statement := "The prevfloat method at base/mpfr.jl:1168-1168 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1168-1168", status := .proven
    prop := ``Prevfloat1168, thm := some ``prevfloat1168_proven },
  { id := "bignumscov-mpfr-1170", juliaFile := "base/mpfr.jl"
    juliaFns := ["eps(::Type{BigFloat})"]
    statement := "The eps method at base/mpfr.jl:1170-1170 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1170-1170", status := .proven
    prop := ``Eps1170, thm := some ``eps1170_proven },
  { id := "bignumscov-mpfr-1172", juliaFile := "base/mpfr.jl"
    juliaFns := ["floatmin(::Type{BigFloat})"]
    statement := "The floatmin method at base/mpfr.jl:1172-1172 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1172-1172", status := .proven
    prop := ``Floatmin1172, thm := some ``floatmin1172_proven },
  { id := "bignumscov-mpfr-1173", juliaFile := "base/mpfr.jl"
    juliaFns := ["floatmax(::Type{BigFloat})"]
    statement := "The floatmax method at base/mpfr.jl:1173-1173 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1173-1173", status := .proven
    prop := ``Floatmax1173, thm := some ``floatmax1173_proven },
  { id := "bignumscov-mpfr-1214", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f::Function, ::Type{BigFloat}, prec::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1214-1216 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1214-1216", status := .proven
    prop := ``Setprecision1214, thm := some ``setprecision1214_proven },
  { id := "bignumscov-mpfr-1217", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f, ::Type{Union{}}, slurp...; kwargs...)"]
    statement := "The setprecision method at base/mpfr.jl:1217-1217 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1217-1217", status := .proven
    prop := ``Setprecision1217, thm := some ``setprecision1217_proven },
  { id := "bignumscov-mpfr-1219", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f::Function, prec::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1219-1219 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1219-1219", status := .proven
    prop := ``Setprecision1219, thm := some ``setprecision1219_proven },
  { id := "bignumscov-mpfr-1221", juliaFile := "base/mpfr.jl"
    juliaFns := ["string_mpfr(x::BigFloat, fmt::String)"]
    statement := "The string_mpfr method at base/mpfr.jl:1221-1237 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1221-1237", status := .proven
    prop := ``StringMpfr1221, thm := some ``stringMpfr1221_proven },
  { id := "bignumscov-mpfr-1239", juliaFile := "base/mpfr.jl"
    juliaFns := ["_prettify_bigfloat(s::String)::String"]
    statement := "The _prettify_bigfloat method at base/mpfr.jl:1239-1265 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1239-1265", status := .proven
    prop := ``Prettify1239, thm := some ``prettify1239_proven },
  { id := "bignumscov-mpfr-1267", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat, fmt::String)::String"]
    statement := "The _string method at base/mpfr.jl:1267-1270 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1267-1270", status := .proven
    prop := ``String1267, thm := some ``string1267_proven },
  { id := "bignumscov-mpfr-1271", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat)"]
    statement := "The _string method at base/mpfr.jl:1271-1271 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1271-1271", status := .proven
    prop := ``String1271, thm := some ``string1271_proven },
  { id := "bignumscov-mpfr-1272", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat, k::Integer)"]
    statement := "The _string method at base/mpfr.jl:1272-1272 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1272-1272", status := .proven
    prop := ``String1272, thm := some ``string1272_proven },
  { id := "bignumscov-mpfr-1274", juliaFile := "base/mpfr.jl"
    juliaFns := ["string(b::BigFloat)"]
    statement := "The string method at base/mpfr.jl:1274-1274 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1274-1274", status := .proven
    prop := ``String1274, thm := some ``string1274_proven },
  { id := "bignumscov-mpfr-1276", juliaFile := "base/mpfr.jl"
    juliaFns := ["print(io::IO, b::BigFloat)"]
    statement := "The print method at base/mpfr.jl:1276-1276 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1276-1276", status := .proven
    prop := ``Print1276, thm := some ``print1276_proven },
  { id := "bignumscov-mpfr-1277", juliaFile := "base/mpfr.jl"
    juliaFns := ["show(io::IO, b::BigFloat)"]
    statement := "The show method at base/mpfr.jl:1277-1283 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1277-1283", status := .proven
    prop := ``Show1277, thm := some ``show1277_proven },
  { id := "bignumscov-mpfr-1295", juliaFile := "base/mpfr.jl"
    juliaFns := ["set_emax!(x)"]
    statement := "The set_emax! method at base/mpfr.jl:1295-1295 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1295-1295", status := .proven
    prop := ``SetEmax1295, thm := some ``setEmax1295_proven },
  { id := "bignumscov-mpfr-1296", juliaFile := "base/mpfr.jl"
    juliaFns := ["set_emin!(x)"]
    statement := "The set_emin! method at base/mpfr.jl:1296-1296 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1296-1296", status := .proven
    prop := ``SetEmin1296, thm := some ``setEmin1296_proven },
  { id := "bignumscov-mpfr-1298", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.deepcopy_internal(x::BigFloat, stackdict::IdDict)"]
    statement := "The Base.deepcopy_internal method at base/mpfr.jl:1298-1305 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1298-1305", status := .proven
    prop := ``Deepcopy1298, thm := some ``deepcopy1298_proven },
  { id := "bignumscov-mpfr-1307", juliaFile := "base/mpfr.jl"
    juliaFns := ["decompose(x::BigFloat)::Tuple{BigInt, Int, Int}"]
    statement := "The decompose method at base/mpfr.jl:1307-1318 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1307-1318", status := .proven
    prop := ``Decompose1307, thm := some ``decompose1307_proven },
  { id := "bignumscov-mpfr-1326", juliaFile := "base/mpfr.jl"
    juliaFns := ["clear_flags()"]
    statement := "The clear_flags method at base/mpfr.jl:1326-1326 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1326-1326", status := .proven
    prop := ``ClearFlags1326, thm := some ``clearFlags1326_proven },
  { id := "bignumscov-mpfr-1327", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_underflow()"]
    statement := "The had_underflow method at base/mpfr.jl:1327-1327 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1327-1327", status := .proven
    prop := ``HadUnderflow1327, thm := some ``hadUnderflow1327_proven },
  { id := "bignumscov-mpfr-1328", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_overflow()"]
    statement := "The had_overflow method at base/mpfr.jl:1328-1328 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1328-1328", status := .proven
    prop := ``HadOverflow1328, thm := some ``hadOverflow1328_proven },
  { id := "bignumscov-mpfr-1329", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_divbyzero()"]
    statement := "The had_divbyzero method at base/mpfr.jl:1329-1329 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1329-1329", status := .proven
    prop := ``HadDivzero1329, thm := some ``hadDivzero1329_proven },
  { id := "bignumscov-mpfr-1330", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_nan()"]
    statement := "The had_nan method at base/mpfr.jl:1330-1330 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1330-1330", status := .proven
    prop := ``HadNan1330, thm := some ``hadNan1330_proven },
  { id := "bignumscov-mpfr-1331", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_inexact_exception()"]
    statement := "The had_inexact_exception method at base/mpfr.jl:1331-1331 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1331-1331", status := .proven
    prop := ``HadInexact1331, thm := some ``hadInexact1331_proven },
  { id := "bignumscov-mpfr-1332", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_range_exception()"]
    statement := "The had_range_exception method at base/mpfr.jl:1332-1332 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1332-1332", status := .proven
    prop := ``HadRange1332, thm := some ``hadRange1332_proven }
]

end JuliaLean.BigNumsCov.MpfrFaithful
