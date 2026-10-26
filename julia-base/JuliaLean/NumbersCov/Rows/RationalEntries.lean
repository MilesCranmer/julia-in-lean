import JuliaLean.NumbersCov.Rows.Rational
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Rational
open JuliaLean.Registry

def entries : List Entry := [
  { id := "numberscov-rational-s14", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(::Type{T}, num, den) where {T}"]
    statement := "unsafe_rational(::Type{T}, num, den) where {T} follows its Julia source body for every allowed input."
    source := "base/rational.jl:14; source equation or documented Rational invariant"
    status := .proven, prop := ``P14, thm := some ``p14 },
  { id := "numberscov-rational-s17", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(num::T, den::T) where {T<:Integer}"]
    statement := "unsafe_rational(num::T, den::T) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:17; source equation or documented Rational invariant"
    status := .proven, prop := ``P17, thm := some ``p17 },
  { id := "numberscov-rational-s18", juliaFile := "base/rational.jl"
    juliaFns := ["unsafe_rational(num::Integer, den::Integer)"]
    statement := "unsafe_rational(num::Integer, den::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:18; source equation or documented Rational invariant"
    status := .proven, prop := ``P18, thm := some ``p18 },
  { id := "numberscov-rational-s20", juliaFile := "base/rational.jl"
    juliaFns := ["checked_den(::Type{T}, num::T, den::T) where T<:Integer"]
    statement := "checked_den(::Type{T}, num::T, den::T) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:20-26; source equation or documented Rational invariant"
    status := .proven, prop := ``P20, thm := some ``p20 },
  { id := "numberscov-rational-s27", juliaFile := "base/rational.jl"
    juliaFns := ["checked_den(num::T, den::T) where T<:Integer"]
    statement := "checked_den(num::T, den::T) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:27; source equation or documented Rational invariant"
    status := .proven, prop := ``P27, thm := some ``p27 },
  { id := "numberscov-rational-s28", juliaFile := "base/rational.jl"
    juliaFns := ["checked_den(num::Integer, den::Integer)"]
    statement := "checked_den(num::Integer, den::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:28; source equation or documented Rational invariant"
    status := .proven, prop := ``P28, thm := some ``p28 },
  { id := "numberscov-rational-s30", juliaFile := "base/rational.jl"
    juliaFns := ["__throw_rational_argerror_zero(T)"]
    statement := "__throw_rational_argerror_zero(T) follows its Julia source body for every allowed input."
    source := "base/rational.jl:30; source equation or documented Rational invariant"
    status := .proven, prop := ``P30, thm := some ``p30 },
  { id := "numberscov-rational-s48", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(n::T, d::T) where {T<:Integer}"]
    statement := "Rational(n::T, d::T) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:48; source equation or documented Rational invariant"
    status := .proven, prop := ``P48, thm := some ``p48 },
  { id := "numberscov-rational-s49", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(n::Integer, d::Integer)"]
    statement := "Rational(n::Integer, d::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:49; source equation or documented Rational invariant"
    status := .proven, prop := ``P49, thm := some ``p49 },
  { id := "numberscov-rational-s50", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(n::Integer)"]
    statement := "Rational(n::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:50; source equation or documented Rational invariant"
    status := .proven, prop := ``P50, thm := some ``p50 },
  { id := "numberscov-rational-s59", juliaFile := "base/rational.jl"
    juliaFns := ["divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}"]
    statement := "divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:59-62; source equation or documented Rational invariant"
    status := .proven, prop := ``P59, thm := some ``p59 },
  { id := "numberscov-rational-s91", juliaFile := "base/rational.jl"
    juliaFns := ["//(n::Integer, d::Integer)"]
    statement := "//(n::Integer, d::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:91; source equation or documented Rational invariant"
    status := .proven, prop := ``P91, thm := some ``p91 },
  { id := "numberscov-rational-s93", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Rational, y::Integer)"]
    statement := "//(x::Rational, y::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:93-101; source equation or documented Rational invariant"
    status := .proven, prop := ``P93, thm := some ``p93 },
  { id := "numberscov-rational-s102", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Integer, y::Rational)"]
    statement := "//(x::Integer, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:102-105; source equation or documented Rational invariant"
    status := .proven, prop := ``P102, thm := some ``p102 },
  { id := "numberscov-rational-s106", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Rational, y::Rational)"]
    statement := "//(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:106-114; source equation or documented Rational invariant"
    status := .proven, prop := ``P106, thm := some ``p106 },
  { id := "numberscov-rational-s116", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Complex, y::Real)"]
    statement := "//(x::Complex, y::Real) follows its Julia source body for every allowed input."
    source := "base/rational.jl:116; source equation or documented Rational invariant"
    status := .proven, prop := ``P116, thm := some ``p116 },
  { id := "numberscov-rational-s120", juliaFile := "base/rational.jl"
    juliaFns := ["_complex_exact_inv(y::Complex)"]
    statement := "_complex_exact_inv(y::Complex) follows its Julia source body for every allowed input."
    source := "base/rational.jl:120-128; source equation or documented Rational invariant"
    status := .proven, prop := ``P120, thm := some ``p120 },
  { id := "numberscov-rational-s129", juliaFile := "base/rational.jl"
    juliaFns := ["_complex_exact_inv(y::Complex{<:Integer})"]
    statement := "_complex_exact_inv(y::Complex{<:Integer}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:129-135; source equation or documented Rational invariant"
    status := .proven, prop := ``P129, thm := some ``p129 },
  { id := "numberscov-rational-s137", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Number, y::Complex)"]
    statement := "//(x::Number, y::Complex) follows its Julia source body for every allowed input."
    source := "base/rational.jl:137-140; source equation or documented Rational invariant"
    status := .proven, prop := ``P137, thm := some ``p137 },
  { id := "numberscov-rational-s141", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Integer, y::Complex{<:Integer})"]
    statement := "//(x::Integer, y::Complex{<:Integer}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:141-143; source equation or documented Rational invariant"
    status := .proven, prop := ``P141, thm := some ``p141 },
  { id := "numberscov-rational-s144", juliaFile := "base/rational.jl"
    juliaFns := ["//(x::Complex{<:Integer}, y::Complex{<:Integer})"]
    statement := "//(x::Complex{<:Integer}, y::Complex{<:Integer}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:144-152; source equation or documented Rational invariant"
    status := .proven, prop := ``P144, thm := some ``p144 },
  { id := "numberscov-rational-s154", juliaFile := "base/rational.jl"
    juliaFns := ["//(X::AbstractArray, y::Number)"]
    statement := "//(X::AbstractArray, y::Number) follows its Julia source body for every allowed input."
    source := "base/rational.jl:154; source equation or documented Rational invariant"
    status := .proven, prop := ``P154, thm := some ``p154 },
  { id := "numberscov-rational-s156", juliaFile := "base/rational.jl"
    juliaFns := ["show(io::IO, x::Rational)"]
    statement := "show(io::IO, x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:156-165; source equation or documented Rational invariant"
    status := .proven, prop := ``P156, thm := some ``p156 },
  { id := "numberscov-rational-s167", juliaFile := "base/rational.jl"
    juliaFns := ["read(s::IO, ::Type{Rational{T}}) where T<:Integer"]
    statement := "read(s::IO, ::Type{Rational{T}}) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:167-171; source equation or documented Rational invariant"
    status := .proven, prop := ``P167, thm := some ``p167 },
  { id := "numberscov-rational-s172", juliaFile := "base/rational.jl"
    juliaFns := ["write(s::IO, z::Rational)"]
    statement := "write(s::IO, z::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:172-174; source equation or documented Rational invariant"
    status := .proven, prop := ``P172, thm := some ``p172 },
  { id := "numberscov-rational-s175", juliaFile := "base/rational.jl"
    juliaFns := ["parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer"]
    statement := "parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:175-187; source equation or documented Rational invariant"
    status := .proven, prop := ``P175, thm := some ``p175 },
  { id := "numberscov-rational-s190", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(x::Rational) where T<:Integer"]
    statement := "Rational{T}(x::Rational) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:190-192; source equation or documented Rational invariant"
    status := .proven, prop := ``P190, thm := some ``p190 },
  { id := "numberscov-rational-s193", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(x::Integer) where T<:Integer"]
    statement := "Rational{T}(x::Integer) where T<:Integer follows its Julia source body for every allowed input."
    source := "base/rational.jl:193-195; source equation or documented Rational invariant"
    status := .proven, prop := ``P193, thm := some ``p193 },
  { id := "numberscov-rational-s197", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(x::Rational)"]
    statement := "Rational(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:197; source equation or documented Rational invariant"
    status := .proven, prop := ``P197, thm := some ``p197 },
  { id := "numberscov-rational-s199", juliaFile := "base/rational.jl"
    juliaFns := ["Bool(x::Rational)"]
    statement := "Bool(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:199-200; source equation or documented Rational invariant"
    status := .proven, prop := ``P199, thm := some ``p199 },
  { id := "numberscov-rational-s201", juliaFile := "base/rational.jl"
    juliaFns := ["(::Type{T})(x::Rational) where {T<:Integer}"]
    statement := "(::Type{T})(x::Rational) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:201-202; source equation or documented Rational invariant"
    status := .proven, prop := ``P201, thm := some ``p201 },
  { id := "numberscov-rational-s204", juliaFile := "base/rational.jl"
    juliaFns := ["AbstractFloat(x::Rational)"]
    statement := "AbstractFloat(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:204; source equation or documented Rational invariant"
    status := .proven, prop := ``P204, thm := some ``p204 },
  { id := "numberscov-rational-s205", juliaFile := "base/rational.jl"
    juliaFns := ["(::Type{T})(x::Rational{S}) where T<:AbstractFloat where S"]
    statement := "(::Type{T})(x::Rational{S}) where T<:AbstractFloat where S follows its Julia source body for every allowed input."
    source := "base/rational.jl:205-208; source equation or documented Rational invariant"
    status := .proven, prop := ``P205, thm := some ``p205 },
  { id := "numberscov-rational-s211", juliaFile := "base/rational.jl"
    juliaFns := ["Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}})"]
    statement := "Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:211-212; source equation or documented Rational invariant"
    status := .proven, prop := ``P211, thm := some ``p211 },
  { id := "numberscov-rational-s213", juliaFile := "base/rational.jl"
    juliaFns := ["Float16(x::Rational{<:Union{Int128,UInt128}})"]
    statement := "Float16(x::Rational{<:Union{Int128,UInt128}}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:213-214; source equation or documented Rational invariant"
    status := .proven, prop := ``P213, thm := some ``p213 },
  { id := "numberscov-rational-s223", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(x::Float64)"]
    statement := "Rational(x::Float64) follows its Julia source body for every allowed input."
    source := "base/rational.jl:223; source equation or documented Rational invariant"
    status := .proven, prop := ``P223, thm := some ``p223 },
  { id := "numberscov-rational-s224", juliaFile := "base/rational.jl"
    juliaFns := ["Rational(x::Float32)"]
    statement := "Rational(x::Float32) follows its Julia source body for every allowed input."
    source := "base/rational.jl:224; source equation or documented Rational invariant"
    status := .proven, prop := ``P224, thm := some ``p224 },
  { id := "numberscov-rational-s226", juliaFile := "base/rational.jl"
    juliaFns := ["big(q::Rational)"]
    statement := "big(q::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:226; source equation or documented Rational invariant"
    status := .proven, prop := ``P226, thm := some ``p226 },
  { id := "numberscov-rational-s228", juliaFile := "base/rational.jl"
    juliaFns := ["big(z::Complex{<:Rational{<:Integer}})"]
    statement := "big(z::Complex{<:Rational{<:Integer}}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:228; source equation or documented Rational invariant"
    status := .proven, prop := ``P228, thm := some ``p228 },
  { id := "numberscov-rational-s230", juliaFile := "base/rational.jl"
    juliaFns := ["promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer}"]
    statement := "promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:230; source equation or documented Rational invariant"
    status := .proven, prop := ``P230, thm := some ``p230 },
  { id := "numberscov-rational-s231", juliaFile := "base/rational.jl"
    juliaFns := ["promote_rule(::Type{Rational{T}}, ::Type{Rational{S}}) where {T<:Integer,S<:Integer}"]
    statement := "promote_rule(::Type{Rational{T}}, ::Type{Rational{S}}) where {T<:Integer,S<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:231; source equation or documented Rational invariant"
    status := .proven, prop := ``P231, thm := some ``p231 },
  { id := "numberscov-rational-s232", juliaFile := "base/rational.jl"
    juliaFns := ["promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat}"]
    statement := "promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat} follows its Julia source body for every allowed input."
    source := "base/rational.jl:232; source equation or documented Rational invariant"
    status := .proven, prop := ``P232, thm := some ``p232 },
  { id := "numberscov-rational-s234", juliaFile := "base/rational.jl"
    juliaFns := ["widen(::Type{Rational{T}}) where {T}"]
    statement := "widen(::Type{Rational{T}}) where {T} follows its Julia source body for every allowed input."
    source := "base/rational.jl:234; source equation or documented Rational invariant"
    status := .proven, prop := ``P234, thm := some ``p234 },
  { id := "numberscov-rational-s236", juliaFile := "base/rational.jl"
    juliaFns := ["__throw_negate_unsigned()"]
    statement := "__throw_negate_unsigned() follows its Julia source body for every allowed input."
    source := "base/rational.jl:236; source equation or documented Rational invariant"
    status := .proven, prop := ``P236, thm := some ``p236 },
  { id := "numberscov-rational-s321", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(x::Real; kvs...)"]
    statement := "rationalize(x::Real; kvs...) follows its Julia source body for every allowed input."
    source := "base/rational.jl:321; source equation or documented Rational invariant"
    status := .proven, prop := ``P321, thm := some ``p321 },
  { id := "numberscov-rational-s322", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer}"]
    statement := "rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:322; source equation or documented Rational invariant"
    status := .proven, prop := ``P322, thm := some ``p322 },
  { id := "numberscov-rational-s323", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(x::Complex; kvs...)"]
    statement := "rationalize(x::Complex; kvs...) follows its Julia source body for every allowed input."
    source := "base/rational.jl:323; source equation or documented Rational invariant"
    status := .proven, prop := ``P323, thm := some ``p323 },
  { id := "numberscov-rational-s324", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T}, x::Rational; tol::Real = eps(float(x))) where {T<:Integer}"]
    statement := "rationalize(::Type{T}, x::Rational; tol::Real = eps(float(x))) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:324; source equation or documented Rational invariant"
    status := .proven, prop := ``P324, thm := some ``p324 },
  { id := "numberscov-rational-s325", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(x::Rational{T}; kvs...) where {T<:Integer}"]
    statement := "rationalize(x::Rational{T}; kvs...) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:325; source equation or documented Rational invariant"
    status := .proven, prop := ``P325, thm := some ``p325 },
  { id := "numberscov-rational-s326", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer}"]
    statement := "rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:326-333; source equation or documented Rational invariant"
    status := .proven, prop := ``P326, thm := some ``p326 },
  { id := "numberscov-rational-s334", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(x::Integer; kvs...)"]
    statement := "rationalize(x::Integer; kvs...) follows its Julia source body for every allowed input."
    source := "base/rational.jl:334; source equation or documented Rational invariant"
    status := .proven, prop := ``P334, thm := some ``p334 },
  { id := "numberscov-rational-s343", juliaFile := "base/rational.jl"
    juliaFns := ["rationalize(::Type{Union{}}, slurp...; kwargs...)"]
    statement := "rationalize(::Type{Union{}}, slurp...; kwargs...) follows its Julia source body for every allowed input."
    source := "base/rational.jl:343; source equation or documented Rational invariant"
    status := .proven, prop := ``P343, thm := some ``p343 },
  { id := "numberscov-rational-s360", juliaFile := "base/rational.jl"
    juliaFns := ["numerator(x::Union{Integer,Complex{<:Integer}})"]
    statement := "numerator(x::Union{Integer,Complex{<:Integer}}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:360; source equation or documented Rational invariant"
    status := .proven, prop := ``P360, thm := some ``p360 },
  { id := "numberscov-rational-s361", juliaFile := "base/rational.jl"
    juliaFns := ["numerator(x::Rational)"]
    statement := "numerator(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:361; source equation or documented Rational invariant"
    status := .proven, prop := ``P361, thm := some ``p361 },
  { id := "numberscov-rational-s362", juliaFile := "base/rational.jl"
    juliaFns := ["numerator(z::Complex{<:Rational})"]
    statement := "numerator(z::Complex{<:Rational}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:362-367; source equation or documented Rational invariant"
    status := .proven, prop := ``P362, thm := some ``p362 },
  { id := "numberscov-rational-s383", juliaFile := "base/rational.jl"
    juliaFns := ["denominator(x::Union{Integer,Complex{<:Integer}})"]
    statement := "denominator(x::Union{Integer,Complex{<:Integer}}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:383; source equation or documented Rational invariant"
    status := .proven, prop := ``P383, thm := some ``p383 },
  { id := "numberscov-rational-s384", juliaFile := "base/rational.jl"
    juliaFns := ["denominator(x::Rational)"]
    statement := "denominator(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:384; source equation or documented Rational invariant"
    status := .proven, prop := ``P384, thm := some ``p384 },
  { id := "numberscov-rational-s385", juliaFile := "base/rational.jl"
    juliaFns := ["denominator(z::Complex{<:Rational})"]
    statement := "denominator(z::Complex{<:Rational}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:385; source equation or documented Rational invariant"
    status := .proven, prop := ``P385, thm := some ``p385 },
  { id := "numberscov-rational-s387", juliaFile := "base/rational.jl"
    juliaFns := ["sign(x::Rational)"]
    statement := "sign(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:387; source equation or documented Rational invariant"
    status := .proven, prop := ``P387, thm := some ``p387 },
  { id := "numberscov-rational-s388", juliaFile := "base/rational.jl"
    juliaFns := ["signbit(x::Rational)"]
    statement := "signbit(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:388; source equation or documented Rational invariant"
    status := .proven, prop := ``P388, thm := some ``p388 },
  { id := "numberscov-rational-s390", juliaFile := "base/rational.jl"
    juliaFns := ["abs(x::Rational)"]
    statement := "abs(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:390; source equation or documented Rational invariant"
    status := .proven, prop := ``P390, thm := some ``p390 },
  { id := "numberscov-rational-s392", juliaFile := "base/rational.jl"
    juliaFns := ["typemin(::Type{Rational{T}}) where {T<:Signed}"]
    statement := "typemin(::Type{Rational{T}}) where {T<:Signed} follows its Julia source body for every allowed input."
    source := "base/rational.jl:392; source equation or documented Rational invariant"
    status := .proven, prop := ``P392, thm := some ``p392 },
  { id := "numberscov-rational-s393", juliaFile := "base/rational.jl"
    juliaFns := ["typemin(::Type{Rational{T}}) where {T<:Integer}"]
    statement := "typemin(::Type{Rational{T}}) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:393; source equation or documented Rational invariant"
    status := .proven, prop := ``P393, thm := some ``p393 },
  { id := "numberscov-rational-s394", juliaFile := "base/rational.jl"
    juliaFns := ["typemax(::Type{Rational{T}}) where {T<:Integer}"]
    statement := "typemax(::Type{Rational{T}}) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:394; source equation or documented Rational invariant"
    status := .proven, prop := ``P394, thm := some ``p394 },
  { id := "numberscov-rational-s396", juliaFile := "base/rational.jl"
    juliaFns := ["isinteger(x::Rational)"]
    statement := "isinteger(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:396; source equation or documented Rational invariant"
    status := .proven, prop := ``P396, thm := some ``p396 },
  { id := "numberscov-rational-s397", juliaFile := "base/rational.jl"
    juliaFns := ["ispow2(x::Rational)"]
    statement := "ispow2(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:397; source equation or documented Rational invariant"
    status := .proven, prop := ``P397, thm := some ``p397 },
  { id := "numberscov-rational-s399", juliaFile := "base/rational.jl"
    juliaFns := ["+(x::Rational)"]
    statement := "+(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:399; source equation or documented Rational invariant"
    status := .proven, prop := ``P399, thm := some ``p399 },
  { id := "numberscov-rational-s400", juliaFile := "base/rational.jl"
    juliaFns := ["-(x::Rational)"]
    statement := "-(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:400; source equation or documented Rational invariant"
    status := .proven, prop := ``P400, thm := some ``p400 },
  { id := "numberscov-rational-s402", juliaFile := "base/rational.jl"
    juliaFns := ["-(x::Rational{T}) where T<:BitSigned"]
    statement := "-(x::Rational{T}) where T<:BitSigned follows its Julia source body for every allowed input."
    source := "base/rational.jl:402-405; source equation or documented Rational invariant"
    status := .proven, prop := ``P402, thm := some ``p402 },
  { id := "numberscov-rational-s406", juliaFile := "base/rational.jl"
    juliaFns := ["__throw_rational_numerator_typemin(T)"]
    statement := "__throw_rational_numerator_typemin(T) follows its Julia source body for every allowed input."
    source := "base/rational.jl:406; source equation or documented Rational invariant"
    status := .proven, prop := ``P406, thm := some ``p406 },
  { id := "numberscov-rational-s408", juliaFile := "base/rational.jl"
    juliaFns := ["-(x::Rational{T}) where T<:Unsigned"]
    statement := "-(x::Rational{T}) where T<:Unsigned follows its Julia source body for every allowed input."
    source := "base/rational.jl:408-411; source equation or documented Rational invariant"
    status := .proven, prop := ``P408, thm := some ``p408 },
  { id := "numberscov-rational-s413", juliaFile := "base/rational.jl"
    juliaFns := ["-%(x::Rational)"]
    statement := "-%(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:413; source equation or documented Rational invariant"
    status := .proven, prop := ``P413, thm := some ``p413 },
  { id := "numberscov-rational-s424", juliaFile := "base/rational.jl"
    juliaFns := ["+%(x::Rational, y::Rational)"]
    statement := "+%(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:424-431; source equation or documented Rational invariant"
    status := .proven, prop := ``P424, thm := some ``p424 },
  { id := "numberscov-rational-s442", juliaFile := "base/rational.jl"
    juliaFns := ["-%(x::Rational, y::Rational)"]
    statement := "-%(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:442-449; source equation or documented Rational invariant"
    status := .proven, prop := ``P442, thm := some ``p442 },
  { id := "numberscov-rational-s453", juliaFile := "base/rational.jl"
    juliaFns := ["($op)(x::Rational, y::Rational)"]
    statement := "($op)(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:453-456; source equation or documented Rational invariant"
    status := .proven, prop := ``P453, thm := some ``p453 },
  { id := "numberscov-rational-s462", juliaFile := "base/rational.jl"
    juliaFns := ["($op)(x::Rational, y::Integer)"]
    statement := "($op)(x::Rational, y::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:462-464; source equation or documented Rational invariant"
    status := .proven, prop := ``P462, thm := some ``p462 },
  { id := "numberscov-rational-s469", juliaFile := "base/rational.jl"
    juliaFns := ["($op)(y::Integer, x::Rational)"]
    statement := "($op)(y::Integer, x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:469-471; source equation or documented Rational invariant"
    status := .proven, prop := ``P469, thm := some ``p469 },
  { id := "numberscov-rational-s476", juliaFile := "base/rational.jl"
    juliaFns := ["($op)(y::Integer, x::Rational)"]
    statement := "($op)(y::Integer, x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:476-478; source equation or documented Rational invariant"
    status := .proven, prop := ``P476, thm := some ``p476 },
  { id := "numberscov-rational-s482", juliaFile := "base/rational.jl"
    juliaFns := ["*(x::Rational, y::Rational)"]
    statement := "*(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:482-486; source equation or documented Rational invariant"
    status := .proven, prop := ``P482, thm := some ``p482 },
  { id := "numberscov-rational-s487", juliaFile := "base/rational.jl"
    juliaFns := ["*(x::Rational, y::Integer)"]
    statement := "*(x::Rational, y::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:487-490; source equation or documented Rational invariant"
    status := .proven, prop := ``P487, thm := some ``p487 },
  { id := "numberscov-rational-s491", juliaFile := "base/rational.jl"
    juliaFns := ["*(y::Integer, x::Rational)"]
    statement := "*(y::Integer, x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:491-494; source equation or documented Rational invariant"
    status := .proven, prop := ``P491, thm := some ``p491 },
  { id := "numberscov-rational-s497", juliaFile := "base/rational.jl"
    juliaFns := ["*(x::Bool, y::T)::promote_type(Bool,T) where T<:Rational"]
    statement := "*(x::Bool, y::T)::promote_type(Bool,T) where T<:Rational follows its Julia source body for every allowed input."
    source := "base/rational.jl:497-499; source equation or documented Rational invariant"
    status := .proven, prop := ``P497, thm := some ``p497 },
  { id := "numberscov-rational-s500", juliaFile := "base/rational.jl"
    juliaFns := ["*(y::Rational, x::Bool)"]
    statement := "*(y::Rational, x::Bool) follows its Julia source body for every allowed input."
    source := "base/rational.jl:500; source equation or documented Rational invariant"
    status := .proven, prop := ``P500, thm := some ``p500 },
  { id := "numberscov-rational-s501", juliaFile := "base/rational.jl"
    juliaFns := ["/(x::Rational, y::Union{Rational, Integer})"]
    statement := "/(x::Rational, y::Union{Rational, Integer}) follows its Julia source body for every allowed input."
    source := "base/rational.jl:501; source equation or documented Rational invariant"
    status := .proven, prop := ``P501, thm := some ``p501 },
  { id := "numberscov-rational-s502", juliaFile := "base/rational.jl"
    juliaFns := ["/(x::Integer, y::Rational)"]
    statement := "/(x::Integer, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:502; source equation or documented Rational invariant"
    status := .proven, prop := ``P502, thm := some ``p502 },
  { id := "numberscov-rational-s503", juliaFile := "base/rational.jl"
    juliaFns := ["inv(x::Rational{T}) where {T}"]
    statement := "inv(x::Rational{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/rational.jl:503; source equation or documented Rational invariant"
    status := .proven, prop := ``P503, thm := some ``p503 },
  { id := "numberscov-rational-s505", juliaFile := "base/rational.jl"
    juliaFns := ["fma(x::Rational, y::Rational, z::Rational)"]
    statement := "fma(x::Rational, y::Rational, z::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:505; source equation or documented Rational invariant"
    status := .proven, prop := ``P505, thm := some ``p505 },
  { id := "numberscov-rational-s507", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::Rational, y::Rational)"]
    statement := "==(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:507; source equation or documented Rational invariant"
    status := .proven, prop := ``P507, thm := some ``p507 },
  { id := "numberscov-rational-s508", juliaFile := "base/rational.jl"
    juliaFns := ["<( x::Rational, y::Rational)"]
    statement := "<( x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:508-509; source equation or documented Rational invariant"
    status := .proven, prop := ``P508, thm := some ``p508 },
  { id := "numberscov-rational-s510", juliaFile := "base/rational.jl"
    juliaFns := ["<=(x::Rational, y::Rational)"]
    statement := "<=(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:510-511; source equation or documented Rational invariant"
    status := .proven, prop := ``P510, thm := some ``p510 },
  { id := "numberscov-rational-s514", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::Rational, y::Integer )"]
    statement := "==(x::Rational, y::Integer ) follows its Julia source body for every allowed input."
    source := "base/rational.jl:514; source equation or documented Rational invariant"
    status := .proven, prop := ``P514, thm := some ``p514 },
  { id := "numberscov-rational-s515", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::Integer , y::Rational)"]
    statement := "==(x::Integer , y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:515; source equation or documented Rational invariant"
    status := .proven, prop := ``P515, thm := some ``p515 },
  { id := "numberscov-rational-s516", juliaFile := "base/rational.jl"
    juliaFns := ["<( x::Rational, y::Integer )"]
    statement := "<( x::Rational, y::Integer ) follows its Julia source body for every allowed input."
    source := "base/rational.jl:516; source equation or documented Rational invariant"
    status := .proven, prop := ``P516, thm := some ``p516 },
  { id := "numberscov-rational-s517", juliaFile := "base/rational.jl"
    juliaFns := ["<( x::Integer , y::Rational)"]
    statement := "<( x::Integer , y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:517; source equation or documented Rational invariant"
    status := .proven, prop := ``P517, thm := some ``p517 },
  { id := "numberscov-rational-s518", juliaFile := "base/rational.jl"
    juliaFns := ["<=(x::Rational, y::Integer )"]
    statement := "<=(x::Rational, y::Integer ) follows its Julia source body for every allowed input."
    source := "base/rational.jl:518; source equation or documented Rational invariant"
    status := .proven, prop := ``P518, thm := some ``p518 },
  { id := "numberscov-rational-s519", juliaFile := "base/rational.jl"
    juliaFns := ["<=(x::Integer , y::Rational)"]
    statement := "<=(x::Integer , y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:519; source equation or documented Rational invariant"
    status := .proven, prop := ``P519, thm := some ``p519 },
  { id := "numberscov-rational-s521", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::AbstractFloat, q::Rational)"]
    statement := "==(x::AbstractFloat, q::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:521-527; source equation or documented Rational invariant"
    status := .proven, prop := ``P521, thm := some ``p521 },
  { id := "numberscov-rational-s529", juliaFile := "base/rational.jl"
    juliaFns := ["==(q::Rational, x::AbstractFloat)"]
    statement := "==(q::Rational, x::AbstractFloat) follows its Julia source body for every allowed input."
    source := "base/rational.jl:529; source equation or documented Rational invariant"
    status := .proven, prop := ``P529, thm := some ``p529 },
  { id := "numberscov-rational-s533", juliaFile := "base/rational.jl"
    juliaFns := ["($rel)(x::$Tx, y::$Ty)"]
    statement := "($rel)(x::$Tx, y::$Ty) follows its Julia source body for every allowed input."
    source := "base/rational.jl:533-578; source equation or documented Rational invariant"
    status := .proven, prop := ``P533, thm := some ``p533 },
  { id := "numberscov-rational-s583", juliaFile := "base/rational.jl"
    juliaFns := ["==(z::Complex , x::Rational)"]
    statement := "==(z::Complex , x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:583; source equation or documented Rational invariant"
    status := .proven, prop := ``P583, thm := some ``p583 },
  { id := "numberscov-rational-s584", juliaFile := "base/rational.jl"
    juliaFns := ["==(x::Rational, z::Complex )"]
    statement := "==(x::Rational, z::Complex ) follows its Julia source body for every allowed input."
    source := "base/rational.jl:584; source equation or documented Rational invariant"
    status := .proven, prop := ``P584, thm := some ``p584 },
  { id := "numberscov-rational-s586", juliaFile := "base/rational.jl"
    juliaFns := ["div(x::Rational, y::Integer, r::RoundingMode)"]
    statement := "div(x::Rational, y::Integer, r::RoundingMode) follows its Julia source body for every allowed input."
    source := "base/rational.jl:586-589; source equation or documented Rational invariant"
    status := .proven, prop := ``P586, thm := some ``p586 },
  { id := "numberscov-rational-s590", juliaFile := "base/rational.jl"
    juliaFns := ["div(x::Integer, y::Rational, r::RoundingMode)"]
    statement := "div(x::Integer, y::Rational, r::RoundingMode) follows its Julia source body for every allowed input."
    source := "base/rational.jl:590-593; source equation or documented Rational invariant"
    status := .proven, prop := ``P590, thm := some ``p590 },
  { id := "numberscov-rational-s594", juliaFile := "base/rational.jl"
    juliaFns := ["div(x::Rational, y::Rational, r::RoundingMode)"]
    statement := "div(x::Rational, y::Rational, r::RoundingMode) follows its Julia source body for every allowed input."
    source := "base/rational.jl:594-598; source equation or documented Rational invariant"
    status := .proven, prop := ``P594, thm := some ``p594 },
  { id := "numberscov-rational-s602", juliaFile := "base/rational.jl"
    juliaFns := ["div(x::T, y::T, r::RoundingMode) where {T<:Rational}"]
    statement := "div(x::T, y::T, r::RoundingMode) where {T<:Rational} follows its Julia source body for every allowed input."
    source := "base/rational.jl:602-603; source equation or documented Rational invariant"
    status := .proven, prop := ``P602, thm := some ``p602 },
  { id := "numberscov-rational-s606", juliaFile := "base/rational.jl"
    juliaFns := ["div(x::$S, y::$T)"]
    statement := "div(x::$S, y::$T) follows its Julia source body for every allowed input."
    source := "base/rational.jl:606; source equation or documented Rational invariant"
    status := .proven, prop := ``P606, thm := some ``p606 },
  { id := "numberscov-rational-s607", juliaFile := "base/rational.jl"
    juliaFns := ["fld(x::$S, y::$T)"]
    statement := "fld(x::$S, y::$T) follows its Julia source body for every allowed input."
    source := "base/rational.jl:607; source equation or documented Rational invariant"
    status := .proven, prop := ``P607, thm := some ``p607 },
  { id := "numberscov-rational-s608", juliaFile := "base/rational.jl"
    juliaFns := ["cld(x::$S, y::$T)"]
    statement := "cld(x::$S, y::$T) follows its Julia source body for every allowed input."
    source := "base/rational.jl:608; source equation or documented Rational invariant"
    status := .proven, prop := ``P608, thm := some ``p608 },
  { id := "numberscov-rational-s612", juliaFile := "base/rational.jl"
    juliaFns := ["round(x::Rational, r::RoundingMode=RoundNearest)"]
    statement := "round(x::Rational, r::RoundingMode=RoundNearest) follows its Julia source body for every allowed input."
    source := "base/rational.jl:612; source equation or documented Rational invariant"
    status := .proven, prop := ``P612, thm := some ``p612 },
  { id := "numberscov-rational-s614", juliaFile := "base/rational.jl"
    juliaFns := ["round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T,Tr}"]
    statement := "round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T,Tr} follows its Julia source body for every allowed input."
    source := "base/rational.jl:614-619; source equation or documented Rational invariant"
    status := .proven, prop := ``P614, thm := some ``p614 },
  { id := "numberscov-rational-s621", juliaFile := "base/rational.jl"
    juliaFns := ["round(::Type{T}, x::Rational{Bool}, ::RoundingMode=RoundNearest) where T"]
    statement := "round(::Type{T}, x::Rational{Bool}, ::RoundingMode=RoundNearest) where T follows its Julia source body for every allowed input."
    source := "base/rational.jl:621-626; source equation or documented Rational invariant"
    status := .proven, prop := ``P621, thm := some ``p621 },
  { id := "numberscov-rational-s628", juliaFile := "base/rational.jl"
    juliaFns := ["^(x::Rational, n::Integer)"]
    statement := "^(x::Rational, n::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:628-630; source equation or documented Rational invariant"
    status := .proven, prop := ``P628, thm := some ``p628 },
  { id := "numberscov-rational-s632", juliaFile := "base/rational.jl"
    juliaFns := ["^(x::Number, y::Rational)"]
    statement := "^(x::Number, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:632; source equation or documented Rational invariant"
    status := .proven, prop := ``P632, thm := some ``p632 },
  { id := "numberscov-rational-s633", juliaFile := "base/rational.jl"
    juliaFns := ["^(x::T, y::Rational) where {T<:AbstractFloat}"]
    statement := "^(x::T, y::Rational) where {T<:AbstractFloat} follows its Julia source body for every allowed input."
    source := "base/rational.jl:633; source equation or documented Rational invariant"
    status := .proven, prop := ``P633, thm := some ``p633 },
  { id := "numberscov-rational-s634", juliaFile := "base/rational.jl"
    juliaFns := ["^(z::Complex{T}, p::Rational) where {T<:Real}"]
    statement := "^(z::Complex{T}, p::Rational) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/rational.jl:634; source equation or documented Rational invariant"
    status := .proven, prop := ``P634, thm := some ``p634 },
  { id := "numberscov-rational-s636", juliaFile := "base/rational.jl"
    juliaFns := ["^(z::Complex{<:Rational}, n::Bool)"]
    statement := "^(z::Complex{<:Rational}, n::Bool) follows its Julia source body for every allowed input."
    source := "base/rational.jl:636; source equation or documented Rational invariant"
    status := .proven, prop := ``P636, thm := some ``p636 },
  { id := "numberscov-rational-s637", juliaFile := "base/rational.jl"
    juliaFns := ["^(z::Complex{<:Rational}, n::Integer)"]
    statement := "^(z::Complex{<:Rational}, n::Integer) follows its Julia source body for every allowed input."
    source := "base/rational.jl:637-639; source equation or documented Rational invariant"
    status := .proven, prop := ``P637, thm := some ``p637 },
  { id := "numberscov-rational-s641", juliaFile := "base/rational.jl"
    juliaFns := ["iszero(x::Rational)"]
    statement := "iszero(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:641; source equation or documented Rational invariant"
    status := .proven, prop := ``P641, thm := some ``p641 },
  { id := "numberscov-rational-s642", juliaFile := "base/rational.jl"
    juliaFns := ["isone(x::Rational)"]
    statement := "isone(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:642; source equation or documented Rational invariant"
    status := .proven, prop := ``P642, thm := some ``p642 },
  { id := "numberscov-rational-s644", juliaFile := "base/rational.jl"
    juliaFns := ["lerpi(j::Integer, d::Integer, a::Rational, b::Rational)"]
    statement := "lerpi(j::Integer, d::Integer, a::Rational, b::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:644-646; source equation or documented Rational invariant"
    status := .proven, prop := ``P644, thm := some ``p644 },
  { id := "numberscov-rational-s648", juliaFile := "base/rational.jl"
    juliaFns := ["float(::Type{Rational{T}}) where {T<:Integer}"]
    statement := "float(::Type{Rational{T}}) where {T<:Integer} follows its Julia source body for every allowed input."
    source := "base/rational.jl:648; source equation or documented Rational invariant"
    status := .proven, prop := ``P648, thm := some ``p648 },
  { id := "numberscov-rational-s650", juliaFile := "base/rational.jl"
    juliaFns := ["gcd(x::Rational, y::Rational)"]
    statement := "gcd(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:650-655; source equation or documented Rational invariant"
    status := .proven, prop := ``P650, thm := some ``p650 },
  { id := "numberscov-rational-s656", juliaFile := "base/rational.jl"
    juliaFns := ["lcm(x::Rational, y::Rational)"]
    statement := "lcm(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:656-661; source equation or documented Rational invariant"
    status := .proven, prop := ``P656, thm := some ``p656 },
  { id := "numberscov-rational-s662", juliaFile := "base/rational.jl"
    juliaFns := ["gcdx(x::Rational, y::Rational)"]
    statement := "gcdx(x::Rational, y::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:662-674; source equation or documented Rational invariant"
    status := .proven, prop := ``P662, thm := some ``p662 },
  { id := "numberscov-rational-s670", juliaFile := "base/rational.jl"
    juliaFns := ["idiv(x, c)"]
    statement := "idiv(x, c) follows its Julia source body for every allowed input."
    source := "base/rational.jl:670; source equation or documented Rational invariant"
    status := .proven, prop := ``P670, thm := some ``p670 },
  { id := "numberscov-rational-s678", juliaFile := "base/rational.jl"
    juliaFns := ["decompose(x::Rational)"]
    statement := "decompose(x::Rational) follows its Julia source body for every allowed input."
    source := "base/rational.jl:678; source equation or documented Rational invariant"
    status := .proven, prop := ``P678, thm := some ``p678 },
  { id := "numberscov-rational-s679", juliaFile := "base/rational.jl"
    juliaFns := ["hash(x::Rational{<:BitInteger64}, h::UInt)"]
    statement := "hash(x::Rational{<:BitInteger64}, h::UInt) follows its Julia source body for every allowed input."
    source := "base/rational.jl:679-702; source equation or documented Rational invariant"
    status := .proven, prop := ``P679, thm := some ``p679 },
  { id := "numberscov-rational-s707", juliaFile := "base/rational.jl"
    juliaFns := ["length(r::AbstractUnitRange{T}) where T<:Rational"]
    statement := "length(r::AbstractUnitRange{T}) where T<:Rational follows its Julia source body for every allowed input."
    source := "base/rational.jl:707-712; source equation or documented Rational invariant"
    status := .proven, prop := ``P707, thm := some ``p707 },
  { id := "numberscov-rational-s713", juliaFile := "base/rational.jl"
    juliaFns := ["checked_length(r::AbstractUnitRange{T}) where T<:Rational"]
    statement := "checked_length(r::AbstractUnitRange{T}) where T<:Rational follows its Julia source body for every allowed input."
    source := "base/rational.jl:713-720; source equation or documented Rational invariant"
    status := .proven, prop := ``P713, thm := some ``p713 }
]

end JuliaLean.NumbersCov.Rows.Rational
