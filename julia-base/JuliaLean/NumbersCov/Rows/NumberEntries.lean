import JuliaLean.NumbersCov.Rows.Number
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Number

open JuliaLean.Registry

/-- Row-specific registry entries for base/number.jl. -/
def entries : List Entry := [
  { id := "numberscov-number-s6", juliaFile := "base/number.jl"
    juliaFns := ["convert(::Type{T}, x::T) where {T<:Number}"]
    statement := "convert(::Type{T}, x::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:6; source equation and documented Number invariant"
    status := .proven, prop := ``P6, thm := some ``p6 },
  { id := "numberscov-number-s7", juliaFile := "base/number.jl"
    juliaFns := ["convert(::Type{T}, x::Number) where {T<:Number}"]
    statement := "convert(::Type{T}, x::Number) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:7; source equation and documented Number invariant"
    status := .proven, prop := ``P7, thm := some ``p7 },
  { id := "numberscov-number-s22", juliaFile := "base/number.jl"
    juliaFns := ["isinteger(x::Integer)"]
    statement := "isinteger(x::Integer) follows its Julia source body for every allowed input."
    source := "base/number.jl:22; source equation and documented Number invariant"
    status := .proven, prop := ``P22, thm := some ``p22 },
  { id := "numberscov-number-s84", juliaFile := "base/number.jl"
    juliaFns := ["isfinite(x::Number)"]
    statement := "isfinite(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:84; source equation and documented Number invariant"
    status := .proven, prop := ``P84, thm := some ``p84 },
  { id := "numberscov-number-s86", juliaFile := "base/number.jl"
    juliaFns := ["size(x::Number)"]
    statement := "size(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:86; source equation and documented Number invariant"
    status := .proven, prop := ``P86, thm := some ``p86 },
  { id := "numberscov-number-s87", juliaFile := "base/number.jl"
    juliaFns := ["size(x::Number, d::Integer)"]
    statement := "size(x::Number, d::Integer) follows its Julia source body for every allowed input."
    source := "base/number.jl:87; source equation and documented Number invariant"
    status := .proven, prop := ``P87, thm := some ``p87 },
  { id := "numberscov-number-s88", juliaFile := "base/number.jl"
    juliaFns := ["axes(x::Number)"]
    statement := "axes(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:88; source equation and documented Number invariant"
    status := .proven, prop := ``P88, thm := some ``p88 },
  { id := "numberscov-number-s89", juliaFile := "base/number.jl"
    juliaFns := ["axes(x::Number, d::Integer)"]
    statement := "axes(x::Number, d::Integer) follows its Julia source body for every allowed input."
    source := "base/number.jl:89; source equation and documented Number invariant"
    status := .proven, prop := ``P89, thm := some ``p89 },
  { id := "numberscov-number-s90", juliaFile := "base/number.jl"
    juliaFns := ["eltype(::Type{T}) where {T<:Number}"]
    statement := "eltype(::Type{T}) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:90; source equation and documented Number invariant"
    status := .proven, prop := ``P90, thm := some ``p90 },
  { id := "numberscov-number-s91", juliaFile := "base/number.jl"
    juliaFns := ["ndims(x::Number)"]
    statement := "ndims(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:91; source equation and documented Number invariant"
    status := .proven, prop := ``P91, thm := some ``p91 },
  { id := "numberscov-number-s92", juliaFile := "base/number.jl"
    juliaFns := ["ndims(::Type{<:Number})"]
    statement := "ndims(::Type{<:Number}) follows its Julia source body for every allowed input."
    source := "base/number.jl:92; source equation and documented Number invariant"
    status := .proven, prop := ``P92, thm := some ``p92 },
  { id := "numberscov-number-s93", juliaFile := "base/number.jl"
    juliaFns := ["length(x::Number)"]
    statement := "length(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:93; source equation and documented Number invariant"
    status := .proven, prop := ``P93, thm := some ``p93 },
  { id := "numberscov-number-s94", juliaFile := "base/number.jl"
    juliaFns := ["firstindex(x::Number)"]
    statement := "firstindex(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:94; source equation and documented Number invariant"
    status := .proven, prop := ``P94, thm := some ``p94 },
  { id := "numberscov-number-s95", juliaFile := "base/number.jl"
    juliaFns := ["firstindex(x::Number, d::Int)"]
    statement := "firstindex(x::Number, d::Int) follows its Julia source body for every allowed input."
    source := "base/number.jl:95; source equation and documented Number invariant"
    status := .proven, prop := ``P95, thm := some ``p95 },
  { id := "numberscov-number-s96", juliaFile := "base/number.jl"
    juliaFns := ["lastindex(x::Number)"]
    statement := "lastindex(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:96; source equation and documented Number invariant"
    status := .proven, prop := ``P96, thm := some ``p96 },
  { id := "numberscov-number-s97", juliaFile := "base/number.jl"
    juliaFns := ["lastindex(x::Number, d::Int)"]
    statement := "lastindex(x::Number, d::Int) follows its Julia source body for every allowed input."
    source := "base/number.jl:97; source equation and documented Number invariant"
    status := .proven, prop := ``P97, thm := some ``p97 },
  { id := "numberscov-number-s98", juliaFile := "base/number.jl"
    juliaFns := ["IteratorSize(::Type{<:Number})"]
    statement := "IteratorSize(::Type{<:Number}) follows its Julia source body for every allowed input."
    source := "base/number.jl:98; source equation and documented Number invariant"
    status := .proven, prop := ``P98, thm := some ``p98 },
  { id := "numberscov-number-s99", juliaFile := "base/number.jl"
    juliaFns := ["keys(::Number)"]
    statement := "keys(::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:99; source equation and documented Number invariant"
    status := .proven, prop := ``P99, thm := some ``p99 },
  { id := "numberscov-number-s101", juliaFile := "base/number.jl"
    juliaFns := ["getindex(x::Number)"]
    statement := "getindex(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:101; source equation and documented Number invariant"
    status := .proven, prop := ``P101, thm := some ``p101 },
  { id := "numberscov-number-s102", juliaFile := "base/number.jl"
    juliaFns := ["getindex(x::Number, i::Integer)"]
    statement := "getindex(x::Number, i::Integer) follows its Julia source body for every allowed input."
    source := "base/number.jl:102-106; source equation and documented Number invariant"
    status := .proven, prop := ``P102, thm := some ``p102 },
  { id := "numberscov-number-s107", juliaFile := "base/number.jl"
    juliaFns := ["getindex(x::Number, I::Integer...)"]
    statement := "getindex(x::Number, I::Integer...) follows its Julia source body for every allowed input."
    source := "base/number.jl:107-111; source equation and documented Number invariant"
    status := .proven, prop := ``P107, thm := some ``p107 },
  { id := "numberscov-number-s112", juliaFile := "base/number.jl"
    juliaFns := ["get(x::Number, i::Integer, default)"]
    statement := "get(x::Number, i::Integer, default) follows its Julia source body for every allowed input."
    source := "base/number.jl:112; source equation and documented Number invariant"
    status := .proven, prop := ``P112, thm := some ``p112 },
  { id := "numberscov-number-s113", juliaFile := "base/number.jl"
    juliaFns := ["get(x::Number, ind::Tuple, default)"]
    statement := "get(x::Number, ind::Tuple, default) follows its Julia source body for every allowed input."
    source := "base/number.jl:113; source equation and documented Number invariant"
    status := .proven, prop := ``P113, thm := some ``p113 },
  { id := "numberscov-number-s114", juliaFile := "base/number.jl"
    juliaFns := ["get(f::Callable, x::Number, i::Integer)"]
    statement := "get(f::Callable, x::Number, i::Integer) follows its Julia source body for every allowed input."
    source := "base/number.jl:114; source equation and documented Number invariant"
    status := .proven, prop := ``P114, thm := some ``p114 },
  { id := "numberscov-number-s115", juliaFile := "base/number.jl"
    juliaFns := ["get(f::Callable, x::Number, ind::Tuple)"]
    statement := "get(f::Callable, x::Number, ind::Tuple) follows its Julia source body for every allowed input."
    source := "base/number.jl:115; source equation and documented Number invariant"
    status := .proven, prop := ``P115, thm := some ``p115 },
  { id := "numberscov-number-s117", juliaFile := "base/number.jl"
    juliaFns := ["first(x::Number)"]
    statement := "first(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:117; source equation and documented Number invariant"
    status := .proven, prop := ``P117, thm := some ``p117 },
  { id := "numberscov-number-s118", juliaFile := "base/number.jl"
    juliaFns := ["last(x::Number)"]
    statement := "last(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:118; source equation and documented Number invariant"
    status := .proven, prop := ``P118, thm := some ``p118 },
  { id := "numberscov-number-s119", juliaFile := "base/number.jl"
    juliaFns := ["copy(x::Number)"]
    statement := "copy(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:119; source equation and documented Number invariant"
    status := .proven, prop := ``P119, thm := some ``p119 },
  { id := "numberscov-number-s165", juliaFile := "base/number.jl"
    juliaFns := ["ispositive(x::Real)"]
    statement := "ispositive(x::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:165; source equation and documented Number invariant"
    status := .proven, prop := ``P165, thm := some ``p165 },
  { id := "numberscov-number-s187", juliaFile := "base/number.jl"
    juliaFns := ["isnegative(x::Real)"]
    statement := "isnegative(x::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:187; source equation and documented Number invariant"
    status := .proven, prop := ``P187, thm := some ``p187 },
  { id := "numberscov-number-s211", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Number)"]
    statement := "sign(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:211; source equation and documented Number invariant"
    status := .proven, prop := ``P211, thm := some ``p211 },
  { id := "numberscov-number-s212", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Real)"]
    statement := "sign(x::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:212; source equation and documented Number invariant"
    status := .proven, prop := ``P212, thm := some ``p212 },
  { id := "numberscov-number-s213", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Unsigned)"]
    statement := "sign(x::Unsigned) follows its Julia source body for every allowed input."
    source := "base/number.jl:213; source equation and documented Number invariant"
    status := .proven, prop := ``P213, thm := some ``p213 },
  { id := "numberscov-number-s238", juliaFile := "base/number.jl"
    juliaFns := ["abs2(x::Number)"]
    statement := "abs2(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:238; source equation and documented Number invariant"
    status := .proven, prop := ``P238, thm := some ``p238 },
  { id := "numberscov-number-s239", juliaFile := "base/number.jl"
    juliaFns := ["abs2(x::Real)"]
    statement := "abs2(x::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:239; source equation and documented Number invariant"
    status := .proven, prop := ``P239, thm := some ``p239 },
  { id := "numberscov-number-s255", juliaFile := "base/number.jl"
    juliaFns := ["flipsign(x::Real, y::Real)"]
    statement := "flipsign(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:255; source equation and documented Number invariant"
    status := .proven, prop := ``P255, thm := some ``p255 },
  { id := "numberscov-number-s271", juliaFile := "base/number.jl"
    juliaFns := ["copysign(x::Real, y::Real)"]
    statement := "copysign(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:271; source equation and documented Number invariant"
    status := .proven, prop := ``P271, thm := some ``p271 },
  { id := "numberscov-number-s273", juliaFile := "base/number.jl"
    juliaFns := ["conj(x::Real)"]
    statement := "conj(x::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:273; source equation and documented Number invariant"
    status := .proven, prop := ``P273, thm := some ``p273 },
  { id := "numberscov-number-s274", juliaFile := "base/number.jl"
    juliaFns := ["transpose(x::Number)"]
    statement := "transpose(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:274; source equation and documented Number invariant"
    status := .proven, prop := ``P274, thm := some ``p274 },
  { id := "numberscov-number-s275", juliaFile := "base/number.jl"
    juliaFns := ["adjoint(x::Number)"]
    statement := "adjoint(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:275; source equation and documented Number invariant"
    status := .proven, prop := ``P275, thm := some ``p275 },
  { id := "numberscov-number-s276", juliaFile := "base/number.jl"
    juliaFns := ["angle(z::Real)"]
    statement := "angle(z::Real) follows its Julia source body for every allowed input."
    source := "base/number.jl:276; source equation and documented Number invariant"
    status := .proven, prop := ``P276, thm := some ``p276 },
  { id := "numberscov-number-s327", juliaFile := "base/number.jl"
    juliaFns := ["widemul(x::Number, y::Number)"]
    statement := "widemul(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:327; source equation and documented Number invariant"
    status := .proven, prop := ``P327, thm := some ``p327 },
  { id := "numberscov-number-s329", juliaFile := "base/number.jl"
    juliaFns := ["iterate(x::Number)"]
    statement := "iterate(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:329; source equation and documented Number invariant"
    status := .proven, prop := ``P329, thm := some ``p329 },
  { id := "numberscov-number-s330", juliaFile := "base/number.jl"
    juliaFns := ["iterate(x::Number, ::Any)"]
    statement := "iterate(x::Number, ::Any) follows its Julia source body for every allowed input."
    source := "base/number.jl:330; source equation and documented Number invariant"
    status := .proven, prop := ``P330, thm := some ``p330 },
  { id := "numberscov-number-s331", juliaFile := "base/number.jl"
    juliaFns := ["isempty(x::Number)"]
    statement := "isempty(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:331; source equation and documented Number invariant"
    status := .proven, prop := ``P331, thm := some ``p331 },
  { id := "numberscov-number-s332", juliaFile := "base/number.jl"
    juliaFns := ["in(x::Number, y::Number)"]
    statement := "in(x::Number, y::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:332; source equation and documented Number invariant"
    status := .proven, prop := ``P332, thm := some ``p332 },
  { id := "numberscov-number-s334", juliaFile := "base/number.jl"
    juliaFns := ["map(f, x::Number, ys::Number...)"]
    statement := "map(f, x::Number, ys::Number...) follows its Julia source body for every allowed input."
    source := "base/number.jl:334; source equation and documented Number invariant"
    status := .proven, prop := ``P334, thm := some ``p334 },
  { id := "numberscov-number-s363", juliaFile := "base/number.jl"
    juliaFns := ["zero(x::Number)"]
    statement := "zero(x::Number) follows its Julia source body for every allowed input."
    source := "base/number.jl:363; source equation and documented Number invariant"
    status := .proven, prop := ``P363, thm := some ``p363 },
  { id := "numberscov-number-s364", juliaFile := "base/number.jl"
    juliaFns := ["zero(::Type{T}) where {T<:Number}"]
    statement := "zero(::Type{T}) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:364; source equation and documented Number invariant"
    status := .proven, prop := ``P364, thm := some ``p364 },
  { id := "numberscov-number-s365", juliaFile := "base/number.jl"
    juliaFns := ["zero(::Type{Union{}}, slurp...)"]
    statement := "zero(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/number.jl:365; source equation and documented Number invariant"
    status := .proven, prop := ``P365, thm := some ``p365 },
  { id := "numberscov-number-s405", juliaFile := "base/number.jl"
    juliaFns := ["one(::Type{T}) where {T<:Number}"]
    statement := "one(::Type{T}) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:405; source equation and documented Number invariant"
    status := .proven, prop := ``P405, thm := some ``p405 },
  { id := "numberscov-number-s406", juliaFile := "base/number.jl"
    juliaFns := ["one(x::T) where {T<:Number}"]
    statement := "one(x::T) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:406; source equation and documented Number invariant"
    status := .proven, prop := ``P406, thm := some ``p406 },
  { id := "numberscov-number-s407", juliaFile := "base/number.jl"
    juliaFns := ["one(::Type{Union{}}, slurp...)"]
    statement := "one(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/number.jl:407; source equation and documented Number invariant"
    status := .proven, prop := ``P407, thm := some ``p407 },
  { id := "numberscov-number-s430", juliaFile := "base/number.jl"
    juliaFns := ["oneunit(x::T) where {T}"]
    statement := "oneunit(x::T) where {T} follows its Julia source body for every allowed input."
    source := "base/number.jl:430; source equation and documented Number invariant"
    status := .proven, prop := ``P430, thm := some ``p430 },
  { id := "numberscov-number-s431", juliaFile := "base/number.jl"
    juliaFns := ["oneunit(::Type{T}) where {T}"]
    statement := "oneunit(::Type{T}) where {T} follows its Julia source body for every allowed input."
    source := "base/number.jl:431; source equation and documented Number invariant"
    status := .proven, prop := ``P431, thm := some ``p431 },
  { id := "numberscov-number-s432", juliaFile := "base/number.jl"
    juliaFns := ["oneunit(::Type{Union{}}, slurp...)"]
    statement := "oneunit(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/number.jl:432; source equation and documented Number invariant"
    status := .proven, prop := ``P432, thm := some ``p432 },
  { id := "numberscov-number-s452", juliaFile := "base/number.jl"
    juliaFns := ["big(::Type{T}) where {T<:Number}"]
    statement := "big(::Type{T}) where {T<:Number} follows its Julia source body for every allowed input."
    source := "base/number.jl:452; source equation and documented Number invariant"
    status := .proven, prop := ``P452, thm := some ``p452 },
  { id := "numberscov-number-s453", juliaFile := "base/number.jl"
    juliaFns := ["big(::Type{Union{}}, slurp...)"]
    statement := "big(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/number.jl:453; source equation and documented Number invariant"
    status := .proven, prop := ``P453, thm := some ``p453 }
]

end JuliaLean.NumbersCov.Rows.Number
