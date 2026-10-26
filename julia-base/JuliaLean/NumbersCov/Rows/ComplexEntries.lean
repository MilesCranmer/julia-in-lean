import JuliaLean.NumbersCov.Rows.ComplexAnalytic
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Complex
open JuliaLean.Registry

def entries : List Entry := [
  { id := "numberscov-complex-s17", juliaFile := "base/complex.jl"
    juliaFns := ["Complex(x::Real, y::Real)"]
    statement := "Complex(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:17; source equation or documented Complex invariant"
    status := .proven, prop := ``P17, thm := some ``p17 },
  { id := "numberscov-complex-s18", juliaFile := "base/complex.jl"
    juliaFns := ["Complex(x::Real)"]
    statement := "Complex(x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:18; source equation or documented Complex invariant"
    status := .proven, prop := ``P18, thm := some ``p18 },
  { id := "numberscov-complex-s42", juliaFile := "base/complex.jl"
    juliaFns := ["Complex{T}(x::Real) where {T<:Real}"]
    statement := "Complex{T}(x::Real) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:42; source equation or documented Complex invariant"
    status := .proven, prop := ``P42, thm := some ``p42 },
  { id := "numberscov-complex-s43", juliaFile := "base/complex.jl"
    juliaFns := ["Complex{T}(z::Complex) where {T<:Real}"]
    statement := "Complex{T}(z::Complex) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:43; source equation or documented Complex invariant"
    status := .proven, prop := ``P43, thm := some ``p43 },
  { id := "numberscov-complex-s44", juliaFile := "base/complex.jl"
    juliaFns := ["(::Type{T})(z::Complex) where {T<:Real}"]
    statement := "(::Type{T})(z::Complex) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:44-45; source equation or documented Complex invariant"
    status := .proven, prop := ``P44, thm := some ``p44 },
  { id := "numberscov-complex-s47", juliaFile := "base/complex.jl"
    juliaFns := ["Complex(z::Complex)"]
    statement := "Complex(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:47; source equation or documented Complex invariant"
    status := .proven, prop := ``P47, thm := some ``p47 },
  { id := "numberscov-complex-s49", juliaFile := "base/complex.jl"
    juliaFns := ["promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real}"]
    statement := "promote_rule(::Type{Complex{T}}, ::Type{S}) where {T<:Real,S<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:49-50; source equation or documented Complex invariant"
    status := .proven, prop := ``P49, thm := some ``p49 },
  { id := "numberscov-complex-s51", juliaFile := "base/complex.jl"
    juliaFns := ["promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real}"]
    statement := "promote_rule(::Type{Complex{T}}, ::Type{Complex{S}}) where {T<:Real,S<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:51-52; source equation or documented Complex invariant"
    status := .proven, prop := ``P51, thm := some ``p51 },
  { id := "numberscov-complex-s54", juliaFile := "base/complex.jl"
    juliaFns := ["widen(::Type{Complex{T}}) where {T}"]
    statement := "widen(::Type{Complex{T}}) where {T} follows its Julia source body for every allowed input."
    source := "base/complex.jl:54; source equation or documented Complex invariant"
    status := .proven, prop := ``P54, thm := some ``p54 },
  { id := "numberscov-complex-s56", juliaFile := "base/complex.jl"
    juliaFns := ["float(::Type{Complex{T}}) where {T<:AbstractFloat}"]
    statement := "float(::Type{Complex{T}}) where {T<:AbstractFloat} follows its Julia source body for every allowed input."
    source := "base/complex.jl:56; source equation or documented Complex invariant"
    status := .proven, prop := ``P56, thm := some ``p56 },
  { id := "numberscov-complex-s57", juliaFile := "base/complex.jl"
    juliaFns := ["float(::Type{Complex{T}}) where {T}"]
    statement := "float(::Type{Complex{T}}) where {T} follows its Julia source body for every allowed input."
    source := "base/complex.jl:57; source equation or documented Complex invariant"
    status := .proven, prop := ``P57, thm := some ``p57 },
  { id := "numberscov-complex-s72", juliaFile := "base/complex.jl"
    juliaFns := ["real(z::Complex)"]
    statement := "real(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:72; source equation or documented Complex invariant"
    status := .proven, prop := ``P72, thm := some ``p72 },
  { id := "numberscov-complex-s87", juliaFile := "base/complex.jl"
    juliaFns := ["imag(z::Complex)"]
    statement := "imag(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:87; source equation or documented Complex invariant"
    status := .proven, prop := ``P87, thm := some ``p87 },
  { id := "numberscov-complex-s88", juliaFile := "base/complex.jl"
    juliaFns := ["real(x::Real)"]
    statement := "real(x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:88; source equation or documented Complex invariant"
    status := .proven, prop := ``P88, thm := some ``p88 },
  { id := "numberscov-complex-s89", juliaFile := "base/complex.jl"
    juliaFns := ["imag(x::Real)"]
    statement := "imag(x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:89; source equation or documented Complex invariant"
    status := .proven, prop := ``P89, thm := some ``p89 },
  { id := "numberscov-complex-s102", juliaFile := "base/complex.jl"
    juliaFns := ["reim(z)"]
    statement := "reim(z) follows its Julia source body for every allowed input."
    source := "base/complex.jl:102; source equation or documented Complex invariant"
    status := .proven, prop := ``P102, thm := some ``p102 },
  { id := "numberscov-complex-s120", juliaFile := "base/complex.jl"
    juliaFns := ["real(T::Type)"]
    statement := "real(T::Type) follows its Julia source body for every allowed input."
    source := "base/complex.jl:120; source equation or documented Complex invariant"
    status := .proven, prop := ``P120, thm := some ``p120 },
  { id := "numberscov-complex-s121", juliaFile := "base/complex.jl"
    juliaFns := ["real(::Type{T}) where {T<:Real}"]
    statement := "real(::Type{T}) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:121; source equation or documented Complex invariant"
    status := .proven, prop := ``P121, thm := some ``p121 },
  { id := "numberscov-complex-s122", juliaFile := "base/complex.jl"
    juliaFns := ["real(C::Type{<:Complex})"]
    statement := "real(C::Type{<:Complex}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:122; source equation or documented Complex invariant"
    status := .proven, prop := ``P122, thm := some ``p122 },
  { id := "numberscov-complex-s123", juliaFile := "base/complex.jl"
    juliaFns := ["real(::Type{Union{}})"]
    statement := "real(::Type{Union{}}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:123; source equation or documented Complex invariant"
    status := .proven, prop := ``P123, thm := some ``p123 },
  { id := "numberscov-complex-s124", juliaFile := "base/complex.jl"
    juliaFns := ["real(::Type{Union{}}, slurp...)"]
    statement := "real(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/complex.jl:124; source equation or documented Complex invariant"
    status := .proven, prop := ``P124, thm := some ``p124 },
  { id := "numberscov-complex-s148", juliaFile := "base/complex.jl"
    juliaFns := ["isreal(x::Real)"]
    statement := "isreal(x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:148; source equation or documented Complex invariant"
    status := .proven, prop := ``P148, thm := some ``p148 },
  { id := "numberscov-complex-s150", juliaFile := "base/complex.jl"
    juliaFns := ["isinteger(z::Complex)"]
    statement := "isinteger(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:150; source equation or documented Complex invariant"
    status := .proven, prop := ``P150, thm := some ``p150 },
  { id := "numberscov-complex-s151", juliaFile := "base/complex.jl"
    juliaFns := ["isfinite(z::Complex)"]
    statement := "isfinite(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:151; source equation or documented Complex invariant"
    status := .proven, prop := ``P151, thm := some ``p151 },
  { id := "numberscov-complex-s152", juliaFile := "base/complex.jl"
    juliaFns := ["isnan(z::Complex)"]
    statement := "isnan(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:152; source equation or documented Complex invariant"
    status := .proven, prop := ``P152, thm := some ``p152 },
  { id := "numberscov-complex-s153", juliaFile := "base/complex.jl"
    juliaFns := ["isinf(z::Complex)"]
    statement := "isinf(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:153; source equation or documented Complex invariant"
    status := .proven, prop := ``P153, thm := some ``p153 },
  { id := "numberscov-complex-s154", juliaFile := "base/complex.jl"
    juliaFns := ["iszero(z::Complex)"]
    statement := "iszero(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:154; source equation or documented Complex invariant"
    status := .proven, prop := ``P154, thm := some ``p154 },
  { id := "numberscov-complex-s155", juliaFile := "base/complex.jl"
    juliaFns := ["isone(z::Complex)"]
    statement := "isone(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:155; source equation or documented Complex invariant"
    status := .proven, prop := ``P155, thm := some ``p155 },
  { id := "numberscov-complex-s168", juliaFile := "base/complex.jl"
    juliaFns := ["complex(z::Complex)"]
    statement := "complex(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:168; source equation or documented Complex invariant"
    status := .proven, prop := ``P168, thm := some ``p168 },
  { id := "numberscov-complex-s169", juliaFile := "base/complex.jl"
    juliaFns := ["complex(x::Real)"]
    statement := "complex(x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:169; source equation or documented Complex invariant"
    status := .proven, prop := ``P169, thm := some ``p169 },
  { id := "numberscov-complex-s170", juliaFile := "base/complex.jl"
    juliaFns := ["complex(x::Real, y::Real)"]
    statement := "complex(x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:170; source equation or documented Complex invariant"
    status := .proven, prop := ``P170, thm := some ``p170 },
  { id := "numberscov-complex-s190", juliaFile := "base/complex.jl"
    juliaFns := ["complex(::Type{T}) where {T<:Real}"]
    statement := "complex(::Type{T}) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:190; source equation or documented Complex invariant"
    status := .proven, prop := ``P190, thm := some ``p190 },
  { id := "numberscov-complex-s191", juliaFile := "base/complex.jl"
    juliaFns := ["complex(::Type{Complex{T}}) where {T<:Real}"]
    statement := "complex(::Type{Complex{T}}) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:191; source equation or documented Complex invariant"
    status := .proven, prop := ``P191, thm := some ``p191 },
  { id := "numberscov-complex-s192", juliaFile := "base/complex.jl"
    juliaFns := ["complex(::Type{Union{}})"]
    statement := "complex(::Type{Union{}}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:192; source equation or documented Complex invariant"
    status := .proven, prop := ``P192, thm := some ``p192 },
  { id := "numberscov-complex-s195", juliaFile := "base/complex.jl"
    juliaFns := ["complex(::Type{Union{}}, slurp...)"]
    statement := "complex(::Type{Union{}}, slurp...) follows its Julia source body for every allowed input."
    source := "base/complex.jl:195; source equation or documented Complex invariant"
    status := .proven, prop := ``P195, thm := some ``p195 },
  { id := "numberscov-complex-s197", juliaFile := "base/complex.jl"
    juliaFns := ["flipsign(x::Complex, y::Real)"]
    statement := "flipsign(x::Complex, y::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:197; source equation or documented Complex invariant"
    status := .proven, prop := ``P197, thm := some ``p197 },
  { id := "numberscov-complex-s199", juliaFile := "base/complex.jl"
    juliaFns := ["show(io::IO, z::Complex)"]
    statement := "show(io::IO, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:199-218; source equation or documented Complex invariant"
    status := .proven, prop := ``P199, thm := some ``p199 },
  { id := "numberscov-complex-s219", juliaFile := "base/complex.jl"
    juliaFns := ["show(io::IO, z::Complex{Bool})"]
    statement := "show(io::IO, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:219-220; source equation or documented Complex invariant"
    status := .proven, prop := ``P219, thm := some ``p219 },
  { id := "numberscov-complex-s222", juliaFile := "base/complex.jl"
    juliaFns := ["show_unquoted(io::IO, z::Complex, ::Int, prec::Int)"]
    statement := "show_unquoted(io::IO, z::Complex, ::Int, prec::Int) follows its Julia source body for every allowed input."
    source := "base/complex.jl:222-230; source equation or documented Complex invariant"
    status := .proven, prop := ``P222, thm := some ``p222 },
  { id := "numberscov-complex-s232", juliaFile := "base/complex.jl"
    juliaFns := ["read(s::IO, ::Type{Complex{T}}) where T<:Real"]
    statement := "read(s::IO, ::Type{Complex{T}}) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:232-236; source equation or documented Complex invariant"
    status := .proven, prop := ``P232, thm := some ``p232 },
  { id := "numberscov-complex-s237", juliaFile := "base/complex.jl"
    juliaFns := ["write(s::IO, z::Complex)"]
    statement := "write(s::IO, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:237-239; source equation or documented Complex invariant"
    status := .proven, prop := ``P237, thm := some ``p237 },
  { id := "numberscov-complex-s242", juliaFile := "base/complex.jl"
    juliaFns := ["bswap(z::Complex)"]
    statement := "bswap(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:242; source equation or documented Complex invariant"
    status := .proven, prop := ``P242, thm := some ``p242 },
  { id := "numberscov-complex-s246", juliaFile := "base/complex.jl"
    juliaFns := ["==(z::Complex, w::Complex)"]
    statement := "==(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:246; source equation or documented Complex invariant"
    status := .proven, prop := ``P246, thm := some ``p246 },
  { id := "numberscov-complex-s248", juliaFile := "base/complex.jl"
    juliaFns := ["==(x::Real, z::Complex)"]
    statement := "==(x::Real, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:248; source equation or documented Complex invariant"
    status := .proven, prop := ``P248, thm := some ``p248 },
  { id := "numberscov-complex-s252", juliaFile := "base/complex.jl"
    juliaFns := ["isequal(z::Real, w::Complex)"]
    statement := "isequal(z::Real, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:252; source equation or documented Complex invariant"
    status := .proven, prop := ``P252, thm := some ``p252 },
  { id := "numberscov-complex-s254", juliaFile := "base/complex.jl"
    juliaFns := ["in(x::Complex, r::AbstractRange{<:Real})"]
    statement := "in(x::Complex, r::AbstractRange{<:Real}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:254; source equation or documented Complex invariant"
    status := .proven, prop := ``P254, thm := some ``p254 },
  { id := "numberscov-complex-s282", juliaFile := "base/complex.jl"
    juliaFns := ["abs2(z::Complex)"]
    statement := "abs2(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:282; source equation or documented Complex invariant"
    status := .proven, prop := ``P282, thm := some ``p282 },
  { id := "numberscov-complex-s283", juliaFile := "base/complex.jl"
    juliaFns := ["inv(z::Complex)"]
    statement := "inv(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:283-287; source equation or documented Complex invariant"
    status := .proven, prop := ``P283, thm := some ``p283 },
  { id := "numberscov-complex-s288", juliaFile := "base/complex.jl"
    juliaFns := ["inv(z::Complex{<:Integer})"]
    statement := "inv(z::Complex{<:Integer}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:288; source equation or documented Complex invariant"
    status := .proven, prop := ``P288, thm := some ``p288 },
  { id := "numberscov-complex-s290", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex)"]
    statement := "+(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:290; source equation or documented Complex invariant"
    status := .proven, prop := ``P290, thm := some ``p290 },
  { id := "numberscov-complex-s291", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex)"]
    statement := "-(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:291; source equation or documented Complex invariant"
    status := .proven, prop := ``P291, thm := some ``p291 },
  { id := "numberscov-complex-s292", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex, w::Complex)"]
    statement := "+(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:292; source equation or documented Complex invariant"
    status := .proven, prop := ``P292, thm := some ``p292 },
  { id := "numberscov-complex-s293", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex, w::Complex)"]
    statement := "-(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:293; source equation or documented Complex invariant"
    status := .proven, prop := ``P293, thm := some ``p293 },
  { id := "numberscov-complex-s294", juliaFile := "base/complex.jl"
    juliaFns := ["*(z::Complex, w::Complex)"]
    statement := "*(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:294-295; source equation or documented Complex invariant"
    status := .proven, prop := ``P294, thm := some ``p294 },
  { id := "numberscov-complex-s297", juliaFile := "base/complex.jl"
    juliaFns := ["-%(z::Complex)"]
    statement := "-%(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:297; source equation or documented Complex invariant"
    status := .proven, prop := ``P297, thm := some ``p297 },
  { id := "numberscov-complex-s298", juliaFile := "base/complex.jl"
    juliaFns := ["+%(z::Complex, w::Complex)"]
    statement := "+%(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:298; source equation or documented Complex invariant"
    status := .proven, prop := ``P298, thm := some ``p298 },
  { id := "numberscov-complex-s299", juliaFile := "base/complex.jl"
    juliaFns := ["-%(z::Complex, w::Complex)"]
    statement := "-%(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:299; source equation or documented Complex invariant"
    status := .proven, prop := ``P299, thm := some ``p299 },
  { id := "numberscov-complex-s300", juliaFile := "base/complex.jl"
    juliaFns := ["*%(z::Complex, w::Complex)"]
    statement := "*%(z::Complex, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:300-301; source equation or documented Complex invariant"
    status := .proven, prop := ``P300, thm := some ``p300 },
  { id := "numberscov-complex-s303", juliaFile := "base/complex.jl"
    juliaFns := ["_mulsub(a, b, c)"]
    statement := "_mulsub(a, b, c) follows its Julia source body for every allowed input."
    source := "base/complex.jl:303; source equation or documented Complex invariant"
    status := .proven, prop := ``P303, thm := some ``p303 },
  { id := "numberscov-complex-s304", juliaFile := "base/complex.jl"
    juliaFns := ["_mulsub(a::T, b::T, c::T) where {T<:Real}"]
    statement := "_mulsub(a::T, b::T, c::T) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:304; source equation or documented Complex invariant"
    status := .proven, prop := ``P304, thm := some ``p304 },
  { id := "numberscov-complex-s311", juliaFile := "base/complex.jl"
    juliaFns := ["+(x::Bool, z::Complex{Bool})"]
    statement := "+(x::Bool, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:311; source equation or documented Complex invariant"
    status := .proven, prop := ``P311, thm := some ``p311 },
  { id := "numberscov-complex-s312", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex{Bool}, x::Bool)"]
    statement := "+(z::Complex{Bool}, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:312; source equation or documented Complex invariant"
    status := .proven, prop := ``P312, thm := some ``p312 },
  { id := "numberscov-complex-s313", juliaFile := "base/complex.jl"
    juliaFns := ["-(x::Bool, z::Complex{Bool})"]
    statement := "-(x::Bool, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:313; source equation or documented Complex invariant"
    status := .proven, prop := ``P313, thm := some ``p313 },
  { id := "numberscov-complex-s314", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex{Bool}, x::Bool)"]
    statement := "-(z::Complex{Bool}, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:314; source equation or documented Complex invariant"
    status := .proven, prop := ``P314, thm := some ``p314 },
  { id := "numberscov-complex-s315", juliaFile := "base/complex.jl"
    juliaFns := ["*(x::Bool, z::Complex{Bool})"]
    statement := "*(x::Bool, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:315; source equation or documented Complex invariant"
    status := .proven, prop := ``P315, thm := some ``p315 },
  { id := "numberscov-complex-s316", juliaFile := "base/complex.jl"
    juliaFns := ["*(z::Complex{Bool}, x::Bool)"]
    statement := "*(z::Complex{Bool}, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:316; source equation or documented Complex invariant"
    status := .proven, prop := ``P316, thm := some ``p316 },
  { id := "numberscov-complex-s318", juliaFile := "base/complex.jl"
    juliaFns := ["+(x::Bool, z::Complex)"]
    statement := "+(x::Bool, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:318; source equation or documented Complex invariant"
    status := .proven, prop := ``P318, thm := some ``p318 },
  { id := "numberscov-complex-s319", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex, x::Bool)"]
    statement := "+(z::Complex, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:319; source equation or documented Complex invariant"
    status := .proven, prop := ``P319, thm := some ``p319 },
  { id := "numberscov-complex-s320", juliaFile := "base/complex.jl"
    juliaFns := ["-(x::Bool, z::Complex)"]
    statement := "-(x::Bool, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:320; source equation or documented Complex invariant"
    status := .proven, prop := ``P320, thm := some ``p320 },
  { id := "numberscov-complex-s321", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex, x::Bool)"]
    statement := "-(z::Complex, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:321; source equation or documented Complex invariant"
    status := .proven, prop := ``P321, thm := some ``p321 },
  { id := "numberscov-complex-s323", juliaFile := "base/complex.jl"
    juliaFns := ["*(z::Complex, x::Bool)"]
    statement := "*(z::Complex, x::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:323; source equation or documented Complex invariant"
    status := .proven, prop := ``P323, thm := some ``p323 },
  { id := "numberscov-complex-s325", juliaFile := "base/complex.jl"
    juliaFns := ["+(x::Real, z::Complex{Bool})"]
    statement := "+(x::Real, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:325; source equation or documented Complex invariant"
    status := .proven, prop := ``P325, thm := some ``p325 },
  { id := "numberscov-complex-s326", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex{Bool}, x::Real)"]
    statement := "+(z::Complex{Bool}, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:326; source equation or documented Complex invariant"
    status := .proven, prop := ``P326, thm := some ``p326 },
  { id := "numberscov-complex-s327", juliaFile := "base/complex.jl"
    juliaFns := ["-(x::Real, z::Complex{Bool})"]
    statement := "-(x::Real, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:327-331; source equation or documented Complex invariant"
    status := .proven, prop := ``P327, thm := some ``p327 },
  { id := "numberscov-complex-s332", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex{Bool}, x::Real)"]
    statement := "-(z::Complex{Bool}, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:332; source equation or documented Complex invariant"
    status := .proven, prop := ``P332, thm := some ``p332 },
  { id := "numberscov-complex-s333", juliaFile := "base/complex.jl"
    juliaFns := ["*(x::Real, z::Complex{Bool})"]
    statement := "*(x::Real, z::Complex{Bool}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:333; source equation or documented Complex invariant"
    status := .proven, prop := ``P333, thm := some ``p333 },
  { id := "numberscov-complex-s334", juliaFile := "base/complex.jl"
    juliaFns := ["*(z::Complex{Bool}, x::Real)"]
    statement := "*(z::Complex{Bool}, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:334; source equation or documented Complex invariant"
    status := .proven, prop := ``P334, thm := some ``p334 },
  { id := "numberscov-complex-s337", juliaFile := "base/complex.jl"
    juliaFns := ["+(x::Real, z::Complex)"]
    statement := "+(x::Real, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:337; source equation or documented Complex invariant"
    status := .proven, prop := ``P337, thm := some ``p337 },
  { id := "numberscov-complex-s338", juliaFile := "base/complex.jl"
    juliaFns := ["+(z::Complex, x::Real)"]
    statement := "+(z::Complex, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:338; source equation or documented Complex invariant"
    status := .proven, prop := ``P338, thm := some ``p338 },
  { id := "numberscov-complex-s339", juliaFile := "base/complex.jl"
    juliaFns := ["-(x::Real, z::Complex)"]
    statement := "-(x::Real, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:339-343; source equation or documented Complex invariant"
    status := .proven, prop := ``P339, thm := some ``p339 },
  { id := "numberscov-complex-s344", juliaFile := "base/complex.jl"
    juliaFns := ["-(z::Complex, x::Real)"]
    statement := "-(z::Complex, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:344; source equation or documented Complex invariant"
    status := .proven, prop := ``P344, thm := some ``p344 },
  { id := "numberscov-complex-s345", juliaFile := "base/complex.jl"
    juliaFns := ["*(x::Real, z::Complex)"]
    statement := "*(x::Real, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:345; source equation or documented Complex invariant"
    status := .proven, prop := ``P345, thm := some ``p345 },
  { id := "numberscov-complex-s346", juliaFile := "base/complex.jl"
    juliaFns := ["*(z::Complex, x::Real)"]
    statement := "*(z::Complex, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:346; source equation or documented Complex invariant"
    status := .proven, prop := ``P346, thm := some ``p346 },
  { id := "numberscov-complex-s348", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(x::Real, z::Complex, y::Union{Real,Complex})"]
    statement := "muladd(x::Real, z::Complex, y::Union{Real,Complex}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:348; source equation or documented Complex invariant"
    status := .proven, prop := ``P348, thm := some ``p348 },
  { id := "numberscov-complex-s349", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(z::Complex, x::Real, y::Real)"]
    statement := "muladd(z::Complex, x::Real, y::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:349; source equation or documented Complex invariant"
    status := .proven, prop := ``P349, thm := some ``p349 },
  { id := "numberscov-complex-s350", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(z::Complex, x::Real, w::Complex)"]
    statement := "muladd(z::Complex, x::Real, w::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:350-351; source equation or documented Complex invariant"
    status := .proven, prop := ``P350, thm := some ``p350 },
  { id := "numberscov-complex-s352", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(x::Real, y::Real, z::Complex)"]
    statement := "muladd(x::Real, y::Real, z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:352; source equation or documented Complex invariant"
    status := .proven, prop := ``P352, thm := some ``p352 },
  { id := "numberscov-complex-s353", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(z::Complex, w::Complex, x::Real)"]
    statement := "muladd(z::Complex, w::Complex, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:353-355; source equation or documented Complex invariant"
    status := .proven, prop := ``P353, thm := some ``p353 },
  { id := "numberscov-complex-s357", juliaFile := "base/complex.jl"
    juliaFns := ["/(a::R, z::S) where {R<:Real,S<:Complex}"]
    statement := "/(a::R, z::S) where {R<:Real,S<:Complex} follows its Julia source body for every allowed input."
    source := "base/complex.jl:357; source equation or documented Complex invariant"
    status := .proven, prop := ``P357, thm := some ``p357 },
  { id := "numberscov-complex-s358", juliaFile := "base/complex.jl"
    juliaFns := ["/(z::Complex, x::Real)"]
    statement := "/(z::Complex, x::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:358; source equation or documented Complex invariant"
    status := .proven, prop := ``P358, thm := some ``p358 },
  { id := "numberscov-complex-s360", juliaFile := "base/complex.jl"
    juliaFns := ["/(a::Complex{T}, b::Complex{T}) where T<:Real"]
    statement := "/(a::Complex{T}, b::Complex{T}) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:360-377; source equation or documented Complex invariant"
    status := .proven, prop := ``P360, thm := some ``p360 },
  { id := "numberscov-complex-s379", juliaFile := "base/complex.jl"
    juliaFns := ["/(z::Complex{T}, w::Complex{T}) where {T<:Union{Float16,Float32}}"]
    statement := "/(z::Complex{T}, w::Complex{T}) where {T<:Union{Float16,Float32}} follows its Julia source body for every allowed input."
    source := "base/complex.jl:379-392; source equation or documented Complex invariant"
    status := .proven, prop := ``P379, thm := some ``p379 },
  { id := "numberscov-complex-s424", juliaFile := "base/complex.jl"
    juliaFns := ["cdiv(a::Float64, b::Float64, c::Float64, d::Float64)"]
    statement := "cdiv(a::Float64, b::Float64, c::Float64, d::Float64) follows its Julia source body for every allowed input."
    source := "base/complex.jl:424-432; source equation or documented Complex invariant"
    status := .proven, prop := ``P424, thm := some ``p424 },
  { id := "numberscov-complex-s433", juliaFile := "base/complex.jl"
    juliaFns := ["scaling_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64)"]
    statement := "scaling_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64) follows its Julia source body for every allowed input."
    source := "base/complex.jl:433-438; source equation or documented Complex invariant"
    status := .proven, prop := ``P433, thm := some ``p433 },
  { id := "numberscov-complex-s439", juliaFile := "base/complex.jl"
    juliaFns := ["scaleargs_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64)"]
    statement := "scaleargs_cdiv(a::Float64, b::Float64, c::Float64, d::Float64, ab::Float64, cd::Float64) follows its Julia source body for every allowed input."
    source := "base/complex.jl:439-459; source equation or documented Complex invariant"
    status := .proven, prop := ``P439, thm := some ``p439 },
  { id := "numberscov-complex-s476", juliaFile := "base/complex.jl"
    juliaFns := ["inv(z::Complex{T}) where T<:Union{Float16,Float32}"]
    statement := "inv(z::Complex{T}) where T<:Union{Float16,Float32} follows its Julia source body for every allowed input."
    source := "base/complex.jl:476-481; source equation or documented Complex invariant"
    status := .proven, prop := ``P476, thm := some ``p476 },
  { id := "numberscov-complex-s482", juliaFile := "base/complex.jl"
    juliaFns := ["inv(w::ComplexF64)"]
    statement := "inv(w::ComplexF64) follows its Julia source body for every allowed input."
    source := "base/complex.jl:482-510; source equation or documented Complex invariant"
    status := .proven, prop := ``P482, thm := some ``p482 },
  { id := "numberscov-complex-s511", juliaFile := "base/complex.jl"
    juliaFns := ["robust_cinv(c::Float64, d::Float64)"]
    statement := "robust_cinv(c::Float64, d::Float64) follows its Julia source body for every allowed input."
    source := "base/complex.jl:511-517; source equation or documented Complex invariant"
    status := .proven, prop := ``P511, thm := some ``p511 },
  { id := "numberscov-complex-s519", juliaFile := "base/complex.jl"
    juliaFns := ["ssqs(x::T, y::T) where T<:Real"]
    statement := "ssqs(x::T, y::T) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:519-531; source equation or documented Complex invariant"
    status := .proven, prop := ``P519, thm := some ``p519 },
  { id := "numberscov-complex-s587", juliaFile := "base/complex.jl"
    juliaFns := ["cis(theta::Real)"]
    statement := "cis(theta::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:587-590; source equation or documented Complex invariant"
    status := .proven, prop := ``P587, thm := some ``p587 },
  { id := "numberscov-complex-s592", juliaFile := "base/complex.jl"
    juliaFns := ["cis(z::Complex)"]
    statement := "cis(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:592-596; source equation or documented Complex invariant"
    status := .proven, prop := ``P592, thm := some ``p592 },
  { id := "numberscov-complex-s618", juliaFile := "base/complex.jl"
    juliaFns := ["cispi(theta::Real)"]
    statement := "cispi(theta::Real) follows its Julia source body for every allowed input."
    source := "base/complex.jl:618; source equation or documented Complex invariant"
    status := .proven, prop := ``P618, thm := some ``p618 },
  { id := "numberscov-complex-s620", juliaFile := "base/complex.jl"
    juliaFns := ["cispi(z::Complex)"]
    statement := "cispi(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:620-624; source equation or documented Complex invariant"
    status := .proven, prop := ``P620, thm := some ``p620 },
  { id := "numberscov-complex-s651", juliaFile := "base/complex.jl"
    juliaFns := ["angle(z::Complex)"]
    statement := "angle(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:651; source equation or documented Complex invariant"
    status := .proven, prop := ``P651, thm := some ``p651 },
  { id := "numberscov-complex-s653", juliaFile := "base/complex.jl"
    juliaFns := ["log(z::Complex)"]
    statement := "log(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:653-674; source equation or documented Complex invariant"
    status := .proven, prop := ``P653, thm := some ``p653 },
  { id := "numberscov-complex-s695", juliaFile := "base/complex.jl"
    juliaFns := ["log10(z::Complex)"]
    statement := "log10(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:695-698; source equation or documented Complex invariant"
    status := .proven, prop := ``P695, thm := some ``p695 },
  { id := "numberscov-complex-s699", juliaFile := "base/complex.jl"
    juliaFns := ["log2(z::Complex)"]
    statement := "log2(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:699-702; source equation or documented Complex invariant"
    status := .proven, prop := ``P699, thm := some ``p699 },
  { id := "numberscov-complex-s704", juliaFile := "base/complex.jl"
    juliaFns := ["exp(z::Complex)"]
    statement := "exp(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:704-725; source equation or documented Complex invariant"
    status := .proven, prop := ``P704, thm := some ``p704 },
  { id := "numberscov-complex-s727", juliaFile := "base/complex.jl"
    juliaFns := ["expm1(z::Complex{T}) where T<:Real"]
    statement := "expm1(z::Complex{T}) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:727-755; source equation or documented Complex invariant"
    status := .proven, prop := ``P727, thm := some ``p727 },
  { id := "numberscov-complex-s757", juliaFile := "base/complex.jl"
    juliaFns := ["log1p(z::Complex{T}) where T"]
    statement := "log1p(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:757-773; source equation or documented Complex invariant"
    status := .proven, prop := ``P757, thm := some ``p757 },
  { id := "numberscov-complex-s775", juliaFile := "base/complex.jl"
    juliaFns := ["exp2(z::Complex{T}) where T"]
    statement := "exp2(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:775-781; source equation or documented Complex invariant"
    status := .proven, prop := ``P775, thm := some ``p775 },
  { id := "numberscov-complex-s783", juliaFile := "base/complex.jl"
    juliaFns := ["exp10(z::Complex{T}) where T"]
    statement := "exp10(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:783-789; source equation or documented Complex invariant"
    status := .proven, prop := ``P783, thm := some ``p783 },
  { id := "numberscov-complex-s792", juliaFile := "base/complex.jl"
    juliaFns := ["_cpow(z::Union{T,Complex{T}}, p::Union{T,Complex{T}}) where T"]
    statement := "_cpow(z::Union{T,Complex{T}}, p::Union{T,Complex{T}}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:792-881; source equation or documented Complex invariant"
    status := .proven, prop := ``P792, thm := some ``p792 },
  { id := "numberscov-complex-s882", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex{T}, p::Complex{T}) where T<:Real"]
    statement := "^(z::Complex{T}, p::Complex{T}) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:882; source equation or documented Complex invariant"
    status := .proven, prop := ``P882, thm := some ``p882 },
  { id := "numberscov-complex-s883", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex{T}, p::T) where T<:Real"]
    statement := "^(z::Complex{T}, p::T) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:883; source equation or documented Complex invariant"
    status := .proven, prop := ``P883, thm := some ``p883 },
  { id := "numberscov-complex-s884", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::T, p::Complex{T}) where T<:Real"]
    statement := "^(z::T, p::Complex{T}) where T<:Real follows its Julia source body for every allowed input."
    source := "base/complex.jl:884; source equation or documented Complex invariant"
    status := .proven, prop := ``P884, thm := some ``p884 },
  { id := "numberscov-complex-s886", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex, n::Bool)"]
    statement := "^(z::Complex, n::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:886; source equation or documented Complex invariant"
    status := .proven, prop := ``P886, thm := some ``p886 },
  { id := "numberscov-complex-s887", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex, n::Integer)"]
    statement := "^(z::Complex, n::Integer) follows its Julia source body for every allowed input."
    source := "base/complex.jl:887; source equation or documented Complex invariant"
    status := .proven, prop := ``P887, thm := some ``p887 },
  { id := "numberscov-complex-s889", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex{<:AbstractFloat}, n::Bool)"]
    statement := "^(z::Complex{<:AbstractFloat}, n::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:889; source equation or documented Complex invariant"
    status := .proven, prop := ``P889, thm := some ``p889 },
  { id := "numberscov-complex-s890", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex{<:Integer}, n::Bool)"]
    statement := "^(z::Complex{<:Integer}, n::Bool) follows its Julia source body for every allowed input."
    source := "base/complex.jl:890; source equation or documented Complex invariant"
    status := .proven, prop := ``P890, thm := some ``p890 },
  { id := "numberscov-complex-s896", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::Complex{T}, p::S) where {T<:Real,S<:Real}"]
    statement := "^(z::Complex{T}, p::S) where {T<:Real,S<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:896-899; source equation or documented Complex invariant"
    status := .proven, prop := ``P896, thm := some ``p896 },
  { id := "numberscov-complex-s900", juliaFile := "base/complex.jl"
    juliaFns := ["^(z::T, p::Complex{S}) where {T<:Real,S<:Real}"]
    statement := "^(z::T, p::Complex{S}) where {T<:Real,S<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:900-903; source equation or documented Complex invariant"
    status := .proven, prop := ``P900, thm := some ``p900 },
  { id := "numberscov-complex-s905", juliaFile := "base/complex.jl"
    juliaFns := ["sin(z::Complex{T}) where T"]
    statement := "sin(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:905-920; source equation or documented Complex invariant"
    status := .proven, prop := ``P905, thm := some ``p905 },
  { id := "numberscov-complex-s923", juliaFile := "base/complex.jl"
    juliaFns := ["cos(z::Complex{T}) where T"]
    statement := "cos(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:923-940; source equation or documented Complex invariant"
    status := .proven, prop := ``P923, thm := some ``p923 },
  { id := "numberscov-complex-s943", juliaFile := "base/complex.jl"
    juliaFns := ["tan(z::Complex)"]
    statement := "tan(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:943-947; source equation or documented Complex invariant"
    status := .proven, prop := ``P943, thm := some ``p943 },
  { id := "numberscov-complex-s949", juliaFile := "base/complex.jl"
    juliaFns := ["asin(z::Complex)"]
    statement := "asin(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:949-961; source equation or documented Complex invariant"
    status := .proven, prop := ``P949, thm := some ``p949 },
  { id := "numberscov-complex-s963", juliaFile := "base/complex.jl"
    juliaFns := ["acos(z::Complex)"]
    statement := "acos(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:963-984; source equation or documented Complex invariant"
    status := .proven, prop := ``P963, thm := some ``p963 },
  { id := "numberscov-complex-s986", juliaFile := "base/complex.jl"
    juliaFns := ["atan(z::Complex)"]
    statement := "atan(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:986-989; source equation or documented Complex invariant"
    status := .proven, prop := ``P986, thm := some ``p986 },
  { id := "numberscov-complex-s991", juliaFile := "base/complex.jl"
    juliaFns := ["sinh(z::Complex)"]
    statement := "sinh(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:991-995; source equation or documented Complex invariant"
    status := .proven, prop := ``P991, thm := some ``p991 },
  { id := "numberscov-complex-s997", juliaFile := "base/complex.jl"
    juliaFns := ["cosh(z::Complex)"]
    statement := "cosh(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:997-1000; source equation or documented Complex invariant"
    status := .proven, prop := ``P997, thm := some ``p997 },
  { id := "numberscov-complex-s1002", juliaFile := "base/complex.jl"
    juliaFns := ["tanh(z::Complex{T}) where T"]
    statement := "tanh(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:1002-1022; source equation or documented Complex invariant"
    status := .proven, prop := ``P1002, thm := some ``p1002 },
  { id := "numberscov-complex-s1024", juliaFile := "base/complex.jl"
    juliaFns := ["asinh(z::Complex)"]
    statement := "asinh(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1024-1027; source equation or documented Complex invariant"
    status := .proven, prop := ``P1024, thm := some ``p1024 },
  { id := "numberscov-complex-s1029", juliaFile := "base/complex.jl"
    juliaFns := ["acosh(z::Complex)"]
    statement := "acosh(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1029-1046; source equation or documented Complex invariant"
    status := .proven, prop := ``P1029, thm := some ``p1029 },
  { id := "numberscov-complex-s1048", juliaFile := "base/complex.jl"
    juliaFns := ["atanh(z::Complex{T}) where T"]
    statement := "atanh(z::Complex{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:1048-1089; source equation or documented Complex invariant"
    status := .proven, prop := ``P1048, thm := some ``p1048 },
  { id := "numberscov-complex-s1123", juliaFile := "base/complex.jl"
    juliaFns := ["round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...)"]
    statement := "round(z::Complex, rr::RoundingMode=RoundNearest, ri::RoundingMode=rr; kwargs...) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1123-1126; source equation or documented Complex invariant"
    status := .proven, prop := ``P1123, thm := some ``p1123 },
  { id := "numberscov-complex-s1129", juliaFile := "base/complex.jl"
    juliaFns := ["float(z::Complex{<:AbstractFloat})"]
    statement := "float(z::Complex{<:AbstractFloat}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1129; source equation or documented Complex invariant"
    status := .proven, prop := ``P1129, thm := some ``p1129 },
  { id := "numberscov-complex-s1130", juliaFile := "base/complex.jl"
    juliaFns := ["float(z::Complex)"]
    statement := "float(z::Complex) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1130; source equation or documented Complex invariant"
    status := .proven, prop := ``P1130, thm := some ``p1130 },
  { id := "numberscov-complex-s1132", juliaFile := "base/complex.jl"
    juliaFns := ["big(::Type{Complex{T}}) where {T<:Real}"]
    statement := "big(::Type{Complex{T}}) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:1132; source equation or documented Complex invariant"
    status := .proven, prop := ``P1132, thm := some ``p1132 },
  { id := "numberscov-complex-s1133", juliaFile := "base/complex.jl"
    juliaFns := ["big(z::Complex{T}) where {T<:Real}"]
    statement := "big(z::Complex{T}) where {T<:Real} follows its Julia source body for every allowed input."
    source := "base/complex.jl:1133; source equation or documented Complex invariant"
    status := .proven, prop := ``P1133, thm := some ``p1133 },
  { id := "numberscov-complex-s1153", juliaFile := "base/complex.jl"
    juliaFns := ["complex(A::AbstractArray{<:Complex})"]
    statement := "complex(A::AbstractArray{<:Complex}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1153; source equation or documented Complex invariant"
    status := .proven, prop := ``P1153, thm := some ``p1153 },
  { id := "numberscov-complex-s1155", juliaFile := "base/complex.jl"
    juliaFns := ["complex(A::AbstractArray{T}) where T"]
    statement := "complex(A::AbstractArray{T}) where T follows its Julia source body for every allowed input."
    source := "base/complex.jl:1155-1160; source equation or documented Complex invariant"
    status := .proven, prop := ``P1155, thm := some ``p1155 },
  { id := "numberscov-complex-s1164", juliaFile := "base/complex.jl"
    juliaFns := ["eps(z::Complex{<:AbstractFloat})"]
    statement := "eps(z::Complex{<:AbstractFloat}) follows its Julia source body for every allowed input."
    source := "base/complex.jl:1164; source equation or documented Complex invariant"
    status := .proven, prop := ``P1164, thm := some ``p1164 },
  { id := "numberscov-complex-s1166", juliaFile := "base/complex.jl"
    juliaFns := ["eps(::Type{Complex{T}}) where {T<:AbstractFloat}"]
    statement := "eps(::Type{Complex{T}}) where {T<:AbstractFloat} follows its Julia source body for every allowed input."
    source := "base/complex.jl:1166; source equation or documented Complex invariant"
    status := .proven, prop := ``P1166, thm := some ``p1166 }
]

end JuliaLean.NumbersCov.Rows.Complex
